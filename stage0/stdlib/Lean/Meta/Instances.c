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
lean_object* l_Lean_stringToMessageData(lean_object*);
extern lean_object* l_Lean_instInhabitedSynthNormMemoSlot_default;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
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
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
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
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
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
lean_object* l_Lean_CollectFVars_State_ofFVarSet(lean_object*, lean_object*);
lean_object* l_Lean_Expr_collectFVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Expr_fvarId_x21(lean_object*);
lean_object* l_Lean_FVarId_getBinderInfo___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_State_add(lean_object*, lean_object*);
lean_object* l_Lean_CollectFVars_State_addDependencies(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* l_Lean_FVarId_getDecl___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_LocalDecl_ppAsBinder(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
extern lean_object* l_Lean_MessageData_nil;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__0 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__0_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__1 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__1_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "unsolvedGoals"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__2 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__2_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "synthPlaceholder"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__3 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__3_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "lean"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__4 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__4_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "inductionWithNoAlts"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__5 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__5_value;
static const lean_string_object l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "_namedError"};
static const lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__6 = (const lean_object*)&l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__6_value;
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "argument "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__0_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ": `"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__2_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1;
static const lean_ctor_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0_value),((lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2_value)}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_value;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "This instance has "};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " argument"};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = " that cannot be inferred using typeclass synthesis. Specifically\n"};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 176, .m_capacity = 176, .m_length = 175, .m_data = "\n\nThese arguments are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they cannot be inferred using typeclass synthesis."};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12_value;
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object*, uint8_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_883_ = lean_unsigned_to_nat(179u);
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
size_t v___x_2107_; size_t v___x_2108_; uint8_t v___x_2109_; 
v___x_2107_ = ((size_t)0ULL);
v___x_2108_ = lean_usize_of_nat(v___x_2105_);
v___x_2109_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_2103_, v_as_2102_, v___x_2107_, v___x_2108_);
return v___x_2109_;
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
uint8_t v___x_22654__boxed_2315_; lean_object* v_res_2316_; 
v___x_22654__boxed_2315_ = lean_unbox(v___x_2307_);
v_res_2316_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2305_, v___x_2306_, v___x_22654__boxed_2315_, v_x_2308_, v_argTy_2309_, v___y_2310_, v___y_2311_, v___y_2312_, v___y_2313_);
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
size_t v___x_2494_; size_t v___x_2495_; lean_object* v___x_2496_; 
v___x_2494_ = ((size_t)0ULL);
v___x_2495_ = lean_usize_of_nat(v___x_2491_);
v___x_2496_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2442_, v_snd_2441_, v___x_2494_, v___x_2495_, v___x_2492_);
v___y_2450_ = v___x_2496_;
goto v___jp_2449_;
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object* v_fst_2497_, lean_object* v___x_2498_, lean_object* v_fst_2499_, lean_object* v_argVars_2500_, lean_object* v_snd_2501_, lean_object* v_next_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v_res_2508_; 
v_res_2508_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2497_, v___x_2498_, v_fst_2499_, v_argVars_2500_, v_snd_2501_, v_next_2502_, v___y_2503_, v___y_2504_, v___y_2505_, v___y_2506_);
lean_dec(v___y_2506_);
lean_dec_ref(v___y_2505_);
lean_dec(v___y_2504_);
lean_dec_ref(v___y_2503_);
lean_dec(v_snd_2501_);
lean_dec_ref(v_argVars_2500_);
lean_dec_ref(v_fst_2499_);
lean_dec_ref(v___x_2498_);
return v_res_2508_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v___x_2515_; lean_object* v_env_2516_; uint8_t v___x_2517_; lean_object* v_env_2518_; lean_object* v___x_2519_; lean_object* v_toCold_2520_; lean_object* v_mctx_2521_; lean_object* v_lctx_2522_; lean_object* v_options_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2515_ = lean_st_ref_get(v___y_2513_);
v_env_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc_ref(v_env_2516_);
lean_dec(v___x_2515_);
v___x_2517_ = 0;
v_env_2518_ = l_Lean_Environment_setRecordingDeps(v_env_2516_, v___x_2517_);
v___x_2519_ = lean_st_ref_get(v___y_2511_);
v_toCold_2520_ = lean_ctor_get(v___y_2512_, 0);
v_mctx_2521_ = lean_ctor_get(v___x_2519_, 0);
lean_inc_ref(v_mctx_2521_);
lean_dec(v___x_2519_);
v_lctx_2522_ = lean_ctor_get(v___y_2510_, 2);
v_options_2523_ = lean_ctor_get(v_toCold_2520_, 2);
lean_inc_ref(v_options_2523_);
lean_inc_ref(v_lctx_2522_);
v___x_2524_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2524_, 0, v_env_2518_);
lean_ctor_set(v___x_2524_, 1, v_mctx_2521_);
lean_ctor_set(v___x_2524_, 2, v_lctx_2522_);
lean_ctor_set(v___x_2524_, 3, v_options_2523_);
v___x_2525_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
lean_ctor_set(v___x_2525_, 1, v_msgData_2509_);
v___x_2526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2526_, 0, v___x_2525_);
return v___x_2526_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_, lean_object* v___y_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2527_, v___y_2528_, v___y_2529_, v___y_2530_, v___y_2531_);
lean_dec(v___y_2531_);
lean_dec_ref(v___y_2530_);
lean_dec(v___y_2529_);
lean_dec_ref(v___y_2528_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_, lean_object* v___y_2538_){
_start:
{
lean_object* v_ref_2540_; lean_object* v___x_2541_; lean_object* v_a_2542_; lean_object* v___x_2544_; uint8_t v_isShared_2545_; uint8_t v_isSharedCheck_2550_; 
v_ref_2540_ = lean_ctor_get(v___y_2537_, 2);
v___x_2541_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2534_, v___y_2535_, v___y_2536_, v___y_2537_, v___y_2538_);
v_a_2542_ = lean_ctor_get(v___x_2541_, 0);
v_isSharedCheck_2550_ = !lean_is_exclusive(v___x_2541_);
if (v_isSharedCheck_2550_ == 0)
{
v___x_2544_ = v___x_2541_;
v_isShared_2545_ = v_isSharedCheck_2550_;
goto v_resetjp_2543_;
}
else
{
lean_inc(v_a_2542_);
lean_dec(v___x_2541_);
v___x_2544_ = lean_box(0);
v_isShared_2545_ = v_isSharedCheck_2550_;
goto v_resetjp_2543_;
}
v_resetjp_2543_:
{
lean_object* v___x_2546_; lean_object* v___x_2548_; 
lean_inc(v_ref_2540_);
v___x_2546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2546_, 0, v_ref_2540_);
lean_ctor_set(v___x_2546_, 1, v_a_2542_);
if (v_isShared_2545_ == 0)
{
lean_ctor_set_tag(v___x_2544_, 1);
lean_ctor_set(v___x_2544_, 0, v___x_2546_);
v___x_2548_ = v___x_2544_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_, lean_object* v___y_2556_){
_start:
{
lean_object* v_res_2557_; 
v_res_2557_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2551_, v___y_2552_, v___y_2553_, v___y_2554_, v___y_2555_);
lean_dec(v___y_2555_);
lean_dec_ref(v___y_2554_);
lean_dec(v___y_2553_);
lean_dec_ref(v___y_2552_);
return v_res_2557_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2558_, size_t v_sz_2559_, size_t v_i_2560_, lean_object* v_bs_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_, lean_object* v___y_2565_){
_start:
{
uint8_t v___x_2567_; 
v___x_2567_ = lean_usize_dec_lt(v_i_2560_, v_sz_2559_);
if (v___x_2567_ == 0)
{
lean_object* v___x_2568_; 
v___x_2568_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2568_, 0, v_bs_2561_);
return v___x_2568_;
}
else
{
lean_object* v___x_2569_; lean_object* v_v_2570_; lean_object* v___x_2571_; lean_object* v_bs_x27_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2569_ = l_Lean_instInhabitedExpr;
v_v_2570_ = lean_array_uget(v_bs_2561_, v_i_2560_);
v___x_2571_ = lean_unsigned_to_nat(0u);
v_bs_x27_2572_ = lean_array_uset(v_bs_2561_, v_i_2560_, v___x_2571_);
v___x_2573_ = lean_array_get_borrowed(v___x_2569_, v_fst_2558_, v_v_2570_);
lean_dec(v_v_2570_);
lean_inc(v___y_2565_);
lean_inc_ref(v___y_2564_);
lean_inc(v___y_2563_);
lean_inc_ref(v___y_2562_);
lean_inc(v___x_2573_);
v___x_2574_ = lean_infer_type(v___x_2573_, v___y_2562_, v___y_2563_, v___y_2564_, v___y_2565_);
if (lean_obj_tag(v___x_2574_) == 0)
{
lean_object* v_a_2575_; lean_object* v___x_2576_; 
v_a_2575_ = lean_ctor_get(v___x_2574_, 0);
lean_inc(v_a_2575_);
lean_dec_ref_known(v___x_2574_, 1);
v___x_2576_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2575_, v___y_2563_);
if (lean_obj_tag(v___x_2576_) == 0)
{
lean_object* v_a_2577_; lean_object* v___x_2578_; lean_object* v___x_2579_; size_t v___x_2580_; size_t v___x_2581_; lean_object* v___x_2582_; 
v_a_2577_ = lean_ctor_get(v___x_2576_, 0);
lean_inc(v_a_2577_);
lean_dec_ref_known(v___x_2576_, 1);
v___x_2578_ = l_Lean_Expr_setPPExplicit(v_a_2577_, v___x_2567_);
v___x_2579_ = l_Lean_indentExpr(v___x_2578_);
v___x_2580_ = ((size_t)1ULL);
v___x_2581_ = lean_usize_add(v_i_2560_, v___x_2580_);
v___x_2582_ = lean_array_uset(v_bs_x27_2572_, v_i_2560_, v___x_2579_);
v_i_2560_ = v___x_2581_;
v_bs_2561_ = v___x_2582_;
goto _start;
}
else
{
lean_object* v_a_2584_; lean_object* v___x_2586_; uint8_t v_isShared_2587_; uint8_t v_isSharedCheck_2591_; 
lean_dec_ref(v_bs_x27_2572_);
v_a_2584_ = lean_ctor_get(v___x_2576_, 0);
v_isSharedCheck_2591_ = !lean_is_exclusive(v___x_2576_);
if (v_isSharedCheck_2591_ == 0)
{
v___x_2586_ = v___x_2576_;
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
else
{
lean_inc(v_a_2584_);
lean_dec(v___x_2576_);
v___x_2586_ = lean_box(0);
v_isShared_2587_ = v_isSharedCheck_2591_;
goto v_resetjp_2585_;
}
v_resetjp_2585_:
{
lean_object* v___x_2589_; 
if (v_isShared_2587_ == 0)
{
v___x_2589_ = v___x_2586_;
goto v_reusejp_2588_;
}
else
{
lean_object* v_reuseFailAlloc_2590_; 
v_reuseFailAlloc_2590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2590_, 0, v_a_2584_);
v___x_2589_ = v_reuseFailAlloc_2590_;
goto v_reusejp_2588_;
}
v_reusejp_2588_:
{
return v___x_2589_;
}
}
}
}
else
{
lean_object* v_a_2592_; lean_object* v___x_2594_; uint8_t v_isShared_2595_; uint8_t v_isSharedCheck_2599_; 
lean_dec_ref(v_bs_x27_2572_);
v_a_2592_ = lean_ctor_get(v___x_2574_, 0);
v_isSharedCheck_2599_ = !lean_is_exclusive(v___x_2574_);
if (v_isSharedCheck_2599_ == 0)
{
v___x_2594_ = v___x_2574_;
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
else
{
lean_inc(v_a_2592_);
lean_dec(v___x_2574_);
v___x_2594_ = lean_box(0);
v_isShared_2595_ = v_isSharedCheck_2599_;
goto v_resetjp_2593_;
}
v_resetjp_2593_:
{
lean_object* v___x_2597_; 
if (v_isShared_2595_ == 0)
{
v___x_2597_ = v___x_2594_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_a_2592_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2600_, lean_object* v_sz_2601_, lean_object* v_i_2602_, lean_object* v_bs_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_, lean_object* v___y_2608_){
_start:
{
size_t v_sz_boxed_2609_; size_t v_i_boxed_2610_; lean_object* v_res_2611_; 
v_sz_boxed_2609_ = lean_unbox_usize(v_sz_2601_);
lean_dec(v_sz_2601_);
v_i_boxed_2610_ = lean_unbox_usize(v_i_2602_);
lean_dec(v_i_2602_);
v_res_2611_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2600_, v_sz_boxed_2609_, v_i_boxed_2610_, v_bs_2603_, v___y_2604_, v___y_2605_, v___y_2606_, v___y_2607_);
lean_dec(v___y_2607_);
lean_dec_ref(v___y_2606_);
lean_dec(v___y_2605_);
lean_dec_ref(v___y_2604_);
lean_dec_ref(v_fst_2600_);
return v_res_2611_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object* v___x_2612_, lean_object* v_snd_2613_, lean_object* v___f_2614_, lean_object* v_____r_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_, lean_object* v___y_2619_){
_start:
{
lean_object* v___x_2621_; lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2621_ = lean_unsigned_to_nat(0u);
v___x_2622_ = lean_array_get_borrowed(v___x_2612_, v_snd_2613_, v___x_2621_);
lean_inc(v___y_2619_);
lean_inc_ref(v___y_2618_);
lean_inc(v___y_2617_);
lean_inc_ref(v___y_2616_);
lean_inc(v___x_2622_);
v___x_2623_ = lean_apply_6(v___f_2614_, v___x_2622_, v___y_2616_, v___y_2617_, v___y_2618_, v___y_2619_, lean_box(0));
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object* v___x_2624_, lean_object* v_snd_2625_, lean_object* v___f_2626_, lean_object* v_____r_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_, lean_object* v___y_2632_){
_start:
{
lean_object* v_res_2633_; 
v_res_2633_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2624_, v_snd_2625_, v___f_2626_, v_____r_2627_, v___y_2628_, v___y_2629_, v___y_2630_, v___y_2631_);
lean_dec(v___y_2631_);
lean_dec_ref(v___y_2630_);
lean_dec(v___y_2629_);
lean_dec_ref(v___y_2628_);
lean_dec(v_snd_2625_);
lean_dec(v___x_2624_);
return v_res_2633_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2637_; lean_object* v___x_2638_; 
v___x_2637_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1));
v___x_2638_ = l_Lean_MessageData_ofFormat(v___x_2637_);
return v___x_2638_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2640_; lean_object* v___x_2641_; 
v___x_2640_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3));
v___x_2641_ = l_Lean_stringToMessageData(v___x_2640_);
return v___x_2641_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2643_; lean_object* v___x_2644_; 
v___x_2643_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5));
v___x_2644_ = l_Lean_stringToMessageData(v___x_2643_);
return v___x_2644_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2646_; lean_object* v___x_2647_; 
v___x_2646_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7));
v___x_2647_ = l_Lean_stringToMessageData(v___x_2646_);
return v___x_2647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(lean_object* v_fst_2648_, lean_object* v_argVars_2649_, lean_object* v_inst_2650_, lean_object* v_a_2651_, lean_object* v_projInfo_x3f_2652_, lean_object* v_a_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v___y_2660_; lean_object* v_fst_2680_; lean_object* v_snd_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2753_; 
v_fst_2680_ = lean_ctor_get(v_a_2653_, 0);
v_snd_2681_ = lean_ctor_get(v_a_2653_, 1);
v_isSharedCheck_2753_ = !lean_is_exclusive(v_a_2653_);
if (v_isSharedCheck_2753_ == 0)
{
v___x_2683_ = v_a_2653_;
v_isShared_2684_ = v_isSharedCheck_2753_;
goto v_resetjp_2682_;
}
else
{
lean_inc(v_snd_2681_);
lean_inc(v_fst_2680_);
lean_dec(v_a_2653_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2753_;
goto v_resetjp_2682_;
}
v___jp_2659_:
{
if (lean_obj_tag(v___y_2660_) == 0)
{
lean_object* v_a_2661_; lean_object* v___x_2663_; uint8_t v_isShared_2664_; uint8_t v_isSharedCheck_2671_; 
v_a_2661_ = lean_ctor_get(v___y_2660_, 0);
v_isSharedCheck_2671_ = !lean_is_exclusive(v___y_2660_);
if (v_isSharedCheck_2671_ == 0)
{
v___x_2663_ = v___y_2660_;
v_isShared_2664_ = v_isSharedCheck_2671_;
goto v_resetjp_2662_;
}
else
{
lean_inc(v_a_2661_);
lean_dec(v___y_2660_);
v___x_2663_ = lean_box(0);
v_isShared_2664_ = v_isSharedCheck_2671_;
goto v_resetjp_2662_;
}
v_resetjp_2662_:
{
if (lean_obj_tag(v_a_2661_) == 0)
{
lean_object* v_a_2665_; lean_object* v___x_2667_; 
lean_dec_ref(v_a_2651_);
lean_dec_ref(v_inst_2650_);
lean_dec_ref(v_argVars_2649_);
lean_dec_ref(v_fst_2648_);
v_a_2665_ = lean_ctor_get(v_a_2661_, 0);
lean_inc(v_a_2665_);
lean_dec_ref_known(v_a_2661_, 1);
if (v_isShared_2664_ == 0)
{
lean_ctor_set(v___x_2663_, 0, v_a_2665_);
v___x_2667_ = v___x_2663_;
goto v_reusejp_2666_;
}
else
{
lean_object* v_reuseFailAlloc_2668_; 
v_reuseFailAlloc_2668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2668_, 0, v_a_2665_);
v___x_2667_ = v_reuseFailAlloc_2668_;
goto v_reusejp_2666_;
}
v_reusejp_2666_:
{
return v___x_2667_;
}
}
else
{
lean_object* v_a_2669_; 
lean_del_object(v___x_2663_);
v_a_2669_ = lean_ctor_get(v_a_2661_, 0);
lean_inc(v_a_2669_);
lean_dec_ref_known(v_a_2661_, 1);
v_a_2653_ = v_a_2669_;
goto _start;
}
}
}
else
{
lean_object* v_a_2672_; lean_object* v___x_2674_; uint8_t v_isShared_2675_; uint8_t v_isSharedCheck_2679_; 
lean_dec_ref(v_a_2651_);
lean_dec_ref(v_inst_2650_);
lean_dec_ref(v_argVars_2649_);
lean_dec_ref(v_fst_2648_);
v_a_2672_ = lean_ctor_get(v___y_2660_, 0);
v_isSharedCheck_2679_ = !lean_is_exclusive(v___y_2660_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2674_ = v___y_2660_;
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
else
{
lean_inc(v_a_2672_);
lean_dec(v___y_2660_);
v___x_2674_ = lean_box(0);
v_isShared_2675_ = v_isSharedCheck_2679_;
goto v_resetjp_2673_;
}
v_resetjp_2673_:
{
lean_object* v___x_2677_; 
if (v_isShared_2675_ == 0)
{
v___x_2677_ = v___x_2674_;
goto v_reusejp_2676_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_a_2672_);
v___x_2677_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2676_;
}
v_reusejp_2676_:
{
return v___x_2677_;
}
}
}
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2686_; uint8_t v___x_2687_; 
v___x_2685_ = lean_array_get_size(v_snd_2681_);
v___x_2686_ = lean_unsigned_to_nat(0u);
v___x_2687_ = lean_nat_dec_eq(v___x_2685_, v___x_2686_);
if (v___x_2687_ == 0)
{
lean_object* v___x_2688_; lean_object* v___f_2689_; lean_object* v___x_2732_; size_t v_sz_2733_; size_t v___x_2734_; lean_object* v___x_2735_; 
lean_del_object(v___x_2683_);
v___x_2688_ = l_Lean_instInhabitedExpr;
lean_inc(v_snd_2681_);
lean_inc_ref(v_argVars_2649_);
lean_inc_ref(v_fst_2648_);
lean_inc(v_fst_2680_);
v___f_2689_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2689_, 0, v_fst_2680_);
lean_closure_set(v___f_2689_, 1, v___x_2688_);
lean_closure_set(v___f_2689_, 2, v_fst_2648_);
lean_closure_set(v___f_2689_, 3, v_argVars_2649_);
lean_closure_set(v___f_2689_, 4, v_snd_2681_);
v___x_2732_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2733_ = lean_array_size(v_snd_2681_);
v___x_2734_ = ((size_t)0ULL);
v___x_2735_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2648_, v_projInfo_x3f_2652_, v___x_2685_, v_argVars_2649_, v_snd_2681_, v_sz_2733_, v___x_2734_, v___x_2732_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
if (lean_obj_tag(v___x_2735_) == 0)
{
lean_object* v_a_2736_; lean_object* v_fst_2737_; 
v_a_2736_ = lean_ctor_get(v___x_2735_, 0);
lean_inc(v_a_2736_);
lean_dec_ref_known(v___x_2735_, 1);
v_fst_2737_ = lean_ctor_get(v_a_2736_, 0);
lean_inc(v_fst_2737_);
lean_dec(v_a_2736_);
if (lean_obj_tag(v_fst_2737_) == 0)
{
lean_dec(v_fst_2680_);
goto v___jp_2690_;
}
else
{
lean_object* v_val_2738_; 
v_val_2738_ = lean_ctor_get(v_fst_2737_, 0);
lean_inc(v_val_2738_);
lean_dec_ref_known(v_fst_2737_, 1);
if (lean_obj_tag(v_val_2738_) == 0)
{
lean_dec(v_fst_2680_);
goto v___jp_2690_;
}
else
{
lean_object* v_val_2739_; lean_object* v___x_2740_; 
lean_dec_ref(v___f_2689_);
v_val_2739_ = lean_ctor_get(v_val_2738_, 0);
lean_inc(v_val_2739_);
lean_dec_ref_known(v_val_2738_, 1);
v___x_2740_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2680_, v___x_2688_, v_fst_2648_, v_argVars_2649_, v_snd_2681_, v_val_2739_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v_snd_2681_);
v___y_2660_ = v___x_2740_;
goto v___jp_2659_;
}
}
}
else
{
lean_object* v_a_2741_; lean_object* v___x_2743_; uint8_t v_isShared_2744_; uint8_t v_isSharedCheck_2748_; 
lean_dec_ref(v___f_2689_);
lean_dec(v_snd_2681_);
lean_dec(v_fst_2680_);
lean_dec_ref(v_a_2651_);
lean_dec_ref(v_inst_2650_);
lean_dec_ref(v_argVars_2649_);
lean_dec_ref(v_fst_2648_);
v_a_2741_ = lean_ctor_get(v___x_2735_, 0);
v_isSharedCheck_2748_ = !lean_is_exclusive(v___x_2735_);
if (v_isSharedCheck_2748_ == 0)
{
v___x_2743_ = v___x_2735_;
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
else
{
lean_inc(v_a_2741_);
lean_dec(v___x_2735_);
v___x_2743_ = lean_box(0);
v_isShared_2744_ = v_isSharedCheck_2748_;
goto v_resetjp_2742_;
}
v_resetjp_2742_:
{
lean_object* v___x_2746_; 
if (v_isShared_2744_ == 0)
{
v___x_2746_ = v___x_2743_;
goto v_reusejp_2745_;
}
else
{
lean_object* v_reuseFailAlloc_2747_; 
v_reuseFailAlloc_2747_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2747_, 0, v_a_2741_);
v___x_2746_ = v_reuseFailAlloc_2747_;
goto v_reusejp_2745_;
}
v_reusejp_2745_:
{
return v___x_2746_;
}
}
}
v___jp_2690_:
{
lean_object* v___x_2691_; lean_object* v___x_2692_; uint8_t v___x_2693_; 
v___x_2691_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2656_);
v___x_2692_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2693_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_2691_, v___x_2692_);
lean_dec_ref(v___x_2691_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; lean_object* v___x_2695_; 
v___x_2694_ = lean_box(0);
v___x_2695_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2686_, v_snd_2681_, v___f_2689_, v___x_2694_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v_snd_2681_);
v___y_2660_ = v___x_2695_;
goto v___jp_2659_;
}
else
{
size_t v_sz_2696_; size_t v___x_2697_; lean_object* v___x_2698_; 
v_sz_2696_ = lean_array_size(v_snd_2681_);
v___x_2697_ = ((size_t)0ULL);
lean_inc(v_snd_2681_);
v___x_2698_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2648_, v_sz_2696_, v___x_2697_, v_snd_2681_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; lean_object* v___x_2713_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = lean_array_to_list(v_a_2699_);
v___x_2701_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2702_ = l_Lean_MessageData_joinSep(v___x_2700_, v___x_2701_);
v___x_2703_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4);
lean_inc_ref(v_inst_2650_);
v___x_2704_ = l_Lean_MessageData_ofExpr(v_inst_2650_);
v___x_2705_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2705_, 0, v___x_2703_);
lean_ctor_set(v___x_2705_, 1, v___x_2704_);
v___x_2706_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6);
v___x_2707_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2707_, 0, v___x_2705_);
lean_ctor_set(v___x_2707_, 1, v___x_2706_);
lean_inc_ref(v_a_2651_);
v___x_2708_ = l_Lean_indentExpr(v_a_2651_);
v___x_2709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2709_, 0, v___x_2707_);
lean_ctor_set(v___x_2709_, 1, v___x_2708_);
v___x_2710_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2709_);
lean_ctor_set(v___x_2711_, 1, v___x_2710_);
v___x_2712_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2712_, 0, v___x_2711_);
lean_ctor_set(v___x_2712_, 1, v___x_2702_);
v___x_2713_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2712_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
if (lean_obj_tag(v___x_2713_) == 0)
{
lean_object* v_a_2714_; lean_object* v___x_2715_; 
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
lean_inc(v_a_2714_);
lean_dec_ref_known(v___x_2713_, 1);
v___x_2715_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2686_, v_snd_2681_, v___f_2689_, v_a_2714_, v___y_2654_, v___y_2655_, v___y_2656_, v___y_2657_);
lean_dec(v_snd_2681_);
v___y_2660_ = v___x_2715_;
goto v___jp_2659_;
}
else
{
lean_object* v_a_2716_; lean_object* v___x_2718_; uint8_t v_isShared_2719_; uint8_t v_isSharedCheck_2723_; 
lean_dec_ref(v___f_2689_);
lean_dec(v_snd_2681_);
lean_dec_ref(v_a_2651_);
lean_dec_ref(v_inst_2650_);
lean_dec_ref(v_argVars_2649_);
lean_dec_ref(v_fst_2648_);
v_a_2716_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2723_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2723_ == 0)
{
v___x_2718_ = v___x_2713_;
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
else
{
lean_inc(v_a_2716_);
lean_dec(v___x_2713_);
v___x_2718_ = lean_box(0);
v_isShared_2719_ = v_isSharedCheck_2723_;
goto v_resetjp_2717_;
}
v_resetjp_2717_:
{
lean_object* v___x_2721_; 
if (v_isShared_2719_ == 0)
{
v___x_2721_ = v___x_2718_;
goto v_reusejp_2720_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_a_2716_);
v___x_2721_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2720_;
}
v_reusejp_2720_:
{
return v___x_2721_;
}
}
}
}
else
{
lean_object* v_a_2724_; lean_object* v___x_2726_; uint8_t v_isShared_2727_; uint8_t v_isSharedCheck_2731_; 
lean_dec_ref(v___f_2689_);
lean_dec(v_snd_2681_);
lean_dec_ref(v_a_2651_);
lean_dec_ref(v_inst_2650_);
lean_dec_ref(v_argVars_2649_);
lean_dec_ref(v_fst_2648_);
v_a_2724_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2731_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2731_ == 0)
{
v___x_2726_ = v___x_2698_;
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
else
{
lean_inc(v_a_2724_);
lean_dec(v___x_2698_);
v___x_2726_ = lean_box(0);
v_isShared_2727_ = v_isSharedCheck_2731_;
goto v_resetjp_2725_;
}
v_resetjp_2725_:
{
lean_object* v___x_2729_; 
if (v_isShared_2727_ == 0)
{
v___x_2729_ = v___x_2726_;
goto v_reusejp_2728_;
}
else
{
lean_object* v_reuseFailAlloc_2730_; 
v_reuseFailAlloc_2730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2730_, 0, v_a_2724_);
v___x_2729_ = v_reuseFailAlloc_2730_;
goto v_reusejp_2728_;
}
v_reusejp_2728_:
{
return v___x_2729_;
}
}
}
}
}
}
else
{
lean_object* v___x_2750_; 
lean_dec_ref(v_a_2651_);
lean_dec_ref(v_inst_2650_);
lean_dec_ref(v_argVars_2649_);
lean_dec_ref(v_fst_2648_);
if (v_isShared_2684_ == 0)
{
v___x_2750_ = v___x_2683_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2752_; 
v_reuseFailAlloc_2752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2752_, 0, v_fst_2680_);
lean_ctor_set(v_reuseFailAlloc_2752_, 1, v_snd_2681_);
v___x_2750_ = v_reuseFailAlloc_2752_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
lean_object* v___x_2751_; 
v___x_2751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2751_, 0, v___x_2750_);
return v___x_2751_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___boxed(lean_object* v_fst_2754_, lean_object* v_argVars_2755_, lean_object* v_inst_2756_, lean_object* v_a_2757_, lean_object* v_projInfo_x3f_2758_, lean_object* v_a_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_, lean_object* v___y_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2754_, v_argVars_2755_, v_inst_2756_, v_a_2757_, v_projInfo_x3f_2758_, v_a_2759_, v___y_2760_, v___y_2761_, v___y_2762_, v___y_2763_);
lean_dec(v___y_2763_);
lean_dec_ref(v___y_2762_);
lean_dec(v___y_2761_);
lean_dec_ref(v___y_2760_);
lean_dec(v_projInfo_x3f_2758_);
return v_res_2765_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2766_, lean_object* v_a_2767_, lean_object* v_a_2768_){
_start:
{
if (lean_obj_tag(v_a_2767_) == 0)
{
lean_object* v___x_2769_; 
v___x_2769_ = l_List_reverse___redArg(v_a_2768_);
return v___x_2769_;
}
else
{
lean_object* v_head_2770_; lean_object* v_tail_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2786_; 
v_head_2770_ = lean_ctor_get(v_a_2767_, 0);
v_tail_2771_ = lean_ctor_get(v_a_2767_, 1);
v_isSharedCheck_2786_ = !lean_is_exclusive(v_a_2767_);
if (v_isSharedCheck_2786_ == 0)
{
v___x_2773_ = v_a_2767_;
v_isShared_2774_ = v_isSharedCheck_2786_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_tail_2771_);
lean_inc(v_head_2770_);
lean_dec(v_a_2767_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2786_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
uint8_t v___x_2775_; lean_object* v___x_2776_; lean_object* v___x_2777_; uint8_t v___x_2778_; uint8_t v___x_2779_; uint8_t v___x_2780_; 
v___x_2775_ = 0;
v___x_2776_ = lean_box(v___x_2775_);
v___x_2777_ = lean_array_get(v___x_2776_, v_fst_2766_, v_head_2770_);
lean_dec(v___x_2776_);
v___x_2778_ = 3;
v___x_2779_ = lean_unbox(v___x_2777_);
lean_dec(v___x_2777_);
v___x_2780_ = l_Lean_instBEqBinderInfo_beq(v___x_2779_, v___x_2778_);
if (v___x_2780_ == 0)
{
lean_del_object(v___x_2773_);
lean_dec(v_head_2770_);
v_a_2767_ = v_tail_2771_;
goto _start;
}
else
{
lean_object* v___x_2783_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 1, v_a_2768_);
v___x_2783_ = v___x_2773_;
goto v_reusejp_2782_;
}
else
{
lean_object* v_reuseFailAlloc_2785_; 
v_reuseFailAlloc_2785_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2785_, 0, v_head_2770_);
lean_ctor_set(v_reuseFailAlloc_2785_, 1, v_a_2768_);
v___x_2783_ = v_reuseFailAlloc_2785_;
goto v_reusejp_2782_;
}
v_reusejp_2782_:
{
v_a_2767_ = v_tail_2771_;
v_a_2768_ = v___x_2783_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2787_, lean_object* v_a_2788_, lean_object* v_a_2789_){
_start:
{
lean_object* v_res_2790_; 
v_res_2790_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2787_, v_a_2788_, v_a_2789_);
lean_dec_ref(v_fst_2787_);
return v_res_2790_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2791_, size_t v_sz_2792_, size_t v_i_2793_, lean_object* v_bs_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_, lean_object* v___y_2798_){
_start:
{
uint8_t v___x_2800_; 
v___x_2800_ = lean_usize_dec_lt(v_i_2793_, v_sz_2792_);
if (v___x_2800_ == 0)
{
lean_object* v___x_2801_; 
v___x_2801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2801_, 0, v_bs_2794_);
return v___x_2801_;
}
else
{
lean_object* v___x_2802_; lean_object* v_v_2803_; lean_object* v___x_2804_; lean_object* v_bs_x27_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; 
v___x_2802_ = l_Lean_instInhabitedExpr;
v_v_2803_ = lean_array_uget(v_bs_2794_, v_i_2793_);
v___x_2804_ = lean_unsigned_to_nat(0u);
v_bs_x27_2805_ = lean_array_uset(v_bs_2794_, v_i_2793_, v___x_2804_);
v___x_2806_ = lean_array_get_borrowed(v___x_2802_, v_argVars_2791_, v_v_2803_);
lean_dec(v_v_2803_);
lean_inc(v___y_2798_);
lean_inc_ref(v___y_2797_);
lean_inc(v___y_2796_);
lean_inc_ref(v___y_2795_);
lean_inc(v___x_2806_);
v___x_2807_ = lean_infer_type(v___x_2806_, v___y_2795_, v___y_2796_, v___y_2797_, v___y_2798_);
if (lean_obj_tag(v___x_2807_) == 0)
{
lean_object* v_a_2808_; lean_object* v___x_2809_; size_t v___x_2810_; size_t v___x_2811_; lean_object* v___x_2812_; 
v_a_2808_ = lean_ctor_get(v___x_2807_, 0);
lean_inc(v_a_2808_);
lean_dec_ref_known(v___x_2807_, 1);
v___x_2809_ = l_Lean_indentExpr(v_a_2808_);
v___x_2810_ = ((size_t)1ULL);
v___x_2811_ = lean_usize_add(v_i_2793_, v___x_2810_);
v___x_2812_ = lean_array_uset(v_bs_x27_2805_, v_i_2793_, v___x_2809_);
v_i_2793_ = v___x_2811_;
v_bs_2794_ = v___x_2812_;
goto _start;
}
else
{
lean_object* v_a_2814_; lean_object* v___x_2816_; uint8_t v_isShared_2817_; uint8_t v_isSharedCheck_2821_; 
lean_dec_ref(v_bs_x27_2805_);
v_a_2814_ = lean_ctor_get(v___x_2807_, 0);
v_isSharedCheck_2821_ = !lean_is_exclusive(v___x_2807_);
if (v_isSharedCheck_2821_ == 0)
{
v___x_2816_ = v___x_2807_;
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
else
{
lean_inc(v_a_2814_);
lean_dec(v___x_2807_);
v___x_2816_ = lean_box(0);
v_isShared_2817_ = v_isSharedCheck_2821_;
goto v_resetjp_2815_;
}
v_resetjp_2815_:
{
lean_object* v___x_2819_; 
if (v_isShared_2817_ == 0)
{
v___x_2819_ = v___x_2816_;
goto v_reusejp_2818_;
}
else
{
lean_object* v_reuseFailAlloc_2820_; 
v_reuseFailAlloc_2820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2820_, 0, v_a_2814_);
v___x_2819_ = v_reuseFailAlloc_2820_;
goto v_reusejp_2818_;
}
v_reusejp_2818_:
{
return v___x_2819_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2822_, lean_object* v_sz_2823_, lean_object* v_i_2824_, lean_object* v_bs_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_, lean_object* v___y_2830_){
_start:
{
size_t v_sz_boxed_2831_; size_t v_i_boxed_2832_; lean_object* v_res_2833_; 
v_sz_boxed_2831_ = lean_unbox_usize(v_sz_2823_);
lean_dec(v_sz_2823_);
v_i_boxed_2832_ = lean_unbox_usize(v_i_2824_);
lean_dec(v_i_2824_);
v_res_2833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2822_, v_sz_boxed_2831_, v_i_boxed_2832_, v_bs_2825_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v___y_2829_);
lean_dec_ref(v___y_2828_);
lean_dec(v___y_2827_);
lean_dec_ref(v___y_2826_);
lean_dec_ref(v_argVars_2822_);
return v_res_2833_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2834_, lean_object* v_a_2835_){
_start:
{
if (lean_obj_tag(v_a_2834_) == 0)
{
lean_object* v___x_2836_; 
v___x_2836_ = l_List_reverse___redArg(v_a_2835_);
return v___x_2836_;
}
else
{
lean_object* v_head_2837_; lean_object* v_tail_2838_; lean_object* v___x_2840_; uint8_t v_isShared_2841_; uint8_t v_isSharedCheck_2849_; 
v_head_2837_ = lean_ctor_get(v_a_2834_, 0);
v_tail_2838_ = lean_ctor_get(v_a_2834_, 1);
v_isSharedCheck_2849_ = !lean_is_exclusive(v_a_2834_);
if (v_isSharedCheck_2849_ == 0)
{
v___x_2840_ = v_a_2834_;
v_isShared_2841_ = v_isSharedCheck_2849_;
goto v_resetjp_2839_;
}
else
{
lean_inc(v_tail_2838_);
lean_inc(v_head_2837_);
lean_dec(v_a_2834_);
v___x_2840_ = lean_box(0);
v_isShared_2841_ = v_isSharedCheck_2849_;
goto v_resetjp_2839_;
}
v_resetjp_2839_:
{
lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2844_; lean_object* v___x_2846_; 
v___x_2842_ = l_Nat_reprFast(v_head_2837_);
v___x_2843_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2843_, 0, v___x_2842_);
v___x_2844_ = l_Lean_MessageData_ofFormat(v___x_2843_);
if (v_isShared_2841_ == 0)
{
lean_ctor_set(v___x_2840_, 1, v_a_2835_);
lean_ctor_set(v___x_2840_, 0, v___x_2844_);
v___x_2846_ = v___x_2840_;
goto v_reusejp_2845_;
}
else
{
lean_object* v_reuseFailAlloc_2848_; 
v_reuseFailAlloc_2848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2848_, 0, v___x_2844_);
lean_ctor_set(v_reuseFailAlloc_2848_, 1, v_a_2835_);
v___x_2846_ = v_reuseFailAlloc_2848_;
goto v_reusejp_2845_;
}
v_reusejp_2845_:
{
v_a_2834_ = v_tail_2838_;
v_a_2835_ = v___x_2846_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2850_; double v___x_2851_; 
v___x_2850_ = lean_unsigned_to_nat(0u);
v___x_2851_ = lean_float_of_nat(v___x_2850_);
return v___x_2851_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2854_, lean_object* v_msg_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_, lean_object* v___y_2859_){
_start:
{
lean_object* v_ref_2861_; lean_object* v___x_2862_; lean_object* v_a_2863_; lean_object* v___x_2865_; uint8_t v_isShared_2866_; uint8_t v_isSharedCheck_2908_; 
v_ref_2861_ = lean_ctor_get(v___y_2858_, 2);
v___x_2862_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2855_, v___y_2856_, v___y_2857_, v___y_2858_, v___y_2859_);
v_a_2863_ = lean_ctor_get(v___x_2862_, 0);
v_isSharedCheck_2908_ = !lean_is_exclusive(v___x_2862_);
if (v_isSharedCheck_2908_ == 0)
{
v___x_2865_ = v___x_2862_;
v_isShared_2866_ = v_isSharedCheck_2908_;
goto v_resetjp_2864_;
}
else
{
lean_inc(v_a_2863_);
lean_dec(v___x_2862_);
v___x_2865_ = lean_box(0);
v_isShared_2866_ = v_isSharedCheck_2908_;
goto v_resetjp_2864_;
}
v_resetjp_2864_:
{
lean_object* v___x_2867_; lean_object* v_traceState_2868_; lean_object* v_env_2869_; lean_object* v_nextMacroScope_2870_; lean_object* v_ngen_2871_; lean_object* v_auxDeclNGen_2872_; lean_object* v_cache_2873_; lean_object* v_recordedDeps_2874_; lean_object* v_messages_2875_; lean_object* v_infoState_2876_; lean_object* v_snapshotTasks_2877_; lean_object* v___x_2879_; uint8_t v_isShared_2880_; uint8_t v_isSharedCheck_2907_; 
v___x_2867_ = lean_st_ref_take(v___y_2859_);
v_traceState_2868_ = lean_ctor_get(v___x_2867_, 4);
v_env_2869_ = lean_ctor_get(v___x_2867_, 0);
v_nextMacroScope_2870_ = lean_ctor_get(v___x_2867_, 1);
v_ngen_2871_ = lean_ctor_get(v___x_2867_, 2);
v_auxDeclNGen_2872_ = lean_ctor_get(v___x_2867_, 3);
v_cache_2873_ = lean_ctor_get(v___x_2867_, 5);
v_recordedDeps_2874_ = lean_ctor_get(v___x_2867_, 6);
v_messages_2875_ = lean_ctor_get(v___x_2867_, 7);
v_infoState_2876_ = lean_ctor_get(v___x_2867_, 8);
v_snapshotTasks_2877_ = lean_ctor_get(v___x_2867_, 9);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2879_ = v___x_2867_;
v_isShared_2880_ = v_isSharedCheck_2907_;
goto v_resetjp_2878_;
}
else
{
lean_inc(v_snapshotTasks_2877_);
lean_inc(v_infoState_2876_);
lean_inc(v_messages_2875_);
lean_inc(v_recordedDeps_2874_);
lean_inc(v_cache_2873_);
lean_inc(v_traceState_2868_);
lean_inc(v_auxDeclNGen_2872_);
lean_inc(v_ngen_2871_);
lean_inc(v_nextMacroScope_2870_);
lean_inc(v_env_2869_);
lean_dec(v___x_2867_);
v___x_2879_ = lean_box(0);
v_isShared_2880_ = v_isSharedCheck_2907_;
goto v_resetjp_2878_;
}
v_resetjp_2878_:
{
uint64_t v_tid_2881_; lean_object* v_traces_2882_; lean_object* v___x_2884_; uint8_t v_isShared_2885_; uint8_t v_isSharedCheck_2906_; 
v_tid_2881_ = lean_ctor_get_uint64(v_traceState_2868_, sizeof(void*)*1);
v_traces_2882_ = lean_ctor_get(v_traceState_2868_, 0);
v_isSharedCheck_2906_ = !lean_is_exclusive(v_traceState_2868_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2884_ = v_traceState_2868_;
v_isShared_2885_ = v_isSharedCheck_2906_;
goto v_resetjp_2883_;
}
else
{
lean_inc(v_traces_2882_);
lean_dec(v_traceState_2868_);
v___x_2884_ = lean_box(0);
v_isShared_2885_ = v_isSharedCheck_2906_;
goto v_resetjp_2883_;
}
v_resetjp_2883_:
{
lean_object* v___x_2886_; lean_object* v___x_2887_; double v___x_2888_; uint8_t v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2897_; 
v___x_2886_ = lean_box(0);
v___x_2887_ = lean_box(0);
v___x_2888_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2889_ = 0;
v___x_2890_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___x_2891_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2891_, 0, v_cls_2854_);
lean_ctor_set(v___x_2891_, 1, v___x_2887_);
lean_ctor_set(v___x_2891_, 2, v___x_2890_);
lean_ctor_set_float(v___x_2891_, sizeof(void*)*3, v___x_2888_);
lean_ctor_set_float(v___x_2891_, sizeof(void*)*3 + 8, v___x_2888_);
lean_ctor_set_uint8(v___x_2891_, sizeof(void*)*3 + 16, v___x_2889_);
v___x_2892_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2893_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2893_, 0, v___x_2891_);
lean_ctor_set(v___x_2893_, 1, v_a_2863_);
lean_ctor_set(v___x_2893_, 2, v___x_2892_);
lean_inc(v_ref_2861_);
v___x_2894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2894_, 0, v_ref_2861_);
lean_ctor_set(v___x_2894_, 1, v___x_2893_);
v___x_2895_ = l_Lean_PersistentArray_push___redArg(v_traces_2882_, v___x_2894_);
if (v_isShared_2885_ == 0)
{
lean_ctor_set(v___x_2884_, 0, v___x_2895_);
v___x_2897_ = v___x_2884_;
goto v_reusejp_2896_;
}
else
{
lean_object* v_reuseFailAlloc_2905_; 
v_reuseFailAlloc_2905_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2905_, 0, v___x_2895_);
lean_ctor_set_uint64(v_reuseFailAlloc_2905_, sizeof(void*)*1, v_tid_2881_);
v___x_2897_ = v_reuseFailAlloc_2905_;
goto v_reusejp_2896_;
}
v_reusejp_2896_:
{
lean_object* v___x_2899_; 
if (v_isShared_2880_ == 0)
{
lean_ctor_set(v___x_2879_, 4, v___x_2897_);
v___x_2899_ = v___x_2879_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v_env_2869_);
lean_ctor_set(v_reuseFailAlloc_2904_, 1, v_nextMacroScope_2870_);
lean_ctor_set(v_reuseFailAlloc_2904_, 2, v_ngen_2871_);
lean_ctor_set(v_reuseFailAlloc_2904_, 3, v_auxDeclNGen_2872_);
lean_ctor_set(v_reuseFailAlloc_2904_, 4, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2904_, 5, v_cache_2873_);
lean_ctor_set(v_reuseFailAlloc_2904_, 6, v_recordedDeps_2874_);
lean_ctor_set(v_reuseFailAlloc_2904_, 7, v_messages_2875_);
lean_ctor_set(v_reuseFailAlloc_2904_, 8, v_infoState_2876_);
lean_ctor_set(v_reuseFailAlloc_2904_, 9, v_snapshotTasks_2877_);
v___x_2899_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2902_; 
v___x_2900_ = lean_st_ref_put(v___y_2859_, v___x_2899_);
if (v_isShared_2866_ == 0)
{
lean_ctor_set(v___x_2865_, 0, v___x_2886_);
v___x_2902_ = v___x_2865_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v___x_2886_);
v___x_2902_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
return v___x_2902_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2909_, lean_object* v_msg_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_, lean_object* v___y_2915_){
_start:
{
lean_object* v_res_2916_; 
v_res_2916_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2909_, v_msg_2910_, v___y_2911_, v___y_2912_, v___y_2913_, v___y_2914_);
lean_dec(v___y_2914_);
lean_dec_ref(v___y_2913_);
lean_dec(v___y_2912_);
lean_dec_ref(v___y_2911_);
return v_res_2916_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; 
v___x_2924_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2925_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2926_ = l_Lean_Name_append(v___x_2925_, v___x_2924_);
return v___x_2926_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2928_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2929_ = l_Lean_stringToMessageData(v___x_2928_);
return v___x_2929_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; 
v___x_2931_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2932_ = l_Lean_stringToMessageData(v___x_2931_);
return v___x_2932_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2934_; lean_object* v___x_2935_; 
v___x_2934_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2935_ = l_Lean_stringToMessageData(v___x_2934_);
return v___x_2935_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2937_; lean_object* v___x_2938_; 
v___x_2937_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2938_ = l_Lean_stringToMessageData(v___x_2937_);
return v___x_2938_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2939_, lean_object* v_fst_2940_, lean_object* v_fst_2941_, lean_object* v_inst_2942_, lean_object* v_a_2943_, lean_object* v_projInfo_x3f_2944_, lean_object* v_argVars_2945_, lean_object* v_x_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_, lean_object* v___y_2950_){
_start:
{
lean_object* v___x_2952_; 
v___x_2952_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2939_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2952_) == 0)
{
lean_object* v_a_2953_; lean_object* v_dummy_2954_; lean_object* v_nargs_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; size_t v_sz_2963_; size_t v___x_2964_; lean_object* v___x_2965_; 
v_a_2953_ = lean_ctor_get(v___x_2952_, 0);
lean_inc(v_a_2953_);
lean_dec_ref_known(v___x_2952_, 1);
v_dummy_2954_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2955_ = l_Lean_Expr_getAppNumArgs(v_a_2939_);
lean_inc(v_nargs_2955_);
v___x_2956_ = lean_mk_array(v_nargs_2955_, v_dummy_2954_);
v___x_2957_ = lean_unsigned_to_nat(1u);
v___x_2958_ = lean_nat_sub(v_nargs_2955_, v___x_2957_);
lean_dec(v_nargs_2955_);
lean_inc_ref(v_a_2939_);
v___x_2959_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2939_, v___x_2956_, v___x_2958_);
v___x_2960_ = lean_array_get_size(v___x_2959_);
v___x_2961_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2962_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2962_, 0, v___x_2961_);
lean_ctor_set(v___x_2962_, 1, v___x_2960_);
v_sz_2963_ = lean_array_size(v___x_2959_);
v___x_2964_ = ((size_t)0ULL);
v___x_2965_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2953_, v_fst_2940_, v_argVars_2945_, v___x_2959_, v_sz_2963_, v___x_2964_, v___x_2962_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
lean_dec_ref(v___x_2959_);
lean_dec(v_a_2953_);
if (lean_obj_tag(v___x_2965_) == 0)
{
lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; lean_object* v___x_2973_; 
lean_dec_ref_known(v___x_2965_, 1);
v___x_2966_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2967_ = lean_array_get_size(v_fst_2940_);
v___x_2968_ = l_List_range(v___x_2967_);
v___x_2969_ = lean_box(0);
v___x_2970_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2941_, v___x_2968_, v___x_2969_);
v___x_2971_ = lean_array_mk(v___x_2970_);
v___x_2972_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2972_, 0, v___x_2966_);
lean_ctor_set(v___x_2972_, 1, v___x_2971_);
lean_inc_ref(v_inst_2942_);
lean_inc_ref(v_argVars_2945_);
v___x_2973_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2940_, v_argVars_2945_, v_inst_2942_, v_a_2943_, v_projInfo_x3f_2944_, v___x_2972_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
if (lean_obj_tag(v___x_2973_) == 0)
{
lean_object* v_a_2974_; lean_object* v___x_2976_; uint8_t v_isShared_2977_; uint8_t v_isSharedCheck_3066_; 
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3066_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3066_ == 0)
{
v___x_2976_ = v___x_2973_;
v_isShared_2977_ = v_isSharedCheck_3066_;
goto v_resetjp_2975_;
}
else
{
lean_inc(v_a_2974_);
lean_dec(v___x_2973_);
v___x_2976_ = lean_box(0);
v_isShared_2977_ = v_isSharedCheck_3066_;
goto v_resetjp_2975_;
}
v_resetjp_2975_:
{
lean_object* v_fst_2978_; lean_object* v___x_2980_; uint8_t v_isShared_2981_; uint8_t v_isSharedCheck_3064_; 
v_fst_2978_ = lean_ctor_get(v_a_2974_, 0);
v_isSharedCheck_3064_ = !lean_is_exclusive(v_a_2974_);
if (v_isSharedCheck_3064_ == 0)
{
lean_object* v_unused_3065_; 
v_unused_3065_ = lean_ctor_get(v_a_2974_, 1);
lean_dec(v_unused_3065_);
v___x_2980_ = v_a_2974_;
v_isShared_2981_ = v_isSharedCheck_3064_;
goto v_resetjp_2979_;
}
else
{
lean_inc(v_fst_2978_);
lean_dec(v_a_2974_);
v___x_2980_ = lean_box(0);
v_isShared_2981_ = v_isSharedCheck_3064_;
goto v_resetjp_2979_;
}
v_resetjp_2979_:
{
lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___y_2986_; lean_object* v___x_3045_; lean_object* v___x_3046_; uint8_t v___x_3047_; 
v___x_3045_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2949_);
v___x_3046_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_3047_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_3045_, v___x_3046_);
lean_dec_ref(v___x_3045_);
if (v___x_3047_ == 0)
{
lean_dec_ref(v_a_2939_);
v___y_2983_ = v___y_2947_;
v___y_2984_ = v___y_2948_;
v___y_2985_ = v___y_2949_;
v___y_2986_ = v___y_2950_;
goto v___jp_2982_;
}
else
{
lean_object* v___x_3048_; lean_object* v_a_3049_; uint8_t v___x_3050_; 
v___x_3048_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2939_, v___y_2948_);
v_a_3049_ = lean_ctor_get(v___x_3048_, 0);
lean_inc(v_a_3049_);
lean_dec_ref(v___x_3048_);
v___x_3050_ = l_Lean_Expr_hasExprMVar(v_a_3049_);
if (v___x_3050_ == 0)
{
lean_dec(v_a_3049_);
v___y_2983_ = v___y_2947_;
v___y_2984_ = v___y_2948_;
v___y_2985_ = v___y_2949_;
v___y_2986_ = v___y_2950_;
goto v___jp_2982_;
}
else
{
lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v_a_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3063_; 
lean_del_object(v___x_2980_);
lean_dec(v_fst_2978_);
lean_del_object(v___x_2976_);
lean_dec_ref(v_argVars_2945_);
lean_dec_ref(v_inst_2942_);
v___x_3051_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_3052_ = l_Lean_Expr_setPPExplicit(v_a_3049_, v___x_3047_);
v___x_3053_ = l_Lean_indentExpr(v___x_3052_);
v___x_3054_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3054_, 0, v___x_3051_);
lean_ctor_set(v___x_3054_, 1, v___x_3053_);
v___x_3055_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3054_, v___y_2947_, v___y_2948_, v___y_2949_, v___y_2950_);
v_a_3056_ = lean_ctor_get(v___x_3055_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v___x_3055_);
if (v_isSharedCheck_3063_ == 0)
{
v___x_3058_ = v___x_3055_;
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_a_3056_);
lean_dec(v___x_3055_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3063_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v___x_3061_; 
if (v_isShared_3059_ == 0)
{
v___x_3061_ = v___x_3058_;
goto v_reusejp_3060_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_a_3056_);
v___x_3061_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3060_;
}
v_reusejp_3060_:
{
return v___x_3061_;
}
}
}
}
v___jp_2982_:
{
lean_object* v_toCold_2987_; lean_object* v_options_2988_; uint8_t v_hasTrace_2989_; 
v_toCold_2987_ = lean_ctor_get(v___y_2985_, 0);
v_options_2988_ = lean_ctor_get(v_toCold_2987_, 2);
v_hasTrace_2989_ = lean_ctor_get_uint8(v_options_2988_, sizeof(void*)*1);
if (v_hasTrace_2989_ == 0)
{
lean_object* v___x_2991_; 
lean_del_object(v___x_2980_);
lean_dec_ref(v_argVars_2945_);
lean_dec_ref(v_inst_2942_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v_fst_2978_);
v___x_2991_ = v___x_2976_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_fst_2978_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; uint8_t v___x_2996_; 
v_inheritedTraceOptions_2993_ = lean_ctor_get(v_toCold_2987_, 11);
v___x_2994_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2995_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2996_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2993_, v_options_2988_, v___x_2995_);
if (v___x_2996_ == 0)
{
lean_object* v___x_2998_; 
lean_del_object(v___x_2980_);
lean_dec_ref(v_argVars_2945_);
lean_dec_ref(v_inst_2942_);
if (v_isShared_2977_ == 0)
{
lean_ctor_set(v___x_2976_, 0, v_fst_2978_);
v___x_2998_ = v___x_2976_;
goto v_reusejp_2997_;
}
else
{
lean_object* v_reuseFailAlloc_2999_; 
v_reuseFailAlloc_2999_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2999_, 0, v_fst_2978_);
v___x_2998_ = v_reuseFailAlloc_2999_;
goto v_reusejp_2997_;
}
v_reusejp_2997_:
{
return v___x_2998_;
}
}
else
{
size_t v_sz_3000_; lean_object* v___x_3001_; 
lean_del_object(v___x_2976_);
v_sz_3000_ = lean_array_size(v_fst_2978_);
lean_inc(v_fst_2978_);
v___x_3001_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2945_, v_sz_3000_, v___x_2964_, v_fst_2978_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
lean_dec_ref(v_argVars_2945_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v___x_3003_; lean_object* v___x_3004_; lean_object* v___x_3006_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v___x_3003_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_3004_ = l_Lean_MessageData_ofExpr(v_inst_2942_);
if (v_isShared_2981_ == 0)
{
lean_ctor_set_tag(v___x_2980_, 7);
lean_ctor_set(v___x_2980_, 1, v___x_3004_);
lean_ctor_set(v___x_2980_, 0, v___x_3003_);
v___x_3006_ = v___x_2980_;
goto v_reusejp_3005_;
}
else
{
lean_object* v_reuseFailAlloc_3036_; 
v_reuseFailAlloc_3036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3036_, 0, v___x_3003_);
lean_ctor_set(v_reuseFailAlloc_3036_, 1, v___x_3004_);
v___x_3006_ = v_reuseFailAlloc_3036_;
goto v_reusejp_3005_;
}
v_reusejp_3005_:
{
lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; 
v___x_3007_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_3008_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3008_, 0, v___x_3006_);
lean_ctor_set(v___x_3008_, 1, v___x_3007_);
lean_inc(v_fst_2978_);
v___x_3009_ = lean_array_to_list(v_fst_2978_);
v___x_3010_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_3009_, v___x_2969_);
v___x_3011_ = l_Lean_MessageData_ofList(v___x_3010_);
v___x_3012_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3012_, 0, v___x_3008_);
lean_ctor_set(v___x_3012_, 1, v___x_3011_);
v___x_3013_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_3014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3014_, 0, v___x_3012_);
lean_ctor_set(v___x_3014_, 1, v___x_3013_);
v___x_3015_ = lean_array_to_list(v_a_3002_);
v___x_3016_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_3017_ = l_Lean_MessageData_joinSep(v___x_3015_, v___x_3016_);
v___x_3018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3018_, 0, v___x_3014_);
lean_ctor_set(v___x_3018_, 1, v___x_3017_);
v___x_3019_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2994_, v___x_3018_, v___y_2983_, v___y_2984_, v___y_2985_, v___y_2986_);
if (lean_obj_tag(v___x_3019_) == 0)
{
lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3026_; 
v_isSharedCheck_3026_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3026_ == 0)
{
lean_object* v_unused_3027_; 
v_unused_3027_ = lean_ctor_get(v___x_3019_, 0);
lean_dec(v_unused_3027_);
v___x_3021_ = v___x_3019_;
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
else
{
lean_dec(v___x_3019_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3026_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 0, v_fst_2978_);
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3025_; 
v_reuseFailAlloc_3025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3025_, 0, v_fst_2978_);
v___x_3024_ = v_reuseFailAlloc_3025_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
return v___x_3024_;
}
}
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v_fst_2978_);
v_a_3028_ = lean_ctor_get(v___x_3019_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3019_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3019_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3019_);
v___x_3030_ = lean_box(0);
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
v_resetjp_3029_:
{
lean_object* v___x_3033_; 
if (v_isShared_3031_ == 0)
{
v___x_3033_ = v___x_3030_;
goto v_reusejp_3032_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_a_3028_);
v___x_3033_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3032_;
}
v_reusejp_3032_:
{
return v___x_3033_;
}
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_del_object(v___x_2980_);
lean_dec(v_fst_2978_);
lean_dec_ref(v_inst_2942_);
v_a_3037_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3001_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3001_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3042_; 
if (v_isShared_3040_ == 0)
{
v___x_3042_ = v___x_3039_;
goto v_reusejp_3041_;
}
else
{
lean_object* v_reuseFailAlloc_3043_; 
v_reuseFailAlloc_3043_ = lean_alloc_ctor(1, 1, 0);
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
}
}
}
}
}
}
else
{
lean_object* v_a_3067_; lean_object* v___x_3069_; uint8_t v_isShared_3070_; uint8_t v_isSharedCheck_3074_; 
lean_dec_ref(v_argVars_2945_);
lean_dec_ref(v_inst_2942_);
lean_dec_ref(v_a_2939_);
v_a_3067_ = lean_ctor_get(v___x_2973_, 0);
v_isSharedCheck_3074_ = !lean_is_exclusive(v___x_2973_);
if (v_isSharedCheck_3074_ == 0)
{
v___x_3069_ = v___x_2973_;
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
else
{
lean_inc(v_a_3067_);
lean_dec(v___x_2973_);
v___x_3069_ = lean_box(0);
v_isShared_3070_ = v_isSharedCheck_3074_;
goto v_resetjp_3068_;
}
v_resetjp_3068_:
{
lean_object* v___x_3072_; 
if (v_isShared_3070_ == 0)
{
v___x_3072_ = v___x_3069_;
goto v_reusejp_3071_;
}
else
{
lean_object* v_reuseFailAlloc_3073_; 
v_reuseFailAlloc_3073_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3073_, 0, v_a_3067_);
v___x_3072_ = v_reuseFailAlloc_3073_;
goto v_reusejp_3071_;
}
v_reusejp_3071_:
{
return v___x_3072_;
}
}
}
}
else
{
lean_object* v_a_3075_; lean_object* v___x_3077_; uint8_t v_isShared_3078_; uint8_t v_isSharedCheck_3082_; 
lean_dec_ref(v_argVars_2945_);
lean_dec_ref(v_a_2943_);
lean_dec_ref(v_inst_2942_);
lean_dec_ref(v_fst_2940_);
lean_dec_ref(v_a_2939_);
v_a_3075_ = lean_ctor_get(v___x_2965_, 0);
v_isSharedCheck_3082_ = !lean_is_exclusive(v___x_2965_);
if (v_isSharedCheck_3082_ == 0)
{
v___x_3077_ = v___x_2965_;
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
else
{
lean_inc(v_a_3075_);
lean_dec(v___x_2965_);
v___x_3077_ = lean_box(0);
v_isShared_3078_ = v_isSharedCheck_3082_;
goto v_resetjp_3076_;
}
v_resetjp_3076_:
{
lean_object* v___x_3080_; 
if (v_isShared_3078_ == 0)
{
v___x_3080_ = v___x_3077_;
goto v_reusejp_3079_;
}
else
{
lean_object* v_reuseFailAlloc_3081_; 
v_reuseFailAlloc_3081_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3081_, 0, v_a_3075_);
v___x_3080_ = v_reuseFailAlloc_3081_;
goto v_reusejp_3079_;
}
v_reusejp_3079_:
{
return v___x_3080_;
}
}
}
}
else
{
lean_dec_ref(v_argVars_2945_);
lean_dec_ref(v_a_2943_);
lean_dec_ref(v_inst_2942_);
lean_dec_ref(v_fst_2940_);
lean_dec_ref(v_a_2939_);
return v___x_2952_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_3083_, lean_object* v_fst_3084_, lean_object* v_fst_3085_, lean_object* v_inst_3086_, lean_object* v_a_3087_, lean_object* v_projInfo_x3f_3088_, lean_object* v_argVars_3089_, lean_object* v_x_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_, lean_object* v___y_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_3083_, v_fst_3084_, v_fst_3085_, v_inst_3086_, v_a_3087_, v_projInfo_x3f_3088_, v_argVars_3089_, v_x_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
lean_dec(v___y_3094_);
lean_dec_ref(v___y_3093_);
lean_dec(v___y_3092_);
lean_dec_ref(v___y_3091_);
lean_dec_ref(v_x_3090_);
lean_dec(v_projInfo_x3f_3088_);
lean_dec_ref(v_fst_3085_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(lean_object* v_inst_3097_, lean_object* v_projInfo_x3f_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v___x_3104_; 
lean_inc(v___y_3102_);
lean_inc_ref(v___y_3101_);
lean_inc(v___y_3100_);
lean_inc_ref(v___y_3099_);
lean_inc_ref(v_inst_3097_);
v___x_3104_ = lean_infer_type(v_inst_3097_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3104_) == 0)
{
lean_object* v_a_3105_; lean_object* v___x_3106_; uint8_t v___x_3107_; lean_object* v___x_3108_; 
v_a_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc_n(v_a_3105_, 2);
lean_dec_ref_known(v___x_3104_, 1);
v___x_3106_ = lean_box(0);
v___x_3107_ = 0;
v___x_3108_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3105_, v___x_3106_, v___x_3107_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3108_) == 0)
{
lean_object* v_a_3109_; lean_object* v_snd_3110_; lean_object* v_fst_3111_; lean_object* v_fst_3112_; lean_object* v_snd_3113_; lean_object* v___x_3114_; 
v_a_3109_ = lean_ctor_get(v___x_3108_, 0);
lean_inc(v_a_3109_);
lean_dec_ref_known(v___x_3108_, 1);
v_snd_3110_ = lean_ctor_get(v_a_3109_, 1);
lean_inc(v_snd_3110_);
v_fst_3111_ = lean_ctor_get(v_a_3109_, 0);
lean_inc(v_fst_3111_);
lean_dec(v_a_3109_);
v_fst_3112_ = lean_ctor_get(v_snd_3110_, 0);
lean_inc(v_fst_3112_);
v_snd_3113_ = lean_ctor_get(v_snd_3110_, 1);
lean_inc(v_snd_3113_);
lean_dec(v_snd_3110_);
lean_inc(v___y_3102_);
lean_inc_ref(v___y_3101_);
lean_inc(v___y_3100_);
lean_inc_ref(v___y_3099_);
v___x_3114_ = lean_whnf(v_snd_3113_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
if (lean_obj_tag(v___x_3114_) == 0)
{
lean_object* v_a_3115_; lean_object* v___f_3116_; uint8_t v___x_3117_; lean_object* v___x_3118_; 
v_a_3115_ = lean_ctor_get(v___x_3114_, 0);
lean_inc(v_a_3115_);
lean_dec_ref_known(v___x_3114_, 1);
lean_inc(v_a_3105_);
v___f_3116_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3116_, 0, v_a_3115_);
lean_closure_set(v___f_3116_, 1, v_fst_3111_);
lean_closure_set(v___f_3116_, 2, v_fst_3112_);
lean_closure_set(v___f_3116_, 3, v_inst_3097_);
lean_closure_set(v___f_3116_, 4, v_a_3105_);
lean_closure_set(v___f_3116_, 5, v_projInfo_x3f_3098_);
v___x_3117_ = 0;
v___x_3118_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3105_, v___f_3116_, v___x_3117_, v___x_3117_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
return v___x_3118_;
}
else
{
lean_object* v_a_3119_; lean_object* v___x_3121_; uint8_t v_isShared_3122_; uint8_t v_isSharedCheck_3126_; 
lean_dec(v_fst_3112_);
lean_dec(v_fst_3111_);
lean_dec(v_a_3105_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v_projInfo_x3f_3098_);
lean_dec_ref(v_inst_3097_);
v_a_3119_ = lean_ctor_get(v___x_3114_, 0);
v_isSharedCheck_3126_ = !lean_is_exclusive(v___x_3114_);
if (v_isSharedCheck_3126_ == 0)
{
v___x_3121_ = v___x_3114_;
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
else
{
lean_inc(v_a_3119_);
lean_dec(v___x_3114_);
v___x_3121_ = lean_box(0);
v_isShared_3122_ = v_isSharedCheck_3126_;
goto v_resetjp_3120_;
}
v_resetjp_3120_:
{
lean_object* v___x_3124_; 
if (v_isShared_3122_ == 0)
{
v___x_3124_ = v___x_3121_;
goto v_reusejp_3123_;
}
else
{
lean_object* v_reuseFailAlloc_3125_; 
v_reuseFailAlloc_3125_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3125_, 0, v_a_3119_);
v___x_3124_ = v_reuseFailAlloc_3125_;
goto v_reusejp_3123_;
}
v_reusejp_3123_:
{
return v___x_3124_;
}
}
}
}
else
{
lean_object* v_a_3127_; lean_object* v___x_3129_; uint8_t v_isShared_3130_; uint8_t v_isSharedCheck_3134_; 
lean_dec(v_a_3105_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v_projInfo_x3f_3098_);
lean_dec_ref(v_inst_3097_);
v_a_3127_ = lean_ctor_get(v___x_3108_, 0);
v_isSharedCheck_3134_ = !lean_is_exclusive(v___x_3108_);
if (v_isSharedCheck_3134_ == 0)
{
v___x_3129_ = v___x_3108_;
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
else
{
lean_inc(v_a_3127_);
lean_dec(v___x_3108_);
v___x_3129_ = lean_box(0);
v_isShared_3130_ = v_isSharedCheck_3134_;
goto v_resetjp_3128_;
}
v_resetjp_3128_:
{
lean_object* v___x_3132_; 
if (v_isShared_3130_ == 0)
{
v___x_3132_ = v___x_3129_;
goto v_reusejp_3131_;
}
else
{
lean_object* v_reuseFailAlloc_3133_; 
v_reuseFailAlloc_3133_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3133_, 0, v_a_3127_);
v___x_3132_ = v_reuseFailAlloc_3133_;
goto v_reusejp_3131_;
}
v_reusejp_3131_:
{
return v___x_3132_;
}
}
}
}
else
{
lean_object* v_a_3135_; lean_object* v___x_3137_; uint8_t v_isShared_3138_; uint8_t v_isSharedCheck_3142_; 
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v_projInfo_x3f_3098_);
lean_dec_ref(v_inst_3097_);
v_a_3135_ = lean_ctor_get(v___x_3104_, 0);
v_isSharedCheck_3142_ = !lean_is_exclusive(v___x_3104_);
if (v_isSharedCheck_3142_ == 0)
{
v___x_3137_ = v___x_3104_;
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
else
{
lean_inc(v_a_3135_);
lean_dec(v___x_3104_);
v___x_3137_ = lean_box(0);
v_isShared_3138_ = v_isSharedCheck_3142_;
goto v_resetjp_3136_;
}
v_resetjp_3136_:
{
lean_object* v___x_3140_; 
if (v_isShared_3138_ == 0)
{
v___x_3140_ = v___x_3137_;
goto v_reusejp_3139_;
}
else
{
lean_object* v_reuseFailAlloc_3141_; 
v_reuseFailAlloc_3141_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3141_, 0, v_a_3135_);
v___x_3140_ = v_reuseFailAlloc_3141_;
goto v_reusejp_3139_;
}
v_reusejp_3139_:
{
return v___x_3140_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1___boxed(lean_object* v_inst_3143_, lean_object* v_projInfo_x3f_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_){
_start:
{
lean_object* v_res_3150_; 
v_res_3150_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3143_, v_projInfo_x3f_3144_, v___y_3145_, v___y_3146_, v___y_3147_, v___y_3148_);
return v_res_3150_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_3151_, lean_object* v_projInfo_x3f_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_, lean_object* v_a_3156_){
_start:
{
lean_object* v___y_3159_; lean_object* v___x_3176_; uint8_t v_transparency_3177_; uint8_t v___x_3178_; uint8_t v___x_3179_; 
v___x_3176_ = l_Lean_Meta_Context_config(v_a_3153_);
v_transparency_3177_ = lean_ctor_get_uint8(v___x_3176_, 9);
lean_dec_ref(v___x_3176_);
v___x_3178_ = 2;
v___x_3179_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3177_, v___x_3178_);
if (v___x_3179_ == 0)
{
lean_object* v_keyedConfig_3180_; uint8_t v_trackZetaDelta_3181_; lean_object* v_zetaDeltaSet_3182_; lean_object* v_lctx_3183_; lean_object* v_localInstances_3184_; lean_object* v_defEqCtx_x3f_3185_; lean_object* v_synthPendingDepth_3186_; lean_object* v_customCanUnfoldPredicate_x3f_3187_; uint8_t v_univApprox_3188_; uint8_t v_inTypeClassResolution_3189_; uint8_t v_cacheInferType_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; lean_object* v___x_3193_; 
v_keyedConfig_3180_ = lean_ctor_get(v_a_3153_, 0);
v_trackZetaDelta_3181_ = lean_ctor_get_uint8(v_a_3153_, sizeof(void*)*7);
v_zetaDeltaSet_3182_ = lean_ctor_get(v_a_3153_, 1);
v_lctx_3183_ = lean_ctor_get(v_a_3153_, 2);
v_localInstances_3184_ = lean_ctor_get(v_a_3153_, 3);
v_defEqCtx_x3f_3185_ = lean_ctor_get(v_a_3153_, 4);
v_synthPendingDepth_3186_ = lean_ctor_get(v_a_3153_, 5);
v_customCanUnfoldPredicate_x3f_3187_ = lean_ctor_get(v_a_3153_, 6);
v_univApprox_3188_ = lean_ctor_get_uint8(v_a_3153_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3189_ = lean_ctor_get_uint8(v_a_3153_, sizeof(void*)*7 + 2);
v_cacheInferType_3190_ = lean_ctor_get_uint8(v_a_3153_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3180_);
v___x_3191_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3178_, v_keyedConfig_3180_);
lean_inc(v_customCanUnfoldPredicate_x3f_3187_);
lean_inc(v_synthPendingDepth_3186_);
lean_inc(v_defEqCtx_x3f_3185_);
lean_inc_ref(v_localInstances_3184_);
lean_inc_ref(v_lctx_3183_);
lean_inc(v_zetaDeltaSet_3182_);
v___x_3192_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3192_, 0, v___x_3191_);
lean_ctor_set(v___x_3192_, 1, v_zetaDeltaSet_3182_);
lean_ctor_set(v___x_3192_, 2, v_lctx_3183_);
lean_ctor_set(v___x_3192_, 3, v_localInstances_3184_);
lean_ctor_set(v___x_3192_, 4, v_defEqCtx_x3f_3185_);
lean_ctor_set(v___x_3192_, 5, v_synthPendingDepth_3186_);
lean_ctor_set(v___x_3192_, 6, v_customCanUnfoldPredicate_x3f_3187_);
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*7, v_trackZetaDelta_3181_);
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*7 + 1, v_univApprox_3188_);
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3189_);
lean_ctor_set_uint8(v___x_3192_, sizeof(void*)*7 + 3, v_cacheInferType_3190_);
lean_inc(v_a_3156_);
lean_inc_ref(v_a_3155_);
lean_inc(v_a_3154_);
v___x_3193_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3151_, v_projInfo_x3f_3152_, v___x_3192_, v_a_3154_, v_a_3155_, v_a_3156_);
v___y_3159_ = v___x_3193_;
goto v___jp_3158_;
}
else
{
lean_object* v___x_3194_; 
lean_inc(v_a_3156_);
lean_inc_ref(v_a_3155_);
lean_inc(v_a_3154_);
lean_inc_ref(v_a_3153_);
v___x_3194_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3151_, v_projInfo_x3f_3152_, v_a_3153_, v_a_3154_, v_a_3155_, v_a_3156_);
v___y_3159_ = v___x_3194_;
goto v___jp_3158_;
}
v___jp_3158_:
{
if (lean_obj_tag(v___y_3159_) == 0)
{
lean_object* v_a_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3167_; 
v_a_3160_ = lean_ctor_get(v___y_3159_, 0);
v_isSharedCheck_3167_ = !lean_is_exclusive(v___y_3159_);
if (v_isSharedCheck_3167_ == 0)
{
v___x_3162_ = v___y_3159_;
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
else
{
lean_inc(v_a_3160_);
lean_dec(v___y_3159_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3167_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3165_; 
if (v_isShared_3163_ == 0)
{
v___x_3165_ = v___x_3162_;
goto v_reusejp_3164_;
}
else
{
lean_object* v_reuseFailAlloc_3166_; 
v_reuseFailAlloc_3166_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3166_, 0, v_a_3160_);
v___x_3165_ = v_reuseFailAlloc_3166_;
goto v_reusejp_3164_;
}
v_reusejp_3164_:
{
return v___x_3165_;
}
}
}
else
{
lean_object* v_a_3168_; lean_object* v___x_3170_; uint8_t v_isShared_3171_; uint8_t v_isSharedCheck_3175_; 
v_a_3168_ = lean_ctor_get(v___y_3159_, 0);
v_isSharedCheck_3175_ = !lean_is_exclusive(v___y_3159_);
if (v_isSharedCheck_3175_ == 0)
{
v___x_3170_ = v___y_3159_;
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
else
{
lean_inc(v_a_3168_);
lean_dec(v___y_3159_);
v___x_3170_ = lean_box(0);
v_isShared_3171_ = v_isSharedCheck_3175_;
goto v_resetjp_3169_;
}
v_resetjp_3169_:
{
lean_object* v___x_3173_; 
if (v_isShared_3171_ == 0)
{
v___x_3173_ = v___x_3170_;
goto v_reusejp_3172_;
}
else
{
lean_object* v_reuseFailAlloc_3174_; 
v_reuseFailAlloc_3174_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3174_, 0, v_a_3168_);
v___x_3173_ = v_reuseFailAlloc_3174_;
goto v_reusejp_3172_;
}
v_reusejp_3172_:
{
return v___x_3173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_3195_, lean_object* v_projInfo_x3f_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_, lean_object* v_a_3201_){
_start:
{
lean_object* v_res_3202_; 
v_res_3202_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_3195_, v_projInfo_x3f_3196_, v_a_3197_, v_a_3198_, v_a_3199_, v_a_3200_);
lean_dec(v_a_3200_);
lean_dec_ref(v_a_3199_);
lean_dec(v_a_3198_);
lean_dec_ref(v_a_3197_);
return v_res_3202_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_3203_, lean_object* v_a_3204_, lean_object* v___x_3205_, lean_object* v_inst_3206_, lean_object* v_R_3207_, lean_object* v_a_3208_, lean_object* v_b_3209_, lean_object* v_c_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_, lean_object* v___y_3214_){
_start:
{
lean_object* v___x_3216_; 
v___x_3216_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_3203_, v_a_3204_, v___x_3205_, v_a_3208_, v_b_3209_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_3217_, lean_object* v_a_3218_, lean_object* v___x_3219_, lean_object* v_inst_3220_, lean_object* v_R_3221_, lean_object* v_a_3222_, lean_object* v_b_3223_, lean_object* v_c_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_){
_start:
{
lean_object* v_res_3230_; 
v_res_3230_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_3217_, v_a_3218_, v___x_3219_, v_inst_3220_, v_R_3221_, v_a_3222_, v_b_3223_, v_c_3224_, v___y_3225_, v___y_3226_, v___y_3227_, v___y_3228_);
lean_dec(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v___y_3225_);
lean_dec(v___x_3219_);
lean_dec_ref(v_a_3218_);
lean_dec(v_upperBound_3217_);
return v_res_3230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3231_, lean_object* v_msg_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3239_, lean_object* v_msg_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_){
_start:
{
lean_object* v_res_3246_; 
v_res_3246_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3239_, v_msg_3240_, v___y_3241_, v___y_3242_, v___y_3243_, v___y_3244_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
lean_dec(v___y_3242_);
lean_dec_ref(v___y_3241_);
return v_res_3246_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_3247_, lean_object* v_argVars_3248_, lean_object* v_inst_3249_, lean_object* v_a_3250_, lean_object* v_projInfo_x3f_3251_, lean_object* v_inst_3252_, lean_object* v_a_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v___x_3259_; 
v___x_3259_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_3247_, v_argVars_3248_, v_inst_3249_, v_a_3250_, v_projInfo_x3f_3251_, v_a_3253_, v___y_3254_, v___y_3255_, v___y_3256_, v___y_3257_);
return v___x_3259_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_3260_, lean_object* v_argVars_3261_, lean_object* v_inst_3262_, lean_object* v_a_3263_, lean_object* v_projInfo_x3f_3264_, lean_object* v_inst_3265_, lean_object* v_a_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_, lean_object* v___y_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_3260_, v_argVars_3261_, v_inst_3262_, v_a_3263_, v_projInfo_x3f_3264_, v_inst_3265_, v_a_3266_, v___y_3267_, v___y_3268_, v___y_3269_, v___y_3270_);
lean_dec(v___y_3270_);
lean_dec_ref(v___y_3269_);
lean_dec(v___y_3268_);
lean_dec_ref(v___y_3267_);
lean_dec(v_projInfo_x3f_3264_);
return v_res_3272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(lean_object* v_type_3273_, lean_object* v_k_3274_, uint8_t v_cleanupAnnotations_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_, lean_object* v___y_3279_){
_start:
{
lean_object* v___f_3281_; uint8_t v___x_3282_; lean_object* v___x_3283_; lean_object* v___x_3284_; 
v___f_3281_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3281_, 0, v_k_3274_);
v___x_3282_ = 0;
v___x_3283_ = lean_box(0);
v___x_3284_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3282_, v___x_3283_, v_type_3273_, v___f_3281_, v_cleanupAnnotations_3275_, v___x_3282_, v___y_3276_, v___y_3277_, v___y_3278_, v___y_3279_);
if (lean_obj_tag(v___x_3284_) == 0)
{
lean_object* v_a_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3292_; 
v_a_3285_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3292_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3292_ == 0)
{
v___x_3287_ = v___x_3284_;
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_a_3285_);
lean_dec(v___x_3284_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3292_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v___x_3290_; 
if (v_isShared_3288_ == 0)
{
v___x_3290_ = v___x_3287_;
goto v_reusejp_3289_;
}
else
{
lean_object* v_reuseFailAlloc_3291_; 
v_reuseFailAlloc_3291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3291_, 0, v_a_3285_);
v___x_3290_ = v_reuseFailAlloc_3291_;
goto v_reusejp_3289_;
}
v_reusejp_3289_:
{
return v___x_3290_;
}
}
}
else
{
lean_object* v_a_3293_; lean_object* v___x_3295_; uint8_t v_isShared_3296_; uint8_t v_isSharedCheck_3300_; 
v_a_3293_ = lean_ctor_get(v___x_3284_, 0);
v_isSharedCheck_3300_ = !lean_is_exclusive(v___x_3284_);
if (v_isSharedCheck_3300_ == 0)
{
v___x_3295_ = v___x_3284_;
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
else
{
lean_inc(v_a_3293_);
lean_dec(v___x_3284_);
v___x_3295_ = lean_box(0);
v_isShared_3296_ = v_isSharedCheck_3300_;
goto v_resetjp_3294_;
}
v_resetjp_3294_:
{
lean_object* v___x_3298_; 
if (v_isShared_3296_ == 0)
{
v___x_3298_ = v___x_3295_;
goto v_reusejp_3297_;
}
else
{
lean_object* v_reuseFailAlloc_3299_; 
v_reuseFailAlloc_3299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3299_, 0, v_a_3293_);
v___x_3298_ = v_reuseFailAlloc_3299_;
goto v_reusejp_3297_;
}
v_reusejp_3297_:
{
return v___x_3298_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg___boxed(lean_object* v_type_3301_, lean_object* v_k_3302_, lean_object* v_cleanupAnnotations_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_, lean_object* v___y_3308_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3309_; lean_object* v_res_3310_; 
v_cleanupAnnotations_boxed_3309_ = lean_unbox(v_cleanupAnnotations_3303_);
v_res_3310_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3301_, v_k_3302_, v_cleanupAnnotations_boxed_3309_, v___y_3304_, v___y_3305_, v___y_3306_, v___y_3307_);
lean_dec(v___y_3307_);
lean_dec_ref(v___y_3306_);
lean_dec(v___y_3305_);
lean_dec_ref(v___y_3304_);
return v_res_3310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(lean_object* v_00_u03b1_3311_, lean_object* v_type_3312_, lean_object* v_k_3313_, uint8_t v_cleanupAnnotations_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_){
_start:
{
lean_object* v___x_3320_; 
v___x_3320_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3312_, v_k_3313_, v_cleanupAnnotations_3314_, v___y_3315_, v___y_3316_, v___y_3317_, v___y_3318_);
return v___x_3320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___boxed(lean_object* v_00_u03b1_3321_, lean_object* v_type_3322_, lean_object* v_k_3323_, lean_object* v_cleanupAnnotations_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_, lean_object* v___y_3329_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3330_; lean_object* v_res_3331_; 
v_cleanupAnnotations_boxed_3330_ = lean_unbox(v_cleanupAnnotations_3324_);
v_res_3331_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(v_00_u03b1_3321_, v_type_3322_, v_k_3323_, v_cleanupAnnotations_boxed_3330_, v___y_3325_, v___y_3326_, v___y_3327_, v___y_3328_);
lean_dec(v___y_3328_);
lean_dec_ref(v___y_3327_);
lean_dec(v___y_3326_);
lean_dec_ref(v___y_3325_);
return v_res_3331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(lean_object* v_as_3332_, size_t v_sz_3333_, size_t v_i_3334_, lean_object* v_b_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_, lean_object* v___y_3339_){
_start:
{
lean_object* v_a_3342_; uint8_t v___x_3346_; 
v___x_3346_ = lean_usize_dec_lt(v_i_3334_, v_sz_3333_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3347_; 
v___x_3347_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3347_, 0, v_b_3335_);
return v___x_3347_;
}
else
{
lean_object* v___x_3348_; lean_object* v_a_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v___x_3348_ = lean_box(0);
v_a_3349_ = lean_array_uget_borrowed(v_as_3332_, v_i_3334_);
v___x_3350_ = l_Lean_Expr_fvarId_x21(v_a_3349_);
lean_inc(v___x_3350_);
v___x_3351_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_3350_, v___y_3337_, v___y_3338_, v___y_3339_);
if (lean_obj_tag(v___x_3351_) == 0)
{
lean_object* v_a_3352_; uint8_t v___x_3353_; uint8_t v___x_3354_; 
v_a_3352_ = lean_ctor_get(v___x_3351_, 0);
lean_inc(v_a_3352_);
lean_dec_ref_known(v___x_3351_, 1);
v___x_3353_ = lean_unbox(v_a_3352_);
lean_dec(v_a_3352_);
v___x_3354_ = l_Lean_BinderInfo_isInstImplicit(v___x_3353_);
if (v___x_3354_ == 0)
{
lean_dec(v___x_3350_);
v_a_3342_ = v___x_3348_;
goto v___jp_3341_;
}
else
{
lean_object* v___x_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; 
v___x_3355_ = lean_st_ref_take(v___y_3336_);
v___x_3356_ = l_Lean_CollectFVars_State_add(v___x_3355_, v___x_3350_);
v___x_3357_ = lean_st_ref_put(v___y_3336_, v___x_3356_);
v_a_3342_ = v___x_3348_;
goto v___jp_3341_;
}
}
else
{
lean_object* v_a_3358_; lean_object* v___x_3360_; uint8_t v_isShared_3361_; uint8_t v_isSharedCheck_3365_; 
lean_dec(v___x_3350_);
v_a_3358_ = lean_ctor_get(v___x_3351_, 0);
v_isSharedCheck_3365_ = !lean_is_exclusive(v___x_3351_);
if (v_isSharedCheck_3365_ == 0)
{
v___x_3360_ = v___x_3351_;
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
else
{
lean_inc(v_a_3358_);
lean_dec(v___x_3351_);
v___x_3360_ = lean_box(0);
v_isShared_3361_ = v_isSharedCheck_3365_;
goto v_resetjp_3359_;
}
v_resetjp_3359_:
{
lean_object* v___x_3363_; 
if (v_isShared_3361_ == 0)
{
v___x_3363_ = v___x_3360_;
goto v_reusejp_3362_;
}
else
{
lean_object* v_reuseFailAlloc_3364_; 
v_reuseFailAlloc_3364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3364_, 0, v_a_3358_);
v___x_3363_ = v_reuseFailAlloc_3364_;
goto v_reusejp_3362_;
}
v_reusejp_3362_:
{
return v___x_3363_;
}
}
}
}
v___jp_3341_:
{
size_t v___x_3343_; size_t v___x_3344_; 
v___x_3343_ = ((size_t)1ULL);
v___x_3344_ = lean_usize_add(v_i_3334_, v___x_3343_);
v_i_3334_ = v___x_3344_;
v_b_3335_ = v_a_3342_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg___boxed(lean_object* v_as_3366_, lean_object* v_sz_3367_, lean_object* v_i_3368_, lean_object* v_b_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_, lean_object* v___y_3374_){
_start:
{
size_t v_sz_boxed_3375_; size_t v_i_boxed_3376_; lean_object* v_res_3377_; 
v_sz_boxed_3375_ = lean_unbox_usize(v_sz_3367_);
lean_dec(v_sz_3367_);
v_i_boxed_3376_ = lean_unbox_usize(v_i_3368_);
lean_dec(v_i_3368_);
v_res_3377_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_as_3366_, v_sz_boxed_3375_, v_i_boxed_3376_, v_b_3369_, v___y_3370_, v___y_3371_, v___y_3372_, v___y_3373_);
lean_dec(v___y_3373_);
lean_dec_ref(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec(v___y_3370_);
lean_dec_ref(v_as_3366_);
return v_res_3377_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(uint8_t v_suppressElabErrors_3385_, lean_object* v_x_3386_){
_start:
{
if (lean_obj_tag(v_x_3386_) == 1)
{
lean_object* v_pre_3387_; 
v_pre_3387_ = lean_ctor_get(v_x_3386_, 0);
switch(lean_obj_tag(v_pre_3387_))
{
case 1:
{
lean_object* v_pre_3388_; 
v_pre_3388_ = lean_ctor_get(v_pre_3387_, 0);
switch(lean_obj_tag(v_pre_3388_))
{
case 0:
{
lean_object* v_str_3389_; lean_object* v_str_3390_; lean_object* v___x_3391_; uint8_t v___x_3392_; 
v_str_3389_ = lean_ctor_get(v_x_3386_, 1);
v_str_3390_ = lean_ctor_get(v_pre_3387_, 1);
v___x_3391_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__0));
v___x_3392_ = lean_string_dec_eq(v_str_3390_, v___x_3391_);
if (v___x_3392_ == 0)
{
lean_object* v___x_3393_; uint8_t v___x_3394_; 
v___x_3393_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__1));
v___x_3394_ = lean_string_dec_eq(v_str_3390_, v___x_3393_);
if (v___x_3394_ == 0)
{
return v___x_3394_;
}
else
{
lean_object* v___x_3395_; uint8_t v___x_3396_; 
v___x_3395_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__2));
v___x_3396_ = lean_string_dec_eq(v_str_3389_, v___x_3395_);
if (v___x_3396_ == 0)
{
return v___x_3396_;
}
else
{
return v_suppressElabErrors_3385_;
}
}
}
else
{
lean_object* v___x_3397_; uint8_t v___x_3398_; 
v___x_3397_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__3));
v___x_3398_ = lean_string_dec_eq(v_str_3389_, v___x_3397_);
if (v___x_3398_ == 0)
{
return v___x_3398_;
}
else
{
return v_suppressElabErrors_3385_;
}
}
}
case 1:
{
lean_object* v_pre_3399_; 
v_pre_3399_ = lean_ctor_get(v_pre_3388_, 0);
if (lean_obj_tag(v_pre_3399_) == 0)
{
lean_object* v_str_3400_; lean_object* v_str_3401_; lean_object* v_str_3402_; lean_object* v___x_3403_; uint8_t v___x_3404_; 
v_str_3400_ = lean_ctor_get(v_x_3386_, 1);
v_str_3401_ = lean_ctor_get(v_pre_3387_, 1);
v_str_3402_ = lean_ctor_get(v_pre_3388_, 1);
v___x_3403_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__4));
v___x_3404_ = lean_string_dec_eq(v_str_3402_, v___x_3403_);
if (v___x_3404_ == 0)
{
return v___x_3404_;
}
else
{
lean_object* v___x_3405_; uint8_t v___x_3406_; 
v___x_3405_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__5));
v___x_3406_ = lean_string_dec_eq(v_str_3401_, v___x_3405_);
if (v___x_3406_ == 0)
{
return v___x_3406_;
}
else
{
lean_object* v___x_3407_; uint8_t v___x_3408_; 
v___x_3407_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__6));
v___x_3408_ = lean_string_dec_eq(v_str_3400_, v___x_3407_);
if (v___x_3408_ == 0)
{
return v___x_3408_;
}
else
{
return v_suppressElabErrors_3385_;
}
}
}
}
else
{
uint8_t v___x_3409_; 
v___x_3409_ = 0;
return v___x_3409_;
}
}
default: 
{
uint8_t v___x_3410_; 
v___x_3410_ = 0;
return v___x_3410_;
}
}
}
case 0:
{
lean_object* v_str_3411_; lean_object* v___x_3412_; uint8_t v___x_3413_; 
v_str_3411_ = lean_ctor_get(v_x_3386_, 1);
v___x_3412_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3413_ = lean_string_dec_eq(v_str_3411_, v___x_3412_);
if (v___x_3413_ == 0)
{
return v___x_3413_;
}
else
{
return v_suppressElabErrors_3385_;
}
}
default: 
{
uint8_t v___x_3414_; 
v___x_3414_ = 0;
return v___x_3414_;
}
}
}
else
{
uint8_t v___x_3415_; 
v___x_3415_ = 0;
return v___x_3415_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_3416_, lean_object* v_x_3417_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3418_; uint8_t v_res_3419_; lean_object* v_r_3420_; 
v_suppressElabErrors_boxed_3418_ = lean_unbox(v_suppressElabErrors_3416_);
v_res_3419_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(v_suppressElabErrors_boxed_3418_, v_x_3417_);
lean_dec(v_x_3417_);
v_r_3420_ = lean_box(v_res_3419_);
return v_r_3420_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(lean_object* v_ref_3421_, lean_object* v_msgData_3422_, uint8_t v_severity_3423_, uint8_t v_isSilent_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_){
_start:
{
lean_object* v___y_3431_; lean_object* v___y_3432_; lean_object* v___y_3433_; uint8_t v___y_3434_; lean_object* v___y_3435_; lean_object* v___y_3436_; uint8_t v___y_3437_; lean_object* v_toCold_3438_; lean_object* v___y_3439_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; uint8_t v___y_3471_; lean_object* v___y_3472_; uint8_t v___y_3473_; uint8_t v___y_3474_; lean_object* v___y_3475_; lean_object* v___y_3495_; uint8_t v___y_3496_; lean_object* v___y_3497_; uint8_t v___y_3498_; lean_object* v___y_3499_; uint8_t v___y_3500_; lean_object* v___y_3501_; uint8_t v___y_3505_; uint8_t v___y_3506_; uint8_t v___x_3516_; uint8_t v___y_3518_; uint8_t v___x_3524_; 
v___x_3516_ = 2;
v___x_3524_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3423_, v___x_3516_);
if (v___x_3524_ == 0)
{
v___y_3518_ = v___x_3524_;
goto v___jp_3517_;
}
else
{
uint8_t v___x_3525_; 
lean_inc_ref(v_msgData_3422_);
v___x_3525_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3422_);
if (v___x_3525_ == 0)
{
v___y_3518_ = v___x_3525_;
goto v___jp_3517_;
}
else
{
lean_object* v___x_3526_; lean_object* v___x_3527_; 
lean_dec_ref(v_msgData_3422_);
v___x_3526_ = lean_box(0);
v___x_3527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3527_, 0, v___x_3526_);
return v___x_3527_;
}
}
v___jp_3430_:
{
lean_object* v_currNamespace_3440_; lean_object* v_openDecls_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v___x_3445_; lean_object* v_env_3446_; lean_object* v_nextMacroScope_3447_; lean_object* v_ngen_3448_; lean_object* v_auxDeclNGen_3449_; lean_object* v_traceState_3450_; lean_object* v_cache_3451_; lean_object* v_recordedDeps_3452_; lean_object* v_messages_3453_; lean_object* v_infoState_3454_; lean_object* v_snapshotTasks_3455_; lean_object* v___x_3457_; uint8_t v_isShared_3458_; uint8_t v_isSharedCheck_3466_; 
v_currNamespace_3440_ = lean_ctor_get(v_toCold_3438_, 4);
v_openDecls_3441_ = lean_ctor_get(v_toCold_3438_, 5);
lean_inc(v_openDecls_3441_);
lean_inc(v_currNamespace_3440_);
v___x_3442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3442_, 0, v_currNamespace_3440_);
lean_ctor_set(v___x_3442_, 1, v_openDecls_3441_);
v___x_3443_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3443_, 0, v___x_3442_);
lean_ctor_set(v___x_3443_, 1, v___y_3435_);
lean_inc_ref(v___y_3436_);
lean_inc_ref(v___y_3432_);
v___x_3444_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3444_, 0, v___y_3432_);
lean_ctor_set(v___x_3444_, 1, v___y_3433_);
lean_ctor_set(v___x_3444_, 2, v___y_3431_);
lean_ctor_set(v___x_3444_, 3, v___y_3436_);
lean_ctor_set(v___x_3444_, 4, v___x_3443_);
lean_ctor_set_uint8(v___x_3444_, sizeof(void*)*5, v___y_3437_);
lean_ctor_set_uint8(v___x_3444_, sizeof(void*)*5 + 1, v___y_3434_);
lean_ctor_set_uint8(v___x_3444_, sizeof(void*)*5 + 2, v_isSilent_3424_);
v___x_3445_ = lean_st_ref_take(v___y_3439_);
v_env_3446_ = lean_ctor_get(v___x_3445_, 0);
v_nextMacroScope_3447_ = lean_ctor_get(v___x_3445_, 1);
v_ngen_3448_ = lean_ctor_get(v___x_3445_, 2);
v_auxDeclNGen_3449_ = lean_ctor_get(v___x_3445_, 3);
v_traceState_3450_ = lean_ctor_get(v___x_3445_, 4);
v_cache_3451_ = lean_ctor_get(v___x_3445_, 5);
v_recordedDeps_3452_ = lean_ctor_get(v___x_3445_, 6);
v_messages_3453_ = lean_ctor_get(v___x_3445_, 7);
v_infoState_3454_ = lean_ctor_get(v___x_3445_, 8);
v_snapshotTasks_3455_ = lean_ctor_get(v___x_3445_, 9);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3445_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3457_ = v___x_3445_;
v_isShared_3458_ = v_isSharedCheck_3466_;
goto v_resetjp_3456_;
}
else
{
lean_inc(v_snapshotTasks_3455_);
lean_inc(v_infoState_3454_);
lean_inc(v_messages_3453_);
lean_inc(v_recordedDeps_3452_);
lean_inc(v_cache_3451_);
lean_inc(v_traceState_3450_);
lean_inc(v_auxDeclNGen_3449_);
lean_inc(v_ngen_3448_);
lean_inc(v_nextMacroScope_3447_);
lean_inc(v_env_3446_);
lean_dec(v___x_3445_);
v___x_3457_ = lean_box(0);
v_isShared_3458_ = v_isSharedCheck_3466_;
goto v_resetjp_3456_;
}
v_resetjp_3456_:
{
lean_object* v___x_3459_; lean_object* v___x_3460_; lean_object* v___x_3462_; 
v___x_3459_ = lean_box(0);
v___x_3460_ = l_Lean_MessageLog_add(v___x_3444_, v_messages_3453_);
if (v_isShared_3458_ == 0)
{
lean_ctor_set(v___x_3457_, 7, v___x_3460_);
v___x_3462_ = v___x_3457_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_env_3446_);
lean_ctor_set(v_reuseFailAlloc_3465_, 1, v_nextMacroScope_3447_);
lean_ctor_set(v_reuseFailAlloc_3465_, 2, v_ngen_3448_);
lean_ctor_set(v_reuseFailAlloc_3465_, 3, v_auxDeclNGen_3449_);
lean_ctor_set(v_reuseFailAlloc_3465_, 4, v_traceState_3450_);
lean_ctor_set(v_reuseFailAlloc_3465_, 5, v_cache_3451_);
lean_ctor_set(v_reuseFailAlloc_3465_, 6, v_recordedDeps_3452_);
lean_ctor_set(v_reuseFailAlloc_3465_, 7, v___x_3460_);
lean_ctor_set(v_reuseFailAlloc_3465_, 8, v_infoState_3454_);
lean_ctor_set(v_reuseFailAlloc_3465_, 9, v_snapshotTasks_3455_);
v___x_3462_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
lean_object* v___x_3463_; lean_object* v___x_3464_; 
v___x_3463_ = lean_st_ref_put(v___y_3439_, v___x_3462_);
v___x_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3464_, 0, v___x_3459_);
return v___x_3464_;
}
}
}
v___jp_3467_:
{
lean_object* v_fileName_3476_; lean_object* v_fileMap_3477_; lean_object* v___x_3478_; lean_object* v___x_3479_; lean_object* v_a_3480_; lean_object* v___x_3482_; uint8_t v_isShared_3483_; uint8_t v_isSharedCheck_3493_; 
v_fileName_3476_ = lean_ctor_get(v___y_3472_, 0);
v_fileMap_3477_ = lean_ctor_get(v___y_3472_, 1);
v___x_3478_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3422_);
v___x_3479_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3478_, v___y_3425_, v___y_3426_, v___y_3427_, v___y_3428_);
v_a_3480_ = lean_ctor_get(v___x_3479_, 0);
v_isSharedCheck_3493_ = !lean_is_exclusive(v___x_3479_);
if (v_isSharedCheck_3493_ == 0)
{
v___x_3482_ = v___x_3479_;
v_isShared_3483_ = v_isSharedCheck_3493_;
goto v_resetjp_3481_;
}
else
{
lean_inc(v_a_3480_);
lean_dec(v___x_3479_);
v___x_3482_ = lean_box(0);
v_isShared_3483_ = v_isSharedCheck_3493_;
goto v_resetjp_3481_;
}
v_resetjp_3481_:
{
lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; lean_object* v___x_3487_; 
lean_inc_ref_n(v_fileMap_3477_, 2);
v___x_3484_ = l_Lean_FileMap_toPosition(v_fileMap_3477_, v___y_3470_);
lean_dec(v___y_3470_);
v___x_3485_ = l_Lean_FileMap_toPosition(v_fileMap_3477_, v___y_3475_);
lean_dec(v___y_3475_);
v___x_3486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3486_, 0, v___x_3485_);
v___x_3487_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3471_ == 0)
{
lean_del_object(v___x_3482_);
lean_dec_ref(v___y_3468_);
v___y_3431_ = v___x_3486_;
v___y_3432_ = v_fileName_3476_;
v___y_3433_ = v___x_3484_;
v___y_3434_ = v___y_3473_;
v___y_3435_ = v_a_3480_;
v___y_3436_ = v___x_3487_;
v___y_3437_ = v___y_3474_;
v_toCold_3438_ = v___y_3469_;
v___y_3439_ = v___y_3428_;
goto v___jp_3430_;
}
else
{
uint8_t v___x_3488_; 
lean_inc(v_a_3480_);
v___x_3488_ = l_Lean_MessageData_hasTag(v___y_3468_, v_a_3480_);
if (v___x_3488_ == 0)
{
lean_object* v___x_3489_; lean_object* v___x_3491_; 
lean_dec_ref_known(v___x_3486_, 1);
lean_dec_ref(v___x_3484_);
lean_dec(v_a_3480_);
v___x_3489_ = lean_box(0);
if (v_isShared_3483_ == 0)
{
lean_ctor_set(v___x_3482_, 0, v___x_3489_);
v___x_3491_ = v___x_3482_;
goto v_reusejp_3490_;
}
else
{
lean_object* v_reuseFailAlloc_3492_; 
v_reuseFailAlloc_3492_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3492_, 0, v___x_3489_);
v___x_3491_ = v_reuseFailAlloc_3492_;
goto v_reusejp_3490_;
}
v_reusejp_3490_:
{
return v___x_3491_;
}
}
else
{
lean_del_object(v___x_3482_);
v___y_3431_ = v___x_3486_;
v___y_3432_ = v_fileName_3476_;
v___y_3433_ = v___x_3484_;
v___y_3434_ = v___y_3473_;
v___y_3435_ = v_a_3480_;
v___y_3436_ = v___x_3487_;
v___y_3437_ = v___y_3474_;
v_toCold_3438_ = v___y_3469_;
v___y_3439_ = v___y_3428_;
goto v___jp_3430_;
}
}
}
}
v___jp_3494_:
{
lean_object* v___x_3502_; 
v___x_3502_ = l_Lean_Syntax_getTailPos_x3f(v___y_3499_, v___y_3500_);
lean_dec(v___y_3499_);
if (lean_obj_tag(v___x_3502_) == 0)
{
lean_inc(v___y_3501_);
v___y_3468_ = v___y_3495_;
v___y_3469_ = v___y_3497_;
v___y_3470_ = v___y_3501_;
v___y_3471_ = v___y_3496_;
v___y_3472_ = v___y_3497_;
v___y_3473_ = v___y_3498_;
v___y_3474_ = v___y_3500_;
v___y_3475_ = v___y_3501_;
goto v___jp_3467_;
}
else
{
lean_object* v_val_3503_; 
v_val_3503_ = lean_ctor_get(v___x_3502_, 0);
lean_inc(v_val_3503_);
lean_dec_ref_known(v___x_3502_, 1);
v___y_3468_ = v___y_3495_;
v___y_3469_ = v___y_3497_;
v___y_3470_ = v___y_3501_;
v___y_3471_ = v___y_3496_;
v___y_3472_ = v___y_3497_;
v___y_3473_ = v___y_3498_;
v___y_3474_ = v___y_3500_;
v___y_3475_ = v_val_3503_;
goto v___jp_3467_;
}
}
v___jp_3504_:
{
lean_object* v_toCold_3507_; lean_object* v_ref_3508_; uint8_t v_suppressElabErrors_3509_; lean_object* v___x_3510_; lean_object* v___f_3511_; lean_object* v_ref_3512_; lean_object* v___x_3513_; 
v_toCold_3507_ = lean_ctor_get(v___y_3427_, 0);
v_ref_3508_ = lean_ctor_get(v___y_3427_, 2);
v_suppressElabErrors_3509_ = lean_ctor_get_uint8(v___y_3427_, sizeof(void*)*3 + 2);
v___x_3510_ = lean_box(v_suppressElabErrors_3509_);
v___f_3511_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3511_, 0, v___x_3510_);
v_ref_3512_ = l_Lean_replaceRef(v_ref_3421_, v_ref_3508_);
v___x_3513_ = l_Lean_Syntax_getPos_x3f(v_ref_3512_, v___y_3505_);
if (lean_obj_tag(v___x_3513_) == 0)
{
lean_object* v___x_3514_; 
v___x_3514_ = lean_unsigned_to_nat(0u);
v___y_3495_ = v___f_3511_;
v___y_3496_ = v_suppressElabErrors_3509_;
v___y_3497_ = v_toCold_3507_;
v___y_3498_ = v___y_3506_;
v___y_3499_ = v_ref_3512_;
v___y_3500_ = v___y_3505_;
v___y_3501_ = v___x_3514_;
goto v___jp_3494_;
}
else
{
lean_object* v_val_3515_; 
v_val_3515_ = lean_ctor_get(v___x_3513_, 0);
lean_inc(v_val_3515_);
lean_dec_ref_known(v___x_3513_, 1);
v___y_3495_ = v___f_3511_;
v___y_3496_ = v_suppressElabErrors_3509_;
v___y_3497_ = v_toCold_3507_;
v___y_3498_ = v___y_3506_;
v___y_3499_ = v_ref_3512_;
v___y_3500_ = v___y_3505_;
v___y_3501_ = v_val_3515_;
goto v___jp_3494_;
}
}
v___jp_3517_:
{
uint8_t v___x_3519_; uint8_t v___x_3520_; 
v___x_3519_ = 1;
v___x_3520_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3423_, v___x_3519_);
if (v___x_3520_ == 0)
{
v___y_3505_ = v___y_3518_;
v___y_3506_ = v_severity_3423_;
goto v___jp_3504_;
}
else
{
lean_object* v___x_3521_; lean_object* v___x_3522_; uint8_t v___x_3523_; 
v___x_3521_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3427_);
v___x_3522_ = l_Lean_warningAsError;
v___x_3523_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_3521_, v___x_3522_);
lean_dec_ref(v___x_3521_);
if (v___x_3523_ == 0)
{
v___y_3505_ = v___y_3518_;
v___y_3506_ = v_severity_3423_;
goto v___jp_3504_;
}
else
{
v___y_3505_ = v___y_3518_;
v___y_3506_ = v___x_3516_;
goto v___jp_3504_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___boxed(lean_object* v_ref_3528_, lean_object* v_msgData_3529_, lean_object* v_severity_3530_, lean_object* v_isSilent_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_, lean_object* v___y_3536_){
_start:
{
uint8_t v_severity_boxed_3537_; uint8_t v_isSilent_boxed_3538_; lean_object* v_res_3539_; 
v_severity_boxed_3537_ = lean_unbox(v_severity_3530_);
v_isSilent_boxed_3538_ = lean_unbox(v_isSilent_3531_);
v_res_3539_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3528_, v_msgData_3529_, v_severity_boxed_3537_, v_isSilent_boxed_3538_, v___y_3532_, v___y_3533_, v___y_3534_, v___y_3535_);
lean_dec(v___y_3535_);
lean_dec_ref(v___y_3534_);
lean_dec(v___y_3533_);
lean_dec_ref(v___y_3532_);
lean_dec(v_ref_3528_);
return v_res_3539_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(lean_object* v_msgData_3540_, uint8_t v_severity_3541_, uint8_t v_isSilent_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
lean_object* v_ref_3548_; lean_object* v___x_3549_; 
v_ref_3548_ = lean_ctor_get(v___y_3545_, 2);
v___x_3549_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3548_, v_msgData_3540_, v_severity_3541_, v_isSilent_3542_, v___y_3543_, v___y_3544_, v___y_3545_, v___y_3546_);
return v___x_3549_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3___boxed(lean_object* v_msgData_3550_, lean_object* v_severity_3551_, lean_object* v_isSilent_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_, lean_object* v___y_3557_){
_start:
{
uint8_t v_severity_boxed_3558_; uint8_t v_isSilent_boxed_3559_; lean_object* v_res_3560_; 
v_severity_boxed_3558_ = lean_unbox(v_severity_3551_);
v_isSilent_boxed_3559_ = lean_unbox(v_isSilent_3552_);
v_res_3560_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3550_, v_severity_boxed_3558_, v_isSilent_boxed_3559_, v___y_3553_, v___y_3554_, v___y_3555_, v___y_3556_);
lean_dec(v___y_3556_);
lean_dec_ref(v___y_3555_);
lean_dec(v___y_3554_);
lean_dec_ref(v___y_3553_);
return v_res_3560_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object* v_msgData_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_, lean_object* v___y_3565_){
_start:
{
uint8_t v___x_3567_; uint8_t v___x_3568_; lean_object* v___x_3569_; 
v___x_3567_ = 1;
v___x_3568_ = 0;
v___x_3569_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3561_, v___x_3567_, v___x_3568_, v___y_3562_, v___y_3563_, v___y_3564_, v___y_3565_);
return v___x_3569_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object* v_msgData_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_){
_start:
{
lean_object* v_res_3576_; 
v_res_3576_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v_msgData_3570_, v___y_3571_, v___y_3572_, v___y_3573_, v___y_3574_);
lean_dec(v___y_3574_);
lean_dec_ref(v___y_3573_);
lean_dec(v___y_3572_);
lean_dec_ref(v___y_3571_);
return v_res_3576_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object* v_k_3577_, lean_object* v_t_3578_){
_start:
{
if (lean_obj_tag(v_t_3578_) == 0)
{
lean_object* v_k_3579_; lean_object* v_l_3580_; lean_object* v_r_3581_; uint8_t v___x_3582_; 
v_k_3579_ = lean_ctor_get(v_t_3578_, 1);
v_l_3580_ = lean_ctor_get(v_t_3578_, 3);
v_r_3581_ = lean_ctor_get(v_t_3578_, 4);
v___x_3582_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3577_, v_k_3579_);
switch(v___x_3582_)
{
case 0:
{
v_t_3578_ = v_l_3580_;
goto _start;
}
case 1:
{
uint8_t v___x_3584_; 
v___x_3584_ = 1;
return v___x_3584_;
}
default: 
{
v_t_3578_ = v_r_3581_;
goto _start;
}
}
}
else
{
uint8_t v___x_3586_; 
v___x_3586_ = 0;
return v___x_3586_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object* v_k_3587_, lean_object* v_t_3588_){
_start:
{
uint8_t v_res_3589_; lean_object* v_r_3590_; 
v_res_3589_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3587_, v_t_3588_);
lean_dec(v_t_3588_);
lean_dec(v_k_3587_);
v_r_3590_ = lean_box(v_res_3589_);
return v_r_3590_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__0));
v___x_3593_ = l_Lean_stringToMessageData(v___x_3592_);
return v___x_3593_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3595_; lean_object* v___x_3596_; 
v___x_3595_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__2));
v___x_3596_ = l_Lean_stringToMessageData(v___x_3595_);
return v___x_3596_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(lean_object* v_a_3597_, lean_object* v_as_3598_, size_t v_sz_3599_, size_t v_i_3600_, lean_object* v_b_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_){
_start:
{
lean_object* v_a_3607_; uint8_t v___x_3611_; 
v___x_3611_ = lean_usize_dec_lt(v_i_3600_, v_sz_3599_);
if (v___x_3611_ == 0)
{
lean_object* v___x_3612_; 
v___x_3612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3612_, 0, v_b_3601_);
return v___x_3612_;
}
else
{
lean_object* v_snd_3613_; 
v_snd_3613_ = lean_ctor_get(v_b_3601_, 1);
lean_inc(v_snd_3613_);
if (lean_obj_tag(v_snd_3613_) == 0)
{
lean_object* v_fst_3614_; lean_object* v___x_3616_; uint8_t v_isShared_3617_; uint8_t v_isSharedCheck_3622_; 
v_fst_3614_ = lean_ctor_get(v_b_3601_, 0);
v_isSharedCheck_3622_ = !lean_is_exclusive(v_b_3601_);
if (v_isSharedCheck_3622_ == 0)
{
lean_object* v_unused_3623_; 
v_unused_3623_ = lean_ctor_get(v_b_3601_, 1);
lean_dec(v_unused_3623_);
v___x_3616_ = v_b_3601_;
v_isShared_3617_ = v_isSharedCheck_3622_;
goto v_resetjp_3615_;
}
else
{
lean_inc(v_fst_3614_);
lean_dec(v_b_3601_);
v___x_3616_ = lean_box(0);
v_isShared_3617_ = v_isSharedCheck_3622_;
goto v_resetjp_3615_;
}
v_resetjp_3615_:
{
lean_object* v___x_3619_; 
if (v_isShared_3617_ == 0)
{
v___x_3619_ = v___x_3616_;
goto v_reusejp_3618_;
}
else
{
lean_object* v_reuseFailAlloc_3621_; 
v_reuseFailAlloc_3621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3621_, 0, v_fst_3614_);
lean_ctor_set(v_reuseFailAlloc_3621_, 1, v_snd_3613_);
v___x_3619_ = v_reuseFailAlloc_3621_;
goto v_reusejp_3618_;
}
v_reusejp_3618_:
{
lean_object* v___x_3620_; 
v___x_3620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3620_, 0, v___x_3619_);
return v___x_3620_;
}
}
}
else
{
lean_object* v_fst_3624_; lean_object* v___x_3626_; uint8_t v_isShared_3627_; uint8_t v_isSharedCheck_3681_; 
v_fst_3624_ = lean_ctor_get(v_b_3601_, 0);
v_isSharedCheck_3681_ = !lean_is_exclusive(v_b_3601_);
if (v_isSharedCheck_3681_ == 0)
{
lean_object* v_unused_3682_; 
v_unused_3682_ = lean_ctor_get(v_b_3601_, 1);
lean_dec(v_unused_3682_);
v___x_3626_ = v_b_3601_;
v_isShared_3627_ = v_isSharedCheck_3681_;
goto v_resetjp_3625_;
}
else
{
lean_inc(v_fst_3624_);
lean_dec(v_b_3601_);
v___x_3626_ = lean_box(0);
v_isShared_3627_ = v_isSharedCheck_3681_;
goto v_resetjp_3625_;
}
v_resetjp_3625_:
{
lean_object* v_val_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3680_; 
v_val_3628_ = lean_ctor_get(v_snd_3613_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v_snd_3613_);
if (v_isSharedCheck_3680_ == 0)
{
v___x_3630_ = v_snd_3613_;
v_isShared_3631_ = v_isSharedCheck_3680_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_val_3628_);
lean_dec(v_snd_3613_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3680_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v_fvarSet_3632_; lean_object* v_a_3633_; lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3637_; 
v_fvarSet_3632_ = lean_ctor_get(v_a_3597_, 1);
v_a_3633_ = lean_array_uget_borrowed(v_as_3598_, v_i_3600_);
v___x_3634_ = lean_unsigned_to_nat(1u);
v___x_3635_ = lean_nat_add(v_val_3628_, v___x_3634_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 0, v___x_3635_);
v___x_3637_ = v___x_3630_;
goto v_reusejp_3636_;
}
else
{
lean_object* v_reuseFailAlloc_3679_; 
v_reuseFailAlloc_3679_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3679_, 0, v___x_3635_);
v___x_3637_ = v_reuseFailAlloc_3679_;
goto v_reusejp_3636_;
}
v_reusejp_3636_:
{
lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3638_ = l_Lean_Expr_fvarId_x21(v_a_3633_);
v___x_3639_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v___x_3638_, v_fvarSet_3632_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; 
v___x_3640_ = l_Lean_FVarId_getDecl___redArg(v___x_3638_, v___y_3602_, v___y_3603_, v___y_3604_);
if (lean_obj_tag(v___x_3640_) == 0)
{
lean_object* v_a_3641_; lean_object* v___x_3642_; 
v_a_3641_ = lean_ctor_get(v___x_3640_, 0);
lean_inc(v_a_3641_);
lean_dec_ref_known(v___x_3640_, 1);
v___x_3642_ = l_Lean_LocalDecl_ppAsBinder(v_a_3641_);
if (lean_obj_tag(v___x_3642_) == 1)
{
lean_object* v_val_3643_; lean_object* v___x_3645_; uint8_t v_isShared_3646_; uint8_t v_isSharedCheck_3664_; 
v_val_3643_ = lean_ctor_get(v___x_3642_, 0);
v_isSharedCheck_3664_ = !lean_is_exclusive(v___x_3642_);
if (v_isSharedCheck_3664_ == 0)
{
v___x_3645_ = v___x_3642_;
v_isShared_3646_ = v_isSharedCheck_3664_;
goto v_resetjp_3644_;
}
else
{
lean_inc(v_val_3643_);
lean_dec(v___x_3642_);
v___x_3645_ = lean_box(0);
v_isShared_3646_ = v_isSharedCheck_3664_;
goto v_resetjp_3644_;
}
v_resetjp_3644_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; lean_object* v___x_3650_; 
v___x_3647_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1);
v___x_3648_ = l_Nat_reprFast(v_val_3628_);
if (v_isShared_3646_ == 0)
{
lean_ctor_set_tag(v___x_3645_, 3);
lean_ctor_set(v___x_3645_, 0, v___x_3648_);
v___x_3650_ = v___x_3645_;
goto v_reusejp_3649_;
}
else
{
lean_object* v_reuseFailAlloc_3663_; 
v_reuseFailAlloc_3663_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3663_, 0, v___x_3648_);
v___x_3650_ = v_reuseFailAlloc_3663_;
goto v_reusejp_3649_;
}
v_reusejp_3649_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3661_; 
v___x_3651_ = l_Lean_MessageData_ofFormat(v___x_3650_);
v___x_3652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3647_);
lean_ctor_set(v___x_3652_, 1, v___x_3651_);
v___x_3653_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3652_);
lean_ctor_set(v___x_3654_, 1, v___x_3653_);
v___x_3655_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3655_, 0, v___x_3654_);
lean_ctor_set(v___x_3655_, 1, v_val_3643_);
v___x_3656_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3657_, 0, v___x_3655_);
lean_ctor_set(v___x_3657_, 1, v___x_3656_);
v___x_3658_ = l_Lean_indentD(v___x_3657_);
v___x_3659_ = lean_array_push(v_fst_3624_, v___x_3658_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 1, v___x_3637_);
lean_ctor_set(v___x_3626_, 0, v___x_3659_);
v___x_3661_ = v___x_3626_;
goto v_reusejp_3660_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3659_);
lean_ctor_set(v_reuseFailAlloc_3662_, 1, v___x_3637_);
v___x_3661_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3660_;
}
v_reusejp_3660_:
{
v_a_3607_ = v___x_3661_;
goto v___jp_3606_;
}
}
}
}
else
{
lean_object* v___x_3666_; 
lean_dec(v___x_3642_);
lean_dec(v_val_3628_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 1, v___x_3637_);
v___x_3666_ = v___x_3626_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_fst_3624_);
lean_ctor_set(v_reuseFailAlloc_3667_, 1, v___x_3637_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
v_a_3607_ = v___x_3666_;
goto v___jp_3606_;
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
lean_dec_ref(v___x_3637_);
lean_dec(v_val_3628_);
lean_del_object(v___x_3626_);
lean_dec(v_fst_3624_);
v_a_3668_ = lean_ctor_get(v___x_3640_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3640_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3640_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3640_);
v___x_3670_ = lean_box(0);
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
v_resetjp_3669_:
{
lean_object* v___x_3673_; 
if (v_isShared_3671_ == 0)
{
v___x_3673_ = v___x_3670_;
goto v_reusejp_3672_;
}
else
{
lean_object* v_reuseFailAlloc_3674_; 
v_reuseFailAlloc_3674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3674_, 0, v_a_3668_);
v___x_3673_ = v_reuseFailAlloc_3674_;
goto v_reusejp_3672_;
}
v_reusejp_3672_:
{
return v___x_3673_;
}
}
}
}
else
{
lean_object* v___x_3677_; 
lean_dec(v___x_3638_);
lean_dec(v_val_3628_);
if (v_isShared_3627_ == 0)
{
lean_ctor_set(v___x_3626_, 1, v___x_3637_);
v___x_3677_ = v___x_3626_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_fst_3624_);
lean_ctor_set(v_reuseFailAlloc_3678_, 1, v___x_3637_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
v_a_3607_ = v___x_3677_;
goto v___jp_3606_;
}
}
}
}
}
}
}
v___jp_3606_:
{
size_t v___x_3608_; size_t v___x_3609_; 
v___x_3608_ = ((size_t)1ULL);
v___x_3609_ = lean_usize_add(v_i_3600_, v___x_3608_);
v_i_3600_ = v___x_3609_;
v_b_3601_ = v_a_3607_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___boxed(lean_object* v_a_3683_, lean_object* v_as_3684_, lean_object* v_sz_3685_, lean_object* v_i_3686_, lean_object* v_b_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
size_t v_sz_boxed_3692_; size_t v_i_boxed_3693_; lean_object* v_res_3694_; 
v_sz_boxed_3692_ = lean_unbox_usize(v_sz_3685_);
lean_dec(v_sz_3685_);
v_i_boxed_3693_ = lean_unbox_usize(v_i_3686_);
lean_dec(v_i_3686_);
v_res_3694_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3683_, v_as_3684_, v_sz_boxed_3692_, v_i_boxed_3693_, v_b_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec_ref(v_as_3684_);
lean_dec_ref(v_a_3683_);
return v_res_3694_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3697_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0));
v___x_3698_ = lean_box(1);
v___x_3699_ = l_Lean_CollectFVars_State_ofFVarSet(v___x_3698_, v___x_3697_);
return v___x_3699_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3706_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4));
v___x_3707_ = l_Lean_stringToMessageData(v___x_3706_);
return v___x_3707_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3709_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6));
v___x_3710_ = l_Lean_stringToMessageData(v___x_3709_);
return v___x_3710_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3712_; lean_object* v___x_3713_; 
v___x_3712_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8));
v___x_3713_ = l_Lean_stringToMessageData(v___x_3712_);
return v___x_3713_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
v___x_3715_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10));
v___x_3716_ = l_Lean_stringToMessageData(v___x_3715_);
return v___x_3716_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v___x_3718_, lean_object* v_args_3719_, lean_object* v_ty_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_, lean_object* v___y_3724_){
_start:
{
lean_object* v___x_3726_; lean_object* v___x_3727_; lean_object* v___x_3728_; lean_object* v___x_3729_; 
v___x_3726_ = lean_unsigned_to_nat(0u);
v___x_3727_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1);
v___x_3728_ = lean_st_mk_ref(v___x_3727_);
v___x_3729_ = l_Lean_Expr_collectFVars(v_ty_3720_, v___x_3728_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3729_) == 0)
{
lean_object* v___x_3730_; size_t v_sz_3731_; size_t v___x_3732_; lean_object* v___x_3733_; 
lean_dec_ref_known(v___x_3729_, 1);
v___x_3730_ = lean_box(0);
v_sz_3731_ = lean_array_size(v_args_3719_);
v___x_3732_ = ((size_t)0ULL);
v___x_3733_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_args_3719_, v_sz_3731_, v___x_3732_, v___x_3730_, v___x_3728_, v___y_3721_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3733_) == 0)
{
lean_object* v___x_3735_; uint8_t v_isShared_3736_; uint8_t v_isSharedCheck_3804_; 
v_isSharedCheck_3804_ = !lean_is_exclusive(v___x_3733_);
if (v_isSharedCheck_3804_ == 0)
{
lean_object* v_unused_3805_; 
v_unused_3805_ = lean_ctor_get(v___x_3733_, 0);
lean_dec(v_unused_3805_);
v___x_3735_ = v___x_3733_;
v_isShared_3736_ = v_isSharedCheck_3804_;
goto v_resetjp_3734_;
}
else
{
lean_dec(v___x_3733_);
v___x_3735_ = lean_box(0);
v_isShared_3736_ = v_isSharedCheck_3804_;
goto v_resetjp_3734_;
}
v_resetjp_3734_:
{
lean_object* v___x_3737_; lean_object* v___x_3738_; 
v___x_3737_ = lean_st_ref_get(v___x_3728_);
lean_dec(v___x_3728_);
v___x_3738_ = l_Lean_CollectFVars_State_addDependencies(v___x_3737_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v_a_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; 
v_a_3739_ = lean_ctor_get(v___x_3738_, 0);
lean_inc(v_a_3739_);
lean_dec_ref_known(v___x_3738_, 1);
v___x_3740_ = lean_unsigned_to_nat(1u);
v___x_3741_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3));
v___x_3742_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3739_, v_args_3719_, v_sz_3731_, v___x_3732_, v___x_3741_, v___y_3721_, v___y_3723_, v___y_3724_);
lean_dec(v_a_3739_);
if (lean_obj_tag(v___x_3742_) == 0)
{
lean_object* v_a_3743_; lean_object* v___x_3745_; uint8_t v_isShared_3746_; uint8_t v_isSharedCheck_3787_; 
v_a_3743_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3787_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3787_ == 0)
{
v___x_3745_ = v___x_3742_;
v_isShared_3746_ = v_isSharedCheck_3787_;
goto v_resetjp_3744_;
}
else
{
lean_inc(v_a_3743_);
lean_dec(v___x_3742_);
v___x_3745_ = lean_box(0);
v_isShared_3746_ = v_isSharedCheck_3787_;
goto v_resetjp_3744_;
}
v_resetjp_3744_:
{
lean_object* v_fst_3747_; lean_object* v___x_3749_; uint8_t v_isShared_3750_; uint8_t v_isSharedCheck_3785_; 
v_fst_3747_ = lean_ctor_get(v_a_3743_, 0);
v_isSharedCheck_3785_ = !lean_is_exclusive(v_a_3743_);
if (v_isSharedCheck_3785_ == 0)
{
lean_object* v_unused_3786_; 
v_unused_3786_ = lean_ctor_get(v_a_3743_, 1);
lean_dec(v_unused_3786_);
v___x_3749_ = v_a_3743_;
v_isShared_3750_ = v_isSharedCheck_3785_;
goto v_resetjp_3748_;
}
else
{
lean_inc(v_fst_3747_);
lean_dec(v_a_3743_);
v___x_3749_ = lean_box(0);
v_isShared_3750_ = v_isSharedCheck_3785_;
goto v_resetjp_3748_;
}
v_resetjp_3748_:
{
lean_object* v___x_3751_; uint8_t v___x_3752_; 
v___x_3751_ = lean_array_get_size(v_fst_3747_);
v___x_3752_ = lean_nat_dec_eq(v___x_3751_, v___x_3726_);
if (v___x_3752_ == 0)
{
lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3756_; 
lean_del_object(v___x_3745_);
v___x_3753_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5);
v___x_3754_ = l_Nat_reprFast(v___x_3751_);
if (v_isShared_3736_ == 0)
{
lean_ctor_set_tag(v___x_3735_, 3);
lean_ctor_set(v___x_3735_, 0, v___x_3754_);
v___x_3756_ = v___x_3735_;
goto v_reusejp_3755_;
}
else
{
lean_object* v_reuseFailAlloc_3781_; 
v_reuseFailAlloc_3781_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3781_, 0, v___x_3754_);
v___x_3756_ = v_reuseFailAlloc_3781_;
goto v_reusejp_3755_;
}
v_reusejp_3755_:
{
lean_object* v___x_3757_; lean_object* v___x_3759_; 
v___x_3757_ = l_Lean_MessageData_ofFormat(v___x_3756_);
if (v_isShared_3750_ == 0)
{
lean_ctor_set_tag(v___x_3749_, 7);
lean_ctor_set(v___x_3749_, 1, v___x_3757_);
lean_ctor_set(v___x_3749_, 0, v___x_3753_);
v___x_3759_ = v___x_3749_;
goto v_reusejp_3758_;
}
else
{
lean_object* v_reuseFailAlloc_3780_; 
v_reuseFailAlloc_3780_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3780_, 0, v___x_3753_);
lean_ctor_set(v_reuseFailAlloc_3780_, 1, v___x_3757_);
v___x_3759_ = v_reuseFailAlloc_3780_;
goto v_reusejp_3758_;
}
v_reusejp_3758_:
{
lean_object* v___x_3760_; lean_object* v___x_3761_; lean_object* v___y_3763_; uint8_t v___x_3777_; 
v___x_3760_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7);
v___x_3761_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3761_, 0, v___x_3759_);
lean_ctor_set(v___x_3761_, 1, v___x_3760_);
v___x_3777_ = lean_nat_dec_eq(v___x_3751_, v___x_3740_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; 
v___x_3778_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12));
v___y_3763_ = v___x_3778_;
goto v___jp_3762_;
}
else
{
lean_object* v___x_3779_; 
v___x_3779_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___y_3763_ = v___x_3779_;
goto v___jp_3762_;
}
v___jp_3762_:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___x_3767_; lean_object* v___x_3768_; lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; uint8_t v___x_3774_; 
lean_inc_ref(v___y_3763_);
v___x_3764_ = l_Lean_stringToMessageData(v___y_3763_);
v___x_3765_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3765_, 0, v___x_3761_);
lean_ctor_set(v___x_3765_, 1, v___x_3764_);
v___x_3766_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9);
v___x_3767_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3767_, 0, v___x_3765_);
lean_ctor_set(v___x_3767_, 1, v___x_3766_);
v___x_3768_ = lean_array_to_list(v_fst_3747_);
v___x_3769_ = l_Lean_MessageData_nil;
v___x_3770_ = l_Lean_MessageData_joinSep(v___x_3768_, v___x_3769_);
v___x_3771_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3771_, 0, v___x_3767_);
lean_ctor_set(v___x_3771_, 1, v___x_3770_);
v___x_3772_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11);
v___x_3773_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3773_, 0, v___x_3771_);
lean_ctor_set(v___x_3773_, 1, v___x_3772_);
v___x_3774_ = l_Lean_Expr_hasSorry(v___x_3718_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3775_; 
v___x_3775_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3773_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
return v___x_3775_;
}
else
{
lean_object* v___x_3776_; 
v___x_3776_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_3773_, v___y_3721_, v___y_3722_, v___y_3723_, v___y_3724_);
return v___x_3776_;
}
}
}
}
}
else
{
lean_object* v___x_3783_; 
lean_del_object(v___x_3749_);
lean_dec(v_fst_3747_);
lean_del_object(v___x_3735_);
if (v_isShared_3746_ == 0)
{
lean_ctor_set(v___x_3745_, 0, v___x_3730_);
v___x_3783_ = v___x_3745_;
goto v_reusejp_3782_;
}
else
{
lean_object* v_reuseFailAlloc_3784_; 
v_reuseFailAlloc_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3784_, 0, v___x_3730_);
v___x_3783_ = v_reuseFailAlloc_3784_;
goto v_reusejp_3782_;
}
v_reusejp_3782_:
{
return v___x_3783_;
}
}
}
}
}
else
{
lean_object* v_a_3788_; lean_object* v___x_3790_; uint8_t v_isShared_3791_; uint8_t v_isSharedCheck_3795_; 
lean_del_object(v___x_3735_);
v_a_3788_ = lean_ctor_get(v___x_3742_, 0);
v_isSharedCheck_3795_ = !lean_is_exclusive(v___x_3742_);
if (v_isSharedCheck_3795_ == 0)
{
v___x_3790_ = v___x_3742_;
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
else
{
lean_inc(v_a_3788_);
lean_dec(v___x_3742_);
v___x_3790_ = lean_box(0);
v_isShared_3791_ = v_isSharedCheck_3795_;
goto v_resetjp_3789_;
}
v_resetjp_3789_:
{
lean_object* v___x_3793_; 
if (v_isShared_3791_ == 0)
{
v___x_3793_ = v___x_3790_;
goto v_reusejp_3792_;
}
else
{
lean_object* v_reuseFailAlloc_3794_; 
v_reuseFailAlloc_3794_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3794_, 0, v_a_3788_);
v___x_3793_ = v_reuseFailAlloc_3794_;
goto v_reusejp_3792_;
}
v_reusejp_3792_:
{
return v___x_3793_;
}
}
}
}
else
{
lean_object* v_a_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3803_; 
lean_del_object(v___x_3735_);
v_a_3796_ = lean_ctor_get(v___x_3738_, 0);
v_isSharedCheck_3803_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3803_ == 0)
{
v___x_3798_ = v___x_3738_;
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_a_3796_);
lean_dec(v___x_3738_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3803_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v___x_3801_; 
if (v_isShared_3799_ == 0)
{
v___x_3801_ = v___x_3798_;
goto v_reusejp_3800_;
}
else
{
lean_object* v_reuseFailAlloc_3802_; 
v_reuseFailAlloc_3802_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3802_, 0, v_a_3796_);
v___x_3801_ = v_reuseFailAlloc_3802_;
goto v_reusejp_3800_;
}
v_reusejp_3800_:
{
return v___x_3801_;
}
}
}
}
}
else
{
lean_dec(v___x_3728_);
return v___x_3733_;
}
}
else
{
lean_dec(v___x_3728_);
return v___x_3729_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v___x_3806_, lean_object* v_args_3807_, lean_object* v_ty_3808_, lean_object* v___y_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_){
_start:
{
lean_object* v_res_3814_; 
v_res_3814_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v___x_3806_, v_args_3807_, v_ty_3808_, v___y_3809_, v___y_3810_, v___y_3811_, v___y_3812_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v___y_3809_);
lean_dec_ref(v_args_3807_);
lean_dec_ref(v___x_3806_);
return v_res_3814_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object* v_e_3815_){
_start:
{
lean_object* v___x_3816_; 
v___x_3816_ = l_Lean_Expr_cleanupAnnotations(v_e_3815_);
lean_dec_ref(v_e_3815_);
switch(lean_obj_tag(v___x_3816_))
{
case 7:
{
lean_object* v_body_3817_; uint8_t v_binderInfo_3818_; uint8_t v___x_3819_; 
v_body_3817_ = lean_ctor_get(v___x_3816_, 2);
lean_inc_ref(v_body_3817_);
v_binderInfo_3818_ = lean_ctor_get_uint8(v___x_3816_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3816_, 3);
v___x_3819_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3818_);
if (v___x_3819_ == 0)
{
lean_object* v___x_3820_; uint8_t v___x_3821_; 
v___x_3820_ = lean_unsigned_to_nat(0u);
v___x_3821_ = lean_expr_has_loose_bvar(v_body_3817_, v___x_3820_);
if (v___x_3821_ == 0)
{
uint8_t v___x_3822_; 
lean_dec_ref(v_body_3817_);
v___x_3822_ = 1;
return v___x_3822_;
}
else
{
v_e_3815_ = v_body_3817_;
goto _start;
}
}
else
{
v_e_3815_ = v_body_3817_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3825_; 
v_body_3825_ = lean_ctor_get(v___x_3816_, 3);
lean_inc_ref(v_body_3825_);
lean_dec_ref_known(v___x_3816_, 4);
v_e_3815_ = v_body_3825_;
goto _start;
}
default: 
{
uint8_t v___x_3827_; 
lean_dec_ref(v___x_3816_);
v___x_3827_ = 0;
return v___x_3827_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object* v_e_3828_){
_start:
{
uint8_t v_res_3829_; lean_object* v_r_3830_; 
v_res_3829_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(v_e_3828_);
v_r_3830_ = lean_box(v_res_3829_);
return v_r_3830_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_cinfo_3831_, lean_object* v_a_3832_, lean_object* v_a_3833_, lean_object* v_a_3834_, lean_object* v_a_3835_){
_start:
{
lean_object* v___x_3837_; uint8_t v___x_3838_; 
v___x_3837_ = l_Lean_ConstantInfo_type(v_cinfo_3831_);
lean_inc_ref(v___x_3837_);
v___x_3838_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(v___x_3837_);
if (v___x_3838_ == 0)
{
lean_object* v___x_3839_; lean_object* v___x_3840_; 
lean_dec_ref(v___x_3837_);
v___x_3839_ = lean_box(0);
v___x_3840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3840_, 0, v___x_3839_);
return v___x_3840_;
}
else
{
lean_object* v___f_3841_; uint8_t v___x_3842_; lean_object* v___x_3843_; 
lean_inc_ref(v___x_3837_);
v___f_3841_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3841_, 0, v___x_3837_);
v___x_3842_ = 0;
v___x_3843_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v___x_3837_, v___f_3841_, v___x_3842_, v_a_3832_, v_a_3833_, v_a_3834_, v_a_3835_);
return v___x_3843_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_cinfo_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_, lean_object* v_a_3848_, lean_object* v_a_3849_){
_start:
{
lean_object* v_res_3850_; 
v_res_3850_ = l_Lean_Meta_checkImpossibleInstance(v_cinfo_3844_, v_a_3845_, v_a_3846_, v_a_3847_, v_a_3848_);
lean_dec(v_a_3848_);
lean_dec_ref(v_a_3847_);
lean_dec(v_a_3846_);
lean_dec_ref(v_a_3845_);
lean_dec_ref(v_cinfo_3844_);
return v_res_3850_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object* v_as_3851_, size_t v_sz_3852_, size_t v_i_3853_, lean_object* v_b_3854_, lean_object* v___y_3855_, lean_object* v___y_3856_, lean_object* v___y_3857_, lean_object* v___y_3858_, lean_object* v___y_3859_){
_start:
{
lean_object* v___x_3861_; 
v___x_3861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_as_3851_, v_sz_3852_, v_i_3853_, v_b_3854_, v___y_3855_, v___y_3856_, v___y_3858_, v___y_3859_);
return v___x_3861_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_as_3862_, lean_object* v_sz_3863_, lean_object* v_i_3864_, lean_object* v_b_3865_, lean_object* v___y_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
size_t v_sz_boxed_3872_; size_t v_i_boxed_3873_; lean_object* v_res_3874_; 
v_sz_boxed_3872_ = lean_unbox_usize(v_sz_3863_);
lean_dec(v_sz_3863_);
v_i_boxed_3873_ = lean_unbox_usize(v_i_3864_);
lean_dec(v_i_3864_);
v_res_3874_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_as_3862_, v_sz_boxed_3872_, v_i_boxed_3873_, v_b_3865_, v___y_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec(v___y_3866_);
lean_dec_ref(v_as_3862_);
return v_res_3874_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v_00_u03b2_3875_, lean_object* v_k_3876_, lean_object* v_t_3877_){
_start:
{
uint8_t v___x_3878_; 
v___x_3878_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3876_, v_t_3877_);
return v___x_3878_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v_00_u03b2_3879_, lean_object* v_k_3880_, lean_object* v_t_3881_){
_start:
{
uint8_t v_res_3882_; lean_object* v_r_3883_; 
v_res_3882_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(v_00_u03b2_3879_, v_k_3880_, v_t_3881_);
lean_dec(v_t_3881_);
lean_dec(v_k_3880_);
v_r_3883_ = lean_box(v_res_3882_);
return v_r_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_a_3884_, lean_object* v_as_3885_, size_t v_sz_3886_, size_t v_i_3887_, lean_object* v_b_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3884_, v_as_3885_, v_sz_3886_, v_i_3887_, v_b_3888_, v___y_3889_, v___y_3891_, v___y_3892_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_a_3895_, lean_object* v_as_3896_, lean_object* v_sz_3897_, lean_object* v_i_3898_, lean_object* v_b_3899_, lean_object* v___y_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_){
_start:
{
size_t v_sz_boxed_3905_; size_t v_i_boxed_3906_; lean_object* v_res_3907_; 
v_sz_boxed_3905_ = lean_unbox_usize(v_sz_3897_);
lean_dec(v_sz_3897_);
v_i_boxed_3906_ = lean_unbox_usize(v_i_3898_);
lean_dec(v_i_3898_);
v_res_3907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_a_3895_, v_as_3896_, v_sz_boxed_3905_, v_i_boxed_3906_, v_b_3899_, v___y_3900_, v___y_3901_, v___y_3902_, v___y_3903_);
lean_dec(v___y_3903_);
lean_dec_ref(v___y_3902_);
lean_dec(v___y_3901_);
lean_dec_ref(v___y_3900_);
lean_dec_ref(v_as_3896_);
lean_dec_ref(v_a_3895_);
return v_res_3907_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3910_ = l_Lean_stringToMessageData(v___x_3909_);
return v___x_3910_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3912_; lean_object* v___x_3913_; 
v___x_3912_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3913_ = l_Lean_stringToMessageData(v___x_3912_);
return v___x_3913_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3915_; lean_object* v___x_3916_; 
v___x_3915_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3916_ = l_Lean_stringToMessageData(v___x_3915_);
return v___x_3916_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_c_3917_, lean_object* v_x_3918_, lean_object* v_target_3919_, lean_object* v___y_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_){
_start:
{
lean_object* v___x_3925_; 
lean_inc_ref(v_target_3919_);
v___x_3925_ = l_Lean_Meta_isClass_x3f(v_target_3919_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
if (lean_obj_tag(v___x_3925_) == 0)
{
lean_object* v_a_3926_; lean_object* v___x_3928_; uint8_t v_isShared_3929_; uint8_t v_isSharedCheck_3944_; 
v_a_3926_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3944_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3944_ == 0)
{
v___x_3928_ = v___x_3925_;
v_isShared_3929_ = v_isSharedCheck_3944_;
goto v_resetjp_3927_;
}
else
{
lean_inc(v_a_3926_);
lean_dec(v___x_3925_);
v___x_3928_ = lean_box(0);
v_isShared_3929_ = v_isSharedCheck_3944_;
goto v_resetjp_3927_;
}
v_resetjp_3927_:
{
if (lean_obj_tag(v_a_3926_) == 0)
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v___x_3935_; lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; 
lean_del_object(v___x_3928_);
v___x_3930_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3931_ = l_Lean_MessageData_ofExpr(v_c_3917_);
v___x_3932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3932_, 0, v___x_3930_);
lean_ctor_set(v___x_3932_, 1, v___x_3931_);
v___x_3933_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3934_, 0, v___x_3932_);
lean_ctor_set(v___x_3934_, 1, v___x_3933_);
v___x_3935_ = l_Lean_MessageData_ofExpr(v_target_3919_);
v___x_3936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3934_);
lean_ctor_set(v___x_3936_, 1, v___x_3935_);
v___x_3937_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3936_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
v___x_3939_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3938_, v___y_3920_, v___y_3921_, v___y_3922_, v___y_3923_);
return v___x_3939_;
}
else
{
lean_object* v___x_3940_; lean_object* v___x_3942_; 
lean_dec_ref_known(v_a_3926_, 1);
lean_dec_ref(v_target_3919_);
lean_dec_ref(v_c_3917_);
v___x_3940_ = lean_box(0);
if (v_isShared_3929_ == 0)
{
lean_ctor_set(v___x_3928_, 0, v___x_3940_);
v___x_3942_ = v___x_3928_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3943_; 
v_reuseFailAlloc_3943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3943_, 0, v___x_3940_);
v___x_3942_ = v_reuseFailAlloc_3943_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
return v___x_3942_;
}
}
}
}
else
{
lean_object* v_a_3945_; lean_object* v___x_3947_; uint8_t v_isShared_3948_; uint8_t v_isSharedCheck_3952_; 
lean_dec_ref(v_target_3919_);
lean_dec_ref(v_c_3917_);
v_a_3945_ = lean_ctor_get(v___x_3925_, 0);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3925_);
if (v_isSharedCheck_3952_ == 0)
{
v___x_3947_ = v___x_3925_;
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
else
{
lean_inc(v_a_3945_);
lean_dec(v___x_3925_);
v___x_3947_ = lean_box(0);
v_isShared_3948_ = v_isSharedCheck_3952_;
goto v_resetjp_3946_;
}
v_resetjp_3946_:
{
lean_object* v___x_3950_; 
if (v_isShared_3948_ == 0)
{
v___x_3950_ = v___x_3947_;
goto v_reusejp_3949_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v_a_3945_);
v___x_3950_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3949_;
}
v_reusejp_3949_:
{
return v___x_3950_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_c_3953_, lean_object* v_x_3954_, lean_object* v_target_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
lean_object* v_res_3961_; 
v_res_3961_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_c_3953_, v_x_3954_, v_target_3955_, v___y_3956_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec_ref(v_x_3954_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_c_3962_, lean_object* v_a_3963_, lean_object* v_a_3964_, lean_object* v_a_3965_, lean_object* v_a_3966_){
_start:
{
lean_object* v___f_3968_; lean_object* v___x_3969_; 
lean_inc_ref(v_c_3962_);
v___f_3968_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3968_, 0, v_c_3962_);
lean_inc(v_a_3966_);
lean_inc_ref(v_a_3965_);
lean_inc(v_a_3964_);
lean_inc_ref(v_a_3963_);
v___x_3969_ = lean_infer_type(v_c_3962_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
if (lean_obj_tag(v___x_3969_) == 0)
{
lean_object* v_a_3970_; uint8_t v___x_3971_; lean_object* v___x_3972_; 
v_a_3970_ = lean_ctor_get(v___x_3969_, 0);
lean_inc(v_a_3970_);
lean_dec_ref_known(v___x_3969_, 1);
v___x_3971_ = 0;
v___x_3972_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3970_, v___f_3968_, v___x_3971_, v___x_3971_, v_a_3963_, v_a_3964_, v_a_3965_, v_a_3966_);
return v___x_3972_;
}
else
{
lean_object* v_a_3973_; lean_object* v___x_3975_; uint8_t v_isShared_3976_; uint8_t v_isSharedCheck_3980_; 
lean_dec_ref(v___f_3968_);
v_a_3973_ = lean_ctor_get(v___x_3969_, 0);
v_isSharedCheck_3980_ = !lean_is_exclusive(v___x_3969_);
if (v_isSharedCheck_3980_ == 0)
{
v___x_3975_ = v___x_3969_;
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
else
{
lean_inc(v_a_3973_);
lean_dec(v___x_3969_);
v___x_3975_ = lean_box(0);
v_isShared_3976_ = v_isSharedCheck_3980_;
goto v_resetjp_3974_;
}
v_resetjp_3974_:
{
lean_object* v___x_3978_; 
if (v_isShared_3976_ == 0)
{
v___x_3978_ = v___x_3975_;
goto v_reusejp_3977_;
}
else
{
lean_object* v_reuseFailAlloc_3979_; 
v_reuseFailAlloc_3979_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3979_, 0, v_a_3973_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_c_3981_, lean_object* v_a_3982_, lean_object* v_a_3983_, lean_object* v_a_3984_, lean_object* v_a_3985_, lean_object* v_a_3986_){
_start:
{
lean_object* v_res_3987_; 
v_res_3987_ = l_Lean_Meta_checkNonClassInstance(v_c_3981_, v_a_3982_, v_a_3983_, v_a_3984_, v_a_3985_);
lean_dec(v_a_3985_);
lean_dec_ref(v_a_3984_);
lean_dec(v_a_3983_);
lean_dec_ref(v_a_3982_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3998_, lean_object* v___y_3999_){
_start:
{
lean_object* v___x_4001_; lean_object* v_env_4002_; lean_object* v___x_4003_; lean_object* v___x_4004_; 
v___x_4001_ = lean_st_ref_get(v___y_3999_);
v_env_4002_ = lean_ctor_get(v___x_4001_, 0);
lean_inc_ref(v_env_4002_);
lean_dec(v___x_4001_);
v___x_4003_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_4002_, v_declName_3998_);
v___x_4004_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4004_, 0, v___x_4003_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_){
_start:
{
lean_object* v_res_4008_; 
v_res_4008_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4005_, v___y_4006_);
lean_dec(v___y_4006_);
return v_res_4008_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_, lean_object* v___y_4013_){
_start:
{
lean_object* v___x_4015_; 
v___x_4015_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4009_, v___y_4013_);
return v___x_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_4016_, v___y_4017_, v___y_4018_, v___y_4019_, v___y_4020_);
lean_dec(v___y_4020_);
lean_dec_ref(v___y_4019_);
lean_dec(v___y_4018_);
lean_dec_ref(v___y_4017_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_4023_, lean_object* v___y_4024_){
_start:
{
lean_object* v___x_4026_; lean_object* v_env_4027_; uint8_t v___x_4028_; lean_object* v___x_4029_; lean_object* v___x_4030_; 
v___x_4026_ = lean_st_ref_get(v___y_4024_);
v_env_4027_ = lean_ctor_get(v___x_4026_, 0);
lean_inc_ref(v_env_4027_);
lean_dec(v___x_4026_);
v___x_4028_ = l_Lean_getReducibilityStatusCore(v_env_4027_, v_declName_4023_);
v___x_4029_ = lean_box(v___x_4028_);
v___x_4030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4030_, 0, v___x_4029_);
return v___x_4030_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_){
_start:
{
lean_object* v_res_4034_; 
v_res_4034_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4031_, v___y_4032_);
lean_dec(v___y_4032_);
return v_res_4034_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_4035_, lean_object* v___y_4036_, lean_object* v___y_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v___x_4041_; 
v___x_4041_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4035_, v___y_4039_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v_res_4048_; 
v_res_4048_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_4042_, v___y_4043_, v___y_4044_, v___y_4045_, v___y_4046_);
lean_dec(v___y_4046_);
lean_dec_ref(v___y_4045_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
return v_res_4048_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
return v___x_4050_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4051_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4052_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_4053_ = lean_unsigned_to_nat(0u);
v___x_4054_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
lean_ctor_set(v___x_4054_, 1, v___x_4053_);
lean_ctor_set(v___x_4054_, 2, v___x_4053_);
lean_ctor_set(v___x_4054_, 3, v___x_4053_);
lean_ctor_set(v___x_4054_, 4, v___x_4052_);
lean_ctor_set(v___x_4054_, 5, v___x_4052_);
lean_ctor_set(v___x_4054_, 6, v___x_4052_);
lean_ctor_set(v___x_4054_, 7, v___x_4052_);
lean_ctor_set(v___x_4054_, 8, v___x_4052_);
lean_ctor_set(v___x_4054_, 9, v___x_4052_);
lean_ctor_set(v___x_4054_, 10, v___x_4052_);
lean_ctor_set(v___x_4054_, 11, v___x_4051_);
return v___x_4054_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; 
v___x_4055_ = lean_unsigned_to_nat(32u);
v___x_4056_ = lean_mk_empty_array_with_capacity(v___x_4055_);
v___x_4057_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4057_, 0, v___x_4056_);
return v___x_4057_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__3(void){
_start:
{
size_t v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4058_ = ((size_t)5ULL);
v___x_4059_ = lean_unsigned_to_nat(0u);
v___x_4060_ = lean_unsigned_to_nat(32u);
v___x_4061_ = lean_mk_empty_array_with_capacity(v___x_4060_);
v___x_4062_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_4063_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
lean_ctor_set(v___x_4063_, 1, v___x_4061_);
lean_ctor_set(v___x_4063_, 2, v___x_4059_);
lean_ctor_set(v___x_4063_, 3, v___x_4059_);
lean_ctor_set_usize(v___x_4063_, 4, v___x_4058_);
return v___x_4063_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4064_ = lean_box(1);
v___x_4065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__3);
v___x_4066_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__0);
v___x_4067_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4067_, 0, v___x_4066_);
lean_ctor_set(v___x_4067_, 1, v___x_4065_);
lean_ctor_set(v___x_4067_, 2, v___x_4064_);
return v___x_4067_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__6(void){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4069_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__5));
v___x_4070_ = l_Lean_stringToMessageData(v___x_4069_);
return v___x_4070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__8(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__7));
v___x_4073_ = l_Lean_stringToMessageData(v___x_4072_);
return v___x_4073_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__10(void){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__9));
v___x_4076_ = l_Lean_stringToMessageData(v___x_4075_);
return v___x_4076_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__12(void){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__11));
v___x_4079_ = l_Lean_stringToMessageData(v___x_4078_);
return v___x_4079_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__14(void){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__13));
v___x_4082_ = l_Lean_stringToMessageData(v___x_4081_);
return v___x_4082_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__16(void){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__15));
v___x_4085_ = l_Lean_stringToMessageData(v___x_4084_);
return v___x_4085_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__18(void){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__17));
v___x_4088_ = l_Lean_stringToMessageData(v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg(lean_object* v_msg_4089_, lean_object* v_declHint_4090_, lean_object* v___y_4091_){
_start:
{
lean_object* v___x_4093_; lean_object* v___x_4094_; lean_object* v_env_4095_; uint8_t v___x_4096_; 
v___x_4093_ = lean_box(0);
v___x_4094_ = lean_st_ref_get(v___y_4091_);
v_env_4095_ = lean_ctor_get(v___x_4094_, 0);
lean_inc_ref(v_env_4095_);
lean_dec(v___x_4094_);
v___x_4096_ = l_Lean_Name_isAnonymous(v_declHint_4090_);
if (v___x_4096_ == 0)
{
uint8_t v_isExporting_4097_; 
v_isExporting_4097_ = lean_ctor_get_uint8(v_env_4095_, sizeof(void*)*13);
if (v_isExporting_4097_ == 0)
{
lean_object* v___x_4098_; 
lean_dec_ref(v_env_4095_);
lean_dec(v_declHint_4090_);
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v_msg_4089_);
return v___x_4098_;
}
else
{
lean_object* v___x_4099_; uint8_t v___x_4100_; 
lean_inc_ref(v_env_4095_);
v___x_4099_ = l_Lean_Environment_setExporting(v_env_4095_, v___x_4096_);
lean_inc(v_declHint_4090_);
lean_inc_ref(v___x_4099_);
v___x_4100_ = l_Lean_Environment_contains(v___x_4099_, v_declHint_4090_, v_isExporting_4097_);
if (v___x_4100_ == 0)
{
lean_object* v___x_4101_; 
lean_dec_ref(v___x_4099_);
lean_dec_ref(v_env_4095_);
lean_dec(v_declHint_4090_);
v___x_4101_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4101_, 0, v_msg_4089_);
return v___x_4101_;
}
else
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v_c_4107_; lean_object* v___x_4108_; 
v___x_4102_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_4103_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__4);
v___x_4104_ = l_Lean_Options_empty;
lean_inc_ref(v___x_4099_);
v___x_4105_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4099_);
lean_ctor_set(v___x_4105_, 1, v___x_4102_);
lean_ctor_set(v___x_4105_, 2, v___x_4103_);
lean_ctor_set(v___x_4105_, 3, v___x_4104_);
lean_inc(v_declHint_4090_);
v___x_4106_ = l_Lean_MessageData_ofConstName(v_declHint_4090_, v___x_4096_);
v_c_4107_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4107_, 0, v___x_4105_);
lean_ctor_set(v_c_4107_, 1, v___x_4106_);
v___x_4108_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_4099_, v_declHint_4090_);
lean_dec_ref(v___x_4099_);
if (lean_obj_tag(v___x_4108_) == 0)
{
lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; 
lean_dec_ref(v_env_4095_);
lean_dec(v_declHint_4090_);
v___x_4109_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__6);
v___x_4110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
lean_ctor_set(v___x_4110_, 1, v_c_4107_);
v___x_4111_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__8);
v___x_4112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4110_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
v___x_4113_ = l_Lean_MessageData_note(v___x_4112_);
v___x_4114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4114_, 0, v_msg_4089_);
lean_ctor_set(v___x_4114_, 1, v___x_4113_);
v___x_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4114_);
return v___x_4115_;
}
else
{
lean_object* v_val_4116_; lean_object* v___x_4118_; uint8_t v_isShared_4119_; uint8_t v_isSharedCheck_4150_; 
v_val_4116_ = lean_ctor_get(v___x_4108_, 0);
v_isSharedCheck_4150_ = !lean_is_exclusive(v___x_4108_);
if (v_isSharedCheck_4150_ == 0)
{
v___x_4118_ = v___x_4108_;
v_isShared_4119_ = v_isSharedCheck_4150_;
goto v_resetjp_4117_;
}
else
{
lean_inc(v_val_4116_);
lean_dec(v___x_4108_);
v___x_4118_ = lean_box(0);
v_isShared_4119_ = v_isSharedCheck_4150_;
goto v_resetjp_4117_;
}
v_resetjp_4117_:
{
lean_object* v___x_4120_; lean_object* v_moduleNames_4121_; lean_object* v_mod_4122_; uint8_t v___x_4123_; 
v___x_4120_ = l_Lean_Environment_header(v_env_4095_);
lean_dec_ref(v_env_4095_);
v_moduleNames_4121_ = lean_ctor_get(v___x_4120_, 4);
lean_inc_ref(v_moduleNames_4121_);
lean_dec_ref(v___x_4120_);
v_mod_4122_ = lean_array_get(v___x_4093_, v_moduleNames_4121_, v_val_4116_);
lean_dec(v_val_4116_);
lean_dec_ref(v_moduleNames_4121_);
v___x_4123_ = l_Lean_isPrivateName(v_declHint_4090_);
lean_dec(v_declHint_4090_);
if (v___x_4123_ == 0)
{
lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4133_; lean_object* v___x_4135_; 
v___x_4124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__10);
v___x_4125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4124_);
lean_ctor_set(v___x_4125_, 1, v_c_4107_);
v___x_4126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__12);
v___x_4127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4125_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = l_Lean_MessageData_ofName(v_mod_4122_);
v___x_4129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4127_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
v___x_4130_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__14);
v___x_4131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4129_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
v___x_4132_ = l_Lean_MessageData_note(v___x_4131_);
v___x_4133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4133_, 0, v_msg_4089_);
lean_ctor_set(v___x_4133_, 1, v___x_4132_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set_tag(v___x_4118_, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4133_);
v___x_4135_ = v___x_4118_;
goto v_reusejp_4134_;
}
else
{
lean_object* v_reuseFailAlloc_4136_; 
v_reuseFailAlloc_4136_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4136_, 0, v___x_4133_);
v___x_4135_ = v_reuseFailAlloc_4136_;
goto v_reusejp_4134_;
}
v_reusejp_4134_:
{
return v___x_4135_;
}
}
else
{
lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4146_; lean_object* v___x_4148_; 
v___x_4137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__6);
v___x_4138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4137_);
lean_ctor_set(v___x_4138_, 1, v_c_4107_);
v___x_4139_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__16);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4138_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = l_Lean_MessageData_ofName(v_mod_4122_);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4140_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__18);
v___x_4144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4142_);
lean_ctor_set(v___x_4144_, 1, v___x_4143_);
v___x_4145_ = l_Lean_MessageData_note(v___x_4144_);
v___x_4146_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4146_, 0, v_msg_4089_);
lean_ctor_set(v___x_4146_, 1, v___x_4145_);
if (v_isShared_4119_ == 0)
{
lean_ctor_set_tag(v___x_4118_, 0);
lean_ctor_set(v___x_4118_, 0, v___x_4146_);
v___x_4148_ = v___x_4118_;
goto v_reusejp_4147_;
}
else
{
lean_object* v_reuseFailAlloc_4149_; 
v_reuseFailAlloc_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4149_, 0, v___x_4146_);
v___x_4148_ = v_reuseFailAlloc_4149_;
goto v_reusejp_4147_;
}
v_reusejp_4147_:
{
return v___x_4148_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4151_; 
lean_dec_ref(v_env_4095_);
lean_dec(v_declHint_4090_);
v___x_4151_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4151_, 0, v_msg_4089_);
return v___x_4151_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___boxed(lean_object* v_msg_4152_, lean_object* v_declHint_4153_, lean_object* v___y_4154_, lean_object* v___y_4155_){
_start:
{
lean_object* v_res_4156_; 
v_res_4156_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg(v_msg_4152_, v_declHint_4153_, v___y_4154_);
lean_dec(v___y_4154_);
return v_res_4156_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11(lean_object* v_msg_4157_, lean_object* v_declHint_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_){
_start:
{
lean_object* v___x_4164_; lean_object* v_a_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4174_; 
v___x_4164_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg(v_msg_4157_, v_declHint_4158_, v___y_4162_);
v_a_4165_ = lean_ctor_get(v___x_4164_, 0);
v_isSharedCheck_4174_ = !lean_is_exclusive(v___x_4164_);
if (v_isSharedCheck_4174_ == 0)
{
v___x_4167_ = v___x_4164_;
v_isShared_4168_ = v_isSharedCheck_4174_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_a_4165_);
lean_dec(v___x_4164_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4174_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4172_; 
v___x_4169_ = l_Lean_unknownIdentifierMessageTag;
v___x_4170_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4170_, 0, v___x_4169_);
lean_ctor_set(v___x_4170_, 1, v_a_4165_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set(v___x_4167_, 0, v___x_4170_);
v___x_4172_ = v___x_4167_;
goto v_reusejp_4171_;
}
else
{
lean_object* v_reuseFailAlloc_4173_; 
v_reuseFailAlloc_4173_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4173_, 0, v___x_4170_);
v___x_4172_ = v_reuseFailAlloc_4173_;
goto v_reusejp_4171_;
}
v_reusejp_4171_:
{
return v___x_4172_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11___boxed(lean_object* v_msg_4175_, lean_object* v_declHint_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_, lean_object* v___y_4181_){
_start:
{
lean_object* v_res_4182_; 
v_res_4182_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11(v_msg_4175_, v_declHint_4176_, v___y_4177_, v___y_4178_, v___y_4179_, v___y_4180_);
lean_dec(v___y_4180_);
lean_dec_ref(v___y_4179_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
return v_res_4182_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__12___redArg(lean_object* v_ref_4183_, lean_object* v_msg_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v_toCold_4190_; lean_object* v_currRecDepth_4191_; lean_object* v_ref_4192_; uint16_t v_optionFlags_4193_; uint8_t v_suppressElabErrors_4194_; uint8_t v_checkDeprecated_4195_; uint8_t v_isRecordingDeps_4196_; lean_object* v_ref_4197_; lean_object* v___x_4198_; lean_object* v___x_4199_; 
v_toCold_4190_ = lean_ctor_get(v___y_4187_, 0);
v_currRecDepth_4191_ = lean_ctor_get(v___y_4187_, 1);
v_ref_4192_ = lean_ctor_get(v___y_4187_, 2);
v_optionFlags_4193_ = lean_ctor_get_uint16(v___y_4187_, sizeof(void*)*3);
v_suppressElabErrors_4194_ = lean_ctor_get_uint8(v___y_4187_, sizeof(void*)*3 + 2);
v_checkDeprecated_4195_ = lean_ctor_get_uint8(v___y_4187_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4196_ = lean_ctor_get_uint8(v___y_4187_, sizeof(void*)*3 + 4);
v_ref_4197_ = l_Lean_replaceRef(v_ref_4183_, v_ref_4192_);
lean_inc(v_currRecDepth_4191_);
lean_inc_ref(v_toCold_4190_);
v___x_4198_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4198_, 0, v_toCold_4190_);
lean_ctor_set(v___x_4198_, 1, v_currRecDepth_4191_);
lean_ctor_set(v___x_4198_, 2, v_ref_4197_);
lean_ctor_set_uint16(v___x_4198_, sizeof(void*)*3, v_optionFlags_4193_);
lean_ctor_set_uint8(v___x_4198_, sizeof(void*)*3 + 2, v_suppressElabErrors_4194_);
lean_ctor_set_uint8(v___x_4198_, sizeof(void*)*3 + 3, v_checkDeprecated_4195_);
lean_ctor_set_uint8(v___x_4198_, sizeof(void*)*3 + 4, v_isRecordingDeps_4196_);
v___x_4199_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_4184_, v___y_4185_, v___y_4186_, v___x_4198_, v___y_4188_);
lean_dec_ref_known(v___x_4198_, 3);
return v___x_4199_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__12___redArg___boxed(lean_object* v_ref_4200_, lean_object* v_msg_4201_, lean_object* v___y_4202_, lean_object* v___y_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_){
_start:
{
lean_object* v_res_4207_; 
v_res_4207_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__12___redArg(v_ref_4200_, v_msg_4201_, v___y_4202_, v___y_4203_, v___y_4204_, v___y_4205_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
lean_dec(v___y_4203_);
lean_dec_ref(v___y_4202_);
lean_dec(v_ref_4200_);
return v_res_4207_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10___redArg(lean_object* v_ref_4208_, lean_object* v_msg_4209_, lean_object* v_declHint_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v___x_4216_; lean_object* v_a_4217_; lean_object* v___x_4218_; 
v___x_4216_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11(v_msg_4209_, v_declHint_4210_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
lean_inc(v_a_4217_);
lean_dec_ref(v___x_4216_);
v___x_4218_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__12___redArg(v_ref_4208_, v_a_4217_, v___y_4211_, v___y_4212_, v___y_4213_, v___y_4214_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10___redArg___boxed(lean_object* v_ref_4219_, lean_object* v_msg_4220_, lean_object* v_declHint_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_){
_start:
{
lean_object* v_res_4227_; 
v_res_4227_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10___redArg(v_ref_4219_, v_msg_4220_, v_declHint_4221_, v___y_4222_, v___y_4223_, v___y_4224_, v___y_4225_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v_ref_4219_);
return v_res_4227_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__1(void){
_start:
{
lean_object* v___x_4229_; lean_object* v___x_4230_; 
v___x_4229_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__0));
v___x_4230_ = l_Lean_stringToMessageData(v___x_4229_);
return v___x_4230_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg(lean_object* v_ref_4231_, lean_object* v_constName_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_){
_start:
{
lean_object* v___x_4238_; uint8_t v___x_4239_; lean_object* v___x_4240_; lean_object* v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4238_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__1);
v___x_4239_ = 0;
lean_inc(v_constName_4232_);
v___x_4240_ = l_Lean_MessageData_ofConstName(v_constName_4232_, v___x_4239_);
v___x_4241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4238_);
lean_ctor_set(v___x_4241_, 1, v___x_4240_);
v___x_4242_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4241_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
v___x_4244_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10___redArg(v_ref_4231_, v___x_4243_, v_constName_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
return v___x_4244_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___boxed(lean_object* v_ref_4245_, lean_object* v_constName_4246_, lean_object* v___y_4247_, lean_object* v___y_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_){
_start:
{
lean_object* v_res_4252_; 
v_res_4252_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg(v_ref_4245_, v_constName_4246_, v___y_4247_, v___y_4248_, v___y_4249_, v___y_4250_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v___y_4248_);
lean_dec_ref(v___y_4247_);
lean_dec(v_ref_4245_);
return v_res_4252_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7___redArg(lean_object* v_constName_4253_, lean_object* v___y_4254_, lean_object* v___y_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_){
_start:
{
lean_object* v_ref_4259_; lean_object* v___x_4260_; 
v_ref_4259_ = lean_ctor_get(v___y_4256_, 2);
v___x_4260_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg(v_ref_4259_, v_constName_4253_, v___y_4254_, v___y_4255_, v___y_4256_, v___y_4257_);
return v___x_4260_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7___redArg___boxed(lean_object* v_constName_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7___redArg(v_constName_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; lean_object* v_env_4275_; uint8_t v___x_4276_; lean_object* v___x_4277_; 
v___x_4274_ = lean_st_ref_get(v___y_4272_);
v_env_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc_ref(v_env_4275_);
lean_dec(v___x_4274_);
v___x_4276_ = 0;
lean_inc(v_constName_4268_);
v___x_4277_ = l_Lean_Environment_find_x3f(v_env_4275_, v_constName_4268_, v___x_4276_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v___x_4278_; 
v___x_4278_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7___redArg(v_constName_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
return v___x_4278_;
}
else
{
lean_object* v_val_4279_; lean_object* v___x_4281_; uint8_t v_isShared_4282_; uint8_t v_isSharedCheck_4286_; 
lean_dec(v_constName_4268_);
v_val_4279_ = lean_ctor_get(v___x_4277_, 0);
v_isSharedCheck_4286_ = !lean_is_exclusive(v___x_4277_);
if (v_isSharedCheck_4286_ == 0)
{
v___x_4281_ = v___x_4277_;
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
else
{
lean_inc(v_val_4279_);
lean_dec(v___x_4277_);
v___x_4281_ = lean_box(0);
v_isShared_4282_ = v_isSharedCheck_4286_;
goto v_resetjp_4280_;
}
v_resetjp_4280_:
{
lean_object* v___x_4284_; 
if (v_isShared_4282_ == 0)
{
lean_ctor_set_tag(v___x_4281_, 0);
v___x_4284_ = v___x_4281_;
goto v_reusejp_4283_;
}
else
{
lean_object* v_reuseFailAlloc_4285_; 
v_reuseFailAlloc_4285_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4285_, 0, v_val_4279_);
v___x_4284_ = v_reuseFailAlloc_4285_;
goto v_reusejp_4283_;
}
v_reusejp_4283_:
{
return v___x_4284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
return v_res_4293_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6___redArg___closed__0(void){
_start:
{
lean_object* v___x_4294_; lean_object* v___x_4295_; 
v___x_4294_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4295_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4295_, 0, v___x_4294_);
return v___x_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6___redArg(){
_start:
{
lean_object* v___x_4297_; 
v___x_4297_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6___redArg___closed__0);
return v___x_4297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6___redArg___boxed(lean_object* v___dummy_4298_){
_start:
{
lean_object* v_res_4299_; 
v_res_4299_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6___redArg();
return v_res_4299_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4300_; lean_object* v___x_4301_; 
v___x_4300_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4301_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4301_, 0, v___x_4300_);
return v___x_4301_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4302_; lean_object* v___x_4303_; 
v___x_4302_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_4303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4303_, 0, v___x_4302_);
lean_ctor_set(v___x_4303_, 1, v___x_4302_);
return v___x_4303_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4304_; 
v___x_4304_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6___redArg();
return v___x_4304_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_4305_; lean_object* v___x_4306_; lean_object* v___x_4307_; 
v___x_4305_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_4306_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
v___x_4307_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4307_, 0, v___x_4306_);
lean_ctor_set(v___x_4307_, 1, v___x_4305_);
lean_ctor_set(v___x_4307_, 2, v___x_4305_);
lean_ctor_set(v___x_4307_, 3, v___x_4305_);
lean_ctor_set(v___x_4307_, 4, v___x_4305_);
lean_ctor_set(v___x_4307_, 5, v___x_4305_);
lean_ctor_set(v___x_4307_, 6, v___x_4305_);
return v___x_4307_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_4308_, lean_object* v_b_4309_, uint8_t v_kind_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_, lean_object* v___y_4313_){
_start:
{
lean_object* v_toCold_4315_; lean_object* v_currNamespace_4316_; lean_object* v___x_4317_; lean_object* v_env_4318_; lean_object* v_nextMacroScope_4319_; lean_object* v_ngen_4320_; lean_object* v_auxDeclNGen_4321_; lean_object* v_traceState_4322_; lean_object* v_recordedDeps_4323_; lean_object* v_messages_4324_; lean_object* v_infoState_4325_; lean_object* v_snapshotTasks_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4353_; 
v_toCold_4315_ = lean_ctor_get(v___y_4312_, 0);
v_currNamespace_4316_ = lean_ctor_get(v_toCold_4315_, 4);
v___x_4317_ = lean_st_ref_take(v___y_4313_);
v_env_4318_ = lean_ctor_get(v___x_4317_, 0);
v_nextMacroScope_4319_ = lean_ctor_get(v___x_4317_, 1);
v_ngen_4320_ = lean_ctor_get(v___x_4317_, 2);
v_auxDeclNGen_4321_ = lean_ctor_get(v___x_4317_, 3);
v_traceState_4322_ = lean_ctor_get(v___x_4317_, 4);
v_recordedDeps_4323_ = lean_ctor_get(v___x_4317_, 6);
v_messages_4324_ = lean_ctor_get(v___x_4317_, 7);
v_infoState_4325_ = lean_ctor_get(v___x_4317_, 8);
v_snapshotTasks_4326_ = lean_ctor_get(v___x_4317_, 9);
v_isSharedCheck_4353_ = !lean_is_exclusive(v___x_4317_);
if (v_isSharedCheck_4353_ == 0)
{
lean_object* v_unused_4354_; 
v_unused_4354_ = lean_ctor_get(v___x_4317_, 5);
lean_dec(v_unused_4354_);
v___x_4328_ = v___x_4317_;
v_isShared_4329_ = v_isSharedCheck_4353_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_snapshotTasks_4326_);
lean_inc(v_infoState_4325_);
lean_inc(v_messages_4324_);
lean_inc(v_recordedDeps_4323_);
lean_inc(v_traceState_4322_);
lean_inc(v_auxDeclNGen_4321_);
lean_inc(v_ngen_4320_);
lean_inc(v_nextMacroScope_4319_);
lean_inc(v_env_4318_);
lean_dec(v___x_4317_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4353_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4330_; lean_object* v___x_4331_; lean_object* v___x_4333_; 
lean_inc(v_currNamespace_4316_);
v___x_4330_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_4318_, v_ext_4308_, v_b_4309_, v_kind_4310_, v_currNamespace_4316_);
v___x_4331_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 5, v___x_4331_);
lean_ctor_set(v___x_4328_, 0, v___x_4330_);
v___x_4333_ = v___x_4328_;
goto v_reusejp_4332_;
}
else
{
lean_object* v_reuseFailAlloc_4352_; 
v_reuseFailAlloc_4352_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4352_, 0, v___x_4330_);
lean_ctor_set(v_reuseFailAlloc_4352_, 1, v_nextMacroScope_4319_);
lean_ctor_set(v_reuseFailAlloc_4352_, 2, v_ngen_4320_);
lean_ctor_set(v_reuseFailAlloc_4352_, 3, v_auxDeclNGen_4321_);
lean_ctor_set(v_reuseFailAlloc_4352_, 4, v_traceState_4322_);
lean_ctor_set(v_reuseFailAlloc_4352_, 5, v___x_4331_);
lean_ctor_set(v_reuseFailAlloc_4352_, 6, v_recordedDeps_4323_);
lean_ctor_set(v_reuseFailAlloc_4352_, 7, v_messages_4324_);
lean_ctor_set(v_reuseFailAlloc_4352_, 8, v_infoState_4325_);
lean_ctor_set(v_reuseFailAlloc_4352_, 9, v_snapshotTasks_4326_);
v___x_4333_ = v_reuseFailAlloc_4352_;
goto v_reusejp_4332_;
}
v_reusejp_4332_:
{
lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v_mctx_4336_; lean_object* v_zetaDeltaFVarIds_4337_; lean_object* v_postponed_4338_; lean_object* v_diag_4339_; lean_object* v___x_4341_; uint8_t v_isShared_4342_; uint8_t v_isSharedCheck_4350_; 
v___x_4334_ = lean_st_ref_put(v___y_4313_, v___x_4333_);
v___x_4335_ = lean_st_ref_take(v___y_4311_);
v_mctx_4336_ = lean_ctor_get(v___x_4335_, 0);
v_zetaDeltaFVarIds_4337_ = lean_ctor_get(v___x_4335_, 2);
v_postponed_4338_ = lean_ctor_get(v___x_4335_, 3);
v_diag_4339_ = lean_ctor_get(v___x_4335_, 4);
v_isSharedCheck_4350_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4350_ == 0)
{
lean_object* v_unused_4351_; 
v_unused_4351_ = lean_ctor_get(v___x_4335_, 1);
lean_dec(v_unused_4351_);
v___x_4341_ = v___x_4335_;
v_isShared_4342_ = v_isSharedCheck_4350_;
goto v_resetjp_4340_;
}
else
{
lean_inc(v_diag_4339_);
lean_inc(v_postponed_4338_);
lean_inc(v_zetaDeltaFVarIds_4337_);
lean_inc(v_mctx_4336_);
lean_dec(v___x_4335_);
v___x_4341_ = lean_box(0);
v_isShared_4342_ = v_isSharedCheck_4350_;
goto v_resetjp_4340_;
}
v_resetjp_4340_:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; lean_object* v___x_4346_; 
v___x_4343_ = lean_box(0);
v___x_4344_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_4342_ == 0)
{
lean_ctor_set(v___x_4341_, 1, v___x_4344_);
v___x_4346_ = v___x_4341_;
goto v_reusejp_4345_;
}
else
{
lean_object* v_reuseFailAlloc_4349_; 
v_reuseFailAlloc_4349_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4349_, 0, v_mctx_4336_);
lean_ctor_set(v_reuseFailAlloc_4349_, 1, v___x_4344_);
lean_ctor_set(v_reuseFailAlloc_4349_, 2, v_zetaDeltaFVarIds_4337_);
lean_ctor_set(v_reuseFailAlloc_4349_, 3, v_postponed_4338_);
lean_ctor_set(v_reuseFailAlloc_4349_, 4, v_diag_4339_);
v___x_4346_ = v_reuseFailAlloc_4349_;
goto v_reusejp_4345_;
}
v_reusejp_4345_:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4347_ = lean_st_ref_put(v___y_4311_, v___x_4346_);
v___x_4348_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4348_, 0, v___x_4343_);
return v___x_4348_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_4355_, lean_object* v_b_4356_, lean_object* v_kind_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_){
_start:
{
uint8_t v_kind_boxed_4362_; lean_object* v_res_4363_; 
v_kind_boxed_4362_ = lean_unbox(v_kind_4357_);
v_res_4363_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_4355_, v_b_4356_, v_kind_boxed_4362_, v___y_4358_, v___y_4359_, v___y_4360_);
lean_dec(v___y_4360_);
lean_dec_ref(v___y_4359_);
lean_dec(v___y_4358_);
return v_res_4363_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v___x_4370_; lean_object* v_env_4371_; uint8_t v___x_4372_; lean_object* v___x_4373_; 
v___x_4370_ = lean_st_ref_get(v___y_4368_);
v_env_4371_ = lean_ctor_get(v___x_4370_, 0);
lean_inc_ref(v_env_4371_);
lean_dec(v___x_4370_);
v___x_4372_ = 0;
lean_inc(v_constName_4364_);
v___x_4373_ = l_Lean_Environment_findConstVal_x3f(v_env_4371_, v_constName_4364_, v___x_4372_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v___x_4374_; 
v___x_4374_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7___redArg(v_constName_4364_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
return v___x_4374_;
}
else
{
lean_object* v_val_4375_; lean_object* v___x_4377_; uint8_t v_isShared_4378_; uint8_t v_isSharedCheck_4382_; 
lean_dec(v_constName_4364_);
v_val_4375_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4382_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4382_ == 0)
{
v___x_4377_ = v___x_4373_;
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
else
{
lean_inc(v_val_4375_);
lean_dec(v___x_4373_);
v___x_4377_ = lean_box(0);
v_isShared_4378_ = v_isSharedCheck_4382_;
goto v_resetjp_4376_;
}
v_resetjp_4376_:
{
lean_object* v___x_4380_; 
if (v_isShared_4378_ == 0)
{
lean_ctor_set_tag(v___x_4377_, 0);
v___x_4380_ = v___x_4377_;
goto v_reusejp_4379_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_val_4375_);
v___x_4380_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4379_;
}
v_reusejp_4379_:
{
return v___x_4380_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_){
_start:
{
lean_object* v_res_4389_; 
v_res_4389_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4383_, v___y_4384_, v___y_4385_, v___y_4386_, v___y_4387_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
lean_dec(v___y_4385_);
lean_dec_ref(v___y_4384_);
return v_res_4389_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4390_, lean_object* v_a_4391_){
_start:
{
if (lean_obj_tag(v_a_4390_) == 0)
{
lean_object* v___x_4392_; 
v___x_4392_ = l_List_reverse___redArg(v_a_4391_);
return v___x_4392_;
}
else
{
lean_object* v_head_4393_; lean_object* v_tail_4394_; lean_object* v___x_4396_; uint8_t v_isShared_4397_; uint8_t v_isSharedCheck_4403_; 
v_head_4393_ = lean_ctor_get(v_a_4390_, 0);
v_tail_4394_ = lean_ctor_get(v_a_4390_, 1);
v_isSharedCheck_4403_ = !lean_is_exclusive(v_a_4390_);
if (v_isSharedCheck_4403_ == 0)
{
v___x_4396_ = v_a_4390_;
v_isShared_4397_ = v_isSharedCheck_4403_;
goto v_resetjp_4395_;
}
else
{
lean_inc(v_tail_4394_);
lean_inc(v_head_4393_);
lean_dec(v_a_4390_);
v___x_4396_ = lean_box(0);
v_isShared_4397_ = v_isSharedCheck_4403_;
goto v_resetjp_4395_;
}
v_resetjp_4395_:
{
lean_object* v___x_4398_; lean_object* v___x_4400_; 
v___x_4398_ = l_Lean_mkLevelParam(v_head_4393_);
if (v_isShared_4397_ == 0)
{
lean_ctor_set(v___x_4396_, 1, v_a_4391_);
lean_ctor_set(v___x_4396_, 0, v___x_4398_);
v___x_4400_ = v___x_4396_;
goto v_reusejp_4399_;
}
else
{
lean_object* v_reuseFailAlloc_4402_; 
v_reuseFailAlloc_4402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4402_, 0, v___x_4398_);
lean_ctor_set(v_reuseFailAlloc_4402_, 1, v_a_4391_);
v___x_4400_ = v_reuseFailAlloc_4402_;
goto v_reusejp_4399_;
}
v_reusejp_4399_:
{
v_a_4390_ = v_tail_4394_;
v_a_4391_ = v___x_4400_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_){
_start:
{
lean_object* v___x_4410_; 
lean_inc(v_constName_4404_);
v___x_4410_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4404_, v___y_4405_, v___y_4406_, v___y_4407_, v___y_4408_);
if (lean_obj_tag(v___x_4410_) == 0)
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4422_; 
v_a_4411_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4422_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4422_ == 0)
{
v___x_4413_ = v___x_4410_;
v_isShared_4414_ = v_isSharedCheck_4422_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4410_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4422_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v_levelParams_4415_; lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4420_; 
v_levelParams_4415_ = lean_ctor_get(v_a_4411_, 1);
lean_inc(v_levelParams_4415_);
lean_dec(v_a_4411_);
v___x_4416_ = lean_box(0);
v___x_4417_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4415_, v___x_4416_);
v___x_4418_ = l_Lean_mkConst(v_constName_4404_, v___x_4417_);
if (v_isShared_4414_ == 0)
{
lean_ctor_set(v___x_4413_, 0, v___x_4418_);
v___x_4420_ = v___x_4413_;
goto v_reusejp_4419_;
}
else
{
lean_object* v_reuseFailAlloc_4421_; 
v_reuseFailAlloc_4421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4421_, 0, v___x_4418_);
v___x_4420_ = v_reuseFailAlloc_4421_;
goto v_reusejp_4419_;
}
v_reusejp_4419_:
{
return v___x_4420_;
}
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec(v_constName_4404_);
v_a_4423_ = lean_ctor_get(v___x_4410_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4410_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4410_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4410_);
v___x_4425_ = lean_box(0);
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
v_resetjp_4424_:
{
lean_object* v___x_4428_; 
if (v_isShared_4426_ == 0)
{
v___x_4428_ = v___x_4425_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4429_; 
v_reuseFailAlloc_4429_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4429_, 0, v_a_4423_);
v___x_4428_ = v_reuseFailAlloc_4429_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
return v___x_4428_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4431_, lean_object* v___y_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v_res_4437_; 
v_res_4437_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4431_, v___y_4432_, v___y_4433_, v___y_4434_, v___y_4435_);
lean_dec(v___y_4435_);
lean_dec_ref(v___y_4434_);
lean_dec(v___y_4433_);
lean_dec_ref(v___y_4432_);
return v_res_4437_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4439_; lean_object* v___x_4440_; 
v___x_4439_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4440_ = l_Lean_stringToMessageData(v___x_4439_);
return v___x_4440_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4442_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4443_ = l_Lean_stringToMessageData(v___x_4442_);
return v___x_4443_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_4445_; lean_object* v___x_4446_; 
v___x_4445_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_4446_ = l_Lean_stringToMessageData(v___x_4445_);
return v___x_4446_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__7(void){
_start:
{
lean_object* v___x_4448_; lean_object* v___x_4449_; 
v___x_4448_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__6));
v___x_4449_ = l_Lean_stringToMessageData(v___x_4448_);
return v___x_4449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4450_, uint8_t v_attrKind_4451_, lean_object* v_prio_4452_, lean_object* v_a_4453_, lean_object* v_a_4454_, lean_object* v_a_4455_, lean_object* v_a_4456_){
_start:
{
lean_object* v___x_4458_; 
lean_inc(v_declName_4450_);
v___x_4458_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4450_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
if (lean_obj_tag(v___x_4458_) == 0)
{
lean_object* v_a_4459_; lean_object* v___y_4461_; lean_object* v___y_4462_; lean_object* v___y_4463_; lean_object* v___y_4464_; lean_object* v___y_4465_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___x_4537_; 
v_a_4459_ = lean_ctor_get(v___x_4458_, 0);
lean_inc(v_a_4459_);
lean_dec_ref_known(v___x_4458_, 1);
lean_inc(v_declName_4450_);
v___x_4537_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4450_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
if (lean_obj_tag(v___x_4537_) == 0)
{
lean_object* v_a_4538_; lean_object* v___x_4539_; uint8_t v___x_4540_; 
v_a_4538_ = lean_ctor_get(v___x_4537_, 0);
lean_inc(v_a_4538_);
lean_dec_ref_known(v___x_4537_, 1);
v___x_4539_ = l_Lean_ConstantInfo_type(v_a_4538_);
v___x_4540_ = l_Lean_Expr_hasSorry(v___x_4539_);
lean_dec_ref(v___x_4539_);
if (v___x_4540_ == 0)
{
lean_object* v___x_4541_; 
lean_inc(v_a_4459_);
v___x_4541_ = l_Lean_Meta_checkNonClassInstance(v_a_4459_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
if (lean_obj_tag(v___x_4541_) == 0)
{
lean_object* v___x_4542_; 
lean_dec_ref_known(v___x_4541_, 1);
v___x_4542_ = l_Lean_Meta_checkImpossibleInstance(v_a_4538_, v_a_4453_, v_a_4454_, v_a_4455_, v_a_4456_);
lean_dec(v_a_4538_);
if (lean_obj_tag(v___x_4542_) == 0)
{
lean_dec_ref_known(v___x_4542_, 1);
v___y_4489_ = v_a_4453_;
v___y_4490_ = v_a_4454_;
v___y_4491_ = v_a_4455_;
v___y_4492_ = v_a_4456_;
goto v___jp_4488_;
}
else
{
lean_dec(v_a_4459_);
lean_dec(v_prio_4452_);
lean_dec(v_declName_4450_);
return v___x_4542_;
}
}
else
{
lean_dec(v_a_4538_);
lean_dec(v_a_4459_);
lean_dec(v_prio_4452_);
lean_dec(v_declName_4450_);
return v___x_4541_;
}
}
else
{
lean_dec(v_a_4538_);
v___y_4489_ = v_a_4453_;
v___y_4490_ = v_a_4454_;
v___y_4491_ = v_a_4455_;
v___y_4492_ = v_a_4456_;
goto v___jp_4488_;
}
}
else
{
lean_object* v_a_4543_; lean_object* v___x_4545_; uint8_t v_isShared_4546_; uint8_t v_isSharedCheck_4550_; 
lean_dec(v_a_4459_);
lean_dec(v_prio_4452_);
lean_dec(v_declName_4450_);
v_a_4543_ = lean_ctor_get(v___x_4537_, 0);
v_isSharedCheck_4550_ = !lean_is_exclusive(v___x_4537_);
if (v_isSharedCheck_4550_ == 0)
{
v___x_4545_ = v___x_4537_;
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
else
{
lean_inc(v_a_4543_);
lean_dec(v___x_4537_);
v___x_4545_ = lean_box(0);
v_isShared_4546_ = v_isSharedCheck_4550_;
goto v_resetjp_4544_;
}
v_resetjp_4544_:
{
lean_object* v___x_4548_; 
if (v_isShared_4546_ == 0)
{
v___x_4548_ = v___x_4545_;
goto v_reusejp_4547_;
}
else
{
lean_object* v_reuseFailAlloc_4549_; 
v_reuseFailAlloc_4549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4549_, 0, v_a_4543_);
v___x_4548_ = v_reuseFailAlloc_4549_;
goto v_reusejp_4547_;
}
v_reusejp_4547_:
{
return v___x_4548_;
}
}
}
v___jp_4460_:
{
lean_object* v___x_4466_; lean_object* v_a_4467_; lean_object* v___x_4469_; uint8_t v_isShared_4470_; uint8_t v_isSharedCheck_4487_; 
lean_inc(v_declName_4450_);
v___x_4466_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4450_, v___y_4465_);
v_a_4467_ = lean_ctor_get(v___x_4466_, 0);
v_isSharedCheck_4487_ = !lean_is_exclusive(v___x_4466_);
if (v_isSharedCheck_4487_ == 0)
{
v___x_4469_ = v___x_4466_;
v_isShared_4470_ = v_isSharedCheck_4487_;
goto v_resetjp_4468_;
}
else
{
lean_inc(v_a_4467_);
lean_dec(v___x_4466_);
v___x_4469_ = lean_box(0);
v_isShared_4470_ = v_isSharedCheck_4487_;
goto v_resetjp_4468_;
}
v_resetjp_4468_:
{
lean_object* v___x_4471_; 
lean_inc(v_a_4459_);
v___x_4471_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4459_, v_a_4467_, v___y_4462_, v___y_4463_, v___y_4464_, v___y_4465_);
if (lean_obj_tag(v___x_4471_) == 0)
{
lean_object* v_a_4472_; lean_object* v___x_4473_; lean_object* v___x_4475_; 
v_a_4472_ = lean_ctor_get(v___x_4471_, 0);
lean_inc(v_a_4472_);
lean_dec_ref_known(v___x_4471_, 1);
v___x_4473_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4470_ == 0)
{
lean_ctor_set_tag(v___x_4469_, 1);
lean_ctor_set(v___x_4469_, 0, v_declName_4450_);
v___x_4475_ = v___x_4469_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4478_; 
v_reuseFailAlloc_4478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4478_, 0, v_declName_4450_);
v___x_4475_ = v_reuseFailAlloc_4478_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4476_, 0, v___y_4461_);
lean_ctor_set(v___x_4476_, 1, v_a_4459_);
lean_ctor_set(v___x_4476_, 2, v_prio_4452_);
lean_ctor_set(v___x_4476_, 3, v___x_4475_);
lean_ctor_set(v___x_4476_, 4, v_a_4472_);
lean_ctor_set_uint8(v___x_4476_, sizeof(void*)*5, v_attrKind_4451_);
v___x_4477_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4473_, v___x_4476_, v_attrKind_4451_, v___y_4463_, v___y_4464_, v___y_4465_);
return v___x_4477_;
}
}
else
{
lean_object* v_a_4479_; lean_object* v___x_4481_; uint8_t v_isShared_4482_; uint8_t v_isSharedCheck_4486_; 
lean_del_object(v___x_4469_);
lean_dec_ref(v___y_4461_);
lean_dec(v_a_4459_);
lean_dec(v_prio_4452_);
lean_dec(v_declName_4450_);
v_a_4479_ = lean_ctor_get(v___x_4471_, 0);
v_isSharedCheck_4486_ = !lean_is_exclusive(v___x_4471_);
if (v_isSharedCheck_4486_ == 0)
{
v___x_4481_ = v___x_4471_;
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
else
{
lean_inc(v_a_4479_);
lean_dec(v___x_4471_);
v___x_4481_ = lean_box(0);
v_isShared_4482_ = v_isSharedCheck_4486_;
goto v_resetjp_4480_;
}
v_resetjp_4480_:
{
lean_object* v___x_4484_; 
if (v_isShared_4482_ == 0)
{
v___x_4484_ = v___x_4481_;
goto v_reusejp_4483_;
}
else
{
lean_object* v_reuseFailAlloc_4485_; 
v_reuseFailAlloc_4485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4485_, 0, v_a_4479_);
v___x_4484_ = v_reuseFailAlloc_4485_;
goto v_reusejp_4483_;
}
v_reusejp_4483_:
{
return v___x_4484_;
}
}
}
}
}
v___jp_4488_:
{
lean_object* v___x_4493_; 
lean_inc(v_a_4459_);
v___x_4493_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4459_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4493_) == 0)
{
lean_object* v_a_4494_; lean_object* v___x_4495_; lean_object* v_a_4496_; uint8_t v___x_4497_; uint8_t v___x_4498_; uint8_t v___x_4499_; 
v_a_4494_ = lean_ctor_get(v___x_4493_, 0);
lean_inc(v_a_4494_);
lean_dec_ref_known(v___x_4493_, 1);
lean_inc(v_declName_4450_);
v___x_4495_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4450_, v___y_4492_);
v_a_4496_ = lean_ctor_get(v___x_4495_, 0);
lean_inc(v_a_4496_);
lean_dec_ref(v___x_4495_);
v___x_4497_ = 1;
v___x_4498_ = lean_unbox(v_a_4496_);
lean_dec(v_a_4496_);
v___x_4499_ = l_Lean_instBEqReducibilityStatus_beq(v___x_4498_, v___x_4497_);
if (v___x_4499_ == 0)
{
v___y_4461_ = v_a_4494_;
v___y_4462_ = v___y_4489_;
v___y_4463_ = v___y_4490_;
v___y_4464_ = v___y_4491_;
v___y_4465_ = v___y_4492_;
goto v___jp_4460_;
}
else
{
lean_object* v___x_4500_; 
lean_inc(v_declName_4450_);
v___x_4500_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4450_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4500_) == 0)
{
lean_object* v_a_4501_; uint8_t v___x_4502_; 
v_a_4501_ = lean_ctor_get(v___x_4500_, 0);
lean_inc(v_a_4501_);
lean_dec_ref_known(v___x_4500_, 1);
v___x_4502_ = l_Lean_ConstantInfo_isDefinition(v_a_4501_);
lean_dec(v_a_4501_);
if (v___x_4502_ == 0)
{
lean_object* v___x_4503_; lean_object* v_env_4504_; uint8_t v___x_4505_; 
v___x_4503_ = lean_st_ref_get(v___y_4492_);
v_env_4504_ = lean_ctor_get(v___x_4503_, 0);
lean_inc_ref(v_env_4504_);
lean_dec(v___x_4503_);
lean_inc(v_declName_4450_);
v___x_4505_ = l_Lean_wasOriginallyDefn(v_env_4504_, v_declName_4450_);
if (v___x_4505_ == 0)
{
v___y_4461_ = v_a_4494_;
v___y_4462_ = v___y_4489_;
v___y_4463_ = v___y_4490_;
v___y_4464_ = v___y_4491_;
v___y_4465_ = v___y_4492_;
goto v___jp_4460_;
}
else
{
lean_object* v___x_4506_; lean_object* v___x_4507_; lean_object* v___x_4508_; lean_object* v___x_4509_; lean_object* v___x_4510_; lean_object* v___x_4511_; 
v___x_4506_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4450_);
v___x_4507_ = l_Lean_MessageData_ofName(v_declName_4450_);
v___x_4508_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4508_, 0, v___x_4506_);
lean_ctor_set(v___x_4508_, 1, v___x_4507_);
v___x_4509_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4510_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4510_, 0, v___x_4508_);
lean_ctor_set(v___x_4510_, 1, v___x_4509_);
v___x_4511_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4510_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4511_) == 0)
{
lean_dec_ref_known(v___x_4511_, 1);
v___y_4461_ = v_a_4494_;
v___y_4462_ = v___y_4489_;
v___y_4463_ = v___y_4490_;
v___y_4464_ = v___y_4491_;
v___y_4465_ = v___y_4492_;
goto v___jp_4460_;
}
else
{
lean_dec(v_a_4494_);
lean_dec(v_a_4459_);
lean_dec(v_prio_4452_);
lean_dec(v_declName_4450_);
return v___x_4511_;
}
}
}
else
{
lean_object* v___x_4512_; lean_object* v___x_4513_; uint8_t v___x_4514_; 
v___x_4512_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4491_);
v___x_4513_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility));
v___x_4514_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_4512_, v___x_4513_);
lean_dec_ref(v___x_4512_);
if (v___x_4514_ == 0)
{
v___y_4461_ = v_a_4494_;
v___y_4462_ = v___y_4489_;
v___y_4463_ = v___y_4490_;
v___y_4464_ = v___y_4491_;
v___y_4465_ = v___y_4492_;
goto v___jp_4460_;
}
else
{
lean_object* v___x_4515_; lean_object* v___x_4516_; lean_object* v___x_4517_; lean_object* v___x_4518_; lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4515_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
lean_inc(v_declName_4450_);
v___x_4516_ = l_Lean_MessageData_ofName(v_declName_4450_);
v___x_4517_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4517_, 0, v___x_4515_);
lean_ctor_set(v___x_4517_, 1, v___x_4516_);
v___x_4518_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__7, &l_Lean_Meta_addInstance___closed__7_once, _init_l_Lean_Meta_addInstance___closed__7);
v___x_4519_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4519_, 0, v___x_4517_);
lean_ctor_set(v___x_4519_, 1, v___x_4518_);
v___x_4520_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4519_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
if (lean_obj_tag(v___x_4520_) == 0)
{
lean_dec_ref_known(v___x_4520_, 1);
v___y_4461_ = v_a_4494_;
v___y_4462_ = v___y_4489_;
v___y_4463_ = v___y_4490_;
v___y_4464_ = v___y_4491_;
v___y_4465_ = v___y_4492_;
goto v___jp_4460_;
}
else
{
lean_dec(v_a_4494_);
lean_dec(v_a_4459_);
lean_dec(v_prio_4452_);
lean_dec(v_declName_4450_);
return v___x_4520_;
}
}
}
}
else
{
lean_object* v_a_4521_; lean_object* v___x_4523_; uint8_t v_isShared_4524_; uint8_t v_isSharedCheck_4528_; 
lean_dec(v_a_4494_);
lean_dec(v_a_4459_);
lean_dec(v_prio_4452_);
lean_dec(v_declName_4450_);
v_a_4521_ = lean_ctor_get(v___x_4500_, 0);
v_isSharedCheck_4528_ = !lean_is_exclusive(v___x_4500_);
if (v_isSharedCheck_4528_ == 0)
{
v___x_4523_ = v___x_4500_;
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
else
{
lean_inc(v_a_4521_);
lean_dec(v___x_4500_);
v___x_4523_ = lean_box(0);
v_isShared_4524_ = v_isSharedCheck_4528_;
goto v_resetjp_4522_;
}
v_resetjp_4522_:
{
lean_object* v___x_4526_; 
if (v_isShared_4524_ == 0)
{
v___x_4526_ = v___x_4523_;
goto v_reusejp_4525_;
}
else
{
lean_object* v_reuseFailAlloc_4527_; 
v_reuseFailAlloc_4527_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4527_, 0, v_a_4521_);
v___x_4526_ = v_reuseFailAlloc_4527_;
goto v_reusejp_4525_;
}
v_reusejp_4525_:
{
return v___x_4526_;
}
}
}
}
}
else
{
lean_object* v_a_4529_; lean_object* v___x_4531_; uint8_t v_isShared_4532_; uint8_t v_isSharedCheck_4536_; 
lean_dec(v_a_4459_);
lean_dec(v_prio_4452_);
lean_dec(v_declName_4450_);
v_a_4529_ = lean_ctor_get(v___x_4493_, 0);
v_isSharedCheck_4536_ = !lean_is_exclusive(v___x_4493_);
if (v_isSharedCheck_4536_ == 0)
{
v___x_4531_ = v___x_4493_;
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
else
{
lean_inc(v_a_4529_);
lean_dec(v___x_4493_);
v___x_4531_ = lean_box(0);
v_isShared_4532_ = v_isSharedCheck_4536_;
goto v_resetjp_4530_;
}
v_resetjp_4530_:
{
lean_object* v___x_4534_; 
if (v_isShared_4532_ == 0)
{
v___x_4534_ = v___x_4531_;
goto v_reusejp_4533_;
}
else
{
lean_object* v_reuseFailAlloc_4535_; 
v_reuseFailAlloc_4535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4535_, 0, v_a_4529_);
v___x_4534_ = v_reuseFailAlloc_4535_;
goto v_reusejp_4533_;
}
v_reusejp_4533_:
{
return v___x_4534_;
}
}
}
}
}
else
{
lean_object* v_a_4551_; lean_object* v___x_4553_; uint8_t v_isShared_4554_; uint8_t v_isSharedCheck_4558_; 
lean_dec(v_prio_4452_);
lean_dec(v_declName_4450_);
v_a_4551_ = lean_ctor_get(v___x_4458_, 0);
v_isSharedCheck_4558_ = !lean_is_exclusive(v___x_4458_);
if (v_isSharedCheck_4558_ == 0)
{
v___x_4553_ = v___x_4458_;
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
else
{
lean_inc(v_a_4551_);
lean_dec(v___x_4458_);
v___x_4553_ = lean_box(0);
v_isShared_4554_ = v_isSharedCheck_4558_;
goto v_resetjp_4552_;
}
v_resetjp_4552_:
{
lean_object* v___x_4556_; 
if (v_isShared_4554_ == 0)
{
v___x_4556_ = v___x_4553_;
goto v_reusejp_4555_;
}
else
{
lean_object* v_reuseFailAlloc_4557_; 
v_reuseFailAlloc_4557_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4557_, 0, v_a_4551_);
v___x_4556_ = v_reuseFailAlloc_4557_;
goto v_reusejp_4555_;
}
v_reusejp_4555_:
{
return v___x_4556_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4559_, lean_object* v_attrKind_4560_, lean_object* v_prio_4561_, lean_object* v_a_4562_, lean_object* v_a_4563_, lean_object* v_a_4564_, lean_object* v_a_4565_, lean_object* v_a_4566_){
_start:
{
uint8_t v_attrKind_boxed_4567_; lean_object* v_res_4568_; 
v_attrKind_boxed_4567_ = lean_unbox(v_attrKind_4560_);
v_res_4568_ = l_Lean_Meta_addInstance(v_declName_4559_, v_attrKind_boxed_4567_, v_prio_4561_, v_a_4562_, v_a_4563_, v_a_4564_, v_a_4565_);
lean_dec(v_a_4565_);
lean_dec_ref(v_a_4564_);
lean_dec(v_a_4563_);
lean_dec_ref(v_a_4562_);
return v_res_4568_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_4569_, lean_object* v_00_u03b2_4570_, lean_object* v_00_u03c3_4571_, lean_object* v_ext_4572_, lean_object* v_b_4573_, uint8_t v_kind_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_, lean_object* v___y_4578_){
_start:
{
lean_object* v___x_4580_; 
v___x_4580_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_4572_, v_b_4573_, v_kind_4574_, v___y_4576_, v___y_4577_, v___y_4578_);
return v___x_4580_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_4581_, lean_object* v_00_u03b2_4582_, lean_object* v_00_u03c3_4583_, lean_object* v_ext_4584_, lean_object* v_b_4585_, lean_object* v_kind_4586_, lean_object* v___y_4587_, lean_object* v___y_4588_, lean_object* v___y_4589_, lean_object* v___y_4590_, lean_object* v___y_4591_){
_start:
{
uint8_t v_kind_boxed_4592_; lean_object* v_res_4593_; 
v_kind_boxed_4592_ = lean_unbox(v_kind_4586_);
v_res_4593_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_4581_, v_00_u03b2_4582_, v_00_u03c3_4583_, v_ext_4584_, v_b_4585_, v_kind_boxed_4592_, v___y_4587_, v___y_4588_, v___y_4589_, v___y_4590_);
lean_dec(v___y_4590_);
lean_dec_ref(v___y_4589_);
lean_dec(v___y_4588_);
lean_dec_ref(v___y_4587_);
return v_res_4593_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4_spec__6(lean_object* v_00_u03b2_4594_){
_start:
{
lean_object* v___x_4595_; 
v___x_4595_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
return v___x_4595_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4___redArg(){
_start:
{
lean_object* v___x_4597_; 
v___x_4597_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
return v___x_4597_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4___redArg___boxed(lean_object* v___dummy_4598_){
_start:
{
lean_object* v_res_4599_; 
v_res_4599_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4___redArg();
return v_res_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2_spec__4(lean_object* v_00_u03b2_4600_){
_start:
{
lean_object* v___x_4601_; 
v___x_4601_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
return v___x_4601_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7(lean_object* v_00_u03b1_4602_, lean_object* v_constName_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_){
_start:
{
lean_object* v___x_4609_; 
v___x_4609_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7___redArg(v_constName_4603_, v___y_4604_, v___y_4605_, v___y_4606_, v___y_4607_);
return v___x_4609_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7___boxed(lean_object* v_00_u03b1_4610_, lean_object* v_constName_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_){
_start:
{
lean_object* v_res_4617_; 
v_res_4617_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7(v_00_u03b1_4610_, v_constName_4611_, v___y_4612_, v___y_4613_, v___y_4614_, v___y_4615_);
lean_dec(v___y_4615_);
lean_dec_ref(v___y_4614_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
return v_res_4617_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9(lean_object* v_00_u03b1_4618_, lean_object* v_ref_4619_, lean_object* v_constName_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v___x_4626_; 
v___x_4626_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg(v_ref_4619_, v_constName_4620_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
return v___x_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___boxed(lean_object* v_00_u03b1_4627_, lean_object* v_ref_4628_, lean_object* v_constName_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_, lean_object* v___y_4634_){
_start:
{
lean_object* v_res_4635_; 
v_res_4635_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9(v_00_u03b1_4627_, v_ref_4628_, v_constName_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
lean_dec(v___y_4633_);
lean_dec_ref(v___y_4632_);
lean_dec(v___y_4631_);
lean_dec_ref(v___y_4630_);
lean_dec(v_ref_4628_);
return v_res_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10(lean_object* v_00_u03b1_4636_, lean_object* v_ref_4637_, lean_object* v_msg_4638_, lean_object* v_declHint_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_){
_start:
{
lean_object* v___x_4645_; 
v___x_4645_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10___redArg(v_ref_4637_, v_msg_4638_, v_declHint_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
return v___x_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10___boxed(lean_object* v_00_u03b1_4646_, lean_object* v_ref_4647_, lean_object* v_msg_4648_, lean_object* v_declHint_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v_res_4655_; 
v_res_4655_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10(v_00_u03b1_4646_, v_ref_4647_, v_msg_4648_, v_declHint_4649_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
lean_dec(v_ref_4647_);
return v_res_4655_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12(lean_object* v_msg_4656_, lean_object* v_declHint_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_){
_start:
{
lean_object* v___x_4663_; 
v___x_4663_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg(v_msg_4656_, v_declHint_4657_, v___y_4661_);
return v___x_4663_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___boxed(lean_object* v_msg_4664_, lean_object* v_declHint_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12(v_msg_4664_, v_declHint_4665_, v___y_4666_, v___y_4667_, v___y_4668_, v___y_4669_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
lean_dec(v___y_4667_);
lean_dec_ref(v___y_4666_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__12(lean_object* v_00_u03b1_4672_, lean_object* v_ref_4673_, lean_object* v_msg_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v___x_4680_; 
v___x_4680_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__12___redArg(v_ref_4673_, v_msg_4674_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
return v___x_4680_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__12___boxed(lean_object* v_00_u03b1_4681_, lean_object* v_ref_4682_, lean_object* v_msg_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_, lean_object* v___y_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v_res_4689_; 
v_res_4689_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__12(v_00_u03b1_4681_, v_ref_4682_, v_msg_4683_, v___y_4684_, v___y_4685_, v___y_4686_, v___y_4687_);
lean_dec(v___y_4687_);
lean_dec_ref(v___y_4686_);
lean_dec(v___y_4685_);
lean_dec_ref(v___y_4684_);
lean_dec(v_ref_4682_);
return v_res_4689_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4690_, uint8_t v_s_4691_, lean_object* v___y_4692_, lean_object* v___y_4693_){
_start:
{
lean_object* v___x_4695_; lean_object* v_env_4696_; lean_object* v_nextMacroScope_4697_; lean_object* v_ngen_4698_; lean_object* v_auxDeclNGen_4699_; lean_object* v_traceState_4700_; lean_object* v_recordedDeps_4701_; lean_object* v_messages_4702_; lean_object* v_infoState_4703_; lean_object* v_snapshotTasks_4704_; lean_object* v___x_4706_; uint8_t v_isShared_4707_; uint8_t v_isSharedCheck_4733_; 
v___x_4695_ = lean_st_ref_take(v___y_4693_);
v_env_4696_ = lean_ctor_get(v___x_4695_, 0);
v_nextMacroScope_4697_ = lean_ctor_get(v___x_4695_, 1);
v_ngen_4698_ = lean_ctor_get(v___x_4695_, 2);
v_auxDeclNGen_4699_ = lean_ctor_get(v___x_4695_, 3);
v_traceState_4700_ = lean_ctor_get(v___x_4695_, 4);
v_recordedDeps_4701_ = lean_ctor_get(v___x_4695_, 6);
v_messages_4702_ = lean_ctor_get(v___x_4695_, 7);
v_infoState_4703_ = lean_ctor_get(v___x_4695_, 8);
v_snapshotTasks_4704_ = lean_ctor_get(v___x_4695_, 9);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4695_);
if (v_isSharedCheck_4733_ == 0)
{
lean_object* v_unused_4734_; 
v_unused_4734_ = lean_ctor_get(v___x_4695_, 5);
lean_dec(v_unused_4734_);
v___x_4706_ = v___x_4695_;
v_isShared_4707_ = v_isSharedCheck_4733_;
goto v_resetjp_4705_;
}
else
{
lean_inc(v_snapshotTasks_4704_);
lean_inc(v_infoState_4703_);
lean_inc(v_messages_4702_);
lean_inc(v_recordedDeps_4701_);
lean_inc(v_traceState_4700_);
lean_inc(v_auxDeclNGen_4699_);
lean_inc(v_ngen_4698_);
lean_inc(v_nextMacroScope_4697_);
lean_inc(v_env_4696_);
lean_dec(v___x_4695_);
v___x_4706_ = lean_box(0);
v_isShared_4707_ = v_isSharedCheck_4733_;
goto v_resetjp_4705_;
}
v_resetjp_4705_:
{
uint8_t v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4713_; 
v___x_4708_ = 0;
v___x_4709_ = lean_box(0);
v___x_4710_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4696_, v_declName_4690_, v_s_4691_, v___x_4708_, v___x_4709_);
v___x_4711_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_4707_ == 0)
{
lean_ctor_set(v___x_4706_, 5, v___x_4711_);
lean_ctor_set(v___x_4706_, 0, v___x_4710_);
v___x_4713_ = v___x_4706_;
goto v_reusejp_4712_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v___x_4710_);
lean_ctor_set(v_reuseFailAlloc_4732_, 1, v_nextMacroScope_4697_);
lean_ctor_set(v_reuseFailAlloc_4732_, 2, v_ngen_4698_);
lean_ctor_set(v_reuseFailAlloc_4732_, 3, v_auxDeclNGen_4699_);
lean_ctor_set(v_reuseFailAlloc_4732_, 4, v_traceState_4700_);
lean_ctor_set(v_reuseFailAlloc_4732_, 5, v___x_4711_);
lean_ctor_set(v_reuseFailAlloc_4732_, 6, v_recordedDeps_4701_);
lean_ctor_set(v_reuseFailAlloc_4732_, 7, v_messages_4702_);
lean_ctor_set(v_reuseFailAlloc_4732_, 8, v_infoState_4703_);
lean_ctor_set(v_reuseFailAlloc_4732_, 9, v_snapshotTasks_4704_);
v___x_4713_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4712_;
}
v_reusejp_4712_:
{
lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v_mctx_4716_; lean_object* v_zetaDeltaFVarIds_4717_; lean_object* v_postponed_4718_; lean_object* v_diag_4719_; lean_object* v___x_4721_; uint8_t v_isShared_4722_; uint8_t v_isSharedCheck_4730_; 
v___x_4714_ = lean_st_ref_put(v___y_4693_, v___x_4713_);
v___x_4715_ = lean_st_ref_take(v___y_4692_);
v_mctx_4716_ = lean_ctor_get(v___x_4715_, 0);
v_zetaDeltaFVarIds_4717_ = lean_ctor_get(v___x_4715_, 2);
v_postponed_4718_ = lean_ctor_get(v___x_4715_, 3);
v_diag_4719_ = lean_ctor_get(v___x_4715_, 4);
v_isSharedCheck_4730_ = !lean_is_exclusive(v___x_4715_);
if (v_isSharedCheck_4730_ == 0)
{
lean_object* v_unused_4731_; 
v_unused_4731_ = lean_ctor_get(v___x_4715_, 1);
lean_dec(v_unused_4731_);
v___x_4721_ = v___x_4715_;
v_isShared_4722_ = v_isSharedCheck_4730_;
goto v_resetjp_4720_;
}
else
{
lean_inc(v_diag_4719_);
lean_inc(v_postponed_4718_);
lean_inc(v_zetaDeltaFVarIds_4717_);
lean_inc(v_mctx_4716_);
lean_dec(v___x_4715_);
v___x_4721_ = lean_box(0);
v_isShared_4722_ = v_isSharedCheck_4730_;
goto v_resetjp_4720_;
}
v_resetjp_4720_:
{
lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4726_; 
v___x_4723_ = lean_box(0);
v___x_4724_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_4722_ == 0)
{
lean_ctor_set(v___x_4721_, 1, v___x_4724_);
v___x_4726_ = v___x_4721_;
goto v_reusejp_4725_;
}
else
{
lean_object* v_reuseFailAlloc_4729_; 
v_reuseFailAlloc_4729_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4729_, 0, v_mctx_4716_);
lean_ctor_set(v_reuseFailAlloc_4729_, 1, v___x_4724_);
lean_ctor_set(v_reuseFailAlloc_4729_, 2, v_zetaDeltaFVarIds_4717_);
lean_ctor_set(v_reuseFailAlloc_4729_, 3, v_postponed_4718_);
lean_ctor_set(v_reuseFailAlloc_4729_, 4, v_diag_4719_);
v___x_4726_ = v_reuseFailAlloc_4729_;
goto v_reusejp_4725_;
}
v_reusejp_4725_:
{
lean_object* v___x_4727_; lean_object* v___x_4728_; 
v___x_4727_ = lean_st_ref_put(v___y_4692_, v___x_4726_);
v___x_4728_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4728_, 0, v___x_4723_);
return v___x_4728_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4735_, lean_object* v_s_4736_, lean_object* v___y_4737_, lean_object* v___y_4738_, lean_object* v___y_4739_){
_start:
{
uint8_t v_s_boxed_4740_; lean_object* v_res_4741_; 
v_s_boxed_4740_ = lean_unbox(v_s_4736_);
v_res_4741_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4735_, v_s_boxed_4740_, v___y_4737_, v___y_4738_);
lean_dec(v___y_4738_);
lean_dec(v___y_4737_);
return v_res_4741_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4742_, uint8_t v_attrKind_4743_, lean_object* v_prio_4744_, lean_object* v_a_4745_, lean_object* v_a_4746_, lean_object* v_a_4747_, lean_object* v_a_4748_){
_start:
{
uint8_t v___x_4750_; lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4750_ = 4;
lean_inc(v_declName_4742_);
v___x_4751_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4742_, v___x_4750_, v_a_4746_, v_a_4748_);
lean_dec_ref(v___x_4751_);
v___x_4752_ = l_Lean_Meta_addInstance(v_declName_4742_, v_attrKind_4743_, v_prio_4744_, v_a_4745_, v_a_4746_, v_a_4747_, v_a_4748_);
return v___x_4752_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4753_, lean_object* v_attrKind_4754_, lean_object* v_prio_4755_, lean_object* v_a_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_){
_start:
{
uint8_t v_attrKind_boxed_4761_; lean_object* v_res_4762_; 
v_attrKind_boxed_4761_ = lean_unbox(v_attrKind_4754_);
v_res_4762_ = l_Lean_Meta_registerInstance(v_declName_4753_, v_attrKind_boxed_4761_, v_prio_4755_, v_a_4756_, v_a_4757_, v_a_4758_, v_a_4759_);
lean_dec(v_a_4759_);
lean_dec_ref(v_a_4758_);
lean_dec(v_a_4757_);
lean_dec_ref(v_a_4756_);
return v_res_4762_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4763_, uint8_t v_s_4764_, lean_object* v___y_4765_, lean_object* v___y_4766_, lean_object* v___y_4767_, lean_object* v___y_4768_){
_start:
{
lean_object* v___x_4770_; 
v___x_4770_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4763_, v_s_4764_, v___y_4766_, v___y_4768_);
return v___x_4770_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4771_, lean_object* v_s_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
uint8_t v_s_boxed_4778_; lean_object* v_res_4779_; 
v_s_boxed_4778_ = lean_unbox(v_s_4772_);
v_res_4779_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4771_, v_s_boxed_4778_, v___y_4773_, v___y_4774_, v___y_4775_, v___y_4776_);
lean_dec(v___y_4776_);
lean_dec_ref(v___y_4775_);
lean_dec(v___y_4774_);
lean_dec_ref(v___y_4773_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4780_, lean_object* v_x_4781_){
_start:
{
lean_inc_ref(v_a_4780_);
return v_a_4780_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4782_, lean_object* v_x_4783_){
_start:
{
lean_object* v_res_4784_; 
v_res_4784_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4782_, v_x_4783_);
lean_dec_ref(v_x_4783_);
lean_dec_ref(v_a_4782_);
return v_res_4784_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4785_, lean_object* v___y_4786_, lean_object* v___y_4787_){
_start:
{
lean_object* v___x_4789_; lean_object* v_toCold_4790_; lean_object* v_env_4791_; lean_object* v_options_4792_; uint8_t v___x_4793_; lean_object* v_env_4794_; lean_object* v___x_4795_; lean_object* v___x_4796_; lean_object* v___x_4797_; lean_object* v___x_4798_; lean_object* v___x_4799_; lean_object* v___x_4800_; lean_object* v___x_4801_; 
v___x_4789_ = lean_st_ref_get(v___y_4787_);
v_toCold_4790_ = lean_ctor_get(v___y_4786_, 0);
v_env_4791_ = lean_ctor_get(v___x_4789_, 0);
lean_inc_ref(v_env_4791_);
lean_dec(v___x_4789_);
v_options_4792_ = lean_ctor_get(v_toCold_4790_, 2);
v___x_4793_ = 0;
v_env_4794_ = l_Lean_Environment_setRecordingDeps(v_env_4791_, v___x_4793_);
v___x_4795_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__1);
v___x_4796_ = lean_unsigned_to_nat(32u);
v___x_4797_ = lean_mk_empty_array_with_capacity(v___x_4796_);
lean_dec_ref(v___x_4797_);
v___x_4798_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__4);
lean_inc_ref(v_options_4792_);
v___x_4799_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4799_, 0, v_env_4794_);
lean_ctor_set(v___x_4799_, 1, v___x_4795_);
lean_ctor_set(v___x_4799_, 2, v___x_4798_);
lean_ctor_set(v___x_4799_, 3, v_options_4792_);
v___x_4800_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4800_, 0, v___x_4799_);
lean_ctor_set(v___x_4800_, 1, v_msgData_4785_);
v___x_4801_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4801_, 0, v___x_4800_);
return v___x_4801_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_, lean_object* v___y_4805_){
_start:
{
lean_object* v_res_4806_; 
v_res_4806_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4802_, v___y_4803_, v___y_4804_);
lean_dec(v___y_4804_);
lean_dec_ref(v___y_4803_);
return v_res_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4807_, lean_object* v___y_4808_, lean_object* v___y_4809_){
_start:
{
lean_object* v_ref_4811_; lean_object* v___x_4812_; lean_object* v_a_4813_; lean_object* v___x_4815_; uint8_t v_isShared_4816_; uint8_t v_isSharedCheck_4821_; 
v_ref_4811_ = lean_ctor_get(v___y_4808_, 2);
v___x_4812_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4807_, v___y_4808_, v___y_4809_);
v_a_4813_ = lean_ctor_get(v___x_4812_, 0);
v_isSharedCheck_4821_ = !lean_is_exclusive(v___x_4812_);
if (v_isSharedCheck_4821_ == 0)
{
v___x_4815_ = v___x_4812_;
v_isShared_4816_ = v_isSharedCheck_4821_;
goto v_resetjp_4814_;
}
else
{
lean_inc(v_a_4813_);
lean_dec(v___x_4812_);
v___x_4815_ = lean_box(0);
v_isShared_4816_ = v_isSharedCheck_4821_;
goto v_resetjp_4814_;
}
v_resetjp_4814_:
{
lean_object* v___x_4817_; lean_object* v___x_4819_; 
lean_inc(v_ref_4811_);
v___x_4817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4817_, 0, v_ref_4811_);
lean_ctor_set(v___x_4817_, 1, v_a_4813_);
if (v_isShared_4816_ == 0)
{
lean_ctor_set_tag(v___x_4815_, 1);
lean_ctor_set(v___x_4815_, 0, v___x_4817_);
v___x_4819_ = v___x_4815_;
goto v_reusejp_4818_;
}
else
{
lean_object* v_reuseFailAlloc_4820_; 
v_reuseFailAlloc_4820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4820_, 0, v___x_4817_);
v___x_4819_ = v_reuseFailAlloc_4820_;
goto v_reusejp_4818_;
}
v_reusejp_4818_:
{
return v___x_4819_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_, lean_object* v___y_4825_){
_start:
{
lean_object* v_res_4826_; 
v_res_4826_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4822_, v___y_4823_, v___y_4824_);
lean_dec(v___y_4824_);
lean_dec_ref(v___y_4823_);
return v_res_4826_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4827_, lean_object* v_i_4828_, lean_object* v_k_4829_){
_start:
{
lean_object* v___x_4830_; uint8_t v___x_4831_; 
v___x_4830_ = lean_array_get_size(v_keys_4827_);
v___x_4831_ = lean_nat_dec_lt(v_i_4828_, v___x_4830_);
if (v___x_4831_ == 0)
{
lean_dec(v_i_4828_);
return v___x_4831_;
}
else
{
lean_object* v_k_x27_4832_; uint8_t v___x_4833_; 
v_k_x27_4832_ = lean_array_fget_borrowed(v_keys_4827_, v_i_4828_);
v___x_4833_ = lean_name_eq(v_k_4829_, v_k_x27_4832_);
if (v___x_4833_ == 0)
{
lean_object* v___x_4834_; lean_object* v___x_4835_; 
v___x_4834_ = lean_unsigned_to_nat(1u);
v___x_4835_ = lean_nat_add(v_i_4828_, v___x_4834_);
lean_dec(v_i_4828_);
v_i_4828_ = v___x_4835_;
goto _start;
}
else
{
lean_dec(v_i_4828_);
return v___x_4831_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4837_, lean_object* v_i_4838_, lean_object* v_k_4839_){
_start:
{
uint8_t v_res_4840_; lean_object* v_r_4841_; 
v_res_4840_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4837_, v_i_4838_, v_k_4839_);
lean_dec(v_k_4839_);
lean_dec_ref(v_keys_4837_);
v_r_4841_ = lean_box(v_res_4840_);
return v_r_4841_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4842_, size_t v_x_4843_, lean_object* v_x_4844_){
_start:
{
if (lean_obj_tag(v_x_4842_) == 0)
{
lean_object* v_es_4845_; lean_object* v___x_4846_; size_t v___x_4847_; size_t v___x_4848_; lean_object* v_j_4849_; lean_object* v___x_4850_; 
v_es_4845_ = lean_ctor_get(v_x_4842_, 0);
v___x_4846_ = lean_box(2);
v___x_4847_ = ((size_t)31ULL);
v___x_4848_ = lean_usize_land(v_x_4843_, v___x_4847_);
v_j_4849_ = lean_usize_to_nat(v___x_4848_);
v___x_4850_ = lean_array_get_borrowed(v___x_4846_, v_es_4845_, v_j_4849_);
lean_dec(v_j_4849_);
switch(lean_obj_tag(v___x_4850_))
{
case 0:
{
lean_object* v_key_4851_; uint8_t v___x_4852_; 
v_key_4851_ = lean_ctor_get(v___x_4850_, 0);
v___x_4852_ = lean_name_eq(v_x_4844_, v_key_4851_);
return v___x_4852_;
}
case 1:
{
lean_object* v_node_4853_; size_t v___x_4854_; size_t v___x_4855_; 
v_node_4853_ = lean_ctor_get(v___x_4850_, 0);
v___x_4854_ = ((size_t)5ULL);
v___x_4855_ = lean_usize_shift_right(v_x_4843_, v___x_4854_);
v_x_4842_ = v_node_4853_;
v_x_4843_ = v___x_4855_;
goto _start;
}
default: 
{
uint8_t v___x_4857_; 
v___x_4857_ = 0;
return v___x_4857_;
}
}
}
else
{
lean_object* v_ks_4858_; lean_object* v___x_4859_; uint8_t v___x_4860_; 
v_ks_4858_ = lean_ctor_get(v_x_4842_, 0);
v___x_4859_ = lean_unsigned_to_nat(0u);
v___x_4860_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4858_, v___x_4859_, v_x_4844_);
return v___x_4860_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4861_, lean_object* v_x_4862_, lean_object* v_x_4863_){
_start:
{
size_t v_x_2459__boxed_4864_; uint8_t v_res_4865_; lean_object* v_r_4866_; 
v_x_2459__boxed_4864_ = lean_unbox_usize(v_x_4862_);
lean_dec(v_x_4862_);
v_res_4865_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4861_, v_x_2459__boxed_4864_, v_x_4863_);
lean_dec(v_x_4863_);
lean_dec_ref(v_x_4861_);
v_r_4866_ = lean_box(v_res_4865_);
return v_r_4866_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4867_, lean_object* v_x_4868_){
_start:
{
uint64_t v___y_4870_; 
if (lean_obj_tag(v_x_4868_) == 0)
{
uint64_t v___x_4873_; 
v___x_4873_ = 1723ULL;
v___y_4870_ = v___x_4873_;
goto v___jp_4869_;
}
else
{
uint64_t v_hash_4874_; 
v_hash_4874_ = lean_ctor_get_uint64(v_x_4868_, sizeof(void*)*2);
v___y_4870_ = v_hash_4874_;
goto v___jp_4869_;
}
v___jp_4869_:
{
size_t v___x_4871_; uint8_t v___x_4872_; 
v___x_4871_ = lean_uint64_to_usize(v___y_4870_);
v___x_4872_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4867_, v___x_4871_, v_x_4868_);
return v___x_4872_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4875_, lean_object* v_x_4876_){
_start:
{
uint8_t v_res_4877_; lean_object* v_r_4878_; 
v_res_4877_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4875_, v_x_4876_);
lean_dec(v_x_4876_);
lean_dec_ref(v_x_4875_);
v_r_4878_ = lean_box(v_res_4877_);
return v_r_4878_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4879_, lean_object* v_declName_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_){
_start:
{
lean_object* v_instanceNames_4887_; uint8_t v___x_4888_; 
v_instanceNames_4887_ = lean_ctor_get(v_d_4879_, 1);
v___x_4888_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4887_, v_declName_4880_);
if (v___x_4888_ == 0)
{
lean_object* v___x_4889_; lean_object* v___x_4890_; lean_object* v___x_4891_; lean_object* v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v_a_4895_; lean_object* v___x_4897_; uint8_t v_isShared_4898_; uint8_t v_isSharedCheck_4902_; 
lean_dec_ref(v_d_4879_);
v___x_4889_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4890_ = l_Lean_MessageData_ofConstName(v_declName_4880_, v___x_4888_);
v___x_4891_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4889_);
lean_ctor_set(v___x_4891_, 1, v___x_4890_);
v___x_4892_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4891_);
lean_ctor_set(v___x_4893_, 1, v___x_4892_);
v___x_4894_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4893_, v___y_4881_, v___y_4882_);
v_a_4895_ = lean_ctor_get(v___x_4894_, 0);
v_isSharedCheck_4902_ = !lean_is_exclusive(v___x_4894_);
if (v_isSharedCheck_4902_ == 0)
{
v___x_4897_ = v___x_4894_;
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
else
{
lean_inc(v_a_4895_);
lean_dec(v___x_4894_);
v___x_4897_ = lean_box(0);
v_isShared_4898_ = v_isSharedCheck_4902_;
goto v_resetjp_4896_;
}
v_resetjp_4896_:
{
lean_object* v___x_4900_; 
if (v_isShared_4898_ == 0)
{
v___x_4900_ = v___x_4897_;
goto v_reusejp_4899_;
}
else
{
lean_object* v_reuseFailAlloc_4901_; 
v_reuseFailAlloc_4901_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4901_, 0, v_a_4895_);
v___x_4900_ = v_reuseFailAlloc_4901_;
goto v_reusejp_4899_;
}
v_reusejp_4899_:
{
return v___x_4900_;
}
}
}
else
{
goto v___jp_4884_;
}
v___jp_4884_:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; 
v___x_4885_ = l_Lean_Meta_Instances_eraseCore(v_d_4879_, v_declName_4880_);
v___x_4886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4885_);
return v___x_4886_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4903_, lean_object* v_declName_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
lean_object* v_res_4908_; 
v_res_4908_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4903_, v_declName_4904_, v___y_4905_, v___y_4906_);
lean_dec(v___y_4906_);
lean_dec_ref(v___y_4905_);
return v_res_4908_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4909_, lean_object* v_declName_4910_, lean_object* v___y_4911_, lean_object* v___y_4912_){
_start:
{
lean_object* v___x_4914_; lean_object* v_env_4915_; lean_object* v___x_4916_; lean_object* v_ext_4917_; lean_object* v_toEnvExtension_4918_; lean_object* v_asyncMode_4919_; uint8_t v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; 
v___x_4914_ = lean_st_ref_get(v___y_4912_);
v_env_4915_ = lean_ctor_get(v___x_4914_, 0);
lean_inc_ref(v_env_4915_);
lean_dec(v___x_4914_);
v___x_4916_ = l_Lean_Meta_instanceExtension;
v_ext_4917_ = lean_ctor_get(v___x_4916_, 1);
v_toEnvExtension_4918_ = lean_ctor_get(v_ext_4917_, 0);
v_asyncMode_4919_ = lean_ctor_get(v_toEnvExtension_4918_, 2);
v___x_4920_ = 0;
v___x_4921_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4909_, v___x_4916_, v_env_4915_, v_asyncMode_4919_, v___x_4920_);
v___x_4922_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4921_, v_declName_4910_, v___y_4911_, v___y_4912_);
if (lean_obj_tag(v___x_4922_) == 0)
{
lean_object* v_a_4923_; lean_object* v___x_4925_; uint8_t v_isShared_4926_; uint8_t v_isSharedCheck_4953_; 
v_a_4923_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4925_ = v___x_4922_;
v_isShared_4926_ = v_isSharedCheck_4953_;
goto v_resetjp_4924_;
}
else
{
lean_inc(v_a_4923_);
lean_dec(v___x_4922_);
v___x_4925_ = lean_box(0);
v_isShared_4926_ = v_isSharedCheck_4953_;
goto v_resetjp_4924_;
}
v_resetjp_4924_:
{
lean_object* v___f_4927_; lean_object* v___x_4928_; lean_object* v_env_4929_; lean_object* v_nextMacroScope_4930_; lean_object* v_ngen_4931_; lean_object* v_auxDeclNGen_4932_; lean_object* v_traceState_4933_; lean_object* v_recordedDeps_4934_; lean_object* v_messages_4935_; lean_object* v_infoState_4936_; lean_object* v_snapshotTasks_4937_; lean_object* v___x_4939_; uint8_t v_isShared_4940_; uint8_t v_isSharedCheck_4951_; 
v___f_4927_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4927_, 0, v_a_4923_);
v___x_4928_ = lean_st_ref_take(v___y_4912_);
v_env_4929_ = lean_ctor_get(v___x_4928_, 0);
v_nextMacroScope_4930_ = lean_ctor_get(v___x_4928_, 1);
v_ngen_4931_ = lean_ctor_get(v___x_4928_, 2);
v_auxDeclNGen_4932_ = lean_ctor_get(v___x_4928_, 3);
v_traceState_4933_ = lean_ctor_get(v___x_4928_, 4);
v_recordedDeps_4934_ = lean_ctor_get(v___x_4928_, 6);
v_messages_4935_ = lean_ctor_get(v___x_4928_, 7);
v_infoState_4936_ = lean_ctor_get(v___x_4928_, 8);
v_snapshotTasks_4937_ = lean_ctor_get(v___x_4928_, 9);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4928_);
if (v_isSharedCheck_4951_ == 0)
{
lean_object* v_unused_4952_; 
v_unused_4952_ = lean_ctor_get(v___x_4928_, 5);
lean_dec(v_unused_4952_);
v___x_4939_ = v___x_4928_;
v_isShared_4940_ = v_isSharedCheck_4951_;
goto v_resetjp_4938_;
}
else
{
lean_inc(v_snapshotTasks_4937_);
lean_inc(v_infoState_4936_);
lean_inc(v_messages_4935_);
lean_inc(v_recordedDeps_4934_);
lean_inc(v_traceState_4933_);
lean_inc(v_auxDeclNGen_4932_);
lean_inc(v_ngen_4931_);
lean_inc(v_nextMacroScope_4930_);
lean_inc(v_env_4929_);
lean_dec(v___x_4928_);
v___x_4939_ = lean_box(0);
v_isShared_4940_ = v_isSharedCheck_4951_;
goto v_resetjp_4938_;
}
v_resetjp_4938_:
{
lean_object* v___x_4941_; lean_object* v___x_4942_; lean_object* v___x_4943_; lean_object* v___x_4945_; 
v___x_4941_ = lean_box(0);
v___x_4942_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4916_, v_env_4929_, v___f_4927_);
v___x_4943_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_4940_ == 0)
{
lean_ctor_set(v___x_4939_, 5, v___x_4943_);
lean_ctor_set(v___x_4939_, 0, v___x_4942_);
v___x_4945_ = v___x_4939_;
goto v_reusejp_4944_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v___x_4942_);
lean_ctor_set(v_reuseFailAlloc_4950_, 1, v_nextMacroScope_4930_);
lean_ctor_set(v_reuseFailAlloc_4950_, 2, v_ngen_4931_);
lean_ctor_set(v_reuseFailAlloc_4950_, 3, v_auxDeclNGen_4932_);
lean_ctor_set(v_reuseFailAlloc_4950_, 4, v_traceState_4933_);
lean_ctor_set(v_reuseFailAlloc_4950_, 5, v___x_4943_);
lean_ctor_set(v_reuseFailAlloc_4950_, 6, v_recordedDeps_4934_);
lean_ctor_set(v_reuseFailAlloc_4950_, 7, v_messages_4935_);
lean_ctor_set(v_reuseFailAlloc_4950_, 8, v_infoState_4936_);
lean_ctor_set(v_reuseFailAlloc_4950_, 9, v_snapshotTasks_4937_);
v___x_4945_ = v_reuseFailAlloc_4950_;
goto v_reusejp_4944_;
}
v_reusejp_4944_:
{
lean_object* v___x_4946_; lean_object* v___x_4948_; 
v___x_4946_ = lean_st_ref_put(v___y_4912_, v___x_4945_);
if (v_isShared_4926_ == 0)
{
lean_ctor_set(v___x_4925_, 0, v___x_4941_);
v___x_4948_ = v___x_4925_;
goto v_reusejp_4947_;
}
else
{
lean_object* v_reuseFailAlloc_4949_; 
v_reuseFailAlloc_4949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4949_, 0, v___x_4941_);
v___x_4948_ = v_reuseFailAlloc_4949_;
goto v_reusejp_4947_;
}
v_reusejp_4947_:
{
return v___x_4948_;
}
}
}
}
}
else
{
lean_object* v_a_4954_; lean_object* v___x_4956_; uint8_t v_isShared_4957_; uint8_t v_isSharedCheck_4961_; 
v_a_4954_ = lean_ctor_get(v___x_4922_, 0);
v_isSharedCheck_4961_ = !lean_is_exclusive(v___x_4922_);
if (v_isSharedCheck_4961_ == 0)
{
v___x_4956_ = v___x_4922_;
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
else
{
lean_inc(v_a_4954_);
lean_dec(v___x_4922_);
v___x_4956_ = lean_box(0);
v_isShared_4957_ = v_isSharedCheck_4961_;
goto v_resetjp_4955_;
}
v_resetjp_4955_:
{
lean_object* v___x_4959_; 
if (v_isShared_4957_ == 0)
{
v___x_4959_ = v___x_4956_;
goto v_reusejp_4958_;
}
else
{
lean_object* v_reuseFailAlloc_4960_; 
v_reuseFailAlloc_4960_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4960_, 0, v_a_4954_);
v___x_4959_ = v_reuseFailAlloc_4960_;
goto v_reusejp_4958_;
}
v_reusejp_4958_:
{
return v___x_4959_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4962_, lean_object* v_declName_4963_, lean_object* v___y_4964_, lean_object* v___y_4965_, lean_object* v___y_4966_){
_start:
{
lean_object* v_res_4967_; 
v_res_4967_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4962_, v_declName_4963_, v___y_4964_, v___y_4965_);
lean_dec(v___y_4965_);
lean_dec_ref(v___y_4964_);
lean_dec_ref(v___x_4962_);
return v_res_4967_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4974_; uint64_t v___x_4975_; 
v___x_4974_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4975_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4974_);
return v___x_4975_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4976_; lean_object* v___x_4977_; lean_object* v___x_4978_; 
v___x_4976_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4977_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4978_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4978_, 0, v___x_4977_);
lean_ctor_set_uint64(v___x_4978_, sizeof(void*)*1, v___x_4976_);
return v___x_4978_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___x_4979_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4980_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4979_);
return v___x_4980_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4981_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4982_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
v___x_4983_ = lean_alloc_ctor(0, 7, 0);
lean_ctor_set(v___x_4983_, 0, v___x_4982_);
lean_ctor_set(v___x_4983_, 1, v___x_4981_);
lean_ctor_set(v___x_4983_, 2, v___x_4981_);
lean_ctor_set(v___x_4983_, 3, v___x_4981_);
lean_ctor_set(v___x_4983_, 4, v___x_4981_);
lean_ctor_set(v___x_4983_, 5, v___x_4981_);
lean_ctor_set(v___x_4983_, 6, v___x_4981_);
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
v___x_5004_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__2);
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
size_t v_x_3114__boxed_5154_; uint8_t v_res_5155_; lean_object* v_r_5156_; 
v_x_3114__boxed_5154_ = lean_unbox_usize(v_x_5152_);
lean_dec(v_x_5152_);
v_res_5155_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_5150_, v_x_5151_, v_x_3114__boxed_5154_, v_x_5153_);
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
v___x_5490_ = lean_nat_add(v___y_5488_, v___y_5489_);
lean_dec(v___y_5489_);
lean_dec(v___y_5488_);
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
lean_ctor_set(v___x_5470_, 3, v___y_5487_);
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
lean_ctor_set(v_reuseFailAlloc_5495_, 3, v___y_5487_);
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
v___y_5487_ = v___x_5501_;
v___y_5488_ = v___x_5502_;
v___y_5489_ = v_size_5503_;
goto v___jp_5486_;
}
else
{
lean_object* v___x_5504_; 
v___x_5504_ = lean_unsigned_to_nat(0u);
v___y_5487_ = v___x_5501_;
v___y_5488_ = v___x_5502_;
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
size_t v___x_5827_; size_t v___x_5828_; lean_object* v___x_5829_; lean_object* v___x_5830_; 
v___x_5827_ = ((size_t)0ULL);
v___x_5828_ = lean_usize_of_nat(v___x_5823_);
v___x_5829_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5818_, v_all_5821_, v___x_5827_, v___x_5828_, v___x_5824_);
lean_inc_ref(v___x_5829_);
v___x_5830_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5830_, 0, v___x_5829_);
lean_ctor_set(v___x_5830_, 1, v___x_5829_);
lean_ctor_set(v___x_5830_, 2, v_all_5821_);
return v___x_5830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5831_, lean_object* v_x_5832_, lean_object* v_entries_5833_){
_start:
{
lean_object* v_res_5834_; 
v_res_5834_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5831_, v_x_5832_, v_entries_5833_);
lean_dec_ref(v_x_5832_);
return v_res_5834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5835_){
_start:
{
lean_object* v___x_5836_; 
v___x_5836_ = lean_array_mk(v_es_5835_);
return v___x_5836_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5837_, size_t v_i_5838_, size_t v_stop_5839_, lean_object* v_b_5840_){
_start:
{
uint8_t v___x_5841_; 
v___x_5841_ = lean_usize_dec_eq(v_i_5838_, v_stop_5839_);
if (v___x_5841_ == 0)
{
lean_object* v___x_5842_; lean_object* v___x_5843_; size_t v___x_5844_; size_t v___x_5845_; 
v___x_5842_ = lean_array_uget_borrowed(v_as_5837_, v_i_5838_);
lean_inc(v___x_5842_);
v___x_5843_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5840_, v___x_5842_);
v___x_5844_ = ((size_t)1ULL);
v___x_5845_ = lean_usize_add(v_i_5838_, v___x_5844_);
v_i_5838_ = v___x_5845_;
v_b_5840_ = v___x_5843_;
goto _start;
}
else
{
return v_b_5840_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5847_, lean_object* v_i_5848_, lean_object* v_stop_5849_, lean_object* v_b_5850_){
_start:
{
size_t v_i_boxed_5851_; size_t v_stop_boxed_5852_; lean_object* v_res_5853_; 
v_i_boxed_5851_ = lean_unbox_usize(v_i_5848_);
lean_dec(v_i_5848_);
v_stop_boxed_5852_ = lean_unbox_usize(v_stop_5849_);
lean_dec(v_stop_5849_);
v_res_5853_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5847_, v_i_boxed_5851_, v_stop_boxed_5852_, v_b_5850_);
lean_dec_ref(v_as_5847_);
return v_res_5853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5854_, size_t v_i_5855_, size_t v_stop_5856_, lean_object* v_b_5857_){
_start:
{
lean_object* v___y_5859_; uint8_t v___x_5863_; 
v___x_5863_ = lean_usize_dec_eq(v_i_5855_, v_stop_5856_);
if (v___x_5863_ == 0)
{
lean_object* v___x_5864_; lean_object* v___x_5865_; lean_object* v___x_5866_; uint8_t v___x_5867_; 
v___x_5864_ = lean_array_uget_borrowed(v_as_5854_, v_i_5855_);
v___x_5865_ = lean_unsigned_to_nat(0u);
v___x_5866_ = lean_array_get_size(v___x_5864_);
v___x_5867_ = lean_nat_dec_lt(v___x_5865_, v___x_5866_);
if (v___x_5867_ == 0)
{
v___y_5859_ = v_b_5857_;
goto v___jp_5858_;
}
else
{
size_t v___x_5868_; size_t v___x_5869_; lean_object* v___x_5870_; 
v___x_5868_ = ((size_t)0ULL);
v___x_5869_ = lean_usize_of_nat(v___x_5866_);
v___x_5870_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5864_, v___x_5868_, v___x_5869_, v_b_5857_);
v___y_5859_ = v___x_5870_;
goto v___jp_5858_;
}
}
else
{
return v_b_5857_;
}
v___jp_5858_:
{
size_t v___x_5860_; size_t v___x_5861_; 
v___x_5860_ = ((size_t)1ULL);
v___x_5861_ = lean_usize_add(v_i_5855_, v___x_5860_);
v_i_5855_ = v___x_5861_;
v_b_5857_ = v___y_5859_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5871_, lean_object* v_i_5872_, lean_object* v_stop_5873_, lean_object* v_b_5874_){
_start:
{
size_t v_i_boxed_5875_; size_t v_stop_boxed_5876_; lean_object* v_res_5877_; 
v_i_boxed_5875_ = lean_unbox_usize(v_i_5872_);
lean_dec(v_i_5872_);
v_stop_boxed_5876_ = lean_unbox_usize(v_stop_5873_);
lean_dec(v_stop_5873_);
v_res_5877_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5871_, v_i_boxed_5875_, v_stop_boxed_5876_, v_b_5874_);
lean_dec_ref(v_as_5871_);
return v_res_5877_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_5878_, lean_object* v_as_5879_){
_start:
{
lean_object* v___x_5880_; lean_object* v___x_5881_; uint8_t v___x_5882_; 
v___x_5880_ = lean_unsigned_to_nat(0u);
v___x_5881_ = lean_array_get_size(v_as_5879_);
v___x_5882_ = lean_nat_dec_lt(v___x_5880_, v___x_5881_);
if (v___x_5882_ == 0)
{
return v_initState_5878_;
}
else
{
size_t v___x_5883_; size_t v___x_5884_; lean_object* v___x_5885_; 
v___x_5883_ = ((size_t)0ULL);
v___x_5884_ = lean_usize_of_nat(v___x_5881_);
v___x_5885_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5879_, v___x_5883_, v___x_5884_, v_initState_5878_);
return v___x_5885_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_5886_, lean_object* v_as_5887_){
_start:
{
lean_object* v_res_5888_; 
v_res_5888_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_5886_, v_as_5887_);
lean_dec_ref(v_as_5887_);
return v_res_5888_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5889_){
_start:
{
lean_object* v___x_5890_; lean_object* v___x_5891_; 
v___x_5890_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5891_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_5890_, v_es_5889_);
return v___x_5891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_5892_){
_start:
{
lean_object* v_res_5893_; 
v_res_5893_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_5892_);
lean_dec_ref(v_es_5892_);
return v_res_5893_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5915_; lean_object* v___x_5916_; 
v___x_5915_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5916_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5915_);
return v___x_5916_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_5917_){
_start:
{
lean_object* v_res_5918_; 
v_res_5918_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_5918_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_addEntryFn_5919_, lean_object* v___x_5920_, lean_object* v_s_5921_){
_start:
{
lean_object* v_importedEntries_5922_; lean_object* v_state_5923_; lean_object* v___x_5925_; uint8_t v_isShared_5926_; uint8_t v_isSharedCheck_5931_; 
v_importedEntries_5922_ = lean_ctor_get(v_s_5921_, 0);
v_state_5923_ = lean_ctor_get(v_s_5921_, 1);
v_isSharedCheck_5931_ = !lean_is_exclusive(v_s_5921_);
if (v_isSharedCheck_5931_ == 0)
{
v___x_5925_ = v_s_5921_;
v_isShared_5926_ = v_isSharedCheck_5931_;
goto v_resetjp_5924_;
}
else
{
lean_inc(v_state_5923_);
lean_inc(v_importedEntries_5922_);
lean_dec(v_s_5921_);
v___x_5925_ = lean_box(0);
v_isShared_5926_ = v_isSharedCheck_5931_;
goto v_resetjp_5924_;
}
v_resetjp_5924_:
{
lean_object* v_state_5927_; lean_object* v___x_5929_; 
v_state_5927_ = lean_apply_2(v_addEntryFn_5919_, v_state_5923_, v___x_5920_);
if (v_isShared_5926_ == 0)
{
lean_ctor_set(v___x_5925_, 1, v_state_5927_);
v___x_5929_ = v___x_5925_;
goto v_reusejp_5928_;
}
else
{
lean_object* v_reuseFailAlloc_5930_; 
v_reuseFailAlloc_5930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5930_, 0, v_importedEntries_5922_);
lean_ctor_set(v_reuseFailAlloc_5930_, 1, v_state_5927_);
v___x_5929_ = v_reuseFailAlloc_5930_;
goto v_reusejp_5928_;
}
v_reusejp_5928_:
{
return v___x_5929_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5932_, lean_object* v___y_5933_, lean_object* v___y_5934_){
_start:
{
lean_object* v___x_5936_; lean_object* v_nextMacroScope_5937_; lean_object* v_ngen_5938_; lean_object* v_auxDeclNGen_5939_; lean_object* v_traceState_5940_; lean_object* v_recordedDeps_5941_; lean_object* v_messages_5942_; lean_object* v_infoState_5943_; lean_object* v_snapshotTasks_5944_; lean_object* v___x_5946_; uint8_t v_isShared_5947_; uint8_t v_isSharedCheck_5970_; 
v___x_5936_ = lean_st_ref_take(v___y_5934_);
v_nextMacroScope_5937_ = lean_ctor_get(v___x_5936_, 1);
v_ngen_5938_ = lean_ctor_get(v___x_5936_, 2);
v_auxDeclNGen_5939_ = lean_ctor_get(v___x_5936_, 3);
v_traceState_5940_ = lean_ctor_get(v___x_5936_, 4);
v_recordedDeps_5941_ = lean_ctor_get(v___x_5936_, 6);
v_messages_5942_ = lean_ctor_get(v___x_5936_, 7);
v_infoState_5943_ = lean_ctor_get(v___x_5936_, 8);
v_snapshotTasks_5944_ = lean_ctor_get(v___x_5936_, 9);
v_isSharedCheck_5970_ = !lean_is_exclusive(v___x_5936_);
if (v_isSharedCheck_5970_ == 0)
{
lean_object* v_unused_5971_; lean_object* v_unused_5972_; 
v_unused_5971_ = lean_ctor_get(v___x_5936_, 5);
lean_dec(v_unused_5971_);
v_unused_5972_ = lean_ctor_get(v___x_5936_, 0);
lean_dec(v_unused_5972_);
v___x_5946_ = v___x_5936_;
v_isShared_5947_ = v_isSharedCheck_5970_;
goto v_resetjp_5945_;
}
else
{
lean_inc(v_snapshotTasks_5944_);
lean_inc(v_infoState_5943_);
lean_inc(v_messages_5942_);
lean_inc(v_recordedDeps_5941_);
lean_inc(v_traceState_5940_);
lean_inc(v_auxDeclNGen_5939_);
lean_inc(v_ngen_5938_);
lean_inc(v_nextMacroScope_5937_);
lean_dec(v___x_5936_);
v___x_5946_ = lean_box(0);
v_isShared_5947_ = v_isSharedCheck_5970_;
goto v_resetjp_5945_;
}
v_resetjp_5945_:
{
lean_object* v___x_5948_; lean_object* v___x_5950_; 
v___x_5948_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_5947_ == 0)
{
lean_ctor_set(v___x_5946_, 5, v___x_5948_);
lean_ctor_set(v___x_5946_, 0, v_env_5932_);
v___x_5950_ = v___x_5946_;
goto v_reusejp_5949_;
}
else
{
lean_object* v_reuseFailAlloc_5969_; 
v_reuseFailAlloc_5969_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5969_, 0, v_env_5932_);
lean_ctor_set(v_reuseFailAlloc_5969_, 1, v_nextMacroScope_5937_);
lean_ctor_set(v_reuseFailAlloc_5969_, 2, v_ngen_5938_);
lean_ctor_set(v_reuseFailAlloc_5969_, 3, v_auxDeclNGen_5939_);
lean_ctor_set(v_reuseFailAlloc_5969_, 4, v_traceState_5940_);
lean_ctor_set(v_reuseFailAlloc_5969_, 5, v___x_5948_);
lean_ctor_set(v_reuseFailAlloc_5969_, 6, v_recordedDeps_5941_);
lean_ctor_set(v_reuseFailAlloc_5969_, 7, v_messages_5942_);
lean_ctor_set(v_reuseFailAlloc_5969_, 8, v_infoState_5943_);
lean_ctor_set(v_reuseFailAlloc_5969_, 9, v_snapshotTasks_5944_);
v___x_5950_ = v_reuseFailAlloc_5969_;
goto v_reusejp_5949_;
}
v_reusejp_5949_:
{
lean_object* v___x_5951_; lean_object* v___x_5952_; lean_object* v_mctx_5953_; lean_object* v_zetaDeltaFVarIds_5954_; lean_object* v_postponed_5955_; lean_object* v_diag_5956_; lean_object* v___x_5958_; uint8_t v_isShared_5959_; uint8_t v_isSharedCheck_5967_; 
v___x_5951_ = lean_st_ref_put(v___y_5934_, v___x_5950_);
v___x_5952_ = lean_st_ref_take(v___y_5933_);
v_mctx_5953_ = lean_ctor_get(v___x_5952_, 0);
v_zetaDeltaFVarIds_5954_ = lean_ctor_get(v___x_5952_, 2);
v_postponed_5955_ = lean_ctor_get(v___x_5952_, 3);
v_diag_5956_ = lean_ctor_get(v___x_5952_, 4);
v_isSharedCheck_5967_ = !lean_is_exclusive(v___x_5952_);
if (v_isSharedCheck_5967_ == 0)
{
lean_object* v_unused_5968_; 
v_unused_5968_ = lean_ctor_get(v___x_5952_, 1);
lean_dec(v_unused_5968_);
v___x_5958_ = v___x_5952_;
v_isShared_5959_ = v_isSharedCheck_5967_;
goto v_resetjp_5957_;
}
else
{
lean_inc(v_diag_5956_);
lean_inc(v_postponed_5955_);
lean_inc(v_zetaDeltaFVarIds_5954_);
lean_inc(v_mctx_5953_);
lean_dec(v___x_5952_);
v___x_5958_ = lean_box(0);
v_isShared_5959_ = v_isSharedCheck_5967_;
goto v_resetjp_5957_;
}
v_resetjp_5957_:
{
lean_object* v___x_5960_; lean_object* v___x_5961_; lean_object* v___x_5963_; 
v___x_5960_ = lean_box(0);
v___x_5961_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5959_ == 0)
{
lean_ctor_set(v___x_5958_, 1, v___x_5961_);
v___x_5963_ = v___x_5958_;
goto v_reusejp_5962_;
}
else
{
lean_object* v_reuseFailAlloc_5966_; 
v_reuseFailAlloc_5966_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5966_, 0, v_mctx_5953_);
lean_ctor_set(v_reuseFailAlloc_5966_, 1, v___x_5961_);
lean_ctor_set(v_reuseFailAlloc_5966_, 2, v_zetaDeltaFVarIds_5954_);
lean_ctor_set(v_reuseFailAlloc_5966_, 3, v_postponed_5955_);
lean_ctor_set(v_reuseFailAlloc_5966_, 4, v_diag_5956_);
v___x_5963_ = v_reuseFailAlloc_5966_;
goto v_reusejp_5962_;
}
v_reusejp_5962_:
{
lean_object* v___x_5964_; lean_object* v___x_5965_; 
v___x_5964_ = lean_st_ref_put(v___y_5933_, v___x_5963_);
v___x_5965_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5965_, 0, v___x_5960_);
return v___x_5965_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5973_, lean_object* v___y_5974_, lean_object* v___y_5975_, lean_object* v___y_5976_){
_start:
{
lean_object* v_res_5977_; 
v_res_5977_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5973_, v___y_5974_, v___y_5975_);
lean_dec(v___y_5975_);
lean_dec(v___y_5974_);
return v_res_5977_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5979_; lean_object* v___x_5980_; 
v___x_5979_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__0));
v___x_5980_ = l_Lean_stringToMessageData(v___x_5979_);
return v___x_5980_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; 
v___x_5982_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__2));
v___x_5983_ = l_Lean_stringToMessageData(v___x_5982_);
return v___x_5983_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__5(void){
_start:
{
lean_object* v___x_5985_; lean_object* v___x_5986_; 
v___x_5985_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__4));
v___x_5986_ = l_Lean_stringToMessageData(v___x_5985_);
return v___x_5986_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__7(void){
_start:
{
lean_object* v___x_5988_; lean_object* v___x_5989_; 
v___x_5988_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__6));
v___x_5989_ = l_Lean_stringToMessageData(v___x_5988_);
return v___x_5989_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__9(void){
_start:
{
lean_object* v___x_5991_; lean_object* v___x_5992_; 
v___x_5991_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__8));
v___x_5992_ = l_Lean_stringToMessageData(v___x_5991_);
return v___x_5992_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__1(lean_object* v_declName_5993_, lean_object* v_prio_5994_, lean_object* v_x_5995_, lean_object* v_type_5996_, lean_object* v___y_5997_, lean_object* v___y_5998_, lean_object* v___y_5999_, lean_object* v___y_6000_){
_start:
{
lean_object* v___x_6002_; 
v___x_6002_ = l_Lean_Expr_getAppFn(v_type_5996_);
if (lean_obj_tag(v___x_6002_) == 4)
{
lean_object* v_declName_6003_; lean_object* v___y_6005_; lean_object* v___y_6006_; lean_object* v___y_6007_; lean_object* v___y_6008_; lean_object* v___x_6025_; lean_object* v_env_6026_; uint8_t v___x_6027_; 
v_declName_6003_ = lean_ctor_get(v___x_6002_, 0);
lean_inc(v_declName_6003_);
lean_dec_ref_known(v___x_6002_, 2);
v___x_6025_ = lean_st_ref_get(v___y_6000_);
v_env_6026_ = lean_ctor_get(v___x_6025_, 0);
lean_inc_ref(v_env_6026_);
lean_dec(v___x_6025_);
v___x_6027_ = l_Lean_isClass(v_env_6026_, v_declName_6003_);
if (v___x_6027_ == 0)
{
lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; 
lean_dec(v_prio_5994_);
v___x_6028_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__1, &l_Lean_Meta_addDefaultInstance___lam__1___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__1);
v___x_6029_ = l_Lean_MessageData_ofConstName(v_declName_5993_, v___x_6027_);
v___x_6030_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6030_, 0, v___x_6028_);
lean_ctor_set(v___x_6030_, 1, v___x_6029_);
v___x_6031_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__3, &l_Lean_Meta_addDefaultInstance___lam__1___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__3);
v___x_6032_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6032_, 0, v___x_6030_);
lean_ctor_set(v___x_6032_, 1, v___x_6031_);
lean_inc(v_declName_6003_);
v___x_6033_ = l_Lean_MessageData_ofName(v_declName_6003_);
v___x_6034_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6034_, 0, v___x_6032_);
lean_ctor_set(v___x_6034_, 1, v___x_6033_);
v___x_6035_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__5, &l_Lean_Meta_addDefaultInstance___lam__1___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__5);
v___x_6036_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6034_);
lean_ctor_set(v___x_6036_, 1, v___x_6035_);
v___x_6037_ = l_Lean_MessageData_ofConstName(v_declName_6003_, v___x_6027_);
v___x_6038_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6038_, 0, v___x_6036_);
lean_ctor_set(v___x_6038_, 1, v___x_6037_);
v___x_6039_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__7, &l_Lean_Meta_addDefaultInstance___lam__1___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__7);
v___x_6040_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6038_);
lean_ctor_set(v___x_6040_, 1, v___x_6039_);
v___x_6041_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6040_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_);
return v___x_6041_;
}
else
{
v___y_6005_ = v___y_5997_;
v___y_6006_ = v___y_5998_;
v___y_6007_ = v___y_5999_;
v___y_6008_ = v___y_6000_;
goto v___jp_6004_;
}
v___jp_6004_:
{
lean_object* v___x_6009_; lean_object* v_env_6010_; lean_object* v___x_6011_; lean_object* v_toEnvExtension_6012_; lean_object* v_addEntryFn_6013_; lean_object* v_asyncMode_6014_; uint8_t v_logWrites_6015_; lean_object* v___x_6016_; lean_object* v___f_6017_; lean_object* v___x_6018_; uint8_t v___x_6019_; 
v___x_6009_ = lean_st_ref_get(v___y_6008_);
v_env_6010_ = lean_ctor_get(v___x_6009_, 0);
lean_inc_ref(v_env_6010_);
lean_dec(v___x_6009_);
v___x_6011_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6012_ = lean_ctor_get(v___x_6011_, 0);
v_addEntryFn_6013_ = lean_ctor_get(v___x_6011_, 3);
v_asyncMode_6014_ = lean_ctor_get(v_toEnvExtension_6012_, 2);
v_logWrites_6015_ = lean_ctor_get_uint8(v_toEnvExtension_6012_, sizeof(void*)*6);
v___x_6016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6016_, 0, v_declName_6003_);
lean_ctor_set(v___x_6016_, 1, v_declName_5993_);
lean_ctor_set(v___x_6016_, 2, v_prio_5994_);
lean_inc(v_addEntryFn_6013_);
v___f_6017_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0), 3, 2);
lean_closure_set(v___f_6017_, 0, v_addEntryFn_6013_);
lean_closure_set(v___f_6017_, 1, v___x_6016_);
v___x_6018_ = lean_box(0);
v___x_6019_ = 1;
if (v_logWrites_6015_ == 0)
{
lean_object* v___x_6020_; lean_object* v___x_6021_; 
lean_inc_ref(v_toEnvExtension_6012_);
v___x_6020_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_6012_, v_env_6010_, v___f_6017_, v_asyncMode_6014_, v___x_6018_, v___x_6019_);
v___x_6021_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_6020_, v___y_6006_, v___y_6008_);
return v___x_6021_;
}
else
{
lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; 
lean_inc_ref_n(v_toEnvExtension_6012_, 2);
v___x_6022_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_6012_, v_env_6010_);
lean_dec_ref(v_env_6010_);
v___x_6023_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_6012_, v___x_6022_, v___f_6017_, v_asyncMode_6014_, v___x_6018_, v___x_6019_);
v___x_6024_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_6023_, v___y_6006_, v___y_6008_);
return v___x_6024_;
}
}
}
else
{
lean_object* v___x_6042_; uint8_t v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; 
lean_dec_ref(v___x_6002_);
lean_dec(v_prio_5994_);
v___x_6042_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__1, &l_Lean_Meta_addDefaultInstance___lam__1___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__1);
v___x_6043_ = 0;
v___x_6044_ = l_Lean_MessageData_ofConstName(v_declName_5993_, v___x_6043_);
v___x_6045_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6045_, 0, v___x_6042_);
lean_ctor_set(v___x_6045_, 1, v___x_6044_);
v___x_6046_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__9, &l_Lean_Meta_addDefaultInstance___lam__1___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__9);
v___x_6047_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6047_, 0, v___x_6045_);
lean_ctor_set(v___x_6047_, 1, v___x_6046_);
v___x_6048_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6047_, v___y_5997_, v___y_5998_, v___y_5999_, v___y_6000_);
return v___x_6048_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__1___boxed(lean_object* v_declName_6049_, lean_object* v_prio_6050_, lean_object* v_x_6051_, lean_object* v_type_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_){
_start:
{
lean_object* v_res_6058_; 
v_res_6058_ = l_Lean_Meta_addDefaultInstance___lam__1(v_declName_6049_, v_prio_6050_, v_x_6051_, v_type_6052_, v___y_6053_, v___y_6054_, v___y_6055_, v___y_6056_);
lean_dec(v___y_6056_);
lean_dec_ref(v___y_6055_);
lean_dec(v___y_6054_);
lean_dec_ref(v___y_6053_);
lean_dec_ref(v_type_6052_);
lean_dec_ref(v_x_6051_);
return v_res_6058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_6059_, lean_object* v_prio_6060_, lean_object* v_a_6061_, lean_object* v_a_6062_, lean_object* v_a_6063_, lean_object* v_a_6064_){
_start:
{
lean_object* v___f_6066_; lean_object* v___x_6067_; lean_object* v_env_6068_; uint8_t v___x_6069_; lean_object* v___x_6070_; 
lean_inc_n(v_declName_6059_, 2);
v___f_6066_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__1___boxed), 9, 2);
lean_closure_set(v___f_6066_, 0, v_declName_6059_);
lean_closure_set(v___f_6066_, 1, v_prio_6060_);
v___x_6067_ = lean_st_ref_get(v_a_6064_);
v_env_6068_ = lean_ctor_get(v___x_6067_, 0);
lean_inc_ref(v_env_6068_);
lean_dec(v___x_6067_);
v___x_6069_ = 0;
v___x_6070_ = l_Lean_Environment_find_x3f(v_env_6068_, v_declName_6059_, v___x_6069_);
if (lean_obj_tag(v___x_6070_) == 0)
{
lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; 
lean_dec_ref(v___f_6066_);
v___x_6071_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9___redArg___closed__1);
v___x_6072_ = l_Lean_MessageData_ofConstName(v_declName_6059_, v___x_6069_);
v___x_6073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6071_);
lean_ctor_set(v___x_6073_, 1, v___x_6072_);
v___x_6074_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_6075_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6075_, 0, v___x_6073_);
lean_ctor_set(v___x_6075_, 1, v___x_6074_);
v___x_6076_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6075_, v_a_6061_, v_a_6062_, v_a_6063_, v_a_6064_);
return v___x_6076_;
}
else
{
lean_object* v_val_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; 
lean_dec(v_declName_6059_);
v_val_6077_ = lean_ctor_get(v___x_6070_, 0);
lean_inc(v_val_6077_);
lean_dec_ref_known(v___x_6070_, 1);
v___x_6078_ = l_Lean_ConstantInfo_type(v_val_6077_);
lean_dec(v_val_6077_);
v___x_6079_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_6078_, v___f_6066_, v___x_6069_, v___x_6069_, v_a_6061_, v_a_6062_, v_a_6063_, v_a_6064_);
return v___x_6079_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_6080_, lean_object* v_prio_6081_, lean_object* v_a_6082_, lean_object* v_a_6083_, lean_object* v_a_6084_, lean_object* v_a_6085_, lean_object* v_a_6086_){
_start:
{
lean_object* v_res_6087_; 
v_res_6087_ = l_Lean_Meta_addDefaultInstance(v_declName_6080_, v_prio_6081_, v_a_6082_, v_a_6083_, v_a_6084_, v_a_6085_);
lean_dec(v_a_6085_);
lean_dec_ref(v_a_6084_);
lean_dec(v_a_6083_);
lean_dec_ref(v_a_6082_);
return v_res_6087_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_6088_, lean_object* v___y_6089_, lean_object* v___y_6090_, lean_object* v___y_6091_, lean_object* v___y_6092_){
_start:
{
lean_object* v___x_6094_; 
v___x_6094_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_6088_, v___y_6090_, v___y_6092_);
return v___x_6094_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_6095_, lean_object* v___y_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_){
_start:
{
lean_object* v_res_6101_; 
v_res_6101_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_6095_, v___y_6096_, v___y_6097_, v___y_6098_, v___y_6099_);
lean_dec(v___y_6099_);
lean_dec_ref(v___y_6098_);
lean_dec(v___y_6097_);
lean_dec_ref(v___y_6096_);
return v_res_6101_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6103_; lean_object* v___x_6104_; 
v___x_6103_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_6104_ = l_Lean_stringToMessageData(v___x_6103_);
return v___x_6104_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_6106_; lean_object* v___x_6107_; 
v___x_6106_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_6107_ = l_Lean_stringToMessageData(v___x_6106_);
return v___x_6107_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_6111_, uint8_t v_kind_6112_, lean_object* v___y_6113_, lean_object* v___y_6114_){
_start:
{
lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; lean_object* v___y_6122_; 
v___x_6116_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_6117_ = l_Lean_MessageData_ofName(v_name_6111_);
v___x_6118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6116_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
v___x_6119_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_6120_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6120_, 0, v___x_6118_);
lean_ctor_set(v___x_6120_, 1, v___x_6119_);
switch(v_kind_6112_)
{
case 0:
{
lean_object* v___x_6129_; 
v___x_6129_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_6122_ = v___x_6129_;
goto v___jp_6121_;
}
case 1:
{
lean_object* v___x_6130_; 
v___x_6130_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_6122_ = v___x_6130_;
goto v___jp_6121_;
}
default: 
{
lean_object* v___x_6131_; 
v___x_6131_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_6122_ = v___x_6131_;
goto v___jp_6121_;
}
}
v___jp_6121_:
{
lean_object* v___x_6123_; lean_object* v___x_6124_; lean_object* v___x_6125_; lean_object* v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; 
lean_inc_ref(v___y_6122_);
v___x_6123_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6123_, 0, v___y_6122_);
v___x_6124_ = l_Lean_MessageData_ofFormat(v___x_6123_);
v___x_6125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6125_, 0, v___x_6120_);
lean_ctor_set(v___x_6125_, 1, v___x_6124_);
v___x_6126_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_6127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6127_, 0, v___x_6125_);
lean_ctor_set(v___x_6127_, 1, v___x_6126_);
v___x_6128_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6127_, v___y_6113_, v___y_6114_);
return v___x_6128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_6132_, lean_object* v_kind_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_, lean_object* v___y_6136_){
_start:
{
uint8_t v_kind_boxed_6137_; lean_object* v_res_6138_; 
v_kind_boxed_6137_ = lean_unbox(v_kind_6133_);
v_res_6138_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6132_, v_kind_boxed_6137_, v___y_6134_, v___y_6135_);
lean_dec(v___y_6135_);
lean_dec_ref(v___y_6134_);
return v_res_6138_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6139_, lean_object* v___x_6140_, lean_object* v___x_6141_, lean_object* v_declName_6142_, lean_object* v_stx_6143_, uint8_t v_kind_6144_, lean_object* v___y_6145_, lean_object* v___y_6146_){
_start:
{
lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; 
v___x_6148_ = lean_unsigned_to_nat(1u);
v___x_6149_ = l_Lean_Syntax_getArg(v_stx_6143_, v___x_6148_);
v___x_6150_ = l_Lean_getAttrParamOptPrio(v___x_6149_, v___y_6145_, v___y_6146_);
if (lean_obj_tag(v___x_6150_) == 0)
{
lean_object* v_a_6151_; lean_object* v___y_6153_; lean_object* v___y_6154_; uint8_t v___x_6186_; uint8_t v___x_6187_; 
v_a_6151_ = lean_ctor_get(v___x_6150_, 0);
lean_inc(v_a_6151_);
lean_dec_ref_known(v___x_6150_, 1);
v___x_6186_ = 0;
v___x_6187_ = l_Lean_instBEqAttributeKind_beq(v_kind_6144_, v___x_6186_);
if (v___x_6187_ == 0)
{
lean_object* v___x_6188_; 
lean_dec(v_a_6151_);
lean_dec(v_declName_6142_);
lean_dec(v___x_6140_);
lean_dec(v___x_6139_);
v___x_6188_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_6141_, v_kind_6144_, v___y_6145_, v___y_6146_);
return v___x_6188_;
}
else
{
lean_dec(v___x_6141_);
v___y_6153_ = v___y_6145_;
v___y_6154_ = v___y_6146_;
goto v___jp_6152_;
}
v___jp_6152_:
{
uint8_t v___x_6155_; uint8_t v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; size_t v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; lean_object* v___x_6170_; lean_object* v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; 
v___x_6155_ = 0;
v___x_6156_ = 1;
v___x_6157_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6158_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6159_ = lean_unsigned_to_nat(32u);
v___x_6160_ = lean_mk_empty_array_with_capacity(v___x_6159_);
v___x_6161_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__7_spec__9_spec__10_spec__11_spec__12___redArg___closed__2);
v___x_6162_ = ((size_t)5ULL);
lean_inc_n(v___x_6139_, 6);
v___x_6163_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6163_, 0, v___x_6161_);
lean_ctor_set(v___x_6163_, 1, v___x_6160_);
lean_ctor_set(v___x_6163_, 2, v___x_6139_);
lean_ctor_set(v___x_6163_, 3, v___x_6139_);
lean_ctor_set_usize(v___x_6163_, 4, v___x_6162_);
v___x_6164_ = lean_box(1);
lean_inc_ref(v___x_6163_);
v___x_6165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6165_, 0, v___x_6158_);
lean_ctor_set(v___x_6165_, 1, v___x_6163_);
lean_ctor_set(v___x_6165_, 2, v___x_6164_);
v___x_6166_ = lean_mk_empty_array_with_capacity(v___x_6139_);
v___x_6167_ = lean_box(0);
lean_inc(v___x_6140_);
v___x_6168_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6168_, 0, v___x_6157_);
lean_ctor_set(v___x_6168_, 1, v___x_6140_);
lean_ctor_set(v___x_6168_, 2, v___x_6165_);
lean_ctor_set(v___x_6168_, 3, v___x_6166_);
lean_ctor_set(v___x_6168_, 4, v___x_6167_);
lean_ctor_set(v___x_6168_, 5, v___x_6139_);
lean_ctor_set(v___x_6168_, 6, v___x_6167_);
lean_ctor_set_uint8(v___x_6168_, sizeof(void*)*7, v___x_6155_);
lean_ctor_set_uint8(v___x_6168_, sizeof(void*)*7 + 1, v___x_6155_);
lean_ctor_set_uint8(v___x_6168_, sizeof(void*)*7 + 2, v___x_6155_);
lean_ctor_set_uint8(v___x_6168_, sizeof(void*)*7 + 3, v___x_6156_);
v___x_6169_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_6170_ = lean_alloc_ctor(0, 12, 0);
lean_ctor_set(v___x_6170_, 0, v___x_6139_);
lean_ctor_set(v___x_6170_, 1, v___x_6139_);
lean_ctor_set(v___x_6170_, 2, v___x_6139_);
lean_ctor_set(v___x_6170_, 3, v___x_6139_);
lean_ctor_set(v___x_6170_, 4, v___x_6158_);
lean_ctor_set(v___x_6170_, 5, v___x_6158_);
lean_ctor_set(v___x_6170_, 6, v___x_6158_);
lean_ctor_set(v___x_6170_, 7, v___x_6158_);
lean_ctor_set(v___x_6170_, 8, v___x_6158_);
lean_ctor_set(v___x_6170_, 9, v___x_6158_);
lean_ctor_set(v___x_6170_, 10, v___x_6158_);
lean_ctor_set(v___x_6170_, 11, v___x_6169_);
v___x_6171_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6172_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6173_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6173_, 0, v___x_6170_);
lean_ctor_set(v___x_6173_, 1, v___x_6171_);
lean_ctor_set(v___x_6173_, 2, v___x_6140_);
lean_ctor_set(v___x_6173_, 3, v___x_6163_);
lean_ctor_set(v___x_6173_, 4, v___x_6172_);
v___x_6174_ = lean_box(0);
v___x_6175_ = lean_st_mk_ref(v___x_6173_);
v___x_6176_ = l_Lean_Meta_addDefaultInstance(v_declName_6142_, v_a_6151_, v___x_6168_, v___x_6175_, v___y_6153_, v___y_6154_);
lean_dec_ref_known(v___x_6168_, 7);
if (lean_obj_tag(v___x_6176_) == 0)
{
lean_object* v___x_6178_; uint8_t v_isShared_6179_; uint8_t v_isSharedCheck_6184_; 
v_isSharedCheck_6184_ = !lean_is_exclusive(v___x_6176_);
if (v_isSharedCheck_6184_ == 0)
{
lean_object* v_unused_6185_; 
v_unused_6185_ = lean_ctor_get(v___x_6176_, 0);
lean_dec(v_unused_6185_);
v___x_6178_ = v___x_6176_;
v_isShared_6179_ = v_isSharedCheck_6184_;
goto v_resetjp_6177_;
}
else
{
lean_dec(v___x_6176_);
v___x_6178_ = lean_box(0);
v_isShared_6179_ = v_isSharedCheck_6184_;
goto v_resetjp_6177_;
}
v_resetjp_6177_:
{
lean_object* v___x_6180_; lean_object* v___x_6182_; 
v___x_6180_ = lean_st_ref_get(v___x_6175_);
lean_dec(v___x_6175_);
lean_dec(v___x_6180_);
if (v_isShared_6179_ == 0)
{
lean_ctor_set(v___x_6178_, 0, v___x_6174_);
v___x_6182_ = v___x_6178_;
goto v_reusejp_6181_;
}
else
{
lean_object* v_reuseFailAlloc_6183_; 
v_reuseFailAlloc_6183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6183_, 0, v___x_6174_);
v___x_6182_ = v_reuseFailAlloc_6183_;
goto v_reusejp_6181_;
}
v_reusejp_6181_:
{
return v___x_6182_;
}
}
}
else
{
lean_dec(v___x_6175_);
return v___x_6176_;
}
}
}
else
{
lean_object* v_a_6189_; lean_object* v___x_6191_; uint8_t v_isShared_6192_; uint8_t v_isSharedCheck_6196_; 
lean_dec(v_declName_6142_);
lean_dec(v___x_6141_);
lean_dec(v___x_6140_);
lean_dec(v___x_6139_);
v_a_6189_ = lean_ctor_get(v___x_6150_, 0);
v_isSharedCheck_6196_ = !lean_is_exclusive(v___x_6150_);
if (v_isSharedCheck_6196_ == 0)
{
v___x_6191_ = v___x_6150_;
v_isShared_6192_ = v_isSharedCheck_6196_;
goto v_resetjp_6190_;
}
else
{
lean_inc(v_a_6189_);
lean_dec(v___x_6150_);
v___x_6191_ = lean_box(0);
v_isShared_6192_ = v_isSharedCheck_6196_;
goto v_resetjp_6190_;
}
v_resetjp_6190_:
{
lean_object* v___x_6194_; 
if (v_isShared_6192_ == 0)
{
v___x_6194_ = v___x_6191_;
goto v_reusejp_6193_;
}
else
{
lean_object* v_reuseFailAlloc_6195_; 
v_reuseFailAlloc_6195_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6195_, 0, v_a_6189_);
v___x_6194_ = v_reuseFailAlloc_6195_;
goto v_reusejp_6193_;
}
v_reusejp_6193_:
{
return v___x_6194_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6197_, lean_object* v___x_6198_, lean_object* v___x_6199_, lean_object* v_declName_6200_, lean_object* v_stx_6201_, lean_object* v_kind_6202_, lean_object* v___y_6203_, lean_object* v___y_6204_, lean_object* v___y_6205_){
_start:
{
uint8_t v_kind_boxed_6206_; lean_object* v_res_6207_; 
v_kind_boxed_6206_ = lean_unbox(v_kind_6202_);
v_res_6207_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6197_, v___x_6198_, v___x_6199_, v_declName_6200_, v_stx_6201_, v_kind_boxed_6206_, v___y_6203_, v___y_6204_);
lean_dec(v___y_6204_);
lean_dec_ref(v___y_6203_);
lean_dec(v_stx_6201_);
return v_res_6207_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6209_; lean_object* v___x_6210_; 
v___x_6209_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6210_ = l_Lean_stringToMessageData(v___x_6209_);
return v___x_6210_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6212_; lean_object* v___x_6213_; 
v___x_6212_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6213_ = l_Lean_stringToMessageData(v___x_6212_);
return v___x_6213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6214_, lean_object* v_decl_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_){
_start:
{
lean_object* v___x_6219_; lean_object* v___x_6220_; lean_object* v___x_6221_; lean_object* v___x_6222_; lean_object* v___x_6223_; lean_object* v___x_6224_; 
v___x_6219_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6220_ = l_Lean_MessageData_ofName(v___x_6214_);
v___x_6221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6221_, 0, v___x_6219_);
lean_ctor_set(v___x_6221_, 1, v___x_6220_);
v___x_6222_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6223_, 0, v___x_6221_);
lean_ctor_set(v___x_6223_, 1, v___x_6222_);
v___x_6224_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6223_, v___y_6216_, v___y_6217_);
return v___x_6224_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6225_, lean_object* v_decl_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_, lean_object* v___y_6229_){
_start:
{
lean_object* v_res_6230_; 
v_res_6230_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6225_, v_decl_6226_, v___y_6227_, v___y_6228_);
lean_dec(v___y_6228_);
lean_dec_ref(v___y_6227_);
lean_dec(v_decl_6226_);
return v_res_6230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6263_; lean_object* v___x_6264_; lean_object* v___x_6265_; 
v___x_6263_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6264_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6265_ = l_Lean_registerBuiltinAttribute(v___x_6264_);
if (lean_obj_tag(v___x_6265_) == 0)
{
lean_object* v___x_6266_; uint8_t v___x_6267_; lean_object* v___x_6268_; 
lean_dec_ref_known(v___x_6265_, 1);
v___x_6266_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_6267_ = 0;
v___x_6268_ = l_Lean_registerTraceClass(v___x_6266_, v___x_6267_, v___x_6263_);
return v___x_6268_;
}
else
{
return v___x_6265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_6269_){
_start:
{
lean_object* v_res_6270_; 
v_res_6270_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_6270_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_6271_, lean_object* v_name_6272_, uint8_t v_kind_6273_, lean_object* v___y_6274_, lean_object* v___y_6275_){
_start:
{
lean_object* v___x_6277_; 
v___x_6277_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6272_, v_kind_6273_, v___y_6274_, v___y_6275_);
return v___x_6277_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_6278_, lean_object* v_name_6279_, lean_object* v_kind_6280_, lean_object* v___y_6281_, lean_object* v___y_6282_, lean_object* v___y_6283_){
_start:
{
uint8_t v_kind_boxed_6284_; lean_object* v_res_6285_; 
v_kind_boxed_6284_ = lean_unbox(v_kind_6280_);
v_res_6285_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_6278_, v_name_6279_, v_kind_boxed_6284_, v___y_6281_, v___y_6282_);
lean_dec(v___y_6282_);
lean_dec_ref(v___y_6281_);
return v_res_6285_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_6286_, lean_object* v_toPure_6287_, lean_object* v_____do__lift_6288_){
_start:
{
lean_object* v___x_6289_; lean_object* v_toEnvExtension_6290_; lean_object* v_asyncMode_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v_priorities_6294_; lean_object* v___x_6295_; 
v___x_6289_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6290_ = lean_ctor_get(v___x_6289_, 0);
v_asyncMode_6291_ = lean_ctor_get(v_toEnvExtension_6290_, 2);
v___x_6292_ = lean_box(0);
v___x_6293_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6286_, v___x_6289_, v_____do__lift_6288_, v_asyncMode_6291_, v___x_6292_);
v_priorities_6294_ = lean_ctor_get(v___x_6293_, 1);
lean_inc(v_priorities_6294_);
lean_dec(v___x_6293_);
v___x_6295_ = lean_apply_2(v_toPure_6287_, lean_box(0), v_priorities_6294_);
return v___x_6295_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_6296_, lean_object* v_inst_6297_){
_start:
{
lean_object* v_toApplicative_6298_; lean_object* v_toBind_6299_; lean_object* v_getEnv_6300_; lean_object* v_toPure_6301_; lean_object* v___x_6302_; lean_object* v___f_6303_; lean_object* v___x_6304_; 
v_toApplicative_6298_ = lean_ctor_get(v_inst_6296_, 0);
lean_inc_ref(v_toApplicative_6298_);
v_toBind_6299_ = lean_ctor_get(v_inst_6296_, 1);
lean_inc(v_toBind_6299_);
lean_dec_ref(v_inst_6296_);
v_getEnv_6300_ = lean_ctor_get(v_inst_6297_, 0);
lean_inc(v_getEnv_6300_);
lean_dec_ref(v_inst_6297_);
v_toPure_6301_ = lean_ctor_get(v_toApplicative_6298_, 1);
lean_inc(v_toPure_6301_);
lean_dec_ref(v_toApplicative_6298_);
v___x_6302_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6303_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6303_, 0, v___x_6302_);
lean_closure_set(v___f_6303_, 1, v_toPure_6301_);
v___x_6304_ = lean_apply_4(v_toBind_6299_, lean_box(0), lean_box(0), v_getEnv_6300_, v___f_6303_);
return v___x_6304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_6305_, lean_object* v_inst_6306_, lean_object* v_inst_6307_){
_start:
{
lean_object* v___x_6308_; 
v___x_6308_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_6306_, v_inst_6307_);
return v___x_6308_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_6309_, uint8_t v_isExporting_6310_, lean_object* v_x_6311_){
_start:
{
lean_object* v_fst_6312_; uint8_t v___x_6313_; 
v_fst_6312_ = lean_ctor_get(v_x_6311_, 0);
lean_inc(v_fst_6312_);
lean_dec_ref(v_x_6311_);
v___x_6313_ = l_Lean_Environment_contains(v_env_6309_, v_fst_6312_, v_isExporting_6310_);
return v___x_6313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_6314_, lean_object* v_isExporting_6315_, lean_object* v_x_6316_){
_start:
{
uint8_t v_isExporting_boxed_6317_; uint8_t v_res_6318_; lean_object* v_r_6319_; 
v_isExporting_boxed_6317_ = lean_unbox(v_isExporting_6315_);
v_res_6318_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_6314_, v_isExporting_boxed_6317_, v_x_6316_);
v_r_6319_ = lean_box(v_res_6318_);
return v_r_6319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_6320_, lean_object* v_toPure_6321_, lean_object* v_className_6322_, lean_object* v_env_6323_){
_start:
{
lean_object* v___y_6325_; lean_object* v___x_6333_; lean_object* v_toEnvExtension_6334_; lean_object* v_asyncMode_6335_; lean_object* v___x_6336_; lean_object* v___x_6337_; lean_object* v_defaultInstances_6338_; lean_object* v___x_6339_; 
v___x_6333_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6334_ = lean_ctor_get(v___x_6333_, 0);
v_asyncMode_6335_ = lean_ctor_get(v_toEnvExtension_6334_, 2);
v___x_6336_ = lean_box(0);
lean_inc_ref(v_env_6323_);
v___x_6337_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6320_, v___x_6333_, v_env_6323_, v_asyncMode_6335_, v___x_6336_);
v_defaultInstances_6338_ = lean_ctor_get(v___x_6337_, 0);
lean_inc(v_defaultInstances_6338_);
lean_dec(v___x_6337_);
v___x_6339_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_6338_, v_className_6322_);
lean_dec(v_defaultInstances_6338_);
if (lean_obj_tag(v___x_6339_) == 0)
{
lean_object* v___x_6340_; 
v___x_6340_ = lean_box(0);
v___y_6325_ = v___x_6340_;
goto v___jp_6324_;
}
else
{
lean_object* v_val_6341_; 
v_val_6341_ = lean_ctor_get(v___x_6339_, 0);
lean_inc(v_val_6341_);
lean_dec_ref_known(v___x_6339_, 1);
v___y_6325_ = v_val_6341_;
goto v___jp_6324_;
}
v___jp_6324_:
{
uint8_t v_isExporting_6326_; 
v_isExporting_6326_ = lean_ctor_get_uint8(v_env_6323_, sizeof(void*)*13);
if (v_isExporting_6326_ == 0)
{
lean_object* v___x_6327_; 
lean_dec_ref(v_env_6323_);
v___x_6327_ = lean_apply_2(v_toPure_6321_, lean_box(0), v___y_6325_);
return v___x_6327_;
}
else
{
lean_object* v___x_6328_; lean_object* v___f_6329_; lean_object* v___x_6330_; lean_object* v___x_6331_; lean_object* v___x_6332_; 
v___x_6328_ = lean_box(v_isExporting_6326_);
v___f_6329_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6329_, 0, v_env_6323_);
lean_closure_set(v___f_6329_, 1, v___x_6328_);
v___x_6330_ = lean_box(0);
v___x_6331_ = l_List_filterTR_loop___redArg(v___f_6329_, v___y_6325_, v___x_6330_);
v___x_6332_ = lean_apply_2(v_toPure_6321_, lean_box(0), v___x_6331_);
return v___x_6332_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_6342_, lean_object* v_toPure_6343_, lean_object* v_className_6344_, lean_object* v_env_6345_){
_start:
{
lean_object* v_res_6346_; 
v_res_6346_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_6342_, v_toPure_6343_, v_className_6344_, v_env_6345_);
lean_dec(v_className_6344_);
return v_res_6346_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_6347_, lean_object* v_inst_6348_, lean_object* v_className_6349_){
_start:
{
lean_object* v_toApplicative_6350_; lean_object* v_toBind_6351_; lean_object* v_getEnv_6352_; lean_object* v_toPure_6353_; lean_object* v___x_6354_; lean_object* v___f_6355_; lean_object* v___x_6356_; 
v_toApplicative_6350_ = lean_ctor_get(v_inst_6347_, 0);
lean_inc_ref(v_toApplicative_6350_);
v_toBind_6351_ = lean_ctor_get(v_inst_6347_, 1);
lean_inc(v_toBind_6351_);
lean_dec_ref(v_inst_6347_);
v_getEnv_6352_ = lean_ctor_get(v_inst_6348_, 0);
lean_inc(v_getEnv_6352_);
lean_dec_ref(v_inst_6348_);
v_toPure_6353_ = lean_ctor_get(v_toApplicative_6350_, 1);
lean_inc(v_toPure_6353_);
lean_dec_ref(v_toApplicative_6350_);
v___x_6354_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6355_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_6355_, 0, v___x_6354_);
lean_closure_set(v___f_6355_, 1, v_toPure_6353_);
lean_closure_set(v___f_6355_, 2, v_className_6349_);
v___x_6356_ = lean_apply_4(v_toBind_6351_, lean_box(0), lean_box(0), v_getEnv_6352_, v___f_6355_);
return v___x_6356_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6357_, lean_object* v_inst_6358_, lean_object* v_inst_6359_, lean_object* v_className_6360_){
_start:
{
lean_object* v___x_6361_; 
v___x_6361_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6358_, v_inst_6359_, v_className_6360_);
return v___x_6361_;
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
