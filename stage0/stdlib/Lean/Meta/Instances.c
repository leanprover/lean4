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
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1;
static const lean_array_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2_value;
static const lean_ctor_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_value;
static const lean_ctor_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2_value),((lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_value)}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_value;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "This instance has "};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " argument"};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 66, .m_capacity = 66, .m_length = 65, .m_data = " that cannot be inferred using typeclass synthesis. Specifically\n"};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 176, .m_capacity = 176, .m_length = 175, .m_data = "\n\nThese arguments are not instance-implicit and appear neither in another instance-implicit argument nor the return type, so they cannot be inferred using typeclass synthesis."};
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
size_t v_x_1607__boxed_1812_; size_t v_x_1608__boxed_1813_; lean_object* v_res_1814_; 
v_x_1607__boxed_1812_ = lean_unbox_usize(v_x_1808_);
lean_dec(v_x_1808_);
v_x_1608__boxed_1813_ = lean_unbox_usize(v_x_1809_);
lean_dec(v_x_1809_);
v_res_1814_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1807_, v_x_1607__boxed_1812_, v_x_1608__boxed_1813_, v_x_1810_, v_x_1811_);
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
lean_object* v___x_1826_; lean_object* v_mctx_1827_; lean_object* v_cache_1828_; lean_object* v_zetaDeltaFVarIds_1829_; lean_object* v_postponed_1830_; lean_object* v_diag_1831_; lean_object* v___x_1833_; uint8_t v_isShared_1834_; uint8_t v_isSharedCheck_1860_; 
v___x_1826_ = lean_st_ref_take(v___y_1824_);
v_mctx_1827_ = lean_ctor_get(v___x_1826_, 0);
v_cache_1828_ = lean_ctor_get(v___x_1826_, 1);
v_zetaDeltaFVarIds_1829_ = lean_ctor_get(v___x_1826_, 2);
v_postponed_1830_ = lean_ctor_get(v___x_1826_, 3);
v_diag_1831_ = lean_ctor_get(v___x_1826_, 4);
v_isSharedCheck_1860_ = !lean_is_exclusive(v___x_1826_);
if (v_isSharedCheck_1860_ == 0)
{
v___x_1833_ = v___x_1826_;
v_isShared_1834_ = v_isSharedCheck_1860_;
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
v_isShared_1834_ = v_isSharedCheck_1860_;
goto v_resetjp_1832_;
}
v_resetjp_1832_:
{
lean_object* v_depth_1835_; lean_object* v_levelAssignDepth_1836_; lean_object* v_lmvarCounter_1837_; lean_object* v_mvarCounter_1838_; lean_object* v_lDecls_1839_; lean_object* v_decls_1840_; lean_object* v_userNames_1841_; lean_object* v_lAssignment_1842_; lean_object* v_eAssignment_1843_; lean_object* v_dAssignment_1844_; lean_object* v_synthNormMemo_1845_; lean_object* v___x_1847_; uint8_t v_isShared_1848_; uint8_t v_isSharedCheck_1859_; 
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
v_synthNormMemo_1845_ = lean_ctor_get(v_mctx_1827_, 10);
v_isSharedCheck_1859_ = !lean_is_exclusive(v_mctx_1827_);
if (v_isSharedCheck_1859_ == 0)
{
v___x_1847_ = v_mctx_1827_;
v_isShared_1848_ = v_isSharedCheck_1859_;
goto v_resetjp_1846_;
}
else
{
lean_inc(v_synthNormMemo_1845_);
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
v___x_1847_ = lean_box(0);
v_isShared_1848_ = v_isSharedCheck_1859_;
goto v_resetjp_1846_;
}
v_resetjp_1846_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1852_; 
v___x_1849_ = lean_box(0);
v___x_1850_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_eAssignment_1843_, v_mvarId_1822_, v_val_1823_);
if (v_isShared_1848_ == 0)
{
lean_ctor_set(v___x_1847_, 8, v___x_1850_);
v___x_1852_ = v___x_1847_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1858_; 
v_reuseFailAlloc_1858_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1858_, 0, v_depth_1835_);
lean_ctor_set(v_reuseFailAlloc_1858_, 1, v_levelAssignDepth_1836_);
lean_ctor_set(v_reuseFailAlloc_1858_, 2, v_lmvarCounter_1837_);
lean_ctor_set(v_reuseFailAlloc_1858_, 3, v_mvarCounter_1838_);
lean_ctor_set(v_reuseFailAlloc_1858_, 4, v_lDecls_1839_);
lean_ctor_set(v_reuseFailAlloc_1858_, 5, v_decls_1840_);
lean_ctor_set(v_reuseFailAlloc_1858_, 6, v_userNames_1841_);
lean_ctor_set(v_reuseFailAlloc_1858_, 7, v_lAssignment_1842_);
lean_ctor_set(v_reuseFailAlloc_1858_, 8, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1858_, 9, v_dAssignment_1844_);
lean_ctor_set(v_reuseFailAlloc_1858_, 10, v_synthNormMemo_1845_);
v___x_1852_ = v_reuseFailAlloc_1858_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1854_; 
if (v_isShared_1834_ == 0)
{
lean_ctor_set(v___x_1833_, 0, v___x_1852_);
v___x_1854_ = v___x_1833_;
goto v_reusejp_1853_;
}
else
{
lean_object* v_reuseFailAlloc_1857_; 
v_reuseFailAlloc_1857_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1857_, 0, v___x_1852_);
lean_ctor_set(v_reuseFailAlloc_1857_, 1, v_cache_1828_);
lean_ctor_set(v_reuseFailAlloc_1857_, 2, v_zetaDeltaFVarIds_1829_);
lean_ctor_set(v_reuseFailAlloc_1857_, 3, v_postponed_1830_);
lean_ctor_set(v_reuseFailAlloc_1857_, 4, v_diag_1831_);
v___x_1854_ = v_reuseFailAlloc_1857_;
goto v_reusejp_1853_;
}
v_reusejp_1853_:
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
v___x_1855_ = lean_st_ref_put(v___y_1824_, v___x_1854_);
v___x_1856_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1856_, 0, v___x_1849_);
return v___x_1856_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg___boxed(lean_object* v_mvarId_1861_, lean_object* v_val_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1861_, v_val_1862_, v___y_1863_);
lean_dec(v___y_1863_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(lean_object* v_argMVars_1866_, lean_object* v_argVars_1867_, lean_object* v_as_1868_, size_t v_sz_1869_, size_t v_i_1870_, lean_object* v_b_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_, lean_object* v___y_1874_, lean_object* v___y_1875_){
_start:
{
uint8_t v___x_1877_; 
v___x_1877_ = lean_usize_dec_lt(v_i_1870_, v_sz_1869_);
if (v___x_1877_ == 0)
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1878_, 0, v_b_1871_);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; lean_object* v_a_1880_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___y_1884_; lean_object* v___y_1885_; lean_object* v___x_1901_; lean_object* v___x_1902_; 
v___x_1879_ = lean_box(0);
v_a_1880_ = lean_array_uget_borrowed(v_as_1868_, v_i_1870_);
v___x_1901_ = lean_unsigned_to_nat(0u);
v___x_1902_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1880_, v_argMVars_1866_, v___x_1901_);
if (lean_obj_tag(v___x_1902_) == 1)
{
lean_object* v_val_1903_; lean_object* v___x_1904_; lean_object* v___x_1905_; lean_object* v___x_1906_; 
v_val_1903_ = lean_ctor_get(v___x_1902_, 0);
lean_inc(v_val_1903_);
lean_dec_ref_known(v___x_1902_, 1);
v___x_1904_ = l_Lean_instInhabitedExpr;
v___x_1905_ = lean_array_get_borrowed(v___x_1904_, v_argVars_1867_, v_val_1903_);
lean_dec(v_val_1903_);
lean_inc(v___x_1905_);
lean_inc(v_a_1880_);
v___x_1906_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_a_1880_, v___x_1905_, v___y_1873_);
if (lean_obj_tag(v___x_1906_) == 0)
{
lean_dec_ref_known(v___x_1906_, 1);
v___y_1882_ = v___y_1872_;
v___y_1883_ = v___y_1873_;
v___y_1884_ = v___y_1874_;
v___y_1885_ = v___y_1875_;
goto v___jp_1881_;
}
else
{
return v___x_1906_;
}
}
else
{
lean_dec(v___x_1902_);
v___y_1882_ = v___y_1872_;
v___y_1883_ = v___y_1873_;
v___y_1884_ = v___y_1874_;
v___y_1885_ = v___y_1875_;
goto v___jp_1881_;
}
v___jp_1881_:
{
lean_object* v___x_1886_; lean_object* v___x_1887_; 
lean_inc(v_a_1880_);
v___x_1886_ = l_Lean_Expr_mvar___override(v_a_1880_);
lean_inc(v___y_1885_);
lean_inc_ref(v___y_1884_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
v___x_1887_ = lean_infer_type(v___x_1886_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1887_) == 0)
{
lean_object* v_a_1888_; lean_object* v___x_1889_; 
v_a_1888_ = lean_ctor_get(v___x_1887_, 0);
lean_inc(v_a_1888_);
lean_dec_ref_known(v___x_1887_, 1);
v___x_1889_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1866_, v_argVars_1867_, v_a_1888_, v___y_1882_, v___y_1883_, v___y_1884_, v___y_1885_);
if (lean_obj_tag(v___x_1889_) == 0)
{
size_t v___x_1890_; size_t v___x_1891_; 
lean_dec_ref_known(v___x_1889_, 1);
v___x_1890_ = ((size_t)1ULL);
v___x_1891_ = lean_usize_add(v_i_1870_, v___x_1890_);
v_i_1870_ = v___x_1891_;
v_b_1871_ = v___x_1879_;
goto _start;
}
else
{
return v___x_1889_;
}
}
else
{
lean_object* v_a_1893_; lean_object* v___x_1895_; uint8_t v_isShared_1896_; uint8_t v_isSharedCheck_1900_; 
v_a_1893_ = lean_ctor_get(v___x_1887_, 0);
v_isSharedCheck_1900_ = !lean_is_exclusive(v___x_1887_);
if (v_isSharedCheck_1900_ == 0)
{
v___x_1895_ = v___x_1887_;
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
else
{
lean_inc(v_a_1893_);
lean_dec(v___x_1887_);
v___x_1895_ = lean_box(0);
v_isShared_1896_ = v_isSharedCheck_1900_;
goto v_resetjp_1894_;
}
v_resetjp_1894_:
{
lean_object* v___x_1898_; 
if (v_isShared_1896_ == 0)
{
v___x_1898_ = v___x_1895_;
goto v_reusejp_1897_;
}
else
{
lean_object* v_reuseFailAlloc_1899_; 
v_reuseFailAlloc_1899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1899_, 0, v_a_1893_);
v___x_1898_ = v_reuseFailAlloc_1899_;
goto v_reusejp_1897_;
}
v_reusejp_1897_:
{
return v___x_1898_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1907_, lean_object* v_argVars_1908_, lean_object* v_e_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_, lean_object* v_a_1913_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_Lean_Meta_getMVars(v_e_1909_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
if (lean_obj_tag(v___x_1915_) == 0)
{
lean_object* v_a_1916_; lean_object* v___x_1917_; size_t v_sz_1918_; size_t v___x_1919_; lean_object* v___x_1920_; 
v_a_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_a_1916_);
lean_dec_ref_known(v___x_1915_, 1);
v___x_1917_ = lean_box(0);
v_sz_1918_ = lean_array_size(v_a_1916_);
v___x_1919_ = ((size_t)0ULL);
v___x_1920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1907_, v_argVars_1908_, v_a_1916_, v_sz_1918_, v___x_1919_, v___x_1917_, v_a_1910_, v_a_1911_, v_a_1912_, v_a_1913_);
lean_dec(v_a_1916_);
if (lean_obj_tag(v___x_1920_) == 0)
{
lean_object* v___x_1922_; uint8_t v_isShared_1923_; uint8_t v_isSharedCheck_1927_; 
v_isSharedCheck_1927_ = !lean_is_exclusive(v___x_1920_);
if (v_isSharedCheck_1927_ == 0)
{
lean_object* v_unused_1928_; 
v_unused_1928_ = lean_ctor_get(v___x_1920_, 0);
lean_dec(v_unused_1928_);
v___x_1922_ = v___x_1920_;
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
else
{
lean_dec(v___x_1920_);
v___x_1922_ = lean_box(0);
v_isShared_1923_ = v_isSharedCheck_1927_;
goto v_resetjp_1921_;
}
v_resetjp_1921_:
{
lean_object* v___x_1925_; 
if (v_isShared_1923_ == 0)
{
lean_ctor_set(v___x_1922_, 0, v___x_1917_);
v___x_1925_ = v___x_1922_;
goto v_reusejp_1924_;
}
else
{
lean_object* v_reuseFailAlloc_1926_; 
v_reuseFailAlloc_1926_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1926_, 0, v___x_1917_);
v___x_1925_ = v_reuseFailAlloc_1926_;
goto v_reusejp_1924_;
}
v_reusejp_1924_:
{
return v___x_1925_;
}
}
}
else
{
return v___x_1920_;
}
}
else
{
lean_object* v_a_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1936_; 
v_a_1929_ = lean_ctor_get(v___x_1915_, 0);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1915_);
if (v_isSharedCheck_1936_ == 0)
{
v___x_1931_ = v___x_1915_;
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_a_1929_);
lean_dec(v___x_1915_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1936_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_a_1929_);
v___x_1934_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
return v___x_1934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1937_, lean_object* v_argVars_1938_, lean_object* v_e_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_, lean_object* v_a_1943_, lean_object* v_a_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1937_, v_argVars_1938_, v_e_1939_, v_a_1940_, v_a_1941_, v_a_1942_, v_a_1943_);
lean_dec(v_a_1943_);
lean_dec_ref(v_a_1942_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec_ref(v_argVars_1938_);
lean_dec_ref(v_argMVars_1937_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2___boxed(lean_object* v_argMVars_1946_, lean_object* v_argVars_1947_, lean_object* v_as_1948_, lean_object* v_sz_1949_, lean_object* v_i_1950_, lean_object* v_b_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
size_t v_sz_boxed_1957_; size_t v_i_boxed_1958_; lean_object* v_res_1959_; 
v_sz_boxed_1957_ = lean_unbox_usize(v_sz_1949_);
lean_dec(v_sz_1949_);
v_i_boxed_1958_ = lean_unbox_usize(v_i_1950_);
lean_dec(v_i_1950_);
v_res_1959_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1946_, v_argVars_1947_, v_as_1948_, v_sz_boxed_1957_, v_i_boxed_1958_, v_b_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec_ref(v_as_1948_);
lean_dec_ref(v_argVars_1947_);
lean_dec_ref(v_argMVars_1946_);
return v_res_1959_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_mvarId_1960_, lean_object* v_val_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_, lean_object* v___y_1964_, lean_object* v___y_1965_){
_start:
{
lean_object* v___x_1967_; 
v___x_1967_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1960_, v_val_1961_, v___y_1963_);
return v___x_1967_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_mvarId_1968_, lean_object* v_val_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_, lean_object* v___y_1973_, lean_object* v___y_1974_){
_start:
{
lean_object* v_res_1975_; 
v_res_1975_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_mvarId_1968_, v_val_1969_, v___y_1970_, v___y_1971_, v___y_1972_, v___y_1973_);
lean_dec(v___y_1973_);
lean_dec_ref(v___y_1972_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
return v_res_1975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1(lean_object* v_00_u03b2_1976_, lean_object* v_x_1977_, lean_object* v_x_1978_, lean_object* v_x_1979_){
_start:
{
lean_object* v___x_1980_; 
v___x_1980_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_x_1977_, v_x_1978_, v_x_1979_);
return v___x_1980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1981_, lean_object* v_x_1982_, size_t v_x_1983_, size_t v_x_1984_, lean_object* v_x_1985_, lean_object* v_x_1986_){
_start:
{
lean_object* v___x_1987_; 
v___x_1987_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1982_, v_x_1983_, v_x_1984_, v_x_1985_, v_x_1986_);
return v___x_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_, lean_object* v_x_1992_, lean_object* v_x_1993_){
_start:
{
size_t v_x_1965__boxed_1994_; size_t v_x_1966__boxed_1995_; lean_object* v_res_1996_; 
v_x_1965__boxed_1994_ = lean_unbox_usize(v_x_1990_);
lean_dec(v_x_1990_);
v_x_1966__boxed_1995_ = lean_unbox_usize(v_x_1991_);
lean_dec(v_x_1991_);
v_res_1996_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(v_00_u03b2_1988_, v_x_1989_, v_x_1965__boxed_1994_, v_x_1966__boxed_1995_, v_x_1992_, v_x_1993_);
return v_res_1996_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1997_, lean_object* v_n_1998_, lean_object* v_k_1999_, lean_object* v_v_2000_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v_n_1998_, v_k_1999_, v_v_2000_);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2002_, size_t v_depth_2003_, lean_object* v_keys_2004_, lean_object* v_vals_2005_, lean_object* v_heq_2006_, lean_object* v_i_2007_, lean_object* v_entries_2008_){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_2003_, v_keys_2004_, v_vals_2005_, v_i_2007_, v_entries_2008_);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2010_, lean_object* v_depth_2011_, lean_object* v_keys_2012_, lean_object* v_vals_2013_, lean_object* v_heq_2014_, lean_object* v_i_2015_, lean_object* v_entries_2016_){
_start:
{
size_t v_depth_boxed_2017_; lean_object* v_res_2018_; 
v_depth_boxed_2017_ = lean_unbox_usize(v_depth_2011_);
lean_dec(v_depth_2011_);
v_res_2018_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_2010_, v_depth_boxed_2017_, v_keys_2012_, v_vals_2013_, v_heq_2014_, v_i_2015_, v_entries_2016_);
lean_dec_ref(v_vals_2013_);
lean_dec_ref(v_keys_2012_);
return v_res_2018_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_, lean_object* v_x_2022_, lean_object* v_x_2023_){
_start:
{
lean_object* v___x_2024_; 
v___x_2024_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2020_, v_x_2021_, v_x_2022_, v_x_2023_);
return v___x_2024_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_2025_, lean_object* v___y_2026_){
_start:
{
uint8_t v___x_2028_; 
v___x_2028_ = l_Lean_Expr_hasMVar(v_e_2025_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
v___x_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2029_, 0, v_e_2025_);
return v___x_2029_;
}
else
{
lean_object* v___x_2030_; lean_object* v_mctx_2031_; lean_object* v___x_2032_; lean_object* v_fst_2033_; lean_object* v_snd_2034_; lean_object* v___x_2035_; lean_object* v_cache_2036_; lean_object* v_zetaDeltaFVarIds_2037_; lean_object* v_postponed_2038_; lean_object* v_diag_2039_; lean_object* v___x_2041_; uint8_t v_isShared_2042_; uint8_t v_isSharedCheck_2048_; 
v___x_2030_ = lean_st_ref_get(v___y_2026_);
v_mctx_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc_ref(v_mctx_2031_);
lean_dec(v___x_2030_);
v___x_2032_ = l_Lean_instantiateMVarsCore(v_mctx_2031_, v_e_2025_);
v_fst_2033_ = lean_ctor_get(v___x_2032_, 0);
lean_inc(v_fst_2033_);
v_snd_2034_ = lean_ctor_get(v___x_2032_, 1);
lean_inc(v_snd_2034_);
lean_dec_ref(v___x_2032_);
v___x_2035_ = lean_st_ref_take(v___y_2026_);
v_cache_2036_ = lean_ctor_get(v___x_2035_, 1);
v_zetaDeltaFVarIds_2037_ = lean_ctor_get(v___x_2035_, 2);
v_postponed_2038_ = lean_ctor_get(v___x_2035_, 3);
v_diag_2039_ = lean_ctor_get(v___x_2035_, 4);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2048_ == 0)
{
lean_object* v_unused_2049_; 
v_unused_2049_ = lean_ctor_get(v___x_2035_, 0);
lean_dec(v_unused_2049_);
v___x_2041_ = v___x_2035_;
v_isShared_2042_ = v_isSharedCheck_2048_;
goto v_resetjp_2040_;
}
else
{
lean_inc(v_diag_2039_);
lean_inc(v_postponed_2038_);
lean_inc(v_zetaDeltaFVarIds_2037_);
lean_inc(v_cache_2036_);
lean_dec(v___x_2035_);
v___x_2041_ = lean_box(0);
v_isShared_2042_ = v_isSharedCheck_2048_;
goto v_resetjp_2040_;
}
v_resetjp_2040_:
{
lean_object* v___x_2044_; 
if (v_isShared_2042_ == 0)
{
lean_ctor_set(v___x_2041_, 0, v_snd_2034_);
v___x_2044_ = v___x_2041_;
goto v_reusejp_2043_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_snd_2034_);
lean_ctor_set(v_reuseFailAlloc_2047_, 1, v_cache_2036_);
lean_ctor_set(v_reuseFailAlloc_2047_, 2, v_zetaDeltaFVarIds_2037_);
lean_ctor_set(v_reuseFailAlloc_2047_, 3, v_postponed_2038_);
lean_ctor_set(v_reuseFailAlloc_2047_, 4, v_diag_2039_);
v___x_2044_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2043_;
}
v_reusejp_2043_:
{
lean_object* v___x_2045_; lean_object* v___x_2046_; 
v___x_2045_ = lean_st_ref_put(v___y_2026_, v___x_2044_);
v___x_2046_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2046_, 0, v_fst_2033_);
return v___x_2046_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_2050_, lean_object* v___y_2051_, lean_object* v___y_2052_){
_start:
{
lean_object* v_res_2053_; 
v_res_2053_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_2050_, v___y_2051_);
lean_dec(v___y_2051_);
return v_res_2053_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_){
_start:
{
lean_object* v___x_2060_; 
v___x_2060_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_2054_, v___y_2056_);
return v___x_2060_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
lean_object* v_res_2067_; 
v_res_2067_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
return v_res_2067_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_2068_, lean_object* v_opt_2069_){
_start:
{
lean_object* v_name_2070_; lean_object* v_defValue_2071_; lean_object* v_map_2072_; lean_object* v___x_2073_; 
v_name_2070_ = lean_ctor_get(v_opt_2069_, 0);
v_defValue_2071_ = lean_ctor_get(v_opt_2069_, 1);
v_map_2072_ = lean_ctor_get(v_opts_2068_, 0);
v___x_2073_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2072_, v_name_2070_);
if (lean_obj_tag(v___x_2073_) == 0)
{
uint8_t v___x_2074_; 
v___x_2074_ = lean_unbox(v_defValue_2071_);
return v___x_2074_;
}
else
{
lean_object* v_val_2075_; 
v_val_2075_ = lean_ctor_get(v___x_2073_, 0);
lean_inc(v_val_2075_);
lean_dec_ref_known(v___x_2073_, 1);
if (lean_obj_tag(v_val_2075_) == 1)
{
uint8_t v_v_2076_; 
v_v_2076_ = lean_ctor_get_uint8(v_val_2075_, 0);
lean_dec_ref_known(v_val_2075_, 0);
return v_v_2076_;
}
else
{
uint8_t v___x_2077_; 
lean_dec(v_val_2075_);
v___x_2077_ = lean_unbox(v_defValue_2071_);
return v___x_2077_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_2078_, lean_object* v_opt_2079_){
_start:
{
uint8_t v_res_2080_; lean_object* v_r_2081_; 
v_res_2080_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_2078_, v_opt_2079_);
lean_dec_ref(v_opt_2079_);
lean_dec_ref(v_opts_2078_);
v_r_2081_ = lean_box(v_res_2080_);
return v_r_2081_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_2082_, lean_object* v_as_2083_, size_t v_i_2084_, size_t v_stop_2085_){
_start:
{
uint8_t v___x_2086_; 
v___x_2086_ = lean_usize_dec_eq(v_i_2084_, v_stop_2085_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; uint8_t v___x_2088_; 
v___x_2087_ = lean_array_uget_borrowed(v_as_2083_, v_i_2084_);
v___x_2088_ = lean_nat_dec_eq(v_a_2082_, v___x_2087_);
if (v___x_2088_ == 0)
{
size_t v___x_2089_; size_t v___x_2090_; 
v___x_2089_ = ((size_t)1ULL);
v___x_2090_ = lean_usize_add(v_i_2084_, v___x_2089_);
v_i_2084_ = v___x_2090_;
goto _start;
}
else
{
return v___x_2088_;
}
}
else
{
uint8_t v___x_2092_; 
v___x_2092_ = 0;
return v___x_2092_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_2093_, lean_object* v_as_2094_, lean_object* v_i_2095_, lean_object* v_stop_2096_){
_start:
{
size_t v_i_boxed_2097_; size_t v_stop_boxed_2098_; uint8_t v_res_2099_; lean_object* v_r_2100_; 
v_i_boxed_2097_ = lean_unbox_usize(v_i_2095_);
lean_dec(v_i_2095_);
v_stop_boxed_2098_ = lean_unbox_usize(v_stop_2096_);
lean_dec(v_stop_2096_);
v_res_2099_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_2093_, v_as_2094_, v_i_boxed_2097_, v_stop_boxed_2098_);
lean_dec_ref(v_as_2094_);
lean_dec(v_a_2093_);
v_r_2100_ = lean_box(v_res_2099_);
return v_r_2100_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_2101_, lean_object* v_a_2102_){
_start:
{
lean_object* v___x_2103_; lean_object* v___x_2104_; uint8_t v___x_2105_; 
v___x_2103_ = lean_unsigned_to_nat(0u);
v___x_2104_ = lean_array_get_size(v_as_2101_);
v___x_2105_ = lean_nat_dec_lt(v___x_2103_, v___x_2104_);
if (v___x_2105_ == 0)
{
return v___x_2105_;
}
else
{
size_t v___x_2106_; size_t v___x_2107_; uint8_t v___x_2108_; 
v___x_2106_ = ((size_t)0ULL);
v___x_2107_ = lean_usize_of_nat(v___x_2104_);
v___x_2108_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_2102_, v_as_2101_, v___x_2106_, v___x_2107_);
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_2109_, lean_object* v_a_2110_){
_start:
{
uint8_t v_res_2111_; lean_object* v_r_2112_; 
v_res_2111_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_2109_, v_a_2110_);
lean_dec(v_a_2110_);
lean_dec_ref(v_as_2109_);
v_r_2112_ = lean_box(v_res_2111_);
return v_r_2112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_2113_, lean_object* v_fst_2114_, lean_object* v_argVars_2115_, lean_object* v_as_2116_, size_t v_sz_2117_, size_t v_i_2118_, lean_object* v_b_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_, lean_object* v___y_2122_, lean_object* v___y_2123_){
_start:
{
lean_object* v_a_2126_; uint8_t v___x_2130_; 
v___x_2130_ = lean_usize_dec_lt(v_i_2118_, v_sz_2117_);
if (v___x_2130_ == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_b_2119_);
return v___x_2131_;
}
else
{
lean_object* v_next_2132_; 
v_next_2132_ = lean_ctor_get(v_b_2119_, 0);
lean_inc(v_next_2132_);
if (lean_obj_tag(v_next_2132_) == 0)
{
lean_object* v___x_2133_; 
v___x_2133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2133_, 0, v_b_2119_);
return v___x_2133_;
}
else
{
lean_object* v_upperBound_2134_; lean_object* v_val_2135_; lean_object* v___x_2137_; uint8_t v_isShared_2138_; uint8_t v_isSharedCheck_2166_; 
v_upperBound_2134_ = lean_ctor_get(v_b_2119_, 1);
v_val_2135_ = lean_ctor_get(v_next_2132_, 0);
v_isSharedCheck_2166_ = !lean_is_exclusive(v_next_2132_);
if (v_isSharedCheck_2166_ == 0)
{
v___x_2137_ = v_next_2132_;
v_isShared_2138_ = v_isSharedCheck_2166_;
goto v_resetjp_2136_;
}
else
{
lean_inc(v_val_2135_);
lean_dec(v_next_2132_);
v___x_2137_ = lean_box(0);
v_isShared_2138_ = v_isSharedCheck_2166_;
goto v_resetjp_2136_;
}
v_resetjp_2136_:
{
uint8_t v___x_2139_; 
v___x_2139_ = lean_nat_dec_lt(v_val_2135_, v_upperBound_2134_);
if (v___x_2139_ == 0)
{
lean_object* v___x_2140_; 
lean_del_object(v___x_2137_);
lean_dec(v_val_2135_);
v___x_2140_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2140_, 0, v_b_2119_);
return v___x_2140_;
}
else
{
lean_object* v___x_2142_; uint8_t v_isShared_2143_; uint8_t v_isSharedCheck_2163_; 
lean_inc(v_upperBound_2134_);
v_isSharedCheck_2163_ = !lean_is_exclusive(v_b_2119_);
if (v_isSharedCheck_2163_ == 0)
{
lean_object* v_unused_2164_; lean_object* v_unused_2165_; 
v_unused_2164_ = lean_ctor_get(v_b_2119_, 1);
lean_dec(v_unused_2164_);
v_unused_2165_ = lean_ctor_get(v_b_2119_, 0);
lean_dec(v_unused_2165_);
v___x_2142_ = v_b_2119_;
v_isShared_2143_ = v_isSharedCheck_2163_;
goto v_resetjp_2141_;
}
else
{
lean_dec(v_b_2119_);
v___x_2142_ = lean_box(0);
v_isShared_2143_ = v_isSharedCheck_2163_;
goto v_resetjp_2141_;
}
v_resetjp_2141_:
{
lean_object* v___x_2144_; lean_object* v___x_2145_; lean_object* v___x_2147_; 
v___x_2144_ = lean_unsigned_to_nat(1u);
v___x_2145_ = lean_nat_add(v_val_2135_, v___x_2144_);
if (v_isShared_2138_ == 0)
{
lean_ctor_set(v___x_2137_, 0, v___x_2145_);
v___x_2147_ = v___x_2137_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2162_; 
v_reuseFailAlloc_2162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2162_, 0, v___x_2145_);
v___x_2147_ = v_reuseFailAlloc_2162_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
lean_object* v___x_2149_; 
if (v_isShared_2143_ == 0)
{
lean_ctor_set(v___x_2142_, 0, v___x_2147_);
v___x_2149_ = v___x_2142_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2161_; 
v_reuseFailAlloc_2161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2161_, 0, v___x_2147_);
lean_ctor_set(v_reuseFailAlloc_2161_, 1, v_upperBound_2134_);
v___x_2149_ = v_reuseFailAlloc_2161_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
uint8_t v___x_2150_; 
v___x_2150_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2113_, v_val_2135_);
lean_dec(v_val_2135_);
if (v___x_2150_ == 0)
{
lean_object* v_a_2151_; lean_object* v___x_2152_; 
v_a_2151_ = lean_array_uget_borrowed(v_as_2116_, v_i_2118_);
lean_inc(v_a_2151_);
v___x_2152_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2114_, v_argVars_2115_, v_a_2151_, v___y_2120_, v___y_2121_, v___y_2122_, v___y_2123_);
if (lean_obj_tag(v___x_2152_) == 0)
{
lean_dec_ref_known(v___x_2152_, 1);
v_a_2126_ = v___x_2149_;
goto v___jp_2125_;
}
else
{
lean_object* v_a_2153_; lean_object* v___x_2155_; uint8_t v_isShared_2156_; uint8_t v_isSharedCheck_2160_; 
lean_dec_ref(v___x_2149_);
v_a_2153_ = lean_ctor_get(v___x_2152_, 0);
v_isSharedCheck_2160_ = !lean_is_exclusive(v___x_2152_);
if (v_isSharedCheck_2160_ == 0)
{
v___x_2155_ = v___x_2152_;
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
else
{
lean_inc(v_a_2153_);
lean_dec(v___x_2152_);
v___x_2155_ = lean_box(0);
v_isShared_2156_ = v_isSharedCheck_2160_;
goto v_resetjp_2154_;
}
v_resetjp_2154_:
{
lean_object* v___x_2158_; 
if (v_isShared_2156_ == 0)
{
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
}
else
{
v_a_2126_ = v___x_2149_;
goto v___jp_2125_;
}
}
}
}
}
}
}
}
v___jp_2125_:
{
size_t v___x_2127_; size_t v___x_2128_; 
v___x_2127_ = ((size_t)1ULL);
v___x_2128_ = lean_usize_add(v_i_2118_, v___x_2127_);
v_i_2118_ = v___x_2128_;
v_b_2119_ = v_a_2126_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2167_, lean_object* v_fst_2168_, lean_object* v_argVars_2169_, lean_object* v_as_2170_, lean_object* v_sz_2171_, lean_object* v_i_2172_, lean_object* v_b_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_, lean_object* v___y_2177_, lean_object* v___y_2178_){
_start:
{
size_t v_sz_boxed_2179_; size_t v_i_boxed_2180_; lean_object* v_res_2181_; 
v_sz_boxed_2179_ = lean_unbox_usize(v_sz_2171_);
lean_dec(v_sz_2171_);
v_i_boxed_2180_ = lean_unbox_usize(v_i_2172_);
lean_dec(v_i_2172_);
v_res_2181_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2167_, v_fst_2168_, v_argVars_2169_, v_as_2170_, v_sz_boxed_2179_, v_i_boxed_2180_, v_b_2173_, v___y_2174_, v___y_2175_, v___y_2176_, v___y_2177_);
lean_dec(v___y_2177_);
lean_dec_ref(v___y_2176_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec_ref(v_as_2170_);
lean_dec_ref(v_argVars_2169_);
lean_dec_ref(v_fst_2168_);
lean_dec_ref(v_a_2167_);
return v_res_2181_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2182_, lean_object* v_a_2183_, lean_object* v___x_2184_, lean_object* v_a_2185_, lean_object* v_b_2186_){
_start:
{
uint8_t v___x_2188_; 
v___x_2188_ = lean_nat_dec_lt(v_a_2185_, v_upperBound_2182_);
if (v___x_2188_ == 0)
{
lean_object* v___x_2189_; 
lean_dec(v_a_2185_);
v___x_2189_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2189_, 0, v_b_2186_);
return v___x_2189_;
}
else
{
lean_object* v_snd_2190_; lean_object* v___x_2192_; uint8_t v_isShared_2193_; uint8_t v_isSharedCheck_2230_; 
v_snd_2190_ = lean_ctor_get(v_b_2186_, 1);
v_isSharedCheck_2230_ = !lean_is_exclusive(v_b_2186_);
if (v_isSharedCheck_2230_ == 0)
{
lean_object* v_unused_2231_; 
v_unused_2231_ = lean_ctor_get(v_b_2186_, 0);
lean_dec(v_unused_2231_);
v___x_2192_ = v_b_2186_;
v_isShared_2193_ = v_isSharedCheck_2230_;
goto v_resetjp_2191_;
}
else
{
lean_inc(v_snd_2190_);
lean_dec(v_b_2186_);
v___x_2192_ = lean_box(0);
v_isShared_2193_ = v_isSharedCheck_2230_;
goto v_resetjp_2191_;
}
v_resetjp_2191_:
{
lean_object* v_array_2194_; lean_object* v_start_2195_; lean_object* v_stop_2196_; lean_object* v___x_2197_; uint8_t v___x_2198_; 
v_array_2194_ = lean_ctor_get(v_snd_2190_, 0);
v_start_2195_ = lean_ctor_get(v_snd_2190_, 1);
v_stop_2196_ = lean_ctor_get(v_snd_2190_, 2);
v___x_2197_ = lean_box(0);
v___x_2198_ = lean_nat_dec_lt(v_start_2195_, v_stop_2196_);
if (v___x_2198_ == 0)
{
lean_object* v___x_2200_; 
lean_dec(v_a_2185_);
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 0, v___x_2197_);
v___x_2200_ = v___x_2192_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2202_; 
v_reuseFailAlloc_2202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2202_, 0, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2202_, 1, v_snd_2190_);
v___x_2200_ = v_reuseFailAlloc_2202_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; 
v___x_2201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2201_, 0, v___x_2200_);
return v___x_2201_;
}
}
else
{
lean_object* v___x_2204_; uint8_t v_isShared_2205_; uint8_t v_isSharedCheck_2226_; 
lean_inc(v_stop_2196_);
lean_inc(v_start_2195_);
lean_inc_ref(v_array_2194_);
v_isSharedCheck_2226_ = !lean_is_exclusive(v_snd_2190_);
if (v_isSharedCheck_2226_ == 0)
{
lean_object* v_unused_2227_; lean_object* v_unused_2228_; lean_object* v_unused_2229_; 
v_unused_2227_ = lean_ctor_get(v_snd_2190_, 2);
lean_dec(v_unused_2227_);
v_unused_2228_ = lean_ctor_get(v_snd_2190_, 1);
lean_dec(v_unused_2228_);
v_unused_2229_ = lean_ctor_get(v_snd_2190_, 0);
lean_dec(v_unused_2229_);
v___x_2204_ = v_snd_2190_;
v_isShared_2205_ = v_isSharedCheck_2226_;
goto v_resetjp_2203_;
}
else
{
lean_dec(v_snd_2190_);
v___x_2204_ = lean_box(0);
v_isShared_2205_ = v_isSharedCheck_2226_;
goto v_resetjp_2203_;
}
v_resetjp_2203_:
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2210_; 
v___x_2206_ = lean_array_fget(v_array_2194_, v_start_2195_);
v___x_2207_ = lean_unsigned_to_nat(1u);
v___x_2208_ = lean_nat_add(v_start_2195_, v___x_2207_);
lean_dec(v_start_2195_);
if (v_isShared_2205_ == 0)
{
lean_ctor_set(v___x_2204_, 1, v___x_2208_);
v___x_2210_ = v___x_2204_;
goto v_reusejp_2209_;
}
else
{
lean_object* v_reuseFailAlloc_2225_; 
v_reuseFailAlloc_2225_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2225_, 0, v_array_2194_);
lean_ctor_set(v_reuseFailAlloc_2225_, 1, v___x_2208_);
lean_ctor_set(v_reuseFailAlloc_2225_, 2, v_stop_2196_);
v___x_2210_ = v_reuseFailAlloc_2225_;
goto v_reusejp_2209_;
}
v_reusejp_2209_:
{
uint8_t v___x_2217_; 
v___x_2217_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2183_, v_a_2185_);
if (v___x_2217_ == 0)
{
uint8_t v___x_2218_; 
v___x_2218_ = l_Lean_Expr_hasExprMVar(v___x_2206_);
lean_dec(v___x_2206_);
if (v___x_2218_ == 0)
{
goto v___jp_2211_;
}
else
{
lean_object* v___x_2219_; uint8_t v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; lean_object* v___x_2223_; lean_object* v___x_2224_; 
lean_del_object(v___x_2192_);
lean_dec(v_a_2185_);
v___x_2219_ = lean_unsigned_to_nat(0u);
v___x_2220_ = lean_nat_dec_eq(v___x_2184_, v___x_2219_);
v___x_2221_ = lean_box(v___x_2220_);
v___x_2222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
v___x_2223_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2223_, 0, v___x_2222_);
lean_ctor_set(v___x_2223_, 1, v___x_2210_);
v___x_2224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2224_, 0, v___x_2223_);
return v___x_2224_;
}
}
else
{
lean_dec(v___x_2206_);
goto v___jp_2211_;
}
v___jp_2211_:
{
lean_object* v___x_2213_; 
if (v_isShared_2193_ == 0)
{
lean_ctor_set(v___x_2192_, 1, v___x_2210_);
lean_ctor_set(v___x_2192_, 0, v___x_2197_);
v___x_2213_ = v___x_2192_;
goto v_reusejp_2212_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v___x_2210_);
v___x_2213_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2212_;
}
v_reusejp_2212_:
{
lean_object* v___x_2214_; 
v___x_2214_ = lean_nat_add(v_a_2185_, v___x_2207_);
lean_dec(v_a_2185_);
v_a_2185_ = v___x_2214_;
v_b_2186_ = v___x_2213_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2232_, lean_object* v_a_2233_, lean_object* v___x_2234_, lean_object* v_a_2235_, lean_object* v_b_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v_res_2238_; 
v_res_2238_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2232_, v_a_2233_, v___x_2234_, v_a_2235_, v_b_2236_);
lean_dec(v___x_2234_);
lean_dec_ref(v_a_2233_);
lean_dec(v_upperBound_2232_);
return v_res_2238_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2239_; lean_object* v_dummy_2240_; 
v___x_2239_ = lean_box(0);
v_dummy_2240_ = l_Lean_Expr_sort___override(v___x_2239_);
return v_dummy_2240_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2241_, lean_object* v___x_2242_, uint8_t v___x_2243_, lean_object* v_x_2244_, lean_object* v_argTy_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_, lean_object* v___y_2248_, lean_object* v___y_2249_){
_start:
{
lean_object* v___x_2251_; 
lean_inc(v___y_2249_);
lean_inc_ref(v___y_2248_);
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
v___x_2251_ = lean_whnf(v_argTy_2245_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2253_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v___x_2253_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2252_, v___y_2246_, v___y_2247_, v___y_2248_, v___y_2249_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v_dummy_2255_; lean_object* v_nargs_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; lean_object* v___x_2264_; lean_object* v___x_2265_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
lean_inc(v_a_2254_);
lean_dec_ref_known(v___x_2253_, 1);
v_dummy_2255_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2256_ = l_Lean_Expr_getAppNumArgs(v_a_2252_);
lean_inc(v_nargs_2256_);
v___x_2257_ = lean_mk_array(v_nargs_2256_, v_dummy_2255_);
v___x_2258_ = lean_unsigned_to_nat(1u);
v___x_2259_ = lean_nat_sub(v_nargs_2256_, v___x_2258_);
lean_dec(v_nargs_2256_);
v___x_2260_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2252_, v___x_2257_, v___x_2259_);
v___x_2261_ = lean_array_get_size(v___x_2260_);
lean_inc(v___x_2241_);
v___x_2262_ = l_Array_toSubarray___redArg(v___x_2260_, v___x_2241_, v___x_2261_);
v___x_2263_ = lean_box(0);
v___x_2264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2264_, 0, v___x_2263_);
lean_ctor_set(v___x_2264_, 1, v___x_2262_);
v___x_2265_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2261_, v_a_2254_, v___x_2242_, v___x_2241_, v___x_2264_);
lean_dec(v_a_2254_);
if (lean_obj_tag(v___x_2265_) == 0)
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2279_; 
v_a_2266_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2279_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2279_ == 0)
{
v___x_2268_ = v___x_2265_;
v_isShared_2269_ = v_isSharedCheck_2279_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2265_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2279_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v_fst_2270_; 
v_fst_2270_ = lean_ctor_get(v_a_2266_, 0);
lean_inc(v_fst_2270_);
lean_dec(v_a_2266_);
if (lean_obj_tag(v_fst_2270_) == 0)
{
lean_object* v___x_2271_; lean_object* v___x_2273_; 
v___x_2271_ = lean_box(v___x_2243_);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v___x_2271_);
v___x_2273_ = v___x_2268_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v___x_2271_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
else
{
lean_object* v_val_2275_; lean_object* v___x_2277_; 
v_val_2275_ = lean_ctor_get(v_fst_2270_, 0);
lean_inc(v_val_2275_);
lean_dec_ref_known(v_fst_2270_, 1);
if (v_isShared_2269_ == 0)
{
lean_ctor_set(v___x_2268_, 0, v_val_2275_);
v___x_2277_ = v___x_2268_;
goto v_reusejp_2276_;
}
else
{
lean_object* v_reuseFailAlloc_2278_; 
v_reuseFailAlloc_2278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2278_, 0, v_val_2275_);
v___x_2277_ = v_reuseFailAlloc_2278_;
goto v_reusejp_2276_;
}
v_reusejp_2276_:
{
return v___x_2277_;
}
}
}
}
else
{
lean_object* v_a_2280_; lean_object* v___x_2282_; uint8_t v_isShared_2283_; uint8_t v_isSharedCheck_2287_; 
v_a_2280_ = lean_ctor_get(v___x_2265_, 0);
v_isSharedCheck_2287_ = !lean_is_exclusive(v___x_2265_);
if (v_isSharedCheck_2287_ == 0)
{
v___x_2282_ = v___x_2265_;
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
else
{
lean_inc(v_a_2280_);
lean_dec(v___x_2265_);
v___x_2282_ = lean_box(0);
v_isShared_2283_ = v_isSharedCheck_2287_;
goto v_resetjp_2281_;
}
v_resetjp_2281_:
{
lean_object* v___x_2285_; 
if (v_isShared_2283_ == 0)
{
v___x_2285_ = v___x_2282_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2286_; 
v_reuseFailAlloc_2286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2286_, 0, v_a_2280_);
v___x_2285_ = v_reuseFailAlloc_2286_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
return v___x_2285_;
}
}
}
}
else
{
lean_object* v_a_2288_; lean_object* v___x_2290_; uint8_t v_isShared_2291_; uint8_t v_isSharedCheck_2295_; 
lean_dec(v_a_2252_);
lean_dec(v___x_2241_);
v_a_2288_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2295_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2295_ == 0)
{
v___x_2290_ = v___x_2253_;
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
else
{
lean_inc(v_a_2288_);
lean_dec(v___x_2253_);
v___x_2290_ = lean_box(0);
v_isShared_2291_ = v_isSharedCheck_2295_;
goto v_resetjp_2289_;
}
v_resetjp_2289_:
{
lean_object* v___x_2293_; 
if (v_isShared_2291_ == 0)
{
v___x_2293_ = v___x_2290_;
goto v_reusejp_2292_;
}
else
{
lean_object* v_reuseFailAlloc_2294_; 
v_reuseFailAlloc_2294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2294_, 0, v_a_2288_);
v___x_2293_ = v_reuseFailAlloc_2294_;
goto v_reusejp_2292_;
}
v_reusejp_2292_:
{
return v___x_2293_;
}
}
}
}
else
{
lean_object* v_a_2296_; lean_object* v___x_2298_; uint8_t v_isShared_2299_; uint8_t v_isSharedCheck_2303_; 
lean_dec(v___x_2241_);
v_a_2296_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2303_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2303_ == 0)
{
v___x_2298_ = v___x_2251_;
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
else
{
lean_inc(v_a_2296_);
lean_dec(v___x_2251_);
v___x_2298_ = lean_box(0);
v_isShared_2299_ = v_isSharedCheck_2303_;
goto v_resetjp_2297_;
}
v_resetjp_2297_:
{
lean_object* v___x_2301_; 
if (v_isShared_2299_ == 0)
{
v___x_2301_ = v___x_2298_;
goto v_reusejp_2300_;
}
else
{
lean_object* v_reuseFailAlloc_2302_; 
v_reuseFailAlloc_2302_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2302_, 0, v_a_2296_);
v___x_2301_ = v_reuseFailAlloc_2302_;
goto v_reusejp_2300_;
}
v_reusejp_2300_:
{
return v___x_2301_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2304_, lean_object* v___x_2305_, lean_object* v___x_2306_, lean_object* v_x_2307_, lean_object* v_argTy_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_){
_start:
{
uint8_t v___x_22648__boxed_2314_; lean_object* v_res_2315_; 
v___x_22648__boxed_2314_ = lean_unbox(v___x_2306_);
v_res_2315_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2304_, v___x_2305_, v___x_22648__boxed_2314_, v_x_2307_, v_argTy_2308_, v___y_2309_, v___y_2310_, v___y_2311_, v___y_2312_);
lean_dec(v___y_2312_);
lean_dec_ref(v___y_2311_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec_ref(v_x_2307_);
lean_dec(v___x_2305_);
return v_res_2315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2319_, lean_object* v_projInfo_x3f_2320_, lean_object* v___x_2321_, lean_object* v_argVars_2322_, lean_object* v_as_2323_, size_t v_sz_2324_, size_t v_i_2325_, lean_object* v_b_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_, lean_object* v___y_2329_, lean_object* v___y_2330_){
_start:
{
uint8_t v___x_2332_; 
v___x_2332_ = lean_usize_dec_lt(v_i_2325_, v_sz_2324_);
if (v___x_2332_ == 0)
{
lean_object* v___x_2333_; 
lean_dec(v___x_2321_);
v___x_2333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2333_, 0, v_b_2326_);
return v___x_2333_;
}
else
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2337_; lean_object* v___x_2338_; lean_object* v___f_2339_; uint8_t v___x_2340_; lean_object* v_a_2341_; lean_object* v___y_2348_; lean_object* v___x_2362_; lean_object* v___x_2363_; 
lean_dec_ref(v_b_2326_);
v___x_2334_ = lean_box(0);
v___x_2335_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2336_ = l_Lean_instInhabitedExpr;
v___x_2337_ = lean_unsigned_to_nat(0u);
v___x_2338_ = lean_box(v___x_2332_);
lean_inc(v___x_2321_);
v___f_2339_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2339_, 0, v___x_2337_);
lean_closure_set(v___f_2339_, 1, v___x_2321_);
lean_closure_set(v___f_2339_, 2, v___x_2338_);
v___x_2340_ = lean_nat_dec_eq(v___x_2321_, v___x_2337_);
v_a_2341_ = lean_array_uget_borrowed(v_as_2323_, v_i_2325_);
v___x_2362_ = lean_array_get_borrowed(v___x_2336_, v_fst_2319_, v_a_2341_);
lean_inc(v___y_2330_);
lean_inc_ref(v___y_2329_);
lean_inc(v___y_2328_);
lean_inc_ref(v___y_2327_);
lean_inc(v___x_2362_);
v___x_2363_ = lean_infer_type(v___x_2362_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_object* v_a_2364_; lean_object* v___x_2365_; 
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2364_);
lean_dec_ref_known(v___x_2363_, 1);
v___x_2365_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2364_, v___y_2328_);
if (lean_obj_tag(v___x_2365_) == 0)
{
if (lean_obj_tag(v_projInfo_x3f_2320_) == 1)
{
lean_object* v_val_2366_; lean_object* v_a_2367_; lean_object* v_numParams_2368_; uint8_t v___x_2369_; 
v_val_2366_ = lean_ctor_get(v_projInfo_x3f_2320_, 0);
v_a_2367_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2367_);
lean_dec_ref_known(v___x_2365_, 1);
v_numParams_2368_ = lean_ctor_get(v_val_2366_, 1);
v___x_2369_ = lean_nat_dec_eq(v_numParams_2368_, v_a_2341_);
if (v___x_2369_ == 0)
{
lean_object* v___x_2370_; 
v___x_2370_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2367_, v___f_2339_, v___x_2340_, v___x_2340_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
v___y_2348_ = v___x_2370_;
goto v___jp_2347_;
}
else
{
lean_object* v___x_2371_; 
lean_dec_ref(v___f_2339_);
lean_dec(v___x_2321_);
v___x_2371_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2319_, v_argVars_2322_, v_a_2367_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
if (lean_obj_tag(v___x_2371_) == 0)
{
lean_dec_ref_known(v___x_2371_, 1);
goto v___jp_2342_;
}
else
{
lean_object* v_a_2372_; lean_object* v___x_2374_; uint8_t v_isShared_2375_; uint8_t v_isSharedCheck_2379_; 
v_a_2372_ = lean_ctor_get(v___x_2371_, 0);
v_isSharedCheck_2379_ = !lean_is_exclusive(v___x_2371_);
if (v_isSharedCheck_2379_ == 0)
{
v___x_2374_ = v___x_2371_;
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
else
{
lean_inc(v_a_2372_);
lean_dec(v___x_2371_);
v___x_2374_ = lean_box(0);
v_isShared_2375_ = v_isSharedCheck_2379_;
goto v_resetjp_2373_;
}
v_resetjp_2373_:
{
lean_object* v___x_2377_; 
if (v_isShared_2375_ == 0)
{
v___x_2377_ = v___x_2374_;
goto v_reusejp_2376_;
}
else
{
lean_object* v_reuseFailAlloc_2378_; 
v_reuseFailAlloc_2378_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2378_, 0, v_a_2372_);
v___x_2377_ = v_reuseFailAlloc_2378_;
goto v_reusejp_2376_;
}
v_reusejp_2376_:
{
return v___x_2377_;
}
}
}
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2381_; 
v_a_2380_ = lean_ctor_get(v___x_2365_, 0);
lean_inc(v_a_2380_);
lean_dec_ref_known(v___x_2365_, 1);
v___x_2381_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2380_, v___f_2339_, v___x_2340_, v___x_2340_, v___y_2327_, v___y_2328_, v___y_2329_, v___y_2330_);
v___y_2348_ = v___x_2381_;
goto v___jp_2347_;
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec_ref(v___f_2339_);
lean_dec(v___x_2321_);
v_a_2382_ = lean_ctor_get(v___x_2365_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2365_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2365_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2365_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v___x_2387_; 
if (v_isShared_2385_ == 0)
{
v___x_2387_ = v___x_2384_;
goto v_reusejp_2386_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_a_2382_);
v___x_2387_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2386_;
}
v_reusejp_2386_:
{
return v___x_2387_;
}
}
}
}
else
{
lean_object* v_a_2390_; lean_object* v___x_2392_; uint8_t v_isShared_2393_; uint8_t v_isSharedCheck_2397_; 
lean_dec_ref(v___f_2339_);
lean_dec(v___x_2321_);
v_a_2390_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2397_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2397_ == 0)
{
v___x_2392_ = v___x_2363_;
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
else
{
lean_inc(v_a_2390_);
lean_dec(v___x_2363_);
v___x_2392_ = lean_box(0);
v_isShared_2393_ = v_isSharedCheck_2397_;
goto v_resetjp_2391_;
}
v_resetjp_2391_:
{
lean_object* v___x_2395_; 
if (v_isShared_2393_ == 0)
{
v___x_2395_ = v___x_2392_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2396_; 
v_reuseFailAlloc_2396_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2396_, 0, v_a_2390_);
v___x_2395_ = v_reuseFailAlloc_2396_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
return v___x_2395_;
}
}
}
v___jp_2342_:
{
lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
lean_inc(v_a_2341_);
v___x_2343_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2343_, 0, v_a_2341_);
v___x_2344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
v___x_2345_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2345_, 0, v___x_2344_);
lean_ctor_set(v___x_2345_, 1, v___x_2334_);
v___x_2346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2346_, 0, v___x_2345_);
return v___x_2346_;
}
v___jp_2347_:
{
if (lean_obj_tag(v___y_2348_) == 0)
{
lean_object* v_a_2349_; uint8_t v___x_2350_; 
v_a_2349_ = lean_ctor_get(v___y_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___y_2348_, 1);
v___x_2350_ = lean_unbox(v_a_2349_);
lean_dec(v_a_2349_);
if (v___x_2350_ == 0)
{
size_t v___x_2351_; size_t v___x_2352_; 
v___x_2351_ = ((size_t)1ULL);
v___x_2352_ = lean_usize_add(v_i_2325_, v___x_2351_);
v_i_2325_ = v___x_2352_;
v_b_2326_ = v___x_2335_;
goto _start;
}
else
{
lean_dec(v___x_2321_);
goto v___jp_2342_;
}
}
else
{
lean_object* v_a_2354_; lean_object* v___x_2356_; uint8_t v_isShared_2357_; uint8_t v_isSharedCheck_2361_; 
lean_dec(v___x_2321_);
v_a_2354_ = lean_ctor_get(v___y_2348_, 0);
v_isSharedCheck_2361_ = !lean_is_exclusive(v___y_2348_);
if (v_isSharedCheck_2361_ == 0)
{
v___x_2356_ = v___y_2348_;
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
else
{
lean_inc(v_a_2354_);
lean_dec(v___y_2348_);
v___x_2356_ = lean_box(0);
v_isShared_2357_ = v_isSharedCheck_2361_;
goto v_resetjp_2355_;
}
v_resetjp_2355_:
{
lean_object* v___x_2359_; 
if (v_isShared_2357_ == 0)
{
v___x_2359_ = v___x_2356_;
goto v_reusejp_2358_;
}
else
{
lean_object* v_reuseFailAlloc_2360_; 
v_reuseFailAlloc_2360_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2360_, 0, v_a_2354_);
v___x_2359_ = v_reuseFailAlloc_2360_;
goto v_reusejp_2358_;
}
v_reusejp_2358_:
{
return v___x_2359_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2398_, lean_object* v_projInfo_x3f_2399_, lean_object* v___x_2400_, lean_object* v_argVars_2401_, lean_object* v_as_2402_, lean_object* v_sz_2403_, lean_object* v_i_2404_, lean_object* v_b_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
size_t v_sz_boxed_2411_; size_t v_i_boxed_2412_; lean_object* v_res_2413_; 
v_sz_boxed_2411_ = lean_unbox_usize(v_sz_2403_);
lean_dec(v_sz_2403_);
v_i_boxed_2412_ = lean_unbox_usize(v_i_2404_);
lean_dec(v_i_2404_);
v_res_2413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2398_, v_projInfo_x3f_2399_, v___x_2400_, v_argVars_2401_, v_as_2402_, v_sz_boxed_2411_, v_i_boxed_2412_, v_b_2405_, v___y_2406_, v___y_2407_, v___y_2408_, v___y_2409_);
lean_dec(v___y_2409_);
lean_dec_ref(v___y_2408_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec_ref(v_as_2402_);
lean_dec_ref(v_argVars_2401_);
lean_dec(v_projInfo_x3f_2399_);
lean_dec_ref(v_fst_2398_);
return v_res_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2414_, lean_object* v_as_2415_, size_t v_i_2416_, size_t v_stop_2417_, lean_object* v_b_2418_){
_start:
{
lean_object* v___y_2420_; uint8_t v___x_2424_; 
v___x_2424_ = lean_usize_dec_eq(v_i_2416_, v_stop_2417_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; uint8_t v___x_2426_; 
v___x_2425_ = lean_array_uget_borrowed(v_as_2415_, v_i_2416_);
v___x_2426_ = lean_nat_dec_eq(v___x_2425_, v_next_2414_);
if (v___x_2426_ == 0)
{
lean_object* v___x_2427_; 
lean_inc(v___x_2425_);
v___x_2427_ = lean_array_push(v_b_2418_, v___x_2425_);
v___y_2420_ = v___x_2427_;
goto v___jp_2419_;
}
else
{
v___y_2420_ = v_b_2418_;
goto v___jp_2419_;
}
}
else
{
return v_b_2418_;
}
v___jp_2419_:
{
size_t v___x_2421_; size_t v___x_2422_; 
v___x_2421_ = ((size_t)1ULL);
v___x_2422_ = lean_usize_add(v_i_2416_, v___x_2421_);
v_i_2416_ = v___x_2422_;
v_b_2418_ = v___y_2420_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2428_, lean_object* v_as_2429_, lean_object* v_i_2430_, lean_object* v_stop_2431_, lean_object* v_b_2432_){
_start:
{
size_t v_i_boxed_2433_; size_t v_stop_boxed_2434_; lean_object* v_res_2435_; 
v_i_boxed_2433_ = lean_unbox_usize(v_i_2430_);
lean_dec(v_i_2430_);
v_stop_boxed_2434_ = lean_unbox_usize(v_stop_2431_);
lean_dec(v_stop_2431_);
v_res_2435_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2428_, v_as_2429_, v_i_boxed_2433_, v_stop_boxed_2434_, v_b_2432_);
lean_dec_ref(v_as_2429_);
lean_dec(v_next_2428_);
return v_res_2435_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object* v_fst_2436_, lean_object* v___x_2437_, lean_object* v_fst_2438_, lean_object* v_argVars_2439_, lean_object* v_snd_2440_, lean_object* v_next_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_, lean_object* v___y_2445_){
_start:
{
lean_object* v___x_2447_; lean_object* v___y_2449_; lean_object* v___x_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; uint8_t v___x_2492_; 
lean_inc(v_next_2441_);
v___x_2447_ = lean_array_push(v_fst_2436_, v_next_2441_);
v___x_2489_ = lean_unsigned_to_nat(0u);
v___x_2490_ = lean_array_get_size(v_snd_2440_);
v___x_2491_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2492_ = lean_nat_dec_lt(v___x_2489_, v___x_2490_);
if (v___x_2492_ == 0)
{
v___y_2449_ = v___x_2491_;
goto v___jp_2448_;
}
else
{
size_t v___x_2493_; size_t v___x_2494_; lean_object* v___x_2495_; 
v___x_2493_ = ((size_t)0ULL);
v___x_2494_ = lean_usize_of_nat(v___x_2490_);
v___x_2495_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2441_, v_snd_2440_, v___x_2493_, v___x_2494_, v___x_2491_);
v___y_2449_ = v___x_2495_;
goto v___jp_2448_;
}
v___jp_2448_:
{
lean_object* v___x_2450_; lean_object* v___x_2451_; 
v___x_2450_ = lean_array_get_borrowed(v___x_2437_, v_fst_2438_, v_next_2441_);
lean_dec(v_next_2441_);
lean_inc(v___y_2445_);
lean_inc_ref(v___y_2444_);
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
lean_inc(v___x_2450_);
v___x_2451_ = lean_infer_type(v___x_2450_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v_a_2452_; lean_object* v___x_2453_; 
v_a_2452_ = lean_ctor_get(v___x_2451_, 0);
lean_inc(v_a_2452_);
lean_dec_ref_known(v___x_2451_, 1);
v___x_2453_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2438_, v_argVars_2439_, v_a_2452_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2453_) == 0)
{
lean_object* v___x_2454_; 
lean_dec_ref_known(v___x_2453_, 1);
lean_inc(v___x_2450_);
v___x_2454_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2438_, v_argVars_2439_, v___x_2450_, v___y_2442_, v___y_2443_, v___y_2444_, v___y_2445_);
if (lean_obj_tag(v___x_2454_) == 0)
{
lean_object* v___x_2456_; uint8_t v_isShared_2457_; uint8_t v_isSharedCheck_2463_; 
v_isSharedCheck_2463_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2463_ == 0)
{
lean_object* v_unused_2464_; 
v_unused_2464_ = lean_ctor_get(v___x_2454_, 0);
lean_dec(v_unused_2464_);
v___x_2456_ = v___x_2454_;
v_isShared_2457_ = v_isSharedCheck_2463_;
goto v_resetjp_2455_;
}
else
{
lean_dec(v___x_2454_);
v___x_2456_ = lean_box(0);
v_isShared_2457_ = v_isSharedCheck_2463_;
goto v_resetjp_2455_;
}
v_resetjp_2455_:
{
lean_object* v___x_2458_; lean_object* v___x_2459_; lean_object* v___x_2461_; 
v___x_2458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2458_, 0, v___x_2447_);
lean_ctor_set(v___x_2458_, 1, v___y_2449_);
v___x_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2459_, 0, v___x_2458_);
if (v_isShared_2457_ == 0)
{
lean_ctor_set(v___x_2456_, 0, v___x_2459_);
v___x_2461_ = v___x_2456_;
goto v_reusejp_2460_;
}
else
{
lean_object* v_reuseFailAlloc_2462_; 
v_reuseFailAlloc_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2462_, 0, v___x_2459_);
v___x_2461_ = v_reuseFailAlloc_2462_;
goto v_reusejp_2460_;
}
v_reusejp_2460_:
{
return v___x_2461_;
}
}
}
else
{
lean_object* v_a_2465_; lean_object* v___x_2467_; uint8_t v_isShared_2468_; uint8_t v_isSharedCheck_2472_; 
lean_dec_ref(v___y_2449_);
lean_dec_ref(v___x_2447_);
v_a_2465_ = lean_ctor_get(v___x_2454_, 0);
v_isSharedCheck_2472_ = !lean_is_exclusive(v___x_2454_);
if (v_isSharedCheck_2472_ == 0)
{
v___x_2467_ = v___x_2454_;
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
else
{
lean_inc(v_a_2465_);
lean_dec(v___x_2454_);
v___x_2467_ = lean_box(0);
v_isShared_2468_ = v_isSharedCheck_2472_;
goto v_resetjp_2466_;
}
v_resetjp_2466_:
{
lean_object* v___x_2470_; 
if (v_isShared_2468_ == 0)
{
v___x_2470_ = v___x_2467_;
goto v_reusejp_2469_;
}
else
{
lean_object* v_reuseFailAlloc_2471_; 
v_reuseFailAlloc_2471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2471_, 0, v_a_2465_);
v___x_2470_ = v_reuseFailAlloc_2471_;
goto v_reusejp_2469_;
}
v_reusejp_2469_:
{
return v___x_2470_;
}
}
}
}
else
{
lean_object* v_a_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2480_; 
lean_dec_ref(v___y_2449_);
lean_dec_ref(v___x_2447_);
v_a_2473_ = lean_ctor_get(v___x_2453_, 0);
v_isSharedCheck_2480_ = !lean_is_exclusive(v___x_2453_);
if (v_isSharedCheck_2480_ == 0)
{
v___x_2475_ = v___x_2453_;
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_a_2473_);
lean_dec(v___x_2453_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2480_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v___x_2478_; 
if (v_isShared_2476_ == 0)
{
v___x_2478_ = v___x_2475_;
goto v_reusejp_2477_;
}
else
{
lean_object* v_reuseFailAlloc_2479_; 
v_reuseFailAlloc_2479_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2479_, 0, v_a_2473_);
v___x_2478_ = v_reuseFailAlloc_2479_;
goto v_reusejp_2477_;
}
v_reusejp_2477_:
{
return v___x_2478_;
}
}
}
}
else
{
lean_object* v_a_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
lean_dec_ref(v___y_2449_);
lean_dec_ref(v___x_2447_);
v_a_2481_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2451_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_a_2481_);
lean_dec(v___x_2451_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_a_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object* v_fst_2496_, lean_object* v___x_2497_, lean_object* v_fst_2498_, lean_object* v_argVars_2499_, lean_object* v_snd_2500_, lean_object* v_next_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2496_, v___x_2497_, v_fst_2498_, v_argVars_2499_, v_snd_2500_, v_next_2501_, v___y_2502_, v___y_2503_, v___y_2504_, v___y_2505_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v___y_2503_);
lean_dec_ref(v___y_2502_);
lean_dec(v_snd_2500_);
lean_dec_ref(v_argVars_2499_);
lean_dec_ref(v_fst_2498_);
lean_dec_ref(v___x_2497_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2514_; lean_object* v_env_2515_; uint8_t v___x_2516_; lean_object* v_env_2517_; lean_object* v___x_2518_; lean_object* v_toCold_2519_; lean_object* v_mctx_2520_; lean_object* v_lctx_2521_; lean_object* v_options_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2514_ = lean_st_ref_get(v___y_2512_);
v_env_2515_ = lean_ctor_get(v___x_2514_, 0);
lean_inc_ref(v_env_2515_);
lean_dec(v___x_2514_);
v___x_2516_ = 0;
v_env_2517_ = l_Lean_Environment_setRecordingDeps(v_env_2515_, v___x_2516_);
v___x_2518_ = lean_st_ref_get(v___y_2510_);
v_toCold_2519_ = lean_ctor_get(v___y_2511_, 0);
v_mctx_2520_ = lean_ctor_get(v___x_2518_, 0);
lean_inc_ref(v_mctx_2520_);
lean_dec(v___x_2518_);
v_lctx_2521_ = lean_ctor_get(v___y_2509_, 2);
v_options_2522_ = lean_ctor_get(v_toCold_2519_, 2);
lean_inc_ref(v_options_2522_);
lean_inc_ref(v_lctx_2521_);
v___x_2523_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2523_, 0, v_env_2517_);
lean_ctor_set(v___x_2523_, 1, v_mctx_2520_);
lean_ctor_set(v___x_2523_, 2, v_lctx_2521_);
lean_ctor_set(v___x_2523_, 3, v_options_2522_);
v___x_2524_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2524_, 0, v___x_2523_);
lean_ctor_set(v___x_2524_, 1, v_msgData_2508_);
v___x_2525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2525_, 0, v___x_2524_);
return v___x_2525_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
lean_object* v_res_2532_; 
v_res_2532_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
return v_res_2532_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2533_, lean_object* v___y_2534_, lean_object* v___y_2535_, lean_object* v___y_2536_, lean_object* v___y_2537_){
_start:
{
lean_object* v_ref_2539_; lean_object* v___x_2540_; lean_object* v_a_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2549_; 
v_ref_2539_ = lean_ctor_get(v___y_2536_, 2);
v___x_2540_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2533_, v___y_2534_, v___y_2535_, v___y_2536_, v___y_2537_);
v_a_2541_ = lean_ctor_get(v___x_2540_, 0);
v_isSharedCheck_2549_ = !lean_is_exclusive(v___x_2540_);
if (v_isSharedCheck_2549_ == 0)
{
v___x_2543_ = v___x_2540_;
v_isShared_2544_ = v_isSharedCheck_2549_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_a_2541_);
lean_dec(v___x_2540_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2549_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v___x_2545_; lean_object* v___x_2547_; 
lean_inc(v_ref_2539_);
v___x_2545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2545_, 0, v_ref_2539_);
lean_ctor_set(v___x_2545_, 1, v_a_2541_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set_tag(v___x_2543_, 1);
lean_ctor_set(v___x_2543_, 0, v___x_2545_);
v___x_2547_ = v___x_2543_;
goto v_reusejp_2546_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v___x_2545_);
v___x_2547_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2546_;
}
v_reusejp_2546_:
{
return v___x_2547_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_, lean_object* v___y_2554_, lean_object* v___y_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2550_, v___y_2551_, v___y_2552_, v___y_2553_, v___y_2554_);
lean_dec(v___y_2554_);
lean_dec_ref(v___y_2553_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2557_, size_t v_sz_2558_, size_t v_i_2559_, lean_object* v_bs_2560_, lean_object* v___y_2561_, lean_object* v___y_2562_, lean_object* v___y_2563_, lean_object* v___y_2564_){
_start:
{
uint8_t v___x_2566_; 
v___x_2566_ = lean_usize_dec_lt(v_i_2559_, v_sz_2558_);
if (v___x_2566_ == 0)
{
lean_object* v___x_2567_; 
v___x_2567_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2567_, 0, v_bs_2560_);
return v___x_2567_;
}
else
{
lean_object* v___x_2568_; lean_object* v_v_2569_; lean_object* v___x_2570_; lean_object* v_bs_x27_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v___x_2568_ = l_Lean_instInhabitedExpr;
v_v_2569_ = lean_array_uget(v_bs_2560_, v_i_2559_);
v___x_2570_ = lean_unsigned_to_nat(0u);
v_bs_x27_2571_ = lean_array_uset(v_bs_2560_, v_i_2559_, v___x_2570_);
v___x_2572_ = lean_array_get_borrowed(v___x_2568_, v_fst_2557_, v_v_2569_);
lean_dec(v_v_2569_);
lean_inc(v___y_2564_);
lean_inc_ref(v___y_2563_);
lean_inc(v___y_2562_);
lean_inc_ref(v___y_2561_);
lean_inc(v___x_2572_);
v___x_2573_ = lean_infer_type(v___x_2572_, v___y_2561_, v___y_2562_, v___y_2563_, v___y_2564_);
if (lean_obj_tag(v___x_2573_) == 0)
{
lean_object* v_a_2574_; lean_object* v___x_2575_; 
v_a_2574_ = lean_ctor_get(v___x_2573_, 0);
lean_inc(v_a_2574_);
lean_dec_ref_known(v___x_2573_, 1);
v___x_2575_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2574_, v___y_2562_);
if (lean_obj_tag(v___x_2575_) == 0)
{
lean_object* v_a_2576_; lean_object* v___x_2577_; lean_object* v___x_2578_; size_t v___x_2579_; size_t v___x_2580_; lean_object* v___x_2581_; 
v_a_2576_ = lean_ctor_get(v___x_2575_, 0);
lean_inc(v_a_2576_);
lean_dec_ref_known(v___x_2575_, 1);
v___x_2577_ = l_Lean_Expr_setPPExplicit(v_a_2576_, v___x_2566_);
v___x_2578_ = l_Lean_indentExpr(v___x_2577_);
v___x_2579_ = ((size_t)1ULL);
v___x_2580_ = lean_usize_add(v_i_2559_, v___x_2579_);
v___x_2581_ = lean_array_uset(v_bs_x27_2571_, v_i_2559_, v___x_2578_);
v_i_2559_ = v___x_2580_;
v_bs_2560_ = v___x_2581_;
goto _start;
}
else
{
lean_object* v_a_2583_; lean_object* v___x_2585_; uint8_t v_isShared_2586_; uint8_t v_isSharedCheck_2590_; 
lean_dec_ref(v_bs_x27_2571_);
v_a_2583_ = lean_ctor_get(v___x_2575_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2575_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2585_ = v___x_2575_;
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
else
{
lean_inc(v_a_2583_);
lean_dec(v___x_2575_);
v___x_2585_ = lean_box(0);
v_isShared_2586_ = v_isSharedCheck_2590_;
goto v_resetjp_2584_;
}
v_resetjp_2584_:
{
lean_object* v___x_2588_; 
if (v_isShared_2586_ == 0)
{
v___x_2588_ = v___x_2585_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2583_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
}
}
else
{
lean_object* v_a_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2598_; 
lean_dec_ref(v_bs_x27_2571_);
v_a_2591_ = lean_ctor_get(v___x_2573_, 0);
v_isSharedCheck_2598_ = !lean_is_exclusive(v___x_2573_);
if (v_isSharedCheck_2598_ == 0)
{
v___x_2593_ = v___x_2573_;
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_a_2591_);
lean_dec(v___x_2573_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2598_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2596_; 
if (v_isShared_2594_ == 0)
{
v___x_2596_ = v___x_2593_;
goto v_reusejp_2595_;
}
else
{
lean_object* v_reuseFailAlloc_2597_; 
v_reuseFailAlloc_2597_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2597_, 0, v_a_2591_);
v___x_2596_ = v_reuseFailAlloc_2597_;
goto v_reusejp_2595_;
}
v_reusejp_2595_:
{
return v___x_2596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2599_, lean_object* v_sz_2600_, lean_object* v_i_2601_, lean_object* v_bs_2602_, lean_object* v___y_2603_, lean_object* v___y_2604_, lean_object* v___y_2605_, lean_object* v___y_2606_, lean_object* v___y_2607_){
_start:
{
size_t v_sz_boxed_2608_; size_t v_i_boxed_2609_; lean_object* v_res_2610_; 
v_sz_boxed_2608_ = lean_unbox_usize(v_sz_2600_);
lean_dec(v_sz_2600_);
v_i_boxed_2609_ = lean_unbox_usize(v_i_2601_);
lean_dec(v_i_2601_);
v_res_2610_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2599_, v_sz_boxed_2608_, v_i_boxed_2609_, v_bs_2602_, v___y_2603_, v___y_2604_, v___y_2605_, v___y_2606_);
lean_dec(v___y_2606_);
lean_dec_ref(v___y_2605_);
lean_dec(v___y_2604_);
lean_dec_ref(v___y_2603_);
lean_dec_ref(v_fst_2599_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object* v___x_2611_, lean_object* v_snd_2612_, lean_object* v___f_2613_, lean_object* v_____r_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; lean_object* v___x_2621_; lean_object* v___x_2622_; 
v___x_2620_ = lean_unsigned_to_nat(0u);
v___x_2621_ = lean_array_get_borrowed(v___x_2611_, v_snd_2612_, v___x_2620_);
lean_inc(v___y_2618_);
lean_inc_ref(v___y_2617_);
lean_inc(v___y_2616_);
lean_inc_ref(v___y_2615_);
lean_inc(v___x_2621_);
v___x_2622_ = lean_apply_6(v___f_2613_, v___x_2621_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_, lean_box(0));
return v___x_2622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object* v___x_2623_, lean_object* v_snd_2624_, lean_object* v___f_2625_, lean_object* v_____r_2626_, lean_object* v___y_2627_, lean_object* v___y_2628_, lean_object* v___y_2629_, lean_object* v___y_2630_, lean_object* v___y_2631_){
_start:
{
lean_object* v_res_2632_; 
v_res_2632_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2623_, v_snd_2624_, v___f_2625_, v_____r_2626_, v___y_2627_, v___y_2628_, v___y_2629_, v___y_2630_);
lean_dec(v___y_2630_);
lean_dec_ref(v___y_2629_);
lean_dec(v___y_2628_);
lean_dec_ref(v___y_2627_);
lean_dec(v_snd_2624_);
lean_dec(v___x_2623_);
return v_res_2632_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2636_; lean_object* v___x_2637_; 
v___x_2636_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1));
v___x_2637_ = l_Lean_MessageData_ofFormat(v___x_2636_);
return v___x_2637_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; 
v___x_2639_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3));
v___x_2640_ = l_Lean_stringToMessageData(v___x_2639_);
return v___x_2640_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2642_; lean_object* v___x_2643_; 
v___x_2642_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5));
v___x_2643_ = l_Lean_stringToMessageData(v___x_2642_);
return v___x_2643_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2645_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7));
v___x_2646_ = l_Lean_stringToMessageData(v___x_2645_);
return v___x_2646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(lean_object* v_fst_2647_, lean_object* v_argVars_2648_, lean_object* v_inst_2649_, lean_object* v_a_2650_, lean_object* v_projInfo_x3f_2651_, lean_object* v_a_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_){
_start:
{
lean_object* v___y_2659_; lean_object* v_fst_2679_; lean_object* v_snd_2680_; lean_object* v___x_2682_; uint8_t v_isShared_2683_; uint8_t v_isSharedCheck_2752_; 
v_fst_2679_ = lean_ctor_get(v_a_2652_, 0);
v_snd_2680_ = lean_ctor_get(v_a_2652_, 1);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_a_2652_);
if (v_isSharedCheck_2752_ == 0)
{
v___x_2682_ = v_a_2652_;
v_isShared_2683_ = v_isSharedCheck_2752_;
goto v_resetjp_2681_;
}
else
{
lean_inc(v_snd_2680_);
lean_inc(v_fst_2679_);
lean_dec(v_a_2652_);
v___x_2682_ = lean_box(0);
v_isShared_2683_ = v_isSharedCheck_2752_;
goto v_resetjp_2681_;
}
v___jp_2658_:
{
if (lean_obj_tag(v___y_2659_) == 0)
{
lean_object* v_a_2660_; lean_object* v___x_2662_; uint8_t v_isShared_2663_; uint8_t v_isSharedCheck_2670_; 
v_a_2660_ = lean_ctor_get(v___y_2659_, 0);
v_isSharedCheck_2670_ = !lean_is_exclusive(v___y_2659_);
if (v_isSharedCheck_2670_ == 0)
{
v___x_2662_ = v___y_2659_;
v_isShared_2663_ = v_isSharedCheck_2670_;
goto v_resetjp_2661_;
}
else
{
lean_inc(v_a_2660_);
lean_dec(v___y_2659_);
v___x_2662_ = lean_box(0);
v_isShared_2663_ = v_isSharedCheck_2670_;
goto v_resetjp_2661_;
}
v_resetjp_2661_:
{
if (lean_obj_tag(v_a_2660_) == 0)
{
lean_object* v_a_2664_; lean_object* v___x_2666_; 
lean_dec_ref(v_a_2650_);
lean_dec_ref(v_inst_2649_);
lean_dec_ref(v_argVars_2648_);
lean_dec_ref(v_fst_2647_);
v_a_2664_ = lean_ctor_get(v_a_2660_, 0);
lean_inc(v_a_2664_);
lean_dec_ref_known(v_a_2660_, 1);
if (v_isShared_2663_ == 0)
{
lean_ctor_set(v___x_2662_, 0, v_a_2664_);
v___x_2666_ = v___x_2662_;
goto v_reusejp_2665_;
}
else
{
lean_object* v_reuseFailAlloc_2667_; 
v_reuseFailAlloc_2667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2667_, 0, v_a_2664_);
v___x_2666_ = v_reuseFailAlloc_2667_;
goto v_reusejp_2665_;
}
v_reusejp_2665_:
{
return v___x_2666_;
}
}
else
{
lean_object* v_a_2668_; 
lean_del_object(v___x_2662_);
v_a_2668_ = lean_ctor_get(v_a_2660_, 0);
lean_inc(v_a_2668_);
lean_dec_ref_known(v_a_2660_, 1);
v_a_2652_ = v_a_2668_;
goto _start;
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec_ref(v_a_2650_);
lean_dec_ref(v_inst_2649_);
lean_dec_ref(v_argVars_2648_);
lean_dec_ref(v_fst_2647_);
v_a_2671_ = lean_ctor_get(v___y_2659_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___y_2659_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___y_2659_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___y_2659_);
v___x_2673_ = lean_box(0);
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
v_resetjp_2672_:
{
lean_object* v___x_2676_; 
if (v_isShared_2674_ == 0)
{
v___x_2676_ = v___x_2673_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2677_; 
v_reuseFailAlloc_2677_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2677_, 0, v_a_2671_);
v___x_2676_ = v_reuseFailAlloc_2677_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
return v___x_2676_;
}
}
}
}
v_resetjp_2681_:
{
lean_object* v___x_2684_; lean_object* v___x_2685_; uint8_t v___x_2686_; 
v___x_2684_ = lean_array_get_size(v_snd_2680_);
v___x_2685_ = lean_unsigned_to_nat(0u);
v___x_2686_ = lean_nat_dec_eq(v___x_2684_, v___x_2685_);
if (v___x_2686_ == 0)
{
lean_object* v___x_2687_; lean_object* v___f_2688_; lean_object* v___x_2731_; size_t v_sz_2732_; size_t v___x_2733_; lean_object* v___x_2734_; 
lean_del_object(v___x_2682_);
v___x_2687_ = l_Lean_instInhabitedExpr;
lean_inc(v_snd_2680_);
lean_inc_ref(v_argVars_2648_);
lean_inc_ref(v_fst_2647_);
lean_inc(v_fst_2679_);
v___f_2688_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2688_, 0, v_fst_2679_);
lean_closure_set(v___f_2688_, 1, v___x_2687_);
lean_closure_set(v___f_2688_, 2, v_fst_2647_);
lean_closure_set(v___f_2688_, 3, v_argVars_2648_);
lean_closure_set(v___f_2688_, 4, v_snd_2680_);
v___x_2731_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2732_ = lean_array_size(v_snd_2680_);
v___x_2733_ = ((size_t)0ULL);
v___x_2734_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2647_, v_projInfo_x3f_2651_, v___x_2684_, v_argVars_2648_, v_snd_2680_, v_sz_2732_, v___x_2733_, v___x_2731_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2734_) == 0)
{
lean_object* v_a_2735_; lean_object* v_fst_2736_; 
v_a_2735_ = lean_ctor_get(v___x_2734_, 0);
lean_inc(v_a_2735_);
lean_dec_ref_known(v___x_2734_, 1);
v_fst_2736_ = lean_ctor_get(v_a_2735_, 0);
lean_inc(v_fst_2736_);
lean_dec(v_a_2735_);
if (lean_obj_tag(v_fst_2736_) == 0)
{
lean_dec(v_fst_2679_);
goto v___jp_2689_;
}
else
{
lean_object* v_val_2737_; 
v_val_2737_ = lean_ctor_get(v_fst_2736_, 0);
lean_inc(v_val_2737_);
lean_dec_ref_known(v_fst_2736_, 1);
if (lean_obj_tag(v_val_2737_) == 0)
{
lean_dec(v_fst_2679_);
goto v___jp_2689_;
}
else
{
lean_object* v_val_2738_; lean_object* v___x_2739_; 
lean_dec_ref(v___f_2688_);
v_val_2738_ = lean_ctor_get(v_val_2737_, 0);
lean_inc(v_val_2738_);
lean_dec_ref_known(v_val_2737_, 1);
v___x_2739_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2679_, v___x_2687_, v_fst_2647_, v_argVars_2648_, v_snd_2680_, v_val_2738_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v_snd_2680_);
v___y_2659_ = v___x_2739_;
goto v___jp_2658_;
}
}
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec_ref(v___f_2688_);
lean_dec(v_snd_2680_);
lean_dec(v_fst_2679_);
lean_dec_ref(v_a_2650_);
lean_dec_ref(v_inst_2649_);
lean_dec_ref(v_argVars_2648_);
lean_dec_ref(v_fst_2647_);
v_a_2740_ = lean_ctor_get(v___x_2734_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2734_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2734_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2734_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
if (v_isShared_2743_ == 0)
{
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2746_; 
v_reuseFailAlloc_2746_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2746_, 0, v_a_2740_);
v___x_2745_ = v_reuseFailAlloc_2746_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
return v___x_2745_;
}
}
}
v___jp_2689_:
{
lean_object* v___x_2690_; lean_object* v___x_2691_; uint8_t v___x_2692_; 
v___x_2690_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2655_);
v___x_2691_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2692_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_2690_, v___x_2691_);
lean_dec_ref(v___x_2690_);
if (v___x_2692_ == 0)
{
lean_object* v___x_2693_; lean_object* v___x_2694_; 
v___x_2693_ = lean_box(0);
v___x_2694_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2685_, v_snd_2680_, v___f_2688_, v___x_2693_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v_snd_2680_);
v___y_2659_ = v___x_2694_;
goto v___jp_2658_;
}
else
{
size_t v_sz_2695_; size_t v___x_2696_; lean_object* v___x_2697_; 
v_sz_2695_ = lean_array_size(v_snd_2680_);
v___x_2696_ = ((size_t)0ULL);
lean_inc(v_snd_2680_);
v___x_2697_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2647_, v_sz_2695_, v___x_2696_, v_snd_2680_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2697_) == 0)
{
lean_object* v_a_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2704_; lean_object* v___x_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; lean_object* v___x_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_a_2698_ = lean_ctor_get(v___x_2697_, 0);
lean_inc(v_a_2698_);
lean_dec_ref_known(v___x_2697_, 1);
v___x_2699_ = lean_array_to_list(v_a_2698_);
v___x_2700_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2701_ = l_Lean_MessageData_joinSep(v___x_2699_, v___x_2700_);
v___x_2702_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4);
lean_inc_ref(v_inst_2649_);
v___x_2703_ = l_Lean_MessageData_ofExpr(v_inst_2649_);
v___x_2704_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2704_, 0, v___x_2702_);
lean_ctor_set(v___x_2704_, 1, v___x_2703_);
v___x_2705_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6);
v___x_2706_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2706_, 0, v___x_2704_);
lean_ctor_set(v___x_2706_, 1, v___x_2705_);
lean_inc_ref(v_a_2650_);
v___x_2707_ = l_Lean_indentExpr(v_a_2650_);
v___x_2708_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2708_, 0, v___x_2706_);
lean_ctor_set(v___x_2708_, 1, v___x_2707_);
v___x_2709_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8);
v___x_2710_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2710_, 0, v___x_2708_);
lean_ctor_set(v___x_2710_, 1, v___x_2709_);
v___x_2711_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2711_, 0, v___x_2710_);
lean_ctor_set(v___x_2711_, 1, v___x_2701_);
v___x_2712_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2711_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
if (lean_obj_tag(v___x_2712_) == 0)
{
lean_object* v_a_2713_; lean_object* v___x_2714_; 
v_a_2713_ = lean_ctor_get(v___x_2712_, 0);
lean_inc(v_a_2713_);
lean_dec_ref_known(v___x_2712_, 1);
v___x_2714_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2685_, v_snd_2680_, v___f_2688_, v_a_2713_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v_snd_2680_);
v___y_2659_ = v___x_2714_;
goto v___jp_2658_;
}
else
{
lean_object* v_a_2715_; lean_object* v___x_2717_; uint8_t v_isShared_2718_; uint8_t v_isSharedCheck_2722_; 
lean_dec_ref(v___f_2688_);
lean_dec(v_snd_2680_);
lean_dec_ref(v_a_2650_);
lean_dec_ref(v_inst_2649_);
lean_dec_ref(v_argVars_2648_);
lean_dec_ref(v_fst_2647_);
v_a_2715_ = lean_ctor_get(v___x_2712_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2712_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2717_ = v___x_2712_;
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
else
{
lean_inc(v_a_2715_);
lean_dec(v___x_2712_);
v___x_2717_ = lean_box(0);
v_isShared_2718_ = v_isSharedCheck_2722_;
goto v_resetjp_2716_;
}
v_resetjp_2716_:
{
lean_object* v___x_2720_; 
if (v_isShared_2718_ == 0)
{
v___x_2720_ = v___x_2717_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v_a_2715_);
v___x_2720_ = v_reuseFailAlloc_2721_;
goto v_reusejp_2719_;
}
v_reusejp_2719_:
{
return v___x_2720_;
}
}
}
}
else
{
lean_object* v_a_2723_; lean_object* v___x_2725_; uint8_t v_isShared_2726_; uint8_t v_isSharedCheck_2730_; 
lean_dec_ref(v___f_2688_);
lean_dec(v_snd_2680_);
lean_dec_ref(v_a_2650_);
lean_dec_ref(v_inst_2649_);
lean_dec_ref(v_argVars_2648_);
lean_dec_ref(v_fst_2647_);
v_a_2723_ = lean_ctor_get(v___x_2697_, 0);
v_isSharedCheck_2730_ = !lean_is_exclusive(v___x_2697_);
if (v_isSharedCheck_2730_ == 0)
{
v___x_2725_ = v___x_2697_;
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
else
{
lean_inc(v_a_2723_);
lean_dec(v___x_2697_);
v___x_2725_ = lean_box(0);
v_isShared_2726_ = v_isSharedCheck_2730_;
goto v_resetjp_2724_;
}
v_resetjp_2724_:
{
lean_object* v___x_2728_; 
if (v_isShared_2726_ == 0)
{
v___x_2728_ = v___x_2725_;
goto v_reusejp_2727_;
}
else
{
lean_object* v_reuseFailAlloc_2729_; 
v_reuseFailAlloc_2729_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2729_, 0, v_a_2723_);
v___x_2728_ = v_reuseFailAlloc_2729_;
goto v_reusejp_2727_;
}
v_reusejp_2727_:
{
return v___x_2728_;
}
}
}
}
}
}
else
{
lean_object* v___x_2749_; 
lean_dec_ref(v_a_2650_);
lean_dec_ref(v_inst_2649_);
lean_dec_ref(v_argVars_2648_);
lean_dec_ref(v_fst_2647_);
if (v_isShared_2683_ == 0)
{
v___x_2749_ = v___x_2682_;
goto v_reusejp_2748_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_fst_2679_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v_snd_2680_);
v___x_2749_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2748_;
}
v_reusejp_2748_:
{
lean_object* v___x_2750_; 
v___x_2750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2750_, 0, v___x_2749_);
return v___x_2750_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___boxed(lean_object* v_fst_2753_, lean_object* v_argVars_2754_, lean_object* v_inst_2755_, lean_object* v_a_2756_, lean_object* v_projInfo_x3f_2757_, lean_object* v_a_2758_, lean_object* v___y_2759_, lean_object* v___y_2760_, lean_object* v___y_2761_, lean_object* v___y_2762_, lean_object* v___y_2763_){
_start:
{
lean_object* v_res_2764_; 
v_res_2764_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2753_, v_argVars_2754_, v_inst_2755_, v_a_2756_, v_projInfo_x3f_2757_, v_a_2758_, v___y_2759_, v___y_2760_, v___y_2761_, v___y_2762_);
lean_dec(v___y_2762_);
lean_dec_ref(v___y_2761_);
lean_dec(v___y_2760_);
lean_dec_ref(v___y_2759_);
lean_dec(v_projInfo_x3f_2757_);
return v_res_2764_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2765_, lean_object* v_a_2766_, lean_object* v_a_2767_){
_start:
{
if (lean_obj_tag(v_a_2766_) == 0)
{
lean_object* v___x_2768_; 
v___x_2768_ = l_List_reverse___redArg(v_a_2767_);
return v___x_2768_;
}
else
{
lean_object* v_head_2769_; lean_object* v_tail_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2785_; 
v_head_2769_ = lean_ctor_get(v_a_2766_, 0);
v_tail_2770_ = lean_ctor_get(v_a_2766_, 1);
v_isSharedCheck_2785_ = !lean_is_exclusive(v_a_2766_);
if (v_isSharedCheck_2785_ == 0)
{
v___x_2772_ = v_a_2766_;
v_isShared_2773_ = v_isSharedCheck_2785_;
goto v_resetjp_2771_;
}
else
{
lean_inc(v_tail_2770_);
lean_inc(v_head_2769_);
lean_dec(v_a_2766_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2785_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
uint8_t v___x_2774_; lean_object* v___x_2775_; lean_object* v___x_2776_; uint8_t v___x_2777_; uint8_t v___x_2778_; uint8_t v___x_2779_; 
v___x_2774_ = 0;
v___x_2775_ = lean_box(v___x_2774_);
v___x_2776_ = lean_array_get(v___x_2775_, v_fst_2765_, v_head_2769_);
lean_dec(v___x_2775_);
v___x_2777_ = 3;
v___x_2778_ = lean_unbox(v___x_2776_);
lean_dec(v___x_2776_);
v___x_2779_ = l_Lean_instBEqBinderInfo_beq(v___x_2778_, v___x_2777_);
if (v___x_2779_ == 0)
{
lean_del_object(v___x_2772_);
lean_dec(v_head_2769_);
v_a_2766_ = v_tail_2770_;
goto _start;
}
else
{
lean_object* v___x_2782_; 
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 1, v_a_2767_);
v___x_2782_ = v___x_2772_;
goto v_reusejp_2781_;
}
else
{
lean_object* v_reuseFailAlloc_2784_; 
v_reuseFailAlloc_2784_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2784_, 0, v_head_2769_);
lean_ctor_set(v_reuseFailAlloc_2784_, 1, v_a_2767_);
v___x_2782_ = v_reuseFailAlloc_2784_;
goto v_reusejp_2781_;
}
v_reusejp_2781_:
{
v_a_2766_ = v_tail_2770_;
v_a_2767_ = v___x_2782_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2786_, lean_object* v_a_2787_, lean_object* v_a_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2786_, v_a_2787_, v_a_2788_);
lean_dec_ref(v_fst_2786_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2790_, size_t v_sz_2791_, size_t v_i_2792_, lean_object* v_bs_2793_, lean_object* v___y_2794_, lean_object* v___y_2795_, lean_object* v___y_2796_, lean_object* v___y_2797_){
_start:
{
uint8_t v___x_2799_; 
v___x_2799_ = lean_usize_dec_lt(v_i_2792_, v_sz_2791_);
if (v___x_2799_ == 0)
{
lean_object* v___x_2800_; 
v___x_2800_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2800_, 0, v_bs_2793_);
return v___x_2800_;
}
else
{
lean_object* v___x_2801_; lean_object* v_v_2802_; lean_object* v___x_2803_; lean_object* v_bs_x27_2804_; lean_object* v___x_2805_; lean_object* v___x_2806_; 
v___x_2801_ = l_Lean_instInhabitedExpr;
v_v_2802_ = lean_array_uget(v_bs_2793_, v_i_2792_);
v___x_2803_ = lean_unsigned_to_nat(0u);
v_bs_x27_2804_ = lean_array_uset(v_bs_2793_, v_i_2792_, v___x_2803_);
v___x_2805_ = lean_array_get_borrowed(v___x_2801_, v_argVars_2790_, v_v_2802_);
lean_dec(v_v_2802_);
lean_inc(v___y_2797_);
lean_inc_ref(v___y_2796_);
lean_inc(v___y_2795_);
lean_inc_ref(v___y_2794_);
lean_inc(v___x_2805_);
v___x_2806_ = lean_infer_type(v___x_2805_, v___y_2794_, v___y_2795_, v___y_2796_, v___y_2797_);
if (lean_obj_tag(v___x_2806_) == 0)
{
lean_object* v_a_2807_; lean_object* v___x_2808_; size_t v___x_2809_; size_t v___x_2810_; lean_object* v___x_2811_; 
v_a_2807_ = lean_ctor_get(v___x_2806_, 0);
lean_inc(v_a_2807_);
lean_dec_ref_known(v___x_2806_, 1);
v___x_2808_ = l_Lean_indentExpr(v_a_2807_);
v___x_2809_ = ((size_t)1ULL);
v___x_2810_ = lean_usize_add(v_i_2792_, v___x_2809_);
v___x_2811_ = lean_array_uset(v_bs_x27_2804_, v_i_2792_, v___x_2808_);
v_i_2792_ = v___x_2810_;
v_bs_2793_ = v___x_2811_;
goto _start;
}
else
{
lean_object* v_a_2813_; lean_object* v___x_2815_; uint8_t v_isShared_2816_; uint8_t v_isSharedCheck_2820_; 
lean_dec_ref(v_bs_x27_2804_);
v_a_2813_ = lean_ctor_get(v___x_2806_, 0);
v_isSharedCheck_2820_ = !lean_is_exclusive(v___x_2806_);
if (v_isSharedCheck_2820_ == 0)
{
v___x_2815_ = v___x_2806_;
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
else
{
lean_inc(v_a_2813_);
lean_dec(v___x_2806_);
v___x_2815_ = lean_box(0);
v_isShared_2816_ = v_isSharedCheck_2820_;
goto v_resetjp_2814_;
}
v_resetjp_2814_:
{
lean_object* v___x_2818_; 
if (v_isShared_2816_ == 0)
{
v___x_2818_ = v___x_2815_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_a_2813_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2821_, lean_object* v_sz_2822_, lean_object* v_i_2823_, lean_object* v_bs_2824_, lean_object* v___y_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
size_t v_sz_boxed_2830_; size_t v_i_boxed_2831_; lean_object* v_res_2832_; 
v_sz_boxed_2830_ = lean_unbox_usize(v_sz_2822_);
lean_dec(v_sz_2822_);
v_i_boxed_2831_ = lean_unbox_usize(v_i_2823_);
lean_dec(v_i_2823_);
v_res_2832_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2821_, v_sz_boxed_2830_, v_i_boxed_2831_, v_bs_2824_, v___y_2825_, v___y_2826_, v___y_2827_, v___y_2828_);
lean_dec(v___y_2828_);
lean_dec_ref(v___y_2827_);
lean_dec(v___y_2826_);
lean_dec_ref(v___y_2825_);
lean_dec_ref(v_argVars_2821_);
return v_res_2832_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2833_, lean_object* v_a_2834_){
_start:
{
if (lean_obj_tag(v_a_2833_) == 0)
{
lean_object* v___x_2835_; 
v___x_2835_ = l_List_reverse___redArg(v_a_2834_);
return v___x_2835_;
}
else
{
lean_object* v_head_2836_; lean_object* v_tail_2837_; lean_object* v___x_2839_; uint8_t v_isShared_2840_; uint8_t v_isSharedCheck_2848_; 
v_head_2836_ = lean_ctor_get(v_a_2833_, 0);
v_tail_2837_ = lean_ctor_get(v_a_2833_, 1);
v_isSharedCheck_2848_ = !lean_is_exclusive(v_a_2833_);
if (v_isSharedCheck_2848_ == 0)
{
v___x_2839_ = v_a_2833_;
v_isShared_2840_ = v_isSharedCheck_2848_;
goto v_resetjp_2838_;
}
else
{
lean_inc(v_tail_2837_);
lean_inc(v_head_2836_);
lean_dec(v_a_2833_);
v___x_2839_ = lean_box(0);
v_isShared_2840_ = v_isSharedCheck_2848_;
goto v_resetjp_2838_;
}
v_resetjp_2838_:
{
lean_object* v___x_2841_; lean_object* v___x_2842_; lean_object* v___x_2843_; lean_object* v___x_2845_; 
v___x_2841_ = l_Nat_reprFast(v_head_2836_);
v___x_2842_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2842_, 0, v___x_2841_);
v___x_2843_ = l_Lean_MessageData_ofFormat(v___x_2842_);
if (v_isShared_2840_ == 0)
{
lean_ctor_set(v___x_2839_, 1, v_a_2834_);
lean_ctor_set(v___x_2839_, 0, v___x_2843_);
v___x_2845_ = v___x_2839_;
goto v_reusejp_2844_;
}
else
{
lean_object* v_reuseFailAlloc_2847_; 
v_reuseFailAlloc_2847_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2847_, 0, v___x_2843_);
lean_ctor_set(v_reuseFailAlloc_2847_, 1, v_a_2834_);
v___x_2845_ = v_reuseFailAlloc_2847_;
goto v_reusejp_2844_;
}
v_reusejp_2844_:
{
v_a_2833_ = v_tail_2837_;
v_a_2834_ = v___x_2845_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2849_; double v___x_2850_; 
v___x_2849_ = lean_unsigned_to_nat(0u);
v___x_2850_ = lean_float_of_nat(v___x_2849_);
return v___x_2850_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2853_, lean_object* v_msg_2854_, lean_object* v___y_2855_, lean_object* v___y_2856_, lean_object* v___y_2857_, lean_object* v___y_2858_){
_start:
{
lean_object* v_ref_2860_; lean_object* v___x_2861_; lean_object* v_a_2862_; lean_object* v___x_2864_; uint8_t v_isShared_2865_; uint8_t v_isSharedCheck_2907_; 
v_ref_2860_ = lean_ctor_get(v___y_2857_, 2);
v___x_2861_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2854_, v___y_2855_, v___y_2856_, v___y_2857_, v___y_2858_);
v_a_2862_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2907_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2907_ == 0)
{
v___x_2864_ = v___x_2861_;
v_isShared_2865_ = v_isSharedCheck_2907_;
goto v_resetjp_2863_;
}
else
{
lean_inc(v_a_2862_);
lean_dec(v___x_2861_);
v___x_2864_ = lean_box(0);
v_isShared_2865_ = v_isSharedCheck_2907_;
goto v_resetjp_2863_;
}
v_resetjp_2863_:
{
lean_object* v___x_2866_; lean_object* v_traceState_2867_; lean_object* v_env_2868_; lean_object* v_nextMacroScope_2869_; lean_object* v_ngen_2870_; lean_object* v_auxDeclNGen_2871_; lean_object* v_cache_2872_; lean_object* v_recordedDeps_2873_; lean_object* v_messages_2874_; lean_object* v_infoState_2875_; lean_object* v_snapshotTasks_2876_; lean_object* v___x_2878_; uint8_t v_isShared_2879_; uint8_t v_isSharedCheck_2906_; 
v___x_2866_ = lean_st_ref_take(v___y_2858_);
v_traceState_2867_ = lean_ctor_get(v___x_2866_, 4);
v_env_2868_ = lean_ctor_get(v___x_2866_, 0);
v_nextMacroScope_2869_ = lean_ctor_get(v___x_2866_, 1);
v_ngen_2870_ = lean_ctor_get(v___x_2866_, 2);
v_auxDeclNGen_2871_ = lean_ctor_get(v___x_2866_, 3);
v_cache_2872_ = lean_ctor_get(v___x_2866_, 5);
v_recordedDeps_2873_ = lean_ctor_get(v___x_2866_, 6);
v_messages_2874_ = lean_ctor_get(v___x_2866_, 7);
v_infoState_2875_ = lean_ctor_get(v___x_2866_, 8);
v_snapshotTasks_2876_ = lean_ctor_get(v___x_2866_, 9);
v_isSharedCheck_2906_ = !lean_is_exclusive(v___x_2866_);
if (v_isSharedCheck_2906_ == 0)
{
v___x_2878_ = v___x_2866_;
v_isShared_2879_ = v_isSharedCheck_2906_;
goto v_resetjp_2877_;
}
else
{
lean_inc(v_snapshotTasks_2876_);
lean_inc(v_infoState_2875_);
lean_inc(v_messages_2874_);
lean_inc(v_recordedDeps_2873_);
lean_inc(v_cache_2872_);
lean_inc(v_traceState_2867_);
lean_inc(v_auxDeclNGen_2871_);
lean_inc(v_ngen_2870_);
lean_inc(v_nextMacroScope_2869_);
lean_inc(v_env_2868_);
lean_dec(v___x_2866_);
v___x_2878_ = lean_box(0);
v_isShared_2879_ = v_isSharedCheck_2906_;
goto v_resetjp_2877_;
}
v_resetjp_2877_:
{
uint64_t v_tid_2880_; lean_object* v_traces_2881_; lean_object* v___x_2883_; uint8_t v_isShared_2884_; uint8_t v_isSharedCheck_2905_; 
v_tid_2880_ = lean_ctor_get_uint64(v_traceState_2867_, sizeof(void*)*1);
v_traces_2881_ = lean_ctor_get(v_traceState_2867_, 0);
v_isSharedCheck_2905_ = !lean_is_exclusive(v_traceState_2867_);
if (v_isSharedCheck_2905_ == 0)
{
v___x_2883_ = v_traceState_2867_;
v_isShared_2884_ = v_isSharedCheck_2905_;
goto v_resetjp_2882_;
}
else
{
lean_inc(v_traces_2881_);
lean_dec(v_traceState_2867_);
v___x_2883_ = lean_box(0);
v_isShared_2884_ = v_isSharedCheck_2905_;
goto v_resetjp_2882_;
}
v_resetjp_2882_:
{
lean_object* v___x_2885_; lean_object* v___x_2886_; double v___x_2887_; uint8_t v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2896_; 
v___x_2885_ = lean_box(0);
v___x_2886_ = lean_box(0);
v___x_2887_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2888_ = 0;
v___x_2889_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___x_2890_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2890_, 0, v_cls_2853_);
lean_ctor_set(v___x_2890_, 1, v___x_2886_);
lean_ctor_set(v___x_2890_, 2, v___x_2889_);
lean_ctor_set_float(v___x_2890_, sizeof(void*)*3, v___x_2887_);
lean_ctor_set_float(v___x_2890_, sizeof(void*)*3 + 8, v___x_2887_);
lean_ctor_set_uint8(v___x_2890_, sizeof(void*)*3 + 16, v___x_2888_);
v___x_2891_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2892_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2892_, 0, v___x_2890_);
lean_ctor_set(v___x_2892_, 1, v_a_2862_);
lean_ctor_set(v___x_2892_, 2, v___x_2891_);
lean_inc(v_ref_2860_);
v___x_2893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2893_, 0, v_ref_2860_);
lean_ctor_set(v___x_2893_, 1, v___x_2892_);
v___x_2894_ = l_Lean_PersistentArray_push___redArg(v_traces_2881_, v___x_2893_);
if (v_isShared_2884_ == 0)
{
lean_ctor_set(v___x_2883_, 0, v___x_2894_);
v___x_2896_ = v___x_2883_;
goto v_reusejp_2895_;
}
else
{
lean_object* v_reuseFailAlloc_2904_; 
v_reuseFailAlloc_2904_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2904_, 0, v___x_2894_);
lean_ctor_set_uint64(v_reuseFailAlloc_2904_, sizeof(void*)*1, v_tid_2880_);
v___x_2896_ = v_reuseFailAlloc_2904_;
goto v_reusejp_2895_;
}
v_reusejp_2895_:
{
lean_object* v___x_2898_; 
if (v_isShared_2879_ == 0)
{
lean_ctor_set(v___x_2878_, 4, v___x_2896_);
v___x_2898_ = v___x_2878_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2903_; 
v_reuseFailAlloc_2903_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_2903_, 0, v_env_2868_);
lean_ctor_set(v_reuseFailAlloc_2903_, 1, v_nextMacroScope_2869_);
lean_ctor_set(v_reuseFailAlloc_2903_, 2, v_ngen_2870_);
lean_ctor_set(v_reuseFailAlloc_2903_, 3, v_auxDeclNGen_2871_);
lean_ctor_set(v_reuseFailAlloc_2903_, 4, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2903_, 5, v_cache_2872_);
lean_ctor_set(v_reuseFailAlloc_2903_, 6, v_recordedDeps_2873_);
lean_ctor_set(v_reuseFailAlloc_2903_, 7, v_messages_2874_);
lean_ctor_set(v_reuseFailAlloc_2903_, 8, v_infoState_2875_);
lean_ctor_set(v_reuseFailAlloc_2903_, 9, v_snapshotTasks_2876_);
v___x_2898_ = v_reuseFailAlloc_2903_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2899_; lean_object* v___x_2901_; 
v___x_2899_ = lean_st_ref_put(v___y_2858_, v___x_2898_);
if (v_isShared_2865_ == 0)
{
lean_ctor_set(v___x_2864_, 0, v___x_2885_);
v___x_2901_ = v___x_2864_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2902_; 
v_reuseFailAlloc_2902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2902_, 0, v___x_2885_);
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
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2908_, lean_object* v_msg_2909_, lean_object* v___y_2910_, lean_object* v___y_2911_, lean_object* v___y_2912_, lean_object* v___y_2913_, lean_object* v___y_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2908_, v_msg_2909_, v___y_2910_, v___y_2911_, v___y_2912_, v___y_2913_);
lean_dec(v___y_2913_);
lean_dec_ref(v___y_2912_);
lean_dec(v___y_2911_);
lean_dec_ref(v___y_2910_);
return v_res_2915_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; 
v___x_2923_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2924_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2925_ = l_Lean_Name_append(v___x_2924_, v___x_2923_);
return v___x_2925_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2927_; lean_object* v___x_2928_; 
v___x_2927_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2928_ = l_Lean_stringToMessageData(v___x_2927_);
return v___x_2928_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2930_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2931_ = l_Lean_stringToMessageData(v___x_2930_);
return v___x_2931_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2933_; lean_object* v___x_2934_; 
v___x_2933_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2934_ = l_Lean_stringToMessageData(v___x_2933_);
return v___x_2934_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2936_; lean_object* v___x_2937_; 
v___x_2936_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2937_ = l_Lean_stringToMessageData(v___x_2936_);
return v___x_2937_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2938_, lean_object* v_fst_2939_, lean_object* v_fst_2940_, lean_object* v_inst_2941_, lean_object* v_a_2942_, lean_object* v_projInfo_x3f_2943_, lean_object* v_argVars_2944_, lean_object* v_x_2945_, lean_object* v___y_2946_, lean_object* v___y_2947_, lean_object* v___y_2948_, lean_object* v___y_2949_){
_start:
{
lean_object* v___x_2951_; 
v___x_2951_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2938_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2951_) == 0)
{
lean_object* v_a_2952_; lean_object* v_dummy_2953_; lean_object* v_nargs_2954_; lean_object* v___x_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2958_; lean_object* v___x_2959_; lean_object* v___x_2960_; lean_object* v___x_2961_; size_t v_sz_2962_; size_t v___x_2963_; lean_object* v___x_2964_; 
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
lean_inc(v_a_2952_);
lean_dec_ref_known(v___x_2951_, 1);
v_dummy_2953_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2954_ = l_Lean_Expr_getAppNumArgs(v_a_2938_);
lean_inc(v_nargs_2954_);
v___x_2955_ = lean_mk_array(v_nargs_2954_, v_dummy_2953_);
v___x_2956_ = lean_unsigned_to_nat(1u);
v___x_2957_ = lean_nat_sub(v_nargs_2954_, v___x_2956_);
lean_dec(v_nargs_2954_);
lean_inc_ref(v_a_2938_);
v___x_2958_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2938_, v___x_2955_, v___x_2957_);
v___x_2959_ = lean_array_get_size(v___x_2958_);
v___x_2960_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2961_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2961_, 0, v___x_2960_);
lean_ctor_set(v___x_2961_, 1, v___x_2959_);
v_sz_2962_ = lean_array_size(v___x_2958_);
v___x_2963_ = ((size_t)0ULL);
v___x_2964_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2952_, v_fst_2939_, v_argVars_2944_, v___x_2958_, v_sz_2962_, v___x_2963_, v___x_2961_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
lean_dec_ref(v___x_2958_);
lean_dec(v_a_2952_);
if (lean_obj_tag(v___x_2964_) == 0)
{
lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; lean_object* v___x_2970_; lean_object* v___x_2971_; lean_object* v___x_2972_; 
lean_dec_ref_known(v___x_2964_, 1);
v___x_2965_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2966_ = lean_array_get_size(v_fst_2939_);
v___x_2967_ = l_List_range(v___x_2966_);
v___x_2968_ = lean_box(0);
v___x_2969_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2940_, v___x_2967_, v___x_2968_);
v___x_2970_ = lean_array_mk(v___x_2969_);
v___x_2971_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2971_, 0, v___x_2965_);
lean_ctor_set(v___x_2971_, 1, v___x_2970_);
lean_inc_ref(v_inst_2941_);
lean_inc_ref(v_argVars_2944_);
v___x_2972_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2939_, v_argVars_2944_, v_inst_2941_, v_a_2942_, v_projInfo_x3f_2943_, v___x_2971_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
if (lean_obj_tag(v___x_2972_) == 0)
{
lean_object* v_a_2973_; lean_object* v___x_2975_; uint8_t v_isShared_2976_; uint8_t v_isSharedCheck_3065_; 
v_a_2973_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3065_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3065_ == 0)
{
v___x_2975_ = v___x_2972_;
v_isShared_2976_ = v_isSharedCheck_3065_;
goto v_resetjp_2974_;
}
else
{
lean_inc(v_a_2973_);
lean_dec(v___x_2972_);
v___x_2975_ = lean_box(0);
v_isShared_2976_ = v_isSharedCheck_3065_;
goto v_resetjp_2974_;
}
v_resetjp_2974_:
{
lean_object* v_fst_2977_; lean_object* v___x_2979_; uint8_t v_isShared_2980_; uint8_t v_isSharedCheck_3063_; 
v_fst_2977_ = lean_ctor_get(v_a_2973_, 0);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_a_2973_);
if (v_isSharedCheck_3063_ == 0)
{
lean_object* v_unused_3064_; 
v_unused_3064_ = lean_ctor_get(v_a_2973_, 1);
lean_dec(v_unused_3064_);
v___x_2979_ = v_a_2973_;
v_isShared_2980_ = v_isSharedCheck_3063_;
goto v_resetjp_2978_;
}
else
{
lean_inc(v_fst_2977_);
lean_dec(v_a_2973_);
v___x_2979_ = lean_box(0);
v_isShared_2980_ = v_isSharedCheck_3063_;
goto v_resetjp_2978_;
}
v_resetjp_2978_:
{
lean_object* v___y_2982_; lean_object* v___y_2983_; lean_object* v___y_2984_; lean_object* v___y_2985_; lean_object* v___x_3044_; lean_object* v___x_3045_; uint8_t v___x_3046_; 
v___x_3044_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2948_);
v___x_3045_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_3046_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_3044_, v___x_3045_);
lean_dec_ref(v___x_3044_);
if (v___x_3046_ == 0)
{
lean_dec_ref(v_a_2938_);
v___y_2982_ = v___y_2946_;
v___y_2983_ = v___y_2947_;
v___y_2984_ = v___y_2948_;
v___y_2985_ = v___y_2949_;
goto v___jp_2981_;
}
else
{
lean_object* v___x_3047_; lean_object* v_a_3048_; uint8_t v___x_3049_; 
v___x_3047_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2938_, v___y_2947_);
v_a_3048_ = lean_ctor_get(v___x_3047_, 0);
lean_inc(v_a_3048_);
lean_dec_ref(v___x_3047_);
v___x_3049_ = l_Lean_Expr_hasExprMVar(v_a_3048_);
if (v___x_3049_ == 0)
{
lean_dec(v_a_3048_);
v___y_2982_ = v___y_2946_;
v___y_2983_ = v___y_2947_;
v___y_2984_ = v___y_2948_;
v___y_2985_ = v___y_2949_;
goto v___jp_2981_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; lean_object* v___x_3052_; lean_object* v___x_3053_; lean_object* v___x_3054_; lean_object* v_a_3055_; lean_object* v___x_3057_; uint8_t v_isShared_3058_; uint8_t v_isSharedCheck_3062_; 
lean_del_object(v___x_2979_);
lean_dec(v_fst_2977_);
lean_del_object(v___x_2975_);
lean_dec_ref(v_argVars_2944_);
lean_dec_ref(v_inst_2941_);
v___x_3050_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_3051_ = l_Lean_Expr_setPPExplicit(v_a_3048_, v___x_3046_);
v___x_3052_ = l_Lean_indentExpr(v___x_3051_);
v___x_3053_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3053_, 0, v___x_3050_);
lean_ctor_set(v___x_3053_, 1, v___x_3052_);
v___x_3054_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3053_, v___y_2946_, v___y_2947_, v___y_2948_, v___y_2949_);
v_a_3055_ = lean_ctor_get(v___x_3054_, 0);
v_isSharedCheck_3062_ = !lean_is_exclusive(v___x_3054_);
if (v_isSharedCheck_3062_ == 0)
{
v___x_3057_ = v___x_3054_;
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
else
{
lean_inc(v_a_3055_);
lean_dec(v___x_3054_);
v___x_3057_ = lean_box(0);
v_isShared_3058_ = v_isSharedCheck_3062_;
goto v_resetjp_3056_;
}
v_resetjp_3056_:
{
lean_object* v___x_3060_; 
if (v_isShared_3058_ == 0)
{
v___x_3060_ = v___x_3057_;
goto v_reusejp_3059_;
}
else
{
lean_object* v_reuseFailAlloc_3061_; 
v_reuseFailAlloc_3061_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3061_, 0, v_a_3055_);
v___x_3060_ = v_reuseFailAlloc_3061_;
goto v_reusejp_3059_;
}
v_reusejp_3059_:
{
return v___x_3060_;
}
}
}
}
v___jp_2981_:
{
lean_object* v_toCold_2986_; lean_object* v_options_2987_; uint8_t v_hasTrace_2988_; 
v_toCold_2986_ = lean_ctor_get(v___y_2984_, 0);
v_options_2987_ = lean_ctor_get(v_toCold_2986_, 2);
v_hasTrace_2988_ = lean_ctor_get_uint8(v_options_2987_, sizeof(void*)*1);
if (v_hasTrace_2988_ == 0)
{
lean_object* v___x_2990_; 
lean_del_object(v___x_2979_);
lean_dec_ref(v_argVars_2944_);
lean_dec_ref(v_inst_2941_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v_fst_2977_);
v___x_2990_ = v___x_2975_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_2991_; 
v_reuseFailAlloc_2991_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2991_, 0, v_fst_2977_);
v___x_2990_ = v_reuseFailAlloc_2991_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
return v___x_2990_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; uint8_t v___x_2995_; 
v_inheritedTraceOptions_2992_ = lean_ctor_get(v_toCold_2986_, 11);
v___x_2993_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2994_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2995_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2992_, v_options_2987_, v___x_2994_);
if (v___x_2995_ == 0)
{
lean_object* v___x_2997_; 
lean_del_object(v___x_2979_);
lean_dec_ref(v_argVars_2944_);
lean_dec_ref(v_inst_2941_);
if (v_isShared_2976_ == 0)
{
lean_ctor_set(v___x_2975_, 0, v_fst_2977_);
v___x_2997_ = v___x_2975_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_fst_2977_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
else
{
size_t v_sz_2999_; lean_object* v___x_3000_; 
lean_del_object(v___x_2975_);
v_sz_2999_ = lean_array_size(v_fst_2977_);
lean_inc(v_fst_2977_);
v___x_3000_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2944_, v_sz_2999_, v___x_2963_, v_fst_2977_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
lean_dec_ref(v_argVars_2944_);
if (lean_obj_tag(v___x_3000_) == 0)
{
lean_object* v_a_3001_; lean_object* v___x_3002_; lean_object* v___x_3003_; lean_object* v___x_3005_; 
v_a_3001_ = lean_ctor_get(v___x_3000_, 0);
lean_inc(v_a_3001_);
lean_dec_ref_known(v___x_3000_, 1);
v___x_3002_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_3003_ = l_Lean_MessageData_ofExpr(v_inst_2941_);
if (v_isShared_2980_ == 0)
{
lean_ctor_set_tag(v___x_2979_, 7);
lean_ctor_set(v___x_2979_, 1, v___x_3003_);
lean_ctor_set(v___x_2979_, 0, v___x_3002_);
v___x_3005_ = v___x_2979_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v___x_3002_);
lean_ctor_set(v_reuseFailAlloc_3035_, 1, v___x_3003_);
v___x_3005_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
lean_object* v___x_3006_; lean_object* v___x_3007_; lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; 
v___x_3006_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_3007_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3007_, 0, v___x_3005_);
lean_ctor_set(v___x_3007_, 1, v___x_3006_);
lean_inc(v_fst_2977_);
v___x_3008_ = lean_array_to_list(v_fst_2977_);
v___x_3009_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_3008_, v___x_2968_);
v___x_3010_ = l_Lean_MessageData_ofList(v___x_3009_);
v___x_3011_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3011_, 0, v___x_3007_);
lean_ctor_set(v___x_3011_, 1, v___x_3010_);
v___x_3012_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_3013_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3013_, 0, v___x_3011_);
lean_ctor_set(v___x_3013_, 1, v___x_3012_);
v___x_3014_ = lean_array_to_list(v_a_3001_);
v___x_3015_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_3016_ = l_Lean_MessageData_joinSep(v___x_3014_, v___x_3015_);
v___x_3017_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3013_);
lean_ctor_set(v___x_3017_, 1, v___x_3016_);
v___x_3018_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2993_, v___x_3017_, v___y_2982_, v___y_2983_, v___y_2984_, v___y_2985_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v___x_3020_; uint8_t v_isShared_3021_; uint8_t v_isSharedCheck_3025_; 
v_isSharedCheck_3025_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3025_ == 0)
{
lean_object* v_unused_3026_; 
v_unused_3026_ = lean_ctor_get(v___x_3018_, 0);
lean_dec(v_unused_3026_);
v___x_3020_ = v___x_3018_;
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
else
{
lean_dec(v___x_3018_);
v___x_3020_ = lean_box(0);
v_isShared_3021_ = v_isSharedCheck_3025_;
goto v_resetjp_3019_;
}
v_resetjp_3019_:
{
lean_object* v___x_3023_; 
if (v_isShared_3021_ == 0)
{
lean_ctor_set(v___x_3020_, 0, v_fst_2977_);
v___x_3023_ = v___x_3020_;
goto v_reusejp_3022_;
}
else
{
lean_object* v_reuseFailAlloc_3024_; 
v_reuseFailAlloc_3024_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3024_, 0, v_fst_2977_);
v___x_3023_ = v_reuseFailAlloc_3024_;
goto v_reusejp_3022_;
}
v_reusejp_3022_:
{
return v___x_3023_;
}
}
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_fst_2977_);
v_a_3027_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3018_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3018_);
v___x_3029_ = lean_box(0);
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
v_resetjp_3028_:
{
lean_object* v___x_3032_; 
if (v_isShared_3030_ == 0)
{
v___x_3032_ = v___x_3029_;
goto v_reusejp_3031_;
}
else
{
lean_object* v_reuseFailAlloc_3033_; 
v_reuseFailAlloc_3033_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3033_, 0, v_a_3027_);
v___x_3032_ = v_reuseFailAlloc_3033_;
goto v_reusejp_3031_;
}
v_reusejp_3031_:
{
return v___x_3032_;
}
}
}
}
}
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_del_object(v___x_2979_);
lean_dec(v_fst_2977_);
lean_dec_ref(v_inst_2941_);
v_a_3036_ = lean_ctor_get(v___x_3000_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3000_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3000_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3000_);
v___x_3038_ = lean_box(0);
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
v_resetjp_3037_:
{
lean_object* v___x_3041_; 
if (v_isShared_3039_ == 0)
{
v___x_3041_ = v___x_3038_;
goto v_reusejp_3040_;
}
else
{
lean_object* v_reuseFailAlloc_3042_; 
v_reuseFailAlloc_3042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3042_, 0, v_a_3036_);
v___x_3041_ = v_reuseFailAlloc_3042_;
goto v_reusejp_3040_;
}
v_reusejp_3040_:
{
return v___x_3041_;
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
lean_object* v_a_3066_; lean_object* v___x_3068_; uint8_t v_isShared_3069_; uint8_t v_isSharedCheck_3073_; 
lean_dec_ref(v_argVars_2944_);
lean_dec_ref(v_inst_2941_);
lean_dec_ref(v_a_2938_);
v_a_3066_ = lean_ctor_get(v___x_2972_, 0);
v_isSharedCheck_3073_ = !lean_is_exclusive(v___x_2972_);
if (v_isSharedCheck_3073_ == 0)
{
v___x_3068_ = v___x_2972_;
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
else
{
lean_inc(v_a_3066_);
lean_dec(v___x_2972_);
v___x_3068_ = lean_box(0);
v_isShared_3069_ = v_isSharedCheck_3073_;
goto v_resetjp_3067_;
}
v_resetjp_3067_:
{
lean_object* v___x_3071_; 
if (v_isShared_3069_ == 0)
{
v___x_3071_ = v___x_3068_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3072_; 
v_reuseFailAlloc_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3072_, 0, v_a_3066_);
v___x_3071_ = v_reuseFailAlloc_3072_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
return v___x_3071_;
}
}
}
}
else
{
lean_object* v_a_3074_; lean_object* v___x_3076_; uint8_t v_isShared_3077_; uint8_t v_isSharedCheck_3081_; 
lean_dec_ref(v_argVars_2944_);
lean_dec_ref(v_a_2942_);
lean_dec_ref(v_inst_2941_);
lean_dec_ref(v_fst_2939_);
lean_dec_ref(v_a_2938_);
v_a_3074_ = lean_ctor_get(v___x_2964_, 0);
v_isSharedCheck_3081_ = !lean_is_exclusive(v___x_2964_);
if (v_isSharedCheck_3081_ == 0)
{
v___x_3076_ = v___x_2964_;
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
else
{
lean_inc(v_a_3074_);
lean_dec(v___x_2964_);
v___x_3076_ = lean_box(0);
v_isShared_3077_ = v_isSharedCheck_3081_;
goto v_resetjp_3075_;
}
v_resetjp_3075_:
{
lean_object* v___x_3079_; 
if (v_isShared_3077_ == 0)
{
v___x_3079_ = v___x_3076_;
goto v_reusejp_3078_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v_a_3074_);
v___x_3079_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3078_;
}
v_reusejp_3078_:
{
return v___x_3079_;
}
}
}
}
else
{
lean_dec_ref(v_argVars_2944_);
lean_dec_ref(v_a_2942_);
lean_dec_ref(v_inst_2941_);
lean_dec_ref(v_fst_2939_);
lean_dec_ref(v_a_2938_);
return v___x_2951_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_3082_, lean_object* v_fst_3083_, lean_object* v_fst_3084_, lean_object* v_inst_3085_, lean_object* v_a_3086_, lean_object* v_projInfo_x3f_3087_, lean_object* v_argVars_3088_, lean_object* v_x_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_3082_, v_fst_3083_, v_fst_3084_, v_inst_3085_, v_a_3086_, v_projInfo_x3f_3087_, v_argVars_3088_, v_x_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
lean_dec(v___y_3093_);
lean_dec_ref(v___y_3092_);
lean_dec(v___y_3091_);
lean_dec_ref(v___y_3090_);
lean_dec_ref(v_x_3089_);
lean_dec(v_projInfo_x3f_3087_);
lean_dec_ref(v_fst_3084_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(lean_object* v_inst_3096_, lean_object* v_projInfo_x3f_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v___x_3103_; 
lean_inc(v___y_3101_);
lean_inc_ref(v___y_3100_);
lean_inc(v___y_3099_);
lean_inc_ref(v___y_3098_);
lean_inc_ref(v_inst_3096_);
v___x_3103_ = lean_infer_type(v_inst_3096_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3103_) == 0)
{
lean_object* v_a_3104_; lean_object* v___x_3105_; uint8_t v___x_3106_; lean_object* v___x_3107_; 
v_a_3104_ = lean_ctor_get(v___x_3103_, 0);
lean_inc_n(v_a_3104_, 2);
lean_dec_ref_known(v___x_3103_, 1);
v___x_3105_ = lean_box(0);
v___x_3106_ = 0;
v___x_3107_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3104_, v___x_3105_, v___x_3106_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3107_) == 0)
{
lean_object* v_a_3108_; lean_object* v_snd_3109_; lean_object* v_fst_3110_; lean_object* v_fst_3111_; lean_object* v_snd_3112_; lean_object* v___x_3113_; 
v_a_3108_ = lean_ctor_get(v___x_3107_, 0);
lean_inc(v_a_3108_);
lean_dec_ref_known(v___x_3107_, 1);
v_snd_3109_ = lean_ctor_get(v_a_3108_, 1);
lean_inc(v_snd_3109_);
v_fst_3110_ = lean_ctor_get(v_a_3108_, 0);
lean_inc(v_fst_3110_);
lean_dec(v_a_3108_);
v_fst_3111_ = lean_ctor_get(v_snd_3109_, 0);
lean_inc(v_fst_3111_);
v_snd_3112_ = lean_ctor_get(v_snd_3109_, 1);
lean_inc(v_snd_3112_);
lean_dec(v_snd_3109_);
lean_inc(v___y_3101_);
lean_inc_ref(v___y_3100_);
lean_inc(v___y_3099_);
lean_inc_ref(v___y_3098_);
v___x_3113_ = lean_whnf(v_snd_3112_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
if (lean_obj_tag(v___x_3113_) == 0)
{
lean_object* v_a_3114_; lean_object* v___f_3115_; uint8_t v___x_3116_; lean_object* v___x_3117_; 
v_a_3114_ = lean_ctor_get(v___x_3113_, 0);
lean_inc(v_a_3114_);
lean_dec_ref_known(v___x_3113_, 1);
lean_inc(v_a_3104_);
v___f_3115_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3115_, 0, v_a_3114_);
lean_closure_set(v___f_3115_, 1, v_fst_3110_);
lean_closure_set(v___f_3115_, 2, v_fst_3111_);
lean_closure_set(v___f_3115_, 3, v_inst_3096_);
lean_closure_set(v___f_3115_, 4, v_a_3104_);
lean_closure_set(v___f_3115_, 5, v_projInfo_x3f_3097_);
v___x_3116_ = 0;
v___x_3117_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3104_, v___f_3115_, v___x_3116_, v___x_3116_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
return v___x_3117_;
}
else
{
lean_object* v_a_3118_; lean_object* v___x_3120_; uint8_t v_isShared_3121_; uint8_t v_isSharedCheck_3125_; 
lean_dec(v_fst_3111_);
lean_dec(v_fst_3110_);
lean_dec(v_a_3104_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v_projInfo_x3f_3097_);
lean_dec_ref(v_inst_3096_);
v_a_3118_ = lean_ctor_get(v___x_3113_, 0);
v_isSharedCheck_3125_ = !lean_is_exclusive(v___x_3113_);
if (v_isSharedCheck_3125_ == 0)
{
v___x_3120_ = v___x_3113_;
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
else
{
lean_inc(v_a_3118_);
lean_dec(v___x_3113_);
v___x_3120_ = lean_box(0);
v_isShared_3121_ = v_isSharedCheck_3125_;
goto v_resetjp_3119_;
}
v_resetjp_3119_:
{
lean_object* v___x_3123_; 
if (v_isShared_3121_ == 0)
{
v___x_3123_ = v___x_3120_;
goto v_reusejp_3122_;
}
else
{
lean_object* v_reuseFailAlloc_3124_; 
v_reuseFailAlloc_3124_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3124_, 0, v_a_3118_);
v___x_3123_ = v_reuseFailAlloc_3124_;
goto v_reusejp_3122_;
}
v_reusejp_3122_:
{
return v___x_3123_;
}
}
}
}
else
{
lean_object* v_a_3126_; lean_object* v___x_3128_; uint8_t v_isShared_3129_; uint8_t v_isSharedCheck_3133_; 
lean_dec(v_a_3104_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v_projInfo_x3f_3097_);
lean_dec_ref(v_inst_3096_);
v_a_3126_ = lean_ctor_get(v___x_3107_, 0);
v_isSharedCheck_3133_ = !lean_is_exclusive(v___x_3107_);
if (v_isSharedCheck_3133_ == 0)
{
v___x_3128_ = v___x_3107_;
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
else
{
lean_inc(v_a_3126_);
lean_dec(v___x_3107_);
v___x_3128_ = lean_box(0);
v_isShared_3129_ = v_isSharedCheck_3133_;
goto v_resetjp_3127_;
}
v_resetjp_3127_:
{
lean_object* v___x_3131_; 
if (v_isShared_3129_ == 0)
{
v___x_3131_ = v___x_3128_;
goto v_reusejp_3130_;
}
else
{
lean_object* v_reuseFailAlloc_3132_; 
v_reuseFailAlloc_3132_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3132_, 0, v_a_3126_);
v___x_3131_ = v_reuseFailAlloc_3132_;
goto v_reusejp_3130_;
}
v_reusejp_3130_:
{
return v___x_3131_;
}
}
}
}
else
{
lean_object* v_a_3134_; lean_object* v___x_3136_; uint8_t v_isShared_3137_; uint8_t v_isSharedCheck_3141_; 
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
lean_dec(v_projInfo_x3f_3097_);
lean_dec_ref(v_inst_3096_);
v_a_3134_ = lean_ctor_get(v___x_3103_, 0);
v_isSharedCheck_3141_ = !lean_is_exclusive(v___x_3103_);
if (v_isSharedCheck_3141_ == 0)
{
v___x_3136_ = v___x_3103_;
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
else
{
lean_inc(v_a_3134_);
lean_dec(v___x_3103_);
v___x_3136_ = lean_box(0);
v_isShared_3137_ = v_isSharedCheck_3141_;
goto v_resetjp_3135_;
}
v_resetjp_3135_:
{
lean_object* v___x_3139_; 
if (v_isShared_3137_ == 0)
{
v___x_3139_ = v___x_3136_;
goto v_reusejp_3138_;
}
else
{
lean_object* v_reuseFailAlloc_3140_; 
v_reuseFailAlloc_3140_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3140_, 0, v_a_3134_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1___boxed(lean_object* v_inst_3142_, lean_object* v_projInfo_x3f_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_){
_start:
{
lean_object* v_res_3149_; 
v_res_3149_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3142_, v_projInfo_x3f_3143_, v___y_3144_, v___y_3145_, v___y_3146_, v___y_3147_);
return v_res_3149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_3150_, lean_object* v_projInfo_x3f_3151_, lean_object* v_a_3152_, lean_object* v_a_3153_, lean_object* v_a_3154_, lean_object* v_a_3155_){
_start:
{
lean_object* v___y_3158_; lean_object* v___x_3175_; uint8_t v_transparency_3176_; uint8_t v___x_3177_; uint8_t v___x_3178_; 
v___x_3175_ = l_Lean_Meta_Context_config(v_a_3152_);
v_transparency_3176_ = lean_ctor_get_uint8(v___x_3175_, 9);
lean_dec_ref(v___x_3175_);
v___x_3177_ = 2;
v___x_3178_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3176_, v___x_3177_);
if (v___x_3178_ == 0)
{
lean_object* v_keyedConfig_3179_; uint8_t v_trackZetaDelta_3180_; lean_object* v_zetaDeltaSet_3181_; lean_object* v_lctx_3182_; lean_object* v_localInstances_3183_; lean_object* v_defEqCtx_x3f_3184_; lean_object* v_synthPendingDepth_3185_; lean_object* v_customCanUnfoldPredicate_x3f_3186_; uint8_t v_univApprox_3187_; uint8_t v_inTypeClassResolution_3188_; uint8_t v_cacheInferType_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v_keyedConfig_3179_ = lean_ctor_get(v_a_3152_, 0);
v_trackZetaDelta_3180_ = lean_ctor_get_uint8(v_a_3152_, sizeof(void*)*7);
v_zetaDeltaSet_3181_ = lean_ctor_get(v_a_3152_, 1);
v_lctx_3182_ = lean_ctor_get(v_a_3152_, 2);
v_localInstances_3183_ = lean_ctor_get(v_a_3152_, 3);
v_defEqCtx_x3f_3184_ = lean_ctor_get(v_a_3152_, 4);
v_synthPendingDepth_3185_ = lean_ctor_get(v_a_3152_, 5);
v_customCanUnfoldPredicate_x3f_3186_ = lean_ctor_get(v_a_3152_, 6);
v_univApprox_3187_ = lean_ctor_get_uint8(v_a_3152_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3188_ = lean_ctor_get_uint8(v_a_3152_, sizeof(void*)*7 + 2);
v_cacheInferType_3189_ = lean_ctor_get_uint8(v_a_3152_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3179_);
v___x_3190_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3177_, v_keyedConfig_3179_);
lean_inc(v_customCanUnfoldPredicate_x3f_3186_);
lean_inc(v_synthPendingDepth_3185_);
lean_inc(v_defEqCtx_x3f_3184_);
lean_inc_ref(v_localInstances_3183_);
lean_inc_ref(v_lctx_3182_);
lean_inc(v_zetaDeltaSet_3181_);
v___x_3191_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
lean_ctor_set(v___x_3191_, 1, v_zetaDeltaSet_3181_);
lean_ctor_set(v___x_3191_, 2, v_lctx_3182_);
lean_ctor_set(v___x_3191_, 3, v_localInstances_3183_);
lean_ctor_set(v___x_3191_, 4, v_defEqCtx_x3f_3184_);
lean_ctor_set(v___x_3191_, 5, v_synthPendingDepth_3185_);
lean_ctor_set(v___x_3191_, 6, v_customCanUnfoldPredicate_x3f_3186_);
lean_ctor_set_uint8(v___x_3191_, sizeof(void*)*7, v_trackZetaDelta_3180_);
lean_ctor_set_uint8(v___x_3191_, sizeof(void*)*7 + 1, v_univApprox_3187_);
lean_ctor_set_uint8(v___x_3191_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3188_);
lean_ctor_set_uint8(v___x_3191_, sizeof(void*)*7 + 3, v_cacheInferType_3189_);
lean_inc(v_a_3155_);
lean_inc_ref(v_a_3154_);
lean_inc(v_a_3153_);
v___x_3192_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3150_, v_projInfo_x3f_3151_, v___x_3191_, v_a_3153_, v_a_3154_, v_a_3155_);
v___y_3158_ = v___x_3192_;
goto v___jp_3157_;
}
else
{
lean_object* v___x_3193_; 
lean_inc(v_a_3155_);
lean_inc_ref(v_a_3154_);
lean_inc(v_a_3153_);
lean_inc_ref(v_a_3152_);
v___x_3193_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3150_, v_projInfo_x3f_3151_, v_a_3152_, v_a_3153_, v_a_3154_, v_a_3155_);
v___y_3158_ = v___x_3193_;
goto v___jp_3157_;
}
v___jp_3157_:
{
if (lean_obj_tag(v___y_3158_) == 0)
{
lean_object* v_a_3159_; lean_object* v___x_3161_; uint8_t v_isShared_3162_; uint8_t v_isSharedCheck_3166_; 
v_a_3159_ = lean_ctor_get(v___y_3158_, 0);
v_isSharedCheck_3166_ = !lean_is_exclusive(v___y_3158_);
if (v_isSharedCheck_3166_ == 0)
{
v___x_3161_ = v___y_3158_;
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
else
{
lean_inc(v_a_3159_);
lean_dec(v___y_3158_);
v___x_3161_ = lean_box(0);
v_isShared_3162_ = v_isSharedCheck_3166_;
goto v_resetjp_3160_;
}
v_resetjp_3160_:
{
lean_object* v___x_3164_; 
if (v_isShared_3162_ == 0)
{
v___x_3164_ = v___x_3161_;
goto v_reusejp_3163_;
}
else
{
lean_object* v_reuseFailAlloc_3165_; 
v_reuseFailAlloc_3165_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3165_, 0, v_a_3159_);
v___x_3164_ = v_reuseFailAlloc_3165_;
goto v_reusejp_3163_;
}
v_reusejp_3163_:
{
return v___x_3164_;
}
}
}
else
{
lean_object* v_a_3167_; lean_object* v___x_3169_; uint8_t v_isShared_3170_; uint8_t v_isSharedCheck_3174_; 
v_a_3167_ = lean_ctor_get(v___y_3158_, 0);
v_isSharedCheck_3174_ = !lean_is_exclusive(v___y_3158_);
if (v_isSharedCheck_3174_ == 0)
{
v___x_3169_ = v___y_3158_;
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
else
{
lean_inc(v_a_3167_);
lean_dec(v___y_3158_);
v___x_3169_ = lean_box(0);
v_isShared_3170_ = v_isSharedCheck_3174_;
goto v_resetjp_3168_;
}
v_resetjp_3168_:
{
lean_object* v___x_3172_; 
if (v_isShared_3170_ == 0)
{
v___x_3172_ = v___x_3169_;
goto v_reusejp_3171_;
}
else
{
lean_object* v_reuseFailAlloc_3173_; 
v_reuseFailAlloc_3173_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3173_, 0, v_a_3167_);
v___x_3172_ = v_reuseFailAlloc_3173_;
goto v_reusejp_3171_;
}
v_reusejp_3171_:
{
return v___x_3172_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_3194_, lean_object* v_projInfo_x3f_3195_, lean_object* v_a_3196_, lean_object* v_a_3197_, lean_object* v_a_3198_, lean_object* v_a_3199_, lean_object* v_a_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_3194_, v_projInfo_x3f_3195_, v_a_3196_, v_a_3197_, v_a_3198_, v_a_3199_);
lean_dec(v_a_3199_);
lean_dec_ref(v_a_3198_);
lean_dec(v_a_3197_);
lean_dec_ref(v_a_3196_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_3202_, lean_object* v_a_3203_, lean_object* v___x_3204_, lean_object* v_inst_3205_, lean_object* v_R_3206_, lean_object* v_a_3207_, lean_object* v_b_3208_, lean_object* v_c_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_, lean_object* v___y_3212_, lean_object* v___y_3213_){
_start:
{
lean_object* v___x_3215_; 
v___x_3215_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_3202_, v_a_3203_, v___x_3204_, v_a_3207_, v_b_3208_);
return v___x_3215_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_3216_, lean_object* v_a_3217_, lean_object* v___x_3218_, lean_object* v_inst_3219_, lean_object* v_R_3220_, lean_object* v_a_3221_, lean_object* v_b_3222_, lean_object* v_c_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_3216_, v_a_3217_, v___x_3218_, v_inst_3219_, v_R_3220_, v_a_3221_, v_b_3222_, v_c_3223_, v___y_3224_, v___y_3225_, v___y_3226_, v___y_3227_);
lean_dec(v___y_3227_);
lean_dec_ref(v___y_3226_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___x_3218_);
lean_dec_ref(v_a_3217_);
lean_dec(v_upperBound_3216_);
return v_res_3229_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3230_, lean_object* v_msg_3231_, lean_object* v___y_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_){
_start:
{
lean_object* v___x_3237_; 
v___x_3237_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3231_, v___y_3232_, v___y_3233_, v___y_3234_, v___y_3235_);
return v___x_3237_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3238_, lean_object* v_msg_3239_, lean_object* v___y_3240_, lean_object* v___y_3241_, lean_object* v___y_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_){
_start:
{
lean_object* v_res_3245_; 
v_res_3245_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3238_, v_msg_3239_, v___y_3240_, v___y_3241_, v___y_3242_, v___y_3243_);
lean_dec(v___y_3243_);
lean_dec_ref(v___y_3242_);
lean_dec(v___y_3241_);
lean_dec_ref(v___y_3240_);
return v_res_3245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_3246_, lean_object* v_argVars_3247_, lean_object* v_inst_3248_, lean_object* v_a_3249_, lean_object* v_projInfo_x3f_3250_, lean_object* v_inst_3251_, lean_object* v_a_3252_, lean_object* v___y_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_3246_, v_argVars_3247_, v_inst_3248_, v_a_3249_, v_projInfo_x3f_3250_, v_a_3252_, v___y_3253_, v___y_3254_, v___y_3255_, v___y_3256_);
return v___x_3258_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_3259_, lean_object* v_argVars_3260_, lean_object* v_inst_3261_, lean_object* v_a_3262_, lean_object* v_projInfo_x3f_3263_, lean_object* v_inst_3264_, lean_object* v_a_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_, lean_object* v___y_3268_, lean_object* v___y_3269_, lean_object* v___y_3270_){
_start:
{
lean_object* v_res_3271_; 
v_res_3271_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_3259_, v_argVars_3260_, v_inst_3261_, v_a_3262_, v_projInfo_x3f_3263_, v_inst_3264_, v_a_3265_, v___y_3266_, v___y_3267_, v___y_3268_, v___y_3269_);
lean_dec(v___y_3269_);
lean_dec_ref(v___y_3268_);
lean_dec(v___y_3267_);
lean_dec_ref(v___y_3266_);
lean_dec(v_projInfo_x3f_3263_);
return v_res_3271_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(lean_object* v_type_3272_, lean_object* v_k_3273_, uint8_t v_cleanupAnnotations_3274_, lean_object* v___y_3275_, lean_object* v___y_3276_, lean_object* v___y_3277_, lean_object* v___y_3278_){
_start:
{
lean_object* v___f_3280_; uint8_t v___x_3281_; lean_object* v___x_3282_; lean_object* v___x_3283_; 
v___f_3280_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3280_, 0, v_k_3273_);
v___x_3281_ = 0;
v___x_3282_ = lean_box(0);
v___x_3283_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3281_, v___x_3282_, v_type_3272_, v___f_3280_, v_cleanupAnnotations_3274_, v___x_3281_, v___y_3275_, v___y_3276_, v___y_3277_, v___y_3278_);
if (lean_obj_tag(v___x_3283_) == 0)
{
lean_object* v_a_3284_; lean_object* v___x_3286_; uint8_t v_isShared_3287_; uint8_t v_isSharedCheck_3291_; 
v_a_3284_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3291_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3291_ == 0)
{
v___x_3286_ = v___x_3283_;
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
else
{
lean_inc(v_a_3284_);
lean_dec(v___x_3283_);
v___x_3286_ = lean_box(0);
v_isShared_3287_ = v_isSharedCheck_3291_;
goto v_resetjp_3285_;
}
v_resetjp_3285_:
{
lean_object* v___x_3289_; 
if (v_isShared_3287_ == 0)
{
v___x_3289_ = v___x_3286_;
goto v_reusejp_3288_;
}
else
{
lean_object* v_reuseFailAlloc_3290_; 
v_reuseFailAlloc_3290_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3290_, 0, v_a_3284_);
v___x_3289_ = v_reuseFailAlloc_3290_;
goto v_reusejp_3288_;
}
v_reusejp_3288_:
{
return v___x_3289_;
}
}
}
else
{
lean_object* v_a_3292_; lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3299_; 
v_a_3292_ = lean_ctor_get(v___x_3283_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3283_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3294_ = v___x_3283_;
v_isShared_3295_ = v_isSharedCheck_3299_;
goto v_resetjp_3293_;
}
else
{
lean_inc(v_a_3292_);
lean_dec(v___x_3283_);
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
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg___boxed(lean_object* v_type_3300_, lean_object* v_k_3301_, lean_object* v_cleanupAnnotations_3302_, lean_object* v___y_3303_, lean_object* v___y_3304_, lean_object* v___y_3305_, lean_object* v___y_3306_, lean_object* v___y_3307_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3308_; lean_object* v_res_3309_; 
v_cleanupAnnotations_boxed_3308_ = lean_unbox(v_cleanupAnnotations_3302_);
v_res_3309_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3300_, v_k_3301_, v_cleanupAnnotations_boxed_3308_, v___y_3303_, v___y_3304_, v___y_3305_, v___y_3306_);
lean_dec(v___y_3306_);
lean_dec_ref(v___y_3305_);
lean_dec(v___y_3304_);
lean_dec_ref(v___y_3303_);
return v_res_3309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(lean_object* v_00_u03b1_3310_, lean_object* v_type_3311_, lean_object* v_k_3312_, uint8_t v_cleanupAnnotations_3313_, lean_object* v___y_3314_, lean_object* v___y_3315_, lean_object* v___y_3316_, lean_object* v___y_3317_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3311_, v_k_3312_, v_cleanupAnnotations_3313_, v___y_3314_, v___y_3315_, v___y_3316_, v___y_3317_);
return v___x_3319_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___boxed(lean_object* v_00_u03b1_3320_, lean_object* v_type_3321_, lean_object* v_k_3322_, lean_object* v_cleanupAnnotations_3323_, lean_object* v___y_3324_, lean_object* v___y_3325_, lean_object* v___y_3326_, lean_object* v___y_3327_, lean_object* v___y_3328_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3329_; lean_object* v_res_3330_; 
v_cleanupAnnotations_boxed_3329_ = lean_unbox(v_cleanupAnnotations_3323_);
v_res_3330_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(v_00_u03b1_3320_, v_type_3321_, v_k_3322_, v_cleanupAnnotations_boxed_3329_, v___y_3324_, v___y_3325_, v___y_3326_, v___y_3327_);
lean_dec(v___y_3327_);
lean_dec_ref(v___y_3326_);
lean_dec(v___y_3325_);
lean_dec_ref(v___y_3324_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(lean_object* v_as_3331_, size_t v_sz_3332_, size_t v_i_3333_, lean_object* v_b_3334_, lean_object* v___y_3335_, lean_object* v___y_3336_, lean_object* v___y_3337_, lean_object* v___y_3338_){
_start:
{
lean_object* v_a_3341_; uint8_t v___x_3345_; 
v___x_3345_ = lean_usize_dec_lt(v_i_3333_, v_sz_3332_);
if (v___x_3345_ == 0)
{
lean_object* v___x_3346_; 
v___x_3346_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3346_, 0, v_b_3334_);
return v___x_3346_;
}
else
{
lean_object* v___x_3347_; lean_object* v_a_3348_; lean_object* v___x_3349_; lean_object* v___x_3350_; 
v___x_3347_ = lean_box(0);
v_a_3348_ = lean_array_uget_borrowed(v_as_3331_, v_i_3333_);
v___x_3349_ = l_Lean_Expr_fvarId_x21(v_a_3348_);
lean_inc(v___x_3349_);
v___x_3350_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_3349_, v___y_3336_, v___y_3337_, v___y_3338_);
if (lean_obj_tag(v___x_3350_) == 0)
{
lean_object* v_a_3351_; uint8_t v___x_3352_; uint8_t v___x_3353_; 
v_a_3351_ = lean_ctor_get(v___x_3350_, 0);
lean_inc(v_a_3351_);
lean_dec_ref_known(v___x_3350_, 1);
v___x_3352_ = lean_unbox(v_a_3351_);
lean_dec(v_a_3351_);
v___x_3353_ = l_Lean_BinderInfo_isInstImplicit(v___x_3352_);
if (v___x_3353_ == 0)
{
lean_dec(v___x_3349_);
v_a_3341_ = v___x_3347_;
goto v___jp_3340_;
}
else
{
lean_object* v___x_3354_; lean_object* v___x_3355_; lean_object* v___x_3356_; 
v___x_3354_ = lean_st_ref_take(v___y_3335_);
v___x_3355_ = l_Lean_CollectFVars_State_add(v___x_3354_, v___x_3349_);
v___x_3356_ = lean_st_ref_put(v___y_3335_, v___x_3355_);
v_a_3341_ = v___x_3347_;
goto v___jp_3340_;
}
}
else
{
lean_object* v_a_3357_; lean_object* v___x_3359_; uint8_t v_isShared_3360_; uint8_t v_isSharedCheck_3364_; 
lean_dec(v___x_3349_);
v_a_3357_ = lean_ctor_get(v___x_3350_, 0);
v_isSharedCheck_3364_ = !lean_is_exclusive(v___x_3350_);
if (v_isSharedCheck_3364_ == 0)
{
v___x_3359_ = v___x_3350_;
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
else
{
lean_inc(v_a_3357_);
lean_dec(v___x_3350_);
v___x_3359_ = lean_box(0);
v_isShared_3360_ = v_isSharedCheck_3364_;
goto v_resetjp_3358_;
}
v_resetjp_3358_:
{
lean_object* v___x_3362_; 
if (v_isShared_3360_ == 0)
{
v___x_3362_ = v___x_3359_;
goto v_reusejp_3361_;
}
else
{
lean_object* v_reuseFailAlloc_3363_; 
v_reuseFailAlloc_3363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3363_, 0, v_a_3357_);
v___x_3362_ = v_reuseFailAlloc_3363_;
goto v_reusejp_3361_;
}
v_reusejp_3361_:
{
return v___x_3362_;
}
}
}
}
v___jp_3340_:
{
size_t v___x_3342_; size_t v___x_3343_; 
v___x_3342_ = ((size_t)1ULL);
v___x_3343_ = lean_usize_add(v_i_3333_, v___x_3342_);
v_i_3333_ = v___x_3343_;
v_b_3334_ = v_a_3341_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg___boxed(lean_object* v_as_3365_, lean_object* v_sz_3366_, lean_object* v_i_3367_, lean_object* v_b_3368_, lean_object* v___y_3369_, lean_object* v___y_3370_, lean_object* v___y_3371_, lean_object* v___y_3372_, lean_object* v___y_3373_){
_start:
{
size_t v_sz_boxed_3374_; size_t v_i_boxed_3375_; lean_object* v_res_3376_; 
v_sz_boxed_3374_ = lean_unbox_usize(v_sz_3366_);
lean_dec(v_sz_3366_);
v_i_boxed_3375_ = lean_unbox_usize(v_i_3367_);
lean_dec(v_i_3367_);
v_res_3376_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_as_3365_, v_sz_boxed_3374_, v_i_boxed_3375_, v_b_3368_, v___y_3369_, v___y_3370_, v___y_3371_, v___y_3372_);
lean_dec(v___y_3372_);
lean_dec_ref(v___y_3371_);
lean_dec_ref(v___y_3370_);
lean_dec(v___y_3369_);
lean_dec_ref(v_as_3365_);
return v_res_3376_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(uint8_t v_suppressElabErrors_3384_, lean_object* v_x_3385_){
_start:
{
if (lean_obj_tag(v_x_3385_) == 1)
{
lean_object* v_pre_3386_; 
v_pre_3386_ = lean_ctor_get(v_x_3385_, 0);
switch(lean_obj_tag(v_pre_3386_))
{
case 1:
{
lean_object* v_pre_3387_; 
v_pre_3387_ = lean_ctor_get(v_pre_3386_, 0);
switch(lean_obj_tag(v_pre_3387_))
{
case 0:
{
lean_object* v_str_3388_; lean_object* v_str_3389_; lean_object* v___x_3390_; uint8_t v___x_3391_; 
v_str_3388_ = lean_ctor_get(v_x_3385_, 1);
v_str_3389_ = lean_ctor_get(v_pre_3386_, 1);
v___x_3390_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__0));
v___x_3391_ = lean_string_dec_eq(v_str_3389_, v___x_3390_);
if (v___x_3391_ == 0)
{
lean_object* v___x_3392_; uint8_t v___x_3393_; 
v___x_3392_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__1));
v___x_3393_ = lean_string_dec_eq(v_str_3389_, v___x_3392_);
if (v___x_3393_ == 0)
{
return v___x_3393_;
}
else
{
lean_object* v___x_3394_; uint8_t v___x_3395_; 
v___x_3394_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__2));
v___x_3395_ = lean_string_dec_eq(v_str_3388_, v___x_3394_);
if (v___x_3395_ == 0)
{
return v___x_3395_;
}
else
{
return v_suppressElabErrors_3384_;
}
}
}
else
{
lean_object* v___x_3396_; uint8_t v___x_3397_; 
v___x_3396_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__3));
v___x_3397_ = lean_string_dec_eq(v_str_3388_, v___x_3396_);
if (v___x_3397_ == 0)
{
return v___x_3397_;
}
else
{
return v_suppressElabErrors_3384_;
}
}
}
case 1:
{
lean_object* v_pre_3398_; 
v_pre_3398_ = lean_ctor_get(v_pre_3387_, 0);
if (lean_obj_tag(v_pre_3398_) == 0)
{
lean_object* v_str_3399_; lean_object* v_str_3400_; lean_object* v_str_3401_; lean_object* v___x_3402_; uint8_t v___x_3403_; 
v_str_3399_ = lean_ctor_get(v_x_3385_, 1);
v_str_3400_ = lean_ctor_get(v_pre_3386_, 1);
v_str_3401_ = lean_ctor_get(v_pre_3387_, 1);
v___x_3402_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__4));
v___x_3403_ = lean_string_dec_eq(v_str_3401_, v___x_3402_);
if (v___x_3403_ == 0)
{
return v___x_3403_;
}
else
{
lean_object* v___x_3404_; uint8_t v___x_3405_; 
v___x_3404_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__5));
v___x_3405_ = lean_string_dec_eq(v_str_3400_, v___x_3404_);
if (v___x_3405_ == 0)
{
return v___x_3405_;
}
else
{
lean_object* v___x_3406_; uint8_t v___x_3407_; 
v___x_3406_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__6));
v___x_3407_ = lean_string_dec_eq(v_str_3399_, v___x_3406_);
if (v___x_3407_ == 0)
{
return v___x_3407_;
}
else
{
return v_suppressElabErrors_3384_;
}
}
}
}
else
{
uint8_t v___x_3408_; 
v___x_3408_ = 0;
return v___x_3408_;
}
}
default: 
{
uint8_t v___x_3409_; 
v___x_3409_ = 0;
return v___x_3409_;
}
}
}
case 0:
{
lean_object* v_str_3410_; lean_object* v___x_3411_; uint8_t v___x_3412_; 
v_str_3410_ = lean_ctor_get(v_x_3385_, 1);
v___x_3411_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3412_ = lean_string_dec_eq(v_str_3410_, v___x_3411_);
if (v___x_3412_ == 0)
{
return v___x_3412_;
}
else
{
return v_suppressElabErrors_3384_;
}
}
default: 
{
uint8_t v___x_3413_; 
v___x_3413_ = 0;
return v___x_3413_;
}
}
}
else
{
uint8_t v___x_3414_; 
v___x_3414_ = 0;
return v___x_3414_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_3415_, lean_object* v_x_3416_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3417_; uint8_t v_res_3418_; lean_object* v_r_3419_; 
v_suppressElabErrors_boxed_3417_ = lean_unbox(v_suppressElabErrors_3415_);
v_res_3418_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(v_suppressElabErrors_boxed_3417_, v_x_3416_);
lean_dec(v_x_3416_);
v_r_3419_ = lean_box(v_res_3418_);
return v_r_3419_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(lean_object* v_ref_3420_, lean_object* v_msgData_3421_, uint8_t v_severity_3422_, uint8_t v_isSilent_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_){
_start:
{
lean_object* v___y_3430_; lean_object* v___y_3431_; uint8_t v___y_3432_; lean_object* v___y_3433_; lean_object* v___y_3434_; lean_object* v___y_3435_; uint8_t v___y_3436_; lean_object* v_toCold_3437_; lean_object* v___y_3438_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; uint8_t v___y_3470_; uint8_t v___y_3471_; lean_object* v___y_3472_; uint8_t v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3494_; lean_object* v___y_3495_; uint8_t v___y_3496_; lean_object* v___y_3497_; uint8_t v___y_3498_; uint8_t v___y_3499_; lean_object* v___y_3500_; uint8_t v___y_3504_; uint8_t v___y_3505_; uint8_t v___x_3515_; uint8_t v___y_3517_; uint8_t v___x_3523_; 
v___x_3515_ = 2;
v___x_3523_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3422_, v___x_3515_);
if (v___x_3523_ == 0)
{
v___y_3517_ = v___x_3523_;
goto v___jp_3516_;
}
else
{
uint8_t v___x_3524_; 
lean_inc_ref(v_msgData_3421_);
v___x_3524_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3421_);
if (v___x_3524_ == 0)
{
v___y_3517_ = v___x_3524_;
goto v___jp_3516_;
}
else
{
lean_object* v___x_3525_; lean_object* v___x_3526_; 
lean_dec_ref(v_msgData_3421_);
v___x_3525_ = lean_box(0);
v___x_3526_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3525_);
return v___x_3526_;
}
}
v___jp_3429_:
{
lean_object* v_currNamespace_3439_; lean_object* v_openDecls_3440_; lean_object* v___x_3441_; lean_object* v___x_3442_; lean_object* v___x_3443_; lean_object* v___x_3444_; lean_object* v_env_3445_; lean_object* v_nextMacroScope_3446_; lean_object* v_ngen_3447_; lean_object* v_auxDeclNGen_3448_; lean_object* v_traceState_3449_; lean_object* v_cache_3450_; lean_object* v_recordedDeps_3451_; lean_object* v_messages_3452_; lean_object* v_infoState_3453_; lean_object* v_snapshotTasks_3454_; lean_object* v___x_3456_; uint8_t v_isShared_3457_; uint8_t v_isSharedCheck_3465_; 
v_currNamespace_3439_ = lean_ctor_get(v_toCold_3437_, 4);
v_openDecls_3440_ = lean_ctor_get(v_toCold_3437_, 5);
lean_inc(v_openDecls_3440_);
lean_inc(v_currNamespace_3439_);
v___x_3441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3441_, 0, v_currNamespace_3439_);
lean_ctor_set(v___x_3441_, 1, v_openDecls_3440_);
v___x_3442_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3442_, 0, v___x_3441_);
lean_ctor_set(v___x_3442_, 1, v___y_3431_);
lean_inc_ref(v___y_3430_);
lean_inc_ref(v___y_3434_);
v___x_3443_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3443_, 0, v___y_3434_);
lean_ctor_set(v___x_3443_, 1, v___y_3433_);
lean_ctor_set(v___x_3443_, 2, v___y_3435_);
lean_ctor_set(v___x_3443_, 3, v___y_3430_);
lean_ctor_set(v___x_3443_, 4, v___x_3442_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*5, v___y_3432_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*5 + 1, v___y_3436_);
lean_ctor_set_uint8(v___x_3443_, sizeof(void*)*5 + 2, v_isSilent_3423_);
v___x_3444_ = lean_st_ref_take(v___y_3438_);
v_env_3445_ = lean_ctor_get(v___x_3444_, 0);
v_nextMacroScope_3446_ = lean_ctor_get(v___x_3444_, 1);
v_ngen_3447_ = lean_ctor_get(v___x_3444_, 2);
v_auxDeclNGen_3448_ = lean_ctor_get(v___x_3444_, 3);
v_traceState_3449_ = lean_ctor_get(v___x_3444_, 4);
v_cache_3450_ = lean_ctor_get(v___x_3444_, 5);
v_recordedDeps_3451_ = lean_ctor_get(v___x_3444_, 6);
v_messages_3452_ = lean_ctor_get(v___x_3444_, 7);
v_infoState_3453_ = lean_ctor_get(v___x_3444_, 8);
v_snapshotTasks_3454_ = lean_ctor_get(v___x_3444_, 9);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3444_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3456_ = v___x_3444_;
v_isShared_3457_ = v_isSharedCheck_3465_;
goto v_resetjp_3455_;
}
else
{
lean_inc(v_snapshotTasks_3454_);
lean_inc(v_infoState_3453_);
lean_inc(v_messages_3452_);
lean_inc(v_recordedDeps_3451_);
lean_inc(v_cache_3450_);
lean_inc(v_traceState_3449_);
lean_inc(v_auxDeclNGen_3448_);
lean_inc(v_ngen_3447_);
lean_inc(v_nextMacroScope_3446_);
lean_inc(v_env_3445_);
lean_dec(v___x_3444_);
v___x_3456_ = lean_box(0);
v_isShared_3457_ = v_isSharedCheck_3465_;
goto v_resetjp_3455_;
}
v_resetjp_3455_:
{
lean_object* v___x_3458_; lean_object* v___x_3459_; lean_object* v___x_3461_; 
v___x_3458_ = lean_box(0);
v___x_3459_ = l_Lean_MessageLog_add(v___x_3443_, v_messages_3452_);
if (v_isShared_3457_ == 0)
{
lean_ctor_set(v___x_3456_, 7, v___x_3459_);
v___x_3461_ = v___x_3456_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v_env_3445_);
lean_ctor_set(v_reuseFailAlloc_3464_, 1, v_nextMacroScope_3446_);
lean_ctor_set(v_reuseFailAlloc_3464_, 2, v_ngen_3447_);
lean_ctor_set(v_reuseFailAlloc_3464_, 3, v_auxDeclNGen_3448_);
lean_ctor_set(v_reuseFailAlloc_3464_, 4, v_traceState_3449_);
lean_ctor_set(v_reuseFailAlloc_3464_, 5, v_cache_3450_);
lean_ctor_set(v_reuseFailAlloc_3464_, 6, v_recordedDeps_3451_);
lean_ctor_set(v_reuseFailAlloc_3464_, 7, v___x_3459_);
lean_ctor_set(v_reuseFailAlloc_3464_, 8, v_infoState_3453_);
lean_ctor_set(v_reuseFailAlloc_3464_, 9, v_snapshotTasks_3454_);
v___x_3461_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
lean_object* v___x_3462_; lean_object* v___x_3463_; 
v___x_3462_ = lean_st_ref_put(v___y_3438_, v___x_3461_);
v___x_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3463_, 0, v___x_3458_);
return v___x_3463_;
}
}
}
v___jp_3466_:
{
lean_object* v_fileName_3475_; lean_object* v_fileMap_3476_; lean_object* v___x_3477_; lean_object* v___x_3478_; lean_object* v_a_3479_; lean_object* v___x_3481_; uint8_t v_isShared_3482_; uint8_t v_isSharedCheck_3492_; 
v_fileName_3475_ = lean_ctor_get(v___y_3469_, 0);
v_fileMap_3476_ = lean_ctor_get(v___y_3469_, 1);
v___x_3477_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3421_);
v___x_3478_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3477_, v___y_3424_, v___y_3425_, v___y_3426_, v___y_3427_);
v_a_3479_ = lean_ctor_get(v___x_3478_, 0);
v_isSharedCheck_3492_ = !lean_is_exclusive(v___x_3478_);
if (v_isSharedCheck_3492_ == 0)
{
v___x_3481_ = v___x_3478_;
v_isShared_3482_ = v_isSharedCheck_3492_;
goto v_resetjp_3480_;
}
else
{
lean_inc(v_a_3479_);
lean_dec(v___x_3478_);
v___x_3481_ = lean_box(0);
v_isShared_3482_ = v_isSharedCheck_3492_;
goto v_resetjp_3480_;
}
v_resetjp_3480_:
{
lean_object* v___x_3483_; lean_object* v___x_3484_; lean_object* v___x_3485_; lean_object* v___x_3486_; 
lean_inc_ref_n(v_fileMap_3476_, 2);
v___x_3483_ = l_Lean_FileMap_toPosition(v_fileMap_3476_, v___y_3472_);
lean_dec(v___y_3472_);
v___x_3484_ = l_Lean_FileMap_toPosition(v_fileMap_3476_, v___y_3474_);
lean_dec(v___y_3474_);
v___x_3485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3485_, 0, v___x_3484_);
v___x_3486_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3470_ == 0)
{
lean_del_object(v___x_3481_);
lean_dec_ref(v___y_3468_);
v___y_3430_ = v___x_3486_;
v___y_3431_ = v_a_3479_;
v___y_3432_ = v___y_3471_;
v___y_3433_ = v___x_3483_;
v___y_3434_ = v_fileName_3475_;
v___y_3435_ = v___x_3485_;
v___y_3436_ = v___y_3473_;
v_toCold_3437_ = v___y_3467_;
v___y_3438_ = v___y_3427_;
goto v___jp_3429_;
}
else
{
uint8_t v___x_3487_; 
lean_inc(v_a_3479_);
v___x_3487_ = l_Lean_MessageData_hasTag(v___y_3468_, v_a_3479_);
if (v___x_3487_ == 0)
{
lean_object* v___x_3488_; lean_object* v___x_3490_; 
lean_dec_ref_known(v___x_3485_, 1);
lean_dec_ref(v___x_3483_);
lean_dec(v_a_3479_);
v___x_3488_ = lean_box(0);
if (v_isShared_3482_ == 0)
{
lean_ctor_set(v___x_3481_, 0, v___x_3488_);
v___x_3490_ = v___x_3481_;
goto v_reusejp_3489_;
}
else
{
lean_object* v_reuseFailAlloc_3491_; 
v_reuseFailAlloc_3491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3491_, 0, v___x_3488_);
v___x_3490_ = v_reuseFailAlloc_3491_;
goto v_reusejp_3489_;
}
v_reusejp_3489_:
{
return v___x_3490_;
}
}
else
{
lean_del_object(v___x_3481_);
v___y_3430_ = v___x_3486_;
v___y_3431_ = v_a_3479_;
v___y_3432_ = v___y_3471_;
v___y_3433_ = v___x_3483_;
v___y_3434_ = v_fileName_3475_;
v___y_3435_ = v___x_3485_;
v___y_3436_ = v___y_3473_;
v_toCold_3437_ = v___y_3467_;
v___y_3438_ = v___y_3427_;
goto v___jp_3429_;
}
}
}
}
v___jp_3493_:
{
lean_object* v___x_3501_; 
v___x_3501_ = l_Lean_Syntax_getTailPos_x3f(v___y_3497_, v___y_3498_);
lean_dec(v___y_3497_);
if (lean_obj_tag(v___x_3501_) == 0)
{
lean_inc(v___y_3500_);
v___y_3467_ = v___y_3494_;
v___y_3468_ = v___y_3495_;
v___y_3469_ = v___y_3494_;
v___y_3470_ = v___y_3496_;
v___y_3471_ = v___y_3498_;
v___y_3472_ = v___y_3500_;
v___y_3473_ = v___y_3499_;
v___y_3474_ = v___y_3500_;
goto v___jp_3466_;
}
else
{
lean_object* v_val_3502_; 
v_val_3502_ = lean_ctor_get(v___x_3501_, 0);
lean_inc(v_val_3502_);
lean_dec_ref_known(v___x_3501_, 1);
v___y_3467_ = v___y_3494_;
v___y_3468_ = v___y_3495_;
v___y_3469_ = v___y_3494_;
v___y_3470_ = v___y_3496_;
v___y_3471_ = v___y_3498_;
v___y_3472_ = v___y_3500_;
v___y_3473_ = v___y_3499_;
v___y_3474_ = v_val_3502_;
goto v___jp_3466_;
}
}
v___jp_3503_:
{
lean_object* v_toCold_3506_; lean_object* v_ref_3507_; uint8_t v_suppressElabErrors_3508_; lean_object* v___x_3509_; lean_object* v___f_3510_; lean_object* v_ref_3511_; lean_object* v___x_3512_; 
v_toCold_3506_ = lean_ctor_get(v___y_3426_, 0);
v_ref_3507_ = lean_ctor_get(v___y_3426_, 2);
v_suppressElabErrors_3508_ = lean_ctor_get_uint8(v___y_3426_, sizeof(void*)*3 + 2);
v___x_3509_ = lean_box(v_suppressElabErrors_3508_);
v___f_3510_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3510_, 0, v___x_3509_);
v_ref_3511_ = l_Lean_replaceRef(v_ref_3420_, v_ref_3507_);
v___x_3512_ = l_Lean_Syntax_getPos_x3f(v_ref_3511_, v___y_3504_);
if (lean_obj_tag(v___x_3512_) == 0)
{
lean_object* v___x_3513_; 
v___x_3513_ = lean_unsigned_to_nat(0u);
v___y_3494_ = v_toCold_3506_;
v___y_3495_ = v___f_3510_;
v___y_3496_ = v_suppressElabErrors_3508_;
v___y_3497_ = v_ref_3511_;
v___y_3498_ = v___y_3504_;
v___y_3499_ = v___y_3505_;
v___y_3500_ = v___x_3513_;
goto v___jp_3493_;
}
else
{
lean_object* v_val_3514_; 
v_val_3514_ = lean_ctor_get(v___x_3512_, 0);
lean_inc(v_val_3514_);
lean_dec_ref_known(v___x_3512_, 1);
v___y_3494_ = v_toCold_3506_;
v___y_3495_ = v___f_3510_;
v___y_3496_ = v_suppressElabErrors_3508_;
v___y_3497_ = v_ref_3511_;
v___y_3498_ = v___y_3504_;
v___y_3499_ = v___y_3505_;
v___y_3500_ = v_val_3514_;
goto v___jp_3493_;
}
}
v___jp_3516_:
{
uint8_t v___x_3518_; uint8_t v___x_3519_; 
v___x_3518_ = 1;
v___x_3519_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3422_, v___x_3518_);
if (v___x_3519_ == 0)
{
v___y_3504_ = v___y_3517_;
v___y_3505_ = v_severity_3422_;
goto v___jp_3503_;
}
else
{
lean_object* v___x_3520_; lean_object* v___x_3521_; uint8_t v___x_3522_; 
v___x_3520_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3426_);
v___x_3521_ = l_Lean_warningAsError;
v___x_3522_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_3520_, v___x_3521_);
lean_dec_ref(v___x_3520_);
if (v___x_3522_ == 0)
{
v___y_3504_ = v___y_3517_;
v___y_3505_ = v_severity_3422_;
goto v___jp_3503_;
}
else
{
v___y_3504_ = v___y_3517_;
v___y_3505_ = v___x_3515_;
goto v___jp_3503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___boxed(lean_object* v_ref_3527_, lean_object* v_msgData_3528_, lean_object* v_severity_3529_, lean_object* v_isSilent_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_, lean_object* v___y_3535_){
_start:
{
uint8_t v_severity_boxed_3536_; uint8_t v_isSilent_boxed_3537_; lean_object* v_res_3538_; 
v_severity_boxed_3536_ = lean_unbox(v_severity_3529_);
v_isSilent_boxed_3537_ = lean_unbox(v_isSilent_3530_);
v_res_3538_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3527_, v_msgData_3528_, v_severity_boxed_3536_, v_isSilent_boxed_3537_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
lean_dec(v___y_3534_);
lean_dec_ref(v___y_3533_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v_ref_3527_);
return v_res_3538_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(lean_object* v_msgData_3539_, uint8_t v_severity_3540_, uint8_t v_isSilent_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
lean_object* v_ref_3547_; lean_object* v___x_3548_; 
v_ref_3547_ = lean_ctor_get(v___y_3544_, 2);
v___x_3548_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3547_, v_msgData_3539_, v_severity_3540_, v_isSilent_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
return v___x_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3___boxed(lean_object* v_msgData_3549_, lean_object* v_severity_3550_, lean_object* v_isSilent_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_, lean_object* v___y_3554_, lean_object* v___y_3555_, lean_object* v___y_3556_){
_start:
{
uint8_t v_severity_boxed_3557_; uint8_t v_isSilent_boxed_3558_; lean_object* v_res_3559_; 
v_severity_boxed_3557_ = lean_unbox(v_severity_3550_);
v_isSilent_boxed_3558_ = lean_unbox(v_isSilent_3551_);
v_res_3559_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3549_, v_severity_boxed_3557_, v_isSilent_boxed_3558_, v___y_3552_, v___y_3553_, v___y_3554_, v___y_3555_);
lean_dec(v___y_3555_);
lean_dec_ref(v___y_3554_);
lean_dec(v___y_3553_);
lean_dec_ref(v___y_3552_);
return v_res_3559_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object* v_msgData_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_, lean_object* v___y_3564_){
_start:
{
uint8_t v___x_3566_; uint8_t v___x_3567_; lean_object* v___x_3568_; 
v___x_3566_ = 1;
v___x_3567_ = 0;
v___x_3568_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3560_, v___x_3566_, v___x_3567_, v___y_3561_, v___y_3562_, v___y_3563_, v___y_3564_);
return v___x_3568_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object* v_msgData_3569_, lean_object* v___y_3570_, lean_object* v___y_3571_, lean_object* v___y_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_){
_start:
{
lean_object* v_res_3575_; 
v_res_3575_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v_msgData_3569_, v___y_3570_, v___y_3571_, v___y_3572_, v___y_3573_);
lean_dec(v___y_3573_);
lean_dec_ref(v___y_3572_);
lean_dec(v___y_3571_);
lean_dec_ref(v___y_3570_);
return v_res_3575_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object* v_k_3576_, lean_object* v_t_3577_){
_start:
{
if (lean_obj_tag(v_t_3577_) == 0)
{
lean_object* v_k_3578_; lean_object* v_l_3579_; lean_object* v_r_3580_; uint8_t v___x_3581_; 
v_k_3578_ = lean_ctor_get(v_t_3577_, 1);
v_l_3579_ = lean_ctor_get(v_t_3577_, 3);
v_r_3580_ = lean_ctor_get(v_t_3577_, 4);
v___x_3581_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3576_, v_k_3578_);
switch(v___x_3581_)
{
case 0:
{
v_t_3577_ = v_l_3579_;
goto _start;
}
case 1:
{
uint8_t v___x_3583_; 
v___x_3583_ = 1;
return v___x_3583_;
}
default: 
{
v_t_3577_ = v_r_3580_;
goto _start;
}
}
}
else
{
uint8_t v___x_3585_; 
v___x_3585_ = 0;
return v___x_3585_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object* v_k_3586_, lean_object* v_t_3587_){
_start:
{
uint8_t v_res_3588_; lean_object* v_r_3589_; 
v_res_3588_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3586_, v_t_3587_);
lean_dec(v_t_3587_);
lean_dec(v_k_3586_);
v_r_3589_ = lean_box(v_res_3588_);
return v_r_3589_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__0));
v___x_3592_ = l_Lean_stringToMessageData(v___x_3591_);
return v___x_3592_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3594_; lean_object* v___x_3595_; 
v___x_3594_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__2));
v___x_3595_ = l_Lean_stringToMessageData(v___x_3594_);
return v___x_3595_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(lean_object* v_a_3596_, lean_object* v_as_3597_, size_t v_sz_3598_, size_t v_i_3599_, lean_object* v_b_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_){
_start:
{
lean_object* v_a_3606_; uint8_t v___x_3610_; 
v___x_3610_ = lean_usize_dec_lt(v_i_3599_, v_sz_3598_);
if (v___x_3610_ == 0)
{
lean_object* v___x_3611_; 
v___x_3611_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3611_, 0, v_b_3600_);
return v___x_3611_;
}
else
{
lean_object* v_snd_3612_; 
v_snd_3612_ = lean_ctor_get(v_b_3600_, 1);
lean_inc(v_snd_3612_);
if (lean_obj_tag(v_snd_3612_) == 0)
{
lean_object* v_fst_3613_; lean_object* v___x_3615_; uint8_t v_isShared_3616_; uint8_t v_isSharedCheck_3621_; 
v_fst_3613_ = lean_ctor_get(v_b_3600_, 0);
v_isSharedCheck_3621_ = !lean_is_exclusive(v_b_3600_);
if (v_isSharedCheck_3621_ == 0)
{
lean_object* v_unused_3622_; 
v_unused_3622_ = lean_ctor_get(v_b_3600_, 1);
lean_dec(v_unused_3622_);
v___x_3615_ = v_b_3600_;
v_isShared_3616_ = v_isSharedCheck_3621_;
goto v_resetjp_3614_;
}
else
{
lean_inc(v_fst_3613_);
lean_dec(v_b_3600_);
v___x_3615_ = lean_box(0);
v_isShared_3616_ = v_isSharedCheck_3621_;
goto v_resetjp_3614_;
}
v_resetjp_3614_:
{
lean_object* v___x_3618_; 
if (v_isShared_3616_ == 0)
{
v___x_3618_ = v___x_3615_;
goto v_reusejp_3617_;
}
else
{
lean_object* v_reuseFailAlloc_3620_; 
v_reuseFailAlloc_3620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3620_, 0, v_fst_3613_);
lean_ctor_set(v_reuseFailAlloc_3620_, 1, v_snd_3612_);
v___x_3618_ = v_reuseFailAlloc_3620_;
goto v_reusejp_3617_;
}
v_reusejp_3617_:
{
lean_object* v___x_3619_; 
v___x_3619_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3619_, 0, v___x_3618_);
return v___x_3619_;
}
}
}
else
{
lean_object* v_fst_3623_; lean_object* v___x_3625_; uint8_t v_isShared_3626_; uint8_t v_isSharedCheck_3680_; 
v_fst_3623_ = lean_ctor_get(v_b_3600_, 0);
v_isSharedCheck_3680_ = !lean_is_exclusive(v_b_3600_);
if (v_isSharedCheck_3680_ == 0)
{
lean_object* v_unused_3681_; 
v_unused_3681_ = lean_ctor_get(v_b_3600_, 1);
lean_dec(v_unused_3681_);
v___x_3625_ = v_b_3600_;
v_isShared_3626_ = v_isSharedCheck_3680_;
goto v_resetjp_3624_;
}
else
{
lean_inc(v_fst_3623_);
lean_dec(v_b_3600_);
v___x_3625_ = lean_box(0);
v_isShared_3626_ = v_isSharedCheck_3680_;
goto v_resetjp_3624_;
}
v_resetjp_3624_:
{
lean_object* v_val_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3679_; 
v_val_3627_ = lean_ctor_get(v_snd_3612_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v_snd_3612_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3629_ = v_snd_3612_;
v_isShared_3630_ = v_isSharedCheck_3679_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_val_3627_);
lean_dec(v_snd_3612_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3679_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v_fvarSet_3631_; lean_object* v_a_3632_; lean_object* v___x_3633_; lean_object* v___x_3634_; lean_object* v___x_3636_; 
v_fvarSet_3631_ = lean_ctor_get(v_a_3596_, 1);
v_a_3632_ = lean_array_uget_borrowed(v_as_3597_, v_i_3599_);
v___x_3633_ = lean_unsigned_to_nat(1u);
v___x_3634_ = lean_nat_add(v_val_3627_, v___x_3633_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 0, v___x_3634_);
v___x_3636_ = v___x_3629_;
goto v_reusejp_3635_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v___x_3634_);
v___x_3636_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3635_;
}
v_reusejp_3635_:
{
lean_object* v___x_3637_; uint8_t v___x_3638_; 
v___x_3637_ = l_Lean_Expr_fvarId_x21(v_a_3632_);
v___x_3638_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v___x_3637_, v_fvarSet_3631_);
if (v___x_3638_ == 0)
{
lean_object* v___x_3639_; 
v___x_3639_ = l_Lean_FVarId_getDecl___redArg(v___x_3637_, v___y_3601_, v___y_3602_, v___y_3603_);
if (lean_obj_tag(v___x_3639_) == 0)
{
lean_object* v_a_3640_; lean_object* v___x_3641_; 
v_a_3640_ = lean_ctor_get(v___x_3639_, 0);
lean_inc(v_a_3640_);
lean_dec_ref_known(v___x_3639_, 1);
v___x_3641_ = l_Lean_LocalDecl_ppAsBinder(v_a_3640_);
if (lean_obj_tag(v___x_3641_) == 1)
{
lean_object* v_val_3642_; lean_object* v___x_3644_; uint8_t v_isShared_3645_; uint8_t v_isSharedCheck_3663_; 
v_val_3642_ = lean_ctor_get(v___x_3641_, 0);
v_isSharedCheck_3663_ = !lean_is_exclusive(v___x_3641_);
if (v_isSharedCheck_3663_ == 0)
{
v___x_3644_ = v___x_3641_;
v_isShared_3645_ = v_isSharedCheck_3663_;
goto v_resetjp_3643_;
}
else
{
lean_inc(v_val_3642_);
lean_dec(v___x_3641_);
v___x_3644_ = lean_box(0);
v_isShared_3645_ = v_isSharedCheck_3663_;
goto v_resetjp_3643_;
}
v_resetjp_3643_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; lean_object* v___x_3649_; 
v___x_3646_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1);
v___x_3647_ = l_Nat_reprFast(v_val_3627_);
if (v_isShared_3645_ == 0)
{
lean_ctor_set_tag(v___x_3644_, 3);
lean_ctor_set(v___x_3644_, 0, v___x_3647_);
v___x_3649_ = v___x_3644_;
goto v_reusejp_3648_;
}
else
{
lean_object* v_reuseFailAlloc_3662_; 
v_reuseFailAlloc_3662_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3662_, 0, v___x_3647_);
v___x_3649_ = v_reuseFailAlloc_3662_;
goto v_reusejp_3648_;
}
v_reusejp_3648_:
{
lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___x_3654_; lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3660_; 
v___x_3650_ = l_Lean_MessageData_ofFormat(v___x_3649_);
v___x_3651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3651_, 0, v___x_3646_);
lean_ctor_set(v___x_3651_, 1, v___x_3650_);
v___x_3652_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3);
v___x_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3653_, 0, v___x_3651_);
lean_ctor_set(v___x_3653_, 1, v___x_3652_);
v___x_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3654_, 0, v___x_3653_);
lean_ctor_set(v___x_3654_, 1, v_val_3642_);
v___x_3655_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3654_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = l_Lean_indentD(v___x_3656_);
v___x_3658_ = lean_array_push(v_fst_3623_, v___x_3657_);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 1, v___x_3636_);
lean_ctor_set(v___x_3625_, 0, v___x_3658_);
v___x_3660_ = v___x_3625_;
goto v_reusejp_3659_;
}
else
{
lean_object* v_reuseFailAlloc_3661_; 
v_reuseFailAlloc_3661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3661_, 0, v___x_3658_);
lean_ctor_set(v_reuseFailAlloc_3661_, 1, v___x_3636_);
v___x_3660_ = v_reuseFailAlloc_3661_;
goto v_reusejp_3659_;
}
v_reusejp_3659_:
{
v_a_3606_ = v___x_3660_;
goto v___jp_3605_;
}
}
}
}
else
{
lean_object* v___x_3665_; 
lean_dec(v___x_3641_);
lean_dec(v_val_3627_);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 1, v___x_3636_);
v___x_3665_ = v___x_3625_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_fst_3623_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v___x_3636_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
v_a_3606_ = v___x_3665_;
goto v___jp_3605_;
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
lean_dec_ref(v___x_3636_);
lean_dec(v_val_3627_);
lean_del_object(v___x_3625_);
lean_dec(v_fst_3623_);
v_a_3667_ = lean_ctor_get(v___x_3639_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3639_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3639_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3639_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3672_; 
if (v_isShared_3670_ == 0)
{
v___x_3672_ = v___x_3669_;
goto v_reusejp_3671_;
}
else
{
lean_object* v_reuseFailAlloc_3673_; 
v_reuseFailAlloc_3673_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3673_, 0, v_a_3667_);
v___x_3672_ = v_reuseFailAlloc_3673_;
goto v_reusejp_3671_;
}
v_reusejp_3671_:
{
return v___x_3672_;
}
}
}
}
else
{
lean_object* v___x_3676_; 
lean_dec(v___x_3637_);
lean_dec(v_val_3627_);
if (v_isShared_3626_ == 0)
{
lean_ctor_set(v___x_3625_, 1, v___x_3636_);
v___x_3676_ = v___x_3625_;
goto v_reusejp_3675_;
}
else
{
lean_object* v_reuseFailAlloc_3677_; 
v_reuseFailAlloc_3677_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3677_, 0, v_fst_3623_);
lean_ctor_set(v_reuseFailAlloc_3677_, 1, v___x_3636_);
v___x_3676_ = v_reuseFailAlloc_3677_;
goto v_reusejp_3675_;
}
v_reusejp_3675_:
{
v_a_3606_ = v___x_3676_;
goto v___jp_3605_;
}
}
}
}
}
}
}
v___jp_3605_:
{
size_t v___x_3607_; size_t v___x_3608_; 
v___x_3607_ = ((size_t)1ULL);
v___x_3608_ = lean_usize_add(v_i_3599_, v___x_3607_);
v_i_3599_ = v___x_3608_;
v_b_3600_ = v_a_3606_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___boxed(lean_object* v_a_3682_, lean_object* v_as_3683_, lean_object* v_sz_3684_, lean_object* v_i_3685_, lean_object* v_b_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
size_t v_sz_boxed_3691_; size_t v_i_boxed_3692_; lean_object* v_res_3693_; 
v_sz_boxed_3691_ = lean_unbox_usize(v_sz_3684_);
lean_dec(v_sz_3684_);
v_i_boxed_3692_ = lean_unbox_usize(v_i_3685_);
lean_dec(v_i_3685_);
v_res_3693_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3682_, v_as_3683_, v_sz_boxed_3691_, v_i_boxed_3692_, v_b_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v_as_3683_);
lean_dec_ref(v_a_3682_);
return v_res_3693_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0(void){
_start:
{
lean_object* v___x_3694_; lean_object* v___x_3695_; lean_object* v___x_3696_; 
v___x_3694_ = lean_box(0);
v___x_3695_ = lean_unsigned_to_nat(16u);
v___x_3696_ = lean_mk_array(v___x_3695_, v___x_3694_);
return v___x_3696_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3697_; lean_object* v___x_3698_; lean_object* v___x_3699_; 
v___x_3697_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0);
v___x_3698_ = lean_unsigned_to_nat(0u);
v___x_3699_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
lean_ctor_set(v___x_3699_, 1, v___x_3697_);
return v___x_3699_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; 
v___x_3708_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5));
v___x_3709_ = l_Lean_stringToMessageData(v___x_3708_);
return v___x_3709_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3711_; lean_object* v___x_3712_; 
v___x_3711_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7));
v___x_3712_ = l_Lean_stringToMessageData(v___x_3711_);
return v___x_3712_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3714_; lean_object* v___x_3715_; 
v___x_3714_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9));
v___x_3715_ = l_Lean_stringToMessageData(v___x_3714_);
return v___x_3715_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12(void){
_start:
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
v___x_3717_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11));
v___x_3718_ = l_Lean_stringToMessageData(v___x_3717_);
return v___x_3718_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v___x_3720_, lean_object* v___x_3721_, lean_object* v_args_3722_, lean_object* v_ty_3723_, lean_object* v___y_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_){
_start:
{
lean_object* v___x_3729_; lean_object* v___x_3730_; lean_object* v___x_3731_; lean_object* v___x_3732_; lean_object* v___x_3733_; lean_object* v___x_3734_; 
v___x_3729_ = lean_unsigned_to_nat(0u);
v___x_3730_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1);
v___x_3731_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2));
v___x_3732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3732_, 0, v___x_3730_);
lean_ctor_set(v___x_3732_, 1, v___x_3720_);
lean_ctor_set(v___x_3732_, 2, v___x_3731_);
v___x_3733_ = lean_st_mk_ref(v___x_3732_);
v___x_3734_ = l_Lean_Expr_collectFVars(v_ty_3723_, v___x_3733_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
if (lean_obj_tag(v___x_3734_) == 0)
{
lean_object* v___x_3735_; size_t v_sz_3736_; size_t v___x_3737_; lean_object* v___x_3738_; 
lean_dec_ref_known(v___x_3734_, 1);
v___x_3735_ = lean_box(0);
v_sz_3736_ = lean_array_size(v_args_3722_);
v___x_3737_ = ((size_t)0ULL);
v___x_3738_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_args_3722_, v_sz_3736_, v___x_3737_, v___x_3735_, v___x_3733_, v___y_3724_, v___y_3726_, v___y_3727_);
if (lean_obj_tag(v___x_3738_) == 0)
{
lean_object* v___x_3740_; uint8_t v_isShared_3741_; uint8_t v_isSharedCheck_3809_; 
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3738_);
if (v_isSharedCheck_3809_ == 0)
{
lean_object* v_unused_3810_; 
v_unused_3810_ = lean_ctor_get(v___x_3738_, 0);
lean_dec(v_unused_3810_);
v___x_3740_ = v___x_3738_;
v_isShared_3741_ = v_isSharedCheck_3809_;
goto v_resetjp_3739_;
}
else
{
lean_dec(v___x_3738_);
v___x_3740_ = lean_box(0);
v_isShared_3741_ = v_isSharedCheck_3809_;
goto v_resetjp_3739_;
}
v_resetjp_3739_:
{
lean_object* v___x_3742_; lean_object* v___x_3743_; 
v___x_3742_ = lean_st_ref_get(v___x_3733_);
lean_dec(v___x_3733_);
v___x_3743_ = l_Lean_CollectFVars_State_addDependencies(v___x_3742_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_object* v_a_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; 
v_a_3744_ = lean_ctor_get(v___x_3743_, 0);
lean_inc(v_a_3744_);
lean_dec_ref_known(v___x_3743_, 1);
v___x_3745_ = lean_unsigned_to_nat(1u);
v___x_3746_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4));
v___x_3747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3744_, v_args_3722_, v_sz_3736_, v___x_3737_, v___x_3746_, v___y_3724_, v___y_3726_, v___y_3727_);
lean_dec(v_a_3744_);
if (lean_obj_tag(v___x_3747_) == 0)
{
lean_object* v_a_3748_; lean_object* v___x_3750_; uint8_t v_isShared_3751_; uint8_t v_isSharedCheck_3792_; 
v_a_3748_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3792_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3792_ == 0)
{
v___x_3750_ = v___x_3747_;
v_isShared_3751_ = v_isSharedCheck_3792_;
goto v_resetjp_3749_;
}
else
{
lean_inc(v_a_3748_);
lean_dec(v___x_3747_);
v___x_3750_ = lean_box(0);
v_isShared_3751_ = v_isSharedCheck_3792_;
goto v_resetjp_3749_;
}
v_resetjp_3749_:
{
lean_object* v_fst_3752_; lean_object* v___x_3754_; uint8_t v_isShared_3755_; uint8_t v_isSharedCheck_3790_; 
v_fst_3752_ = lean_ctor_get(v_a_3748_, 0);
v_isSharedCheck_3790_ = !lean_is_exclusive(v_a_3748_);
if (v_isSharedCheck_3790_ == 0)
{
lean_object* v_unused_3791_; 
v_unused_3791_ = lean_ctor_get(v_a_3748_, 1);
lean_dec(v_unused_3791_);
v___x_3754_ = v_a_3748_;
v_isShared_3755_ = v_isSharedCheck_3790_;
goto v_resetjp_3753_;
}
else
{
lean_inc(v_fst_3752_);
lean_dec(v_a_3748_);
v___x_3754_ = lean_box(0);
v_isShared_3755_ = v_isSharedCheck_3790_;
goto v_resetjp_3753_;
}
v_resetjp_3753_:
{
lean_object* v___x_3756_; uint8_t v___x_3757_; 
v___x_3756_ = lean_array_get_size(v_fst_3752_);
v___x_3757_ = lean_nat_dec_eq(v___x_3756_, v___x_3729_);
if (v___x_3757_ == 0)
{
lean_object* v___x_3758_; lean_object* v___x_3759_; lean_object* v___x_3761_; 
lean_del_object(v___x_3750_);
v___x_3758_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6);
v___x_3759_ = l_Nat_reprFast(v___x_3756_);
if (v_isShared_3741_ == 0)
{
lean_ctor_set_tag(v___x_3740_, 3);
lean_ctor_set(v___x_3740_, 0, v___x_3759_);
v___x_3761_ = v___x_3740_;
goto v_reusejp_3760_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3759_);
v___x_3761_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3760_;
}
v_reusejp_3760_:
{
lean_object* v___x_3762_; lean_object* v___x_3764_; 
v___x_3762_ = l_Lean_MessageData_ofFormat(v___x_3761_);
if (v_isShared_3755_ == 0)
{
lean_ctor_set_tag(v___x_3754_, 7);
lean_ctor_set(v___x_3754_, 1, v___x_3762_);
lean_ctor_set(v___x_3754_, 0, v___x_3758_);
v___x_3764_ = v___x_3754_;
goto v_reusejp_3763_;
}
else
{
lean_object* v_reuseFailAlloc_3785_; 
v_reuseFailAlloc_3785_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3785_, 0, v___x_3758_);
lean_ctor_set(v_reuseFailAlloc_3785_, 1, v___x_3762_);
v___x_3764_ = v_reuseFailAlloc_3785_;
goto v_reusejp_3763_;
}
v_reusejp_3763_:
{
lean_object* v___x_3765_; lean_object* v___x_3766_; lean_object* v___y_3768_; uint8_t v___x_3782_; 
v___x_3765_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8);
v___x_3766_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3766_, 0, v___x_3764_);
lean_ctor_set(v___x_3766_, 1, v___x_3765_);
v___x_3782_ = lean_nat_dec_eq(v___x_3756_, v___x_3745_);
if (v___x_3782_ == 0)
{
lean_object* v___x_3783_; 
v___x_3783_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13));
v___y_3768_ = v___x_3783_;
goto v___jp_3767_;
}
else
{
lean_object* v___x_3784_; 
v___x_3784_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___y_3768_ = v___x_3784_;
goto v___jp_3767_;
}
v___jp_3767_:
{
lean_object* v___x_3769_; lean_object* v___x_3770_; lean_object* v___x_3771_; lean_object* v___x_3772_; lean_object* v___x_3773_; lean_object* v___x_3774_; lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; uint8_t v___x_3779_; 
lean_inc_ref(v___y_3768_);
v___x_3769_ = l_Lean_stringToMessageData(v___y_3768_);
v___x_3770_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3770_, 0, v___x_3766_);
lean_ctor_set(v___x_3770_, 1, v___x_3769_);
v___x_3771_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10);
v___x_3772_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3772_, 0, v___x_3770_);
lean_ctor_set(v___x_3772_, 1, v___x_3771_);
v___x_3773_ = lean_array_to_list(v_fst_3752_);
v___x_3774_ = l_Lean_MessageData_nil;
v___x_3775_ = l_Lean_MessageData_joinSep(v___x_3773_, v___x_3774_);
v___x_3776_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3776_, 0, v___x_3772_);
lean_ctor_set(v___x_3776_, 1, v___x_3775_);
v___x_3777_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12);
v___x_3778_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3778_, 0, v___x_3776_);
lean_ctor_set(v___x_3778_, 1, v___x_3777_);
v___x_3779_ = l_Lean_Expr_hasSorry(v___x_3721_);
if (v___x_3779_ == 0)
{
lean_object* v___x_3780_; 
v___x_3780_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3778_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
return v___x_3780_;
}
else
{
lean_object* v___x_3781_; 
v___x_3781_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_3778_, v___y_3724_, v___y_3725_, v___y_3726_, v___y_3727_);
return v___x_3781_;
}
}
}
}
}
else
{
lean_object* v___x_3788_; 
lean_del_object(v___x_3754_);
lean_dec(v_fst_3752_);
lean_del_object(v___x_3740_);
if (v_isShared_3751_ == 0)
{
lean_ctor_set(v___x_3750_, 0, v___x_3735_);
v___x_3788_ = v___x_3750_;
goto v_reusejp_3787_;
}
else
{
lean_object* v_reuseFailAlloc_3789_; 
v_reuseFailAlloc_3789_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3789_, 0, v___x_3735_);
v___x_3788_ = v_reuseFailAlloc_3789_;
goto v_reusejp_3787_;
}
v_reusejp_3787_:
{
return v___x_3788_;
}
}
}
}
}
else
{
lean_object* v_a_3793_; lean_object* v___x_3795_; uint8_t v_isShared_3796_; uint8_t v_isSharedCheck_3800_; 
lean_del_object(v___x_3740_);
v_a_3793_ = lean_ctor_get(v___x_3747_, 0);
v_isSharedCheck_3800_ = !lean_is_exclusive(v___x_3747_);
if (v_isSharedCheck_3800_ == 0)
{
v___x_3795_ = v___x_3747_;
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
else
{
lean_inc(v_a_3793_);
lean_dec(v___x_3747_);
v___x_3795_ = lean_box(0);
v_isShared_3796_ = v_isSharedCheck_3800_;
goto v_resetjp_3794_;
}
v_resetjp_3794_:
{
lean_object* v___x_3798_; 
if (v_isShared_3796_ == 0)
{
v___x_3798_ = v___x_3795_;
goto v_reusejp_3797_;
}
else
{
lean_object* v_reuseFailAlloc_3799_; 
v_reuseFailAlloc_3799_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3799_, 0, v_a_3793_);
v___x_3798_ = v_reuseFailAlloc_3799_;
goto v_reusejp_3797_;
}
v_reusejp_3797_:
{
return v___x_3798_;
}
}
}
}
else
{
lean_object* v_a_3801_; lean_object* v___x_3803_; uint8_t v_isShared_3804_; uint8_t v_isSharedCheck_3808_; 
lean_del_object(v___x_3740_);
v_a_3801_ = lean_ctor_get(v___x_3743_, 0);
v_isSharedCheck_3808_ = !lean_is_exclusive(v___x_3743_);
if (v_isSharedCheck_3808_ == 0)
{
v___x_3803_ = v___x_3743_;
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
else
{
lean_inc(v_a_3801_);
lean_dec(v___x_3743_);
v___x_3803_ = lean_box(0);
v_isShared_3804_ = v_isSharedCheck_3808_;
goto v_resetjp_3802_;
}
v_resetjp_3802_:
{
lean_object* v___x_3806_; 
if (v_isShared_3804_ == 0)
{
v___x_3806_ = v___x_3803_;
goto v_reusejp_3805_;
}
else
{
lean_object* v_reuseFailAlloc_3807_; 
v_reuseFailAlloc_3807_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3807_, 0, v_a_3801_);
v___x_3806_ = v_reuseFailAlloc_3807_;
goto v_reusejp_3805_;
}
v_reusejp_3805_:
{
return v___x_3806_;
}
}
}
}
}
else
{
lean_dec(v___x_3733_);
return v___x_3738_;
}
}
else
{
lean_dec(v___x_3733_);
return v___x_3734_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v___x_3811_, lean_object* v___x_3812_, lean_object* v_args_3813_, lean_object* v_ty_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
lean_object* v_res_3820_; 
v_res_3820_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v___x_3811_, v___x_3812_, v_args_3813_, v_ty_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec_ref(v_args_3813_);
lean_dec_ref(v___x_3812_);
return v_res_3820_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object* v_e_3821_){
_start:
{
lean_object* v___x_3822_; 
v___x_3822_ = l_Lean_Expr_cleanupAnnotations(v_e_3821_);
switch(lean_obj_tag(v___x_3822_))
{
case 7:
{
lean_object* v_body_3823_; uint8_t v_binderInfo_3824_; uint8_t v___x_3825_; 
v_body_3823_ = lean_ctor_get(v___x_3822_, 2);
lean_inc_ref(v_body_3823_);
v_binderInfo_3824_ = lean_ctor_get_uint8(v___x_3822_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3822_, 3);
v___x_3825_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3824_);
if (v___x_3825_ == 0)
{
lean_object* v___x_3826_; uint8_t v___x_3827_; 
v___x_3826_ = lean_unsigned_to_nat(0u);
v___x_3827_ = lean_expr_has_loose_bvar(v_body_3823_, v___x_3826_);
if (v___x_3827_ == 0)
{
uint8_t v___x_3828_; 
lean_dec_ref(v_body_3823_);
v___x_3828_ = 1;
return v___x_3828_;
}
else
{
v_e_3821_ = v_body_3823_;
goto _start;
}
}
else
{
v_e_3821_ = v_body_3823_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3831_; 
v_body_3831_ = lean_ctor_get(v___x_3822_, 3);
lean_inc_ref(v_body_3831_);
lean_dec_ref_known(v___x_3822_, 4);
v_e_3821_ = v_body_3831_;
goto _start;
}
default: 
{
uint8_t v___x_3833_; 
lean_dec_ref(v___x_3822_);
v___x_3833_ = 0;
return v___x_3833_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object* v_e_3834_){
_start:
{
uint8_t v_res_3835_; lean_object* v_r_3836_; 
v_res_3835_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(v_e_3834_);
v_r_3836_ = lean_box(v_res_3835_);
return v_r_3836_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_cinfo_3837_, lean_object* v_a_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_){
_start:
{
lean_object* v___x_3843_; uint8_t v___x_3844_; 
v___x_3843_ = l_Lean_ConstantInfo_type(v_cinfo_3837_);
lean_inc_ref(v___x_3843_);
v___x_3844_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(v___x_3843_);
if (v___x_3844_ == 0)
{
lean_object* v___x_3845_; lean_object* v___x_3846_; 
lean_dec_ref(v___x_3843_);
v___x_3845_ = lean_box(0);
v___x_3846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3846_, 0, v___x_3845_);
return v___x_3846_;
}
else
{
lean_object* v___x_3847_; lean_object* v___f_3848_; uint8_t v___x_3849_; lean_object* v___x_3850_; 
v___x_3847_ = lean_box(1);
lean_inc_ref(v___x_3843_);
v___f_3848_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3848_, 0, v___x_3847_);
lean_closure_set(v___f_3848_, 1, v___x_3843_);
v___x_3849_ = 0;
v___x_3850_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v___x_3843_, v___f_3848_, v___x_3849_, v_a_3838_, v_a_3839_, v_a_3840_, v_a_3841_);
return v___x_3850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_cinfo_3851_, lean_object* v_a_3852_, lean_object* v_a_3853_, lean_object* v_a_3854_, lean_object* v_a_3855_, lean_object* v_a_3856_){
_start:
{
lean_object* v_res_3857_; 
v_res_3857_ = l_Lean_Meta_checkImpossibleInstance(v_cinfo_3851_, v_a_3852_, v_a_3853_, v_a_3854_, v_a_3855_);
lean_dec(v_a_3855_);
lean_dec_ref(v_a_3854_);
lean_dec(v_a_3853_);
lean_dec_ref(v_a_3852_);
lean_dec_ref(v_cinfo_3851_);
return v_res_3857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object* v_as_3858_, size_t v_sz_3859_, size_t v_i_3860_, lean_object* v_b_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_, lean_object* v___y_3864_, lean_object* v___y_3865_, lean_object* v___y_3866_){
_start:
{
lean_object* v___x_3868_; 
v___x_3868_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_as_3858_, v_sz_3859_, v_i_3860_, v_b_3861_, v___y_3862_, v___y_3863_, v___y_3865_, v___y_3866_);
return v___x_3868_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_as_3869_, lean_object* v_sz_3870_, lean_object* v_i_3871_, lean_object* v_b_3872_, lean_object* v___y_3873_, lean_object* v___y_3874_, lean_object* v___y_3875_, lean_object* v___y_3876_, lean_object* v___y_3877_, lean_object* v___y_3878_){
_start:
{
size_t v_sz_boxed_3879_; size_t v_i_boxed_3880_; lean_object* v_res_3881_; 
v_sz_boxed_3879_ = lean_unbox_usize(v_sz_3870_);
lean_dec(v_sz_3870_);
v_i_boxed_3880_ = lean_unbox_usize(v_i_3871_);
lean_dec(v_i_3871_);
v_res_3881_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_as_3869_, v_sz_boxed_3879_, v_i_boxed_3880_, v_b_3872_, v___y_3873_, v___y_3874_, v___y_3875_, v___y_3876_, v___y_3877_);
lean_dec(v___y_3877_);
lean_dec_ref(v___y_3876_);
lean_dec(v___y_3875_);
lean_dec_ref(v___y_3874_);
lean_dec(v___y_3873_);
lean_dec_ref(v_as_3869_);
return v_res_3881_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v_00_u03b2_3882_, lean_object* v_k_3883_, lean_object* v_t_3884_){
_start:
{
uint8_t v___x_3885_; 
v___x_3885_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3883_, v_t_3884_);
return v___x_3885_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v_00_u03b2_3886_, lean_object* v_k_3887_, lean_object* v_t_3888_){
_start:
{
uint8_t v_res_3889_; lean_object* v_r_3890_; 
v_res_3889_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(v_00_u03b2_3886_, v_k_3887_, v_t_3888_);
lean_dec(v_t_3888_);
lean_dec(v_k_3887_);
v_r_3890_ = lean_box(v_res_3889_);
return v_r_3890_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_a_3891_, lean_object* v_as_3892_, size_t v_sz_3893_, size_t v_i_3894_, lean_object* v_b_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v___x_3901_; 
v___x_3901_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3891_, v_as_3892_, v_sz_3893_, v_i_3894_, v_b_3895_, v___y_3896_, v___y_3898_, v___y_3899_);
return v___x_3901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_a_3902_, lean_object* v_as_3903_, lean_object* v_sz_3904_, lean_object* v_i_3905_, lean_object* v_b_3906_, lean_object* v___y_3907_, lean_object* v___y_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
size_t v_sz_boxed_3912_; size_t v_i_boxed_3913_; lean_object* v_res_3914_; 
v_sz_boxed_3912_ = lean_unbox_usize(v_sz_3904_);
lean_dec(v_sz_3904_);
v_i_boxed_3913_ = lean_unbox_usize(v_i_3905_);
lean_dec(v_i_3905_);
v_res_3914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_a_3902_, v_as_3903_, v_sz_boxed_3912_, v_i_boxed_3913_, v_b_3906_, v___y_3907_, v___y_3908_, v___y_3909_, v___y_3910_);
lean_dec(v___y_3910_);
lean_dec_ref(v___y_3909_);
lean_dec(v___y_3908_);
lean_dec_ref(v___y_3907_);
lean_dec_ref(v_as_3903_);
lean_dec_ref(v_a_3902_);
return v_res_3914_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3916_; lean_object* v___x_3917_; 
v___x_3916_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3917_ = l_Lean_stringToMessageData(v___x_3916_);
return v___x_3917_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3919_; lean_object* v___x_3920_; 
v___x_3919_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3920_ = l_Lean_stringToMessageData(v___x_3919_);
return v___x_3920_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3923_ = l_Lean_stringToMessageData(v___x_3922_);
return v___x_3923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_c_3924_, lean_object* v_x_3925_, lean_object* v_target_3926_, lean_object* v___y_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_){
_start:
{
lean_object* v___x_3932_; 
lean_inc_ref(v_target_3926_);
v___x_3932_ = l_Lean_Meta_isClass_x3f(v_target_3926_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
if (lean_obj_tag(v___x_3932_) == 0)
{
lean_object* v_a_3933_; lean_object* v___x_3935_; uint8_t v_isShared_3936_; uint8_t v_isSharedCheck_3951_; 
v_a_3933_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3951_ == 0)
{
v___x_3935_ = v___x_3932_;
v_isShared_3936_ = v_isSharedCheck_3951_;
goto v_resetjp_3934_;
}
else
{
lean_inc(v_a_3933_);
lean_dec(v___x_3932_);
v___x_3935_ = lean_box(0);
v_isShared_3936_ = v_isSharedCheck_3951_;
goto v_resetjp_3934_;
}
v_resetjp_3934_:
{
if (lean_obj_tag(v_a_3933_) == 0)
{
lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
lean_del_object(v___x_3935_);
v___x_3937_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3938_ = l_Lean_MessageData_ofExpr(v_c_3924_);
v___x_3939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3937_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3941_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3941_, 0, v___x_3939_);
lean_ctor_set(v___x_3941_, 1, v___x_3940_);
v___x_3942_ = l_Lean_MessageData_ofExpr(v_target_3926_);
v___x_3943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3941_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3943_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3945_, v___y_3927_, v___y_3928_, v___y_3929_, v___y_3930_);
return v___x_3946_;
}
else
{
lean_object* v___x_3947_; lean_object* v___x_3949_; 
lean_dec_ref_known(v_a_3933_, 1);
lean_dec_ref(v_target_3926_);
lean_dec_ref(v_c_3924_);
v___x_3947_ = lean_box(0);
if (v_isShared_3936_ == 0)
{
lean_ctor_set(v___x_3935_, 0, v___x_3947_);
v___x_3949_ = v___x_3935_;
goto v_reusejp_3948_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3947_);
v___x_3949_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3948_;
}
v_reusejp_3948_:
{
return v___x_3949_;
}
}
}
}
else
{
lean_object* v_a_3952_; lean_object* v___x_3954_; uint8_t v_isShared_3955_; uint8_t v_isSharedCheck_3959_; 
lean_dec_ref(v_target_3926_);
lean_dec_ref(v_c_3924_);
v_a_3952_ = lean_ctor_get(v___x_3932_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3954_ = v___x_3932_;
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
else
{
lean_inc(v_a_3952_);
lean_dec(v___x_3932_);
v___x_3954_ = lean_box(0);
v_isShared_3955_ = v_isSharedCheck_3959_;
goto v_resetjp_3953_;
}
v_resetjp_3953_:
{
lean_object* v___x_3957_; 
if (v_isShared_3955_ == 0)
{
v___x_3957_ = v___x_3954_;
goto v_reusejp_3956_;
}
else
{
lean_object* v_reuseFailAlloc_3958_; 
v_reuseFailAlloc_3958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3958_, 0, v_a_3952_);
v___x_3957_ = v_reuseFailAlloc_3958_;
goto v_reusejp_3956_;
}
v_reusejp_3956_:
{
return v___x_3957_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_c_3960_, lean_object* v_x_3961_, lean_object* v_target_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_, lean_object* v___y_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_){
_start:
{
lean_object* v_res_3968_; 
v_res_3968_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_c_3960_, v_x_3961_, v_target_3962_, v___y_3963_, v___y_3964_, v___y_3965_, v___y_3966_);
lean_dec(v___y_3966_);
lean_dec_ref(v___y_3965_);
lean_dec(v___y_3964_);
lean_dec_ref(v___y_3963_);
lean_dec_ref(v_x_3961_);
return v_res_3968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_c_3969_, lean_object* v_a_3970_, lean_object* v_a_3971_, lean_object* v_a_3972_, lean_object* v_a_3973_){
_start:
{
lean_object* v___f_3975_; lean_object* v___x_3976_; 
lean_inc_ref(v_c_3969_);
v___f_3975_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3975_, 0, v_c_3969_);
lean_inc(v_a_3973_);
lean_inc_ref(v_a_3972_);
lean_inc(v_a_3971_);
lean_inc_ref(v_a_3970_);
v___x_3976_ = lean_infer_type(v_c_3969_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
if (lean_obj_tag(v___x_3976_) == 0)
{
lean_object* v_a_3977_; uint8_t v___x_3978_; lean_object* v___x_3979_; 
v_a_3977_ = lean_ctor_get(v___x_3976_, 0);
lean_inc(v_a_3977_);
lean_dec_ref_known(v___x_3976_, 1);
v___x_3978_ = 0;
v___x_3979_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3977_, v___f_3975_, v___x_3978_, v___x_3978_, v_a_3970_, v_a_3971_, v_a_3972_, v_a_3973_);
return v___x_3979_;
}
else
{
lean_object* v_a_3980_; lean_object* v___x_3982_; uint8_t v_isShared_3983_; uint8_t v_isSharedCheck_3987_; 
lean_dec_ref(v___f_3975_);
v_a_3980_ = lean_ctor_get(v___x_3976_, 0);
v_isSharedCheck_3987_ = !lean_is_exclusive(v___x_3976_);
if (v_isSharedCheck_3987_ == 0)
{
v___x_3982_ = v___x_3976_;
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
else
{
lean_inc(v_a_3980_);
lean_dec(v___x_3976_);
v___x_3982_ = lean_box(0);
v_isShared_3983_ = v_isSharedCheck_3987_;
goto v_resetjp_3981_;
}
v_resetjp_3981_:
{
lean_object* v___x_3985_; 
if (v_isShared_3983_ == 0)
{
v___x_3985_ = v___x_3982_;
goto v_reusejp_3984_;
}
else
{
lean_object* v_reuseFailAlloc_3986_; 
v_reuseFailAlloc_3986_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3986_, 0, v_a_3980_);
v___x_3985_ = v_reuseFailAlloc_3986_;
goto v_reusejp_3984_;
}
v_reusejp_3984_:
{
return v___x_3985_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_c_3988_, lean_object* v_a_3989_, lean_object* v_a_3990_, lean_object* v_a_3991_, lean_object* v_a_3992_, lean_object* v_a_3993_){
_start:
{
lean_object* v_res_3994_; 
v_res_3994_ = l_Lean_Meta_checkNonClassInstance(v_c_3988_, v_a_3989_, v_a_3990_, v_a_3991_, v_a_3992_);
lean_dec(v_a_3992_);
lean_dec_ref(v_a_3991_);
lean_dec(v_a_3990_);
lean_dec_ref(v_a_3989_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_4005_, lean_object* v___y_4006_){
_start:
{
lean_object* v___x_4008_; lean_object* v_env_4009_; lean_object* v___x_4010_; lean_object* v___x_4011_; 
v___x_4008_ = lean_st_ref_get(v___y_4006_);
v_env_4009_ = lean_ctor_get(v___x_4008_, 0);
lean_inc_ref(v_env_4009_);
lean_dec(v___x_4008_);
v___x_4010_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_4009_, v_declName_4005_);
v___x_4011_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4011_, 0, v___x_4010_);
return v___x_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_){
_start:
{
lean_object* v_res_4015_; 
v_res_4015_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4012_, v___y_4013_);
lean_dec(v___y_4013_);
return v_res_4015_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v___x_4022_; 
v___x_4022_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4016_, v___y_4020_);
return v___x_4022_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_){
_start:
{
lean_object* v_res_4029_; 
v_res_4029_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_4023_, v___y_4024_, v___y_4025_, v___y_4026_, v___y_4027_);
lean_dec(v___y_4027_);
lean_dec_ref(v___y_4026_);
lean_dec(v___y_4025_);
lean_dec_ref(v___y_4024_);
return v_res_4029_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4030_; lean_object* v___x_4031_; 
v___x_4030_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4031_, 0, v___x_4030_);
return v___x_4031_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4032_; lean_object* v___x_4033_; 
v___x_4032_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_4033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4033_, 0, v___x_4032_);
lean_ctor_set(v___x_4033_, 1, v___x_4032_);
return v___x_4033_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4034_; lean_object* v___x_4035_; 
v___x_4034_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_4035_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4035_, 0, v___x_4034_);
lean_ctor_set(v___x_4035_, 1, v___x_4034_);
lean_ctor_set(v___x_4035_, 2, v___x_4034_);
lean_ctor_set(v___x_4035_, 3, v___x_4034_);
lean_ctor_set(v___x_4035_, 4, v___x_4034_);
lean_ctor_set(v___x_4035_, 5, v___x_4034_);
return v___x_4035_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_4036_, lean_object* v_b_4037_, uint8_t v_kind_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_){
_start:
{
lean_object* v_toCold_4043_; lean_object* v_currNamespace_4044_; lean_object* v___x_4045_; lean_object* v_env_4046_; lean_object* v_nextMacroScope_4047_; lean_object* v_ngen_4048_; lean_object* v_auxDeclNGen_4049_; lean_object* v_traceState_4050_; lean_object* v_recordedDeps_4051_; lean_object* v_messages_4052_; lean_object* v_infoState_4053_; lean_object* v_snapshotTasks_4054_; lean_object* v___x_4056_; uint8_t v_isShared_4057_; uint8_t v_isSharedCheck_4081_; 
v_toCold_4043_ = lean_ctor_get(v___y_4040_, 0);
v_currNamespace_4044_ = lean_ctor_get(v_toCold_4043_, 4);
v___x_4045_ = lean_st_ref_take(v___y_4041_);
v_env_4046_ = lean_ctor_get(v___x_4045_, 0);
v_nextMacroScope_4047_ = lean_ctor_get(v___x_4045_, 1);
v_ngen_4048_ = lean_ctor_get(v___x_4045_, 2);
v_auxDeclNGen_4049_ = lean_ctor_get(v___x_4045_, 3);
v_traceState_4050_ = lean_ctor_get(v___x_4045_, 4);
v_recordedDeps_4051_ = lean_ctor_get(v___x_4045_, 6);
v_messages_4052_ = lean_ctor_get(v___x_4045_, 7);
v_infoState_4053_ = lean_ctor_get(v___x_4045_, 8);
v_snapshotTasks_4054_ = lean_ctor_get(v___x_4045_, 9);
v_isSharedCheck_4081_ = !lean_is_exclusive(v___x_4045_);
if (v_isSharedCheck_4081_ == 0)
{
lean_object* v_unused_4082_; 
v_unused_4082_ = lean_ctor_get(v___x_4045_, 5);
lean_dec(v_unused_4082_);
v___x_4056_ = v___x_4045_;
v_isShared_4057_ = v_isSharedCheck_4081_;
goto v_resetjp_4055_;
}
else
{
lean_inc(v_snapshotTasks_4054_);
lean_inc(v_infoState_4053_);
lean_inc(v_messages_4052_);
lean_inc(v_recordedDeps_4051_);
lean_inc(v_traceState_4050_);
lean_inc(v_auxDeclNGen_4049_);
lean_inc(v_ngen_4048_);
lean_inc(v_nextMacroScope_4047_);
lean_inc(v_env_4046_);
lean_dec(v___x_4045_);
v___x_4056_ = lean_box(0);
v_isShared_4057_ = v_isSharedCheck_4081_;
goto v_resetjp_4055_;
}
v_resetjp_4055_:
{
lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4061_; 
lean_inc(v_currNamespace_4044_);
v___x_4058_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_4046_, v_ext_4036_, v_b_4037_, v_kind_4038_, v_currNamespace_4044_);
v___x_4059_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_4057_ == 0)
{
lean_ctor_set(v___x_4056_, 5, v___x_4059_);
lean_ctor_set(v___x_4056_, 0, v___x_4058_);
v___x_4061_ = v___x_4056_;
goto v_reusejp_4060_;
}
else
{
lean_object* v_reuseFailAlloc_4080_; 
v_reuseFailAlloc_4080_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4080_, 0, v___x_4058_);
lean_ctor_set(v_reuseFailAlloc_4080_, 1, v_nextMacroScope_4047_);
lean_ctor_set(v_reuseFailAlloc_4080_, 2, v_ngen_4048_);
lean_ctor_set(v_reuseFailAlloc_4080_, 3, v_auxDeclNGen_4049_);
lean_ctor_set(v_reuseFailAlloc_4080_, 4, v_traceState_4050_);
lean_ctor_set(v_reuseFailAlloc_4080_, 5, v___x_4059_);
lean_ctor_set(v_reuseFailAlloc_4080_, 6, v_recordedDeps_4051_);
lean_ctor_set(v_reuseFailAlloc_4080_, 7, v_messages_4052_);
lean_ctor_set(v_reuseFailAlloc_4080_, 8, v_infoState_4053_);
lean_ctor_set(v_reuseFailAlloc_4080_, 9, v_snapshotTasks_4054_);
v___x_4061_ = v_reuseFailAlloc_4080_;
goto v_reusejp_4060_;
}
v_reusejp_4060_:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v_mctx_4064_; lean_object* v_zetaDeltaFVarIds_4065_; lean_object* v_postponed_4066_; lean_object* v_diag_4067_; lean_object* v___x_4069_; uint8_t v_isShared_4070_; uint8_t v_isSharedCheck_4078_; 
v___x_4062_ = lean_st_ref_put(v___y_4041_, v___x_4061_);
v___x_4063_ = lean_st_ref_take(v___y_4039_);
v_mctx_4064_ = lean_ctor_get(v___x_4063_, 0);
v_zetaDeltaFVarIds_4065_ = lean_ctor_get(v___x_4063_, 2);
v_postponed_4066_ = lean_ctor_get(v___x_4063_, 3);
v_diag_4067_ = lean_ctor_get(v___x_4063_, 4);
v_isSharedCheck_4078_ = !lean_is_exclusive(v___x_4063_);
if (v_isSharedCheck_4078_ == 0)
{
lean_object* v_unused_4079_; 
v_unused_4079_ = lean_ctor_get(v___x_4063_, 1);
lean_dec(v_unused_4079_);
v___x_4069_ = v___x_4063_;
v_isShared_4070_ = v_isSharedCheck_4078_;
goto v_resetjp_4068_;
}
else
{
lean_inc(v_diag_4067_);
lean_inc(v_postponed_4066_);
lean_inc(v_zetaDeltaFVarIds_4065_);
lean_inc(v_mctx_4064_);
lean_dec(v___x_4063_);
v___x_4069_ = lean_box(0);
v_isShared_4070_ = v_isSharedCheck_4078_;
goto v_resetjp_4068_;
}
v_resetjp_4068_:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; lean_object* v___x_4074_; 
v___x_4071_ = lean_box(0);
v___x_4072_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4070_ == 0)
{
lean_ctor_set(v___x_4069_, 1, v___x_4072_);
v___x_4074_ = v___x_4069_;
goto v_reusejp_4073_;
}
else
{
lean_object* v_reuseFailAlloc_4077_; 
v_reuseFailAlloc_4077_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4077_, 0, v_mctx_4064_);
lean_ctor_set(v_reuseFailAlloc_4077_, 1, v___x_4072_);
lean_ctor_set(v_reuseFailAlloc_4077_, 2, v_zetaDeltaFVarIds_4065_);
lean_ctor_set(v_reuseFailAlloc_4077_, 3, v_postponed_4066_);
lean_ctor_set(v_reuseFailAlloc_4077_, 4, v_diag_4067_);
v___x_4074_ = v_reuseFailAlloc_4077_;
goto v_reusejp_4073_;
}
v_reusejp_4073_:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = lean_st_ref_put(v___y_4039_, v___x_4074_);
v___x_4076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4076_, 0, v___x_4071_);
return v___x_4076_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_4083_, lean_object* v_b_4084_, lean_object* v_kind_4085_, lean_object* v___y_4086_, lean_object* v___y_4087_, lean_object* v___y_4088_, lean_object* v___y_4089_){
_start:
{
uint8_t v_kind_boxed_4090_; lean_object* v_res_4091_; 
v_kind_boxed_4090_ = lean_unbox(v_kind_4085_);
v_res_4091_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_4083_, v_b_4084_, v_kind_boxed_4090_, v___y_4086_, v___y_4087_, v___y_4088_);
lean_dec(v___y_4088_);
lean_dec_ref(v___y_4087_);
lean_dec(v___y_4086_);
return v_res_4091_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_4092_, lean_object* v_00_u03b2_4093_, lean_object* v_00_u03c3_4094_, lean_object* v_ext_4095_, lean_object* v_b_4096_, uint8_t v_kind_4097_, lean_object* v___y_4098_, lean_object* v___y_4099_, lean_object* v___y_4100_, lean_object* v___y_4101_){
_start:
{
lean_object* v___x_4103_; 
v___x_4103_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_4095_, v_b_4096_, v_kind_4097_, v___y_4099_, v___y_4100_, v___y_4101_);
return v___x_4103_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_4104_, lean_object* v_00_u03b2_4105_, lean_object* v_00_u03c3_4106_, lean_object* v_ext_4107_, lean_object* v_b_4108_, lean_object* v_kind_4109_, lean_object* v___y_4110_, lean_object* v___y_4111_, lean_object* v___y_4112_, lean_object* v___y_4113_, lean_object* v___y_4114_){
_start:
{
uint8_t v_kind_boxed_4115_; lean_object* v_res_4116_; 
v_kind_boxed_4115_ = lean_unbox(v_kind_4109_);
v_res_4116_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_4104_, v_00_u03b2_4105_, v_00_u03c3_4106_, v_ext_4107_, v_b_4108_, v_kind_boxed_4115_, v___y_4110_, v___y_4111_, v___y_4112_, v___y_4113_);
lean_dec(v___y_4113_);
lean_dec_ref(v___y_4112_);
lean_dec(v___y_4111_);
lean_dec_ref(v___y_4110_);
return v_res_4116_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___x_4120_; lean_object* v_env_4121_; uint8_t v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; 
v___x_4120_ = lean_st_ref_get(v___y_4118_);
v_env_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc_ref(v_env_4121_);
lean_dec(v___x_4120_);
v___x_4122_ = l_Lean_getReducibilityStatusCore(v_env_4121_, v_declName_4117_);
v___x_4123_ = lean_box(v___x_4122_);
v___x_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
return v___x_4124_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_4125_, lean_object* v___y_4126_, lean_object* v___y_4127_){
_start:
{
lean_object* v_res_4128_; 
v_res_4128_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4125_, v___y_4126_);
lean_dec(v___y_4126_);
return v_res_4128_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v___x_4135_; 
v___x_4135_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4129_, v___y_4133_);
return v___x_4135_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_, lean_object* v___y_4140_, lean_object* v___y_4141_){
_start:
{
lean_object* v_res_4142_; 
v_res_4142_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_4136_, v___y_4137_, v___y_4138_, v___y_4139_, v___y_4140_);
lean_dec(v___y_4140_);
lean_dec_ref(v___y_4139_);
lean_dec(v___y_4138_);
lean_dec_ref(v___y_4137_);
return v_res_4142_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_4143_, lean_object* v_msg_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_, lean_object* v___y_4148_){
_start:
{
lean_object* v_toCold_4150_; lean_object* v_currRecDepth_4151_; lean_object* v_ref_4152_; uint16_t v_optionFlags_4153_; uint8_t v_suppressElabErrors_4154_; uint8_t v_isRecordingDeps_4155_; lean_object* v_ref_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; 
v_toCold_4150_ = lean_ctor_get(v___y_4147_, 0);
v_currRecDepth_4151_ = lean_ctor_get(v___y_4147_, 1);
v_ref_4152_ = lean_ctor_get(v___y_4147_, 2);
v_optionFlags_4153_ = lean_ctor_get_uint16(v___y_4147_, sizeof(void*)*3);
v_suppressElabErrors_4154_ = lean_ctor_get_uint8(v___y_4147_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4155_ = lean_ctor_get_uint8(v___y_4147_, sizeof(void*)*3 + 3);
v_ref_4156_ = l_Lean_replaceRef(v_ref_4143_, v_ref_4152_);
lean_inc(v_currRecDepth_4151_);
lean_inc_ref(v_toCold_4150_);
v___x_4157_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4157_, 0, v_toCold_4150_);
lean_ctor_set(v___x_4157_, 1, v_currRecDepth_4151_);
lean_ctor_set(v___x_4157_, 2, v_ref_4156_);
lean_ctor_set_uint16(v___x_4157_, sizeof(void*)*3, v_optionFlags_4153_);
lean_ctor_set_uint8(v___x_4157_, sizeof(void*)*3 + 2, v_suppressElabErrors_4154_);
lean_ctor_set_uint8(v___x_4157_, sizeof(void*)*3 + 3, v_isRecordingDeps_4155_);
v___x_4158_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_4144_, v___y_4145_, v___y_4146_, v___x_4157_, v___y_4148_);
lean_dec_ref_known(v___x_4157_, 3);
return v___x_4158_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_4159_, lean_object* v_msg_4160_, lean_object* v___y_4161_, lean_object* v___y_4162_, lean_object* v___y_4163_, lean_object* v___y_4164_, lean_object* v___y_4165_){
_start:
{
lean_object* v_res_4166_; 
v_res_4166_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4159_, v_msg_4160_, v___y_4161_, v___y_4162_, v___y_4163_, v___y_4164_);
lean_dec(v___y_4164_);
lean_dec_ref(v___y_4163_);
lean_dec(v___y_4162_);
lean_dec_ref(v___y_4161_);
lean_dec(v_ref_4159_);
return v_res_4166_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; 
v___x_4167_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
return v___x_4168_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; 
v___x_4169_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_4170_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4171_ = lean_unsigned_to_nat(0u);
v___x_4172_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4172_, 0, v___x_4171_);
lean_ctor_set(v___x_4172_, 1, v___x_4171_);
lean_ctor_set(v___x_4172_, 2, v___x_4171_);
lean_ctor_set(v___x_4172_, 3, v___x_4171_);
lean_ctor_set(v___x_4172_, 4, v___x_4170_);
lean_ctor_set(v___x_4172_, 5, v___x_4170_);
lean_ctor_set(v___x_4172_, 6, v___x_4170_);
lean_ctor_set(v___x_4172_, 7, v___x_4170_);
lean_ctor_set(v___x_4172_, 8, v___x_4170_);
lean_ctor_set(v___x_4172_, 9, v___x_4170_);
lean_ctor_set(v___x_4172_, 10, v___x_4169_);
return v___x_4172_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; lean_object* v___x_4175_; 
v___x_4173_ = lean_unsigned_to_nat(32u);
v___x_4174_ = lean_mk_empty_array_with_capacity(v___x_4173_);
v___x_4175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
return v___x_4175_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
size_t v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; 
v___x_4176_ = ((size_t)5ULL);
v___x_4177_ = lean_unsigned_to_nat(0u);
v___x_4178_ = lean_unsigned_to_nat(32u);
v___x_4179_ = lean_mk_empty_array_with_capacity(v___x_4178_);
v___x_4180_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4181_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4181_, 0, v___x_4180_);
lean_ctor_set(v___x_4181_, 1, v___x_4179_);
lean_ctor_set(v___x_4181_, 2, v___x_4177_);
lean_ctor_set(v___x_4181_, 3, v___x_4177_);
lean_ctor_set_usize(v___x_4181_, 4, v___x_4176_);
return v___x_4181_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; 
v___x_4182_ = lean_box(1);
v___x_4183_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4184_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4185_, 0, v___x_4184_);
lean_ctor_set(v___x_4185_, 1, v___x_4183_);
lean_ctor_set(v___x_4185_, 2, v___x_4182_);
return v___x_4185_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; 
v___x_4187_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5));
v___x_4188_ = l_Lean_stringToMessageData(v___x_4187_);
return v___x_4188_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_4190_; lean_object* v___x_4191_; 
v___x_4190_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7));
v___x_4191_ = l_Lean_stringToMessageData(v___x_4190_);
return v___x_4191_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10(void){
_start:
{
lean_object* v___x_4193_; lean_object* v___x_4194_; 
v___x_4193_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9));
v___x_4194_ = l_Lean_stringToMessageData(v___x_4193_);
return v___x_4194_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12(void){
_start:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; 
v___x_4196_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11));
v___x_4197_ = l_Lean_stringToMessageData(v___x_4196_);
return v___x_4197_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14(void){
_start:
{
lean_object* v___x_4199_; lean_object* v___x_4200_; 
v___x_4199_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13));
v___x_4200_ = l_Lean_stringToMessageData(v___x_4199_);
return v___x_4200_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16(void){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15));
v___x_4203_ = l_Lean_stringToMessageData(v___x_4202_);
return v___x_4203_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18(void){
_start:
{
lean_object* v___x_4205_; lean_object* v___x_4206_; 
v___x_4205_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17));
v___x_4206_ = l_Lean_stringToMessageData(v___x_4205_);
return v___x_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_4207_, lean_object* v_declHint_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v_env_4213_; uint8_t v___x_4214_; 
v___x_4211_ = lean_box(0);
v___x_4212_ = lean_st_ref_get(v___y_4209_);
v_env_4213_ = lean_ctor_get(v___x_4212_, 0);
lean_inc_ref(v_env_4213_);
lean_dec(v___x_4212_);
v___x_4214_ = l_Lean_Name_isAnonymous(v_declHint_4208_);
if (v___x_4214_ == 0)
{
uint8_t v_isExporting_4215_; 
v_isExporting_4215_ = lean_ctor_get_uint8(v_env_4213_, sizeof(void*)*13);
if (v_isExporting_4215_ == 0)
{
lean_object* v___x_4216_; 
lean_dec_ref(v_env_4213_);
lean_dec(v_declHint_4208_);
v___x_4216_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4216_, 0, v_msg_4207_);
return v___x_4216_;
}
else
{
lean_object* v___x_4217_; uint8_t v___x_4218_; 
lean_inc_ref(v_env_4213_);
v___x_4217_ = l_Lean_Environment_setExporting(v_env_4213_, v___x_4214_);
lean_inc(v_declHint_4208_);
lean_inc_ref(v___x_4217_);
v___x_4218_ = l_Lean_Environment_contains(v___x_4217_, v_declHint_4208_, v_isExporting_4215_);
if (v___x_4218_ == 0)
{
lean_object* v___x_4219_; 
lean_dec_ref(v___x_4217_);
lean_dec_ref(v_env_4213_);
lean_dec(v_declHint_4208_);
v___x_4219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4219_, 0, v_msg_4207_);
return v___x_4219_;
}
else
{
lean_object* v___x_4220_; lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v_c_4225_; lean_object* v___x_4226_; 
v___x_4220_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4221_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_4222_ = l_Lean_Options_empty;
v___x_4223_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4223_, 0, v___x_4217_);
lean_ctor_set(v___x_4223_, 1, v___x_4220_);
lean_ctor_set(v___x_4223_, 2, v___x_4221_);
lean_ctor_set(v___x_4223_, 3, v___x_4222_);
lean_inc(v_declHint_4208_);
v___x_4224_ = l_Lean_MessageData_ofConstName(v_declHint_4208_, v___x_4214_);
v_c_4225_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4225_, 0, v___x_4223_);
lean_ctor_set(v_c_4225_, 1, v___x_4224_);
v___x_4226_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4213_, v_declHint_4208_);
if (lean_obj_tag(v___x_4226_) == 0)
{
lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; 
lean_dec_ref(v_env_4213_);
lean_dec(v_declHint_4208_);
v___x_4227_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6);
v___x_4228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
lean_ctor_set(v___x_4228_, 1, v_c_4225_);
v___x_4229_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8);
v___x_4230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4230_, 0, v___x_4228_);
lean_ctor_set(v___x_4230_, 1, v___x_4229_);
v___x_4231_ = l_Lean_MessageData_note(v___x_4230_);
v___x_4232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4232_, 0, v_msg_4207_);
lean_ctor_set(v___x_4232_, 1, v___x_4231_);
v___x_4233_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4232_);
return v___x_4233_;
}
else
{
lean_object* v_val_4234_; lean_object* v___x_4236_; uint8_t v_isShared_4237_; uint8_t v_isSharedCheck_4268_; 
v_val_4234_ = lean_ctor_get(v___x_4226_, 0);
v_isSharedCheck_4268_ = !lean_is_exclusive(v___x_4226_);
if (v_isSharedCheck_4268_ == 0)
{
v___x_4236_ = v___x_4226_;
v_isShared_4237_ = v_isSharedCheck_4268_;
goto v_resetjp_4235_;
}
else
{
lean_inc(v_val_4234_);
lean_dec(v___x_4226_);
v___x_4236_ = lean_box(0);
v_isShared_4237_ = v_isSharedCheck_4268_;
goto v_resetjp_4235_;
}
v_resetjp_4235_:
{
lean_object* v___x_4238_; lean_object* v_moduleNames_4239_; lean_object* v_mod_4240_; uint8_t v___x_4241_; 
v___x_4238_ = l_Lean_Environment_header(v_env_4213_);
lean_dec_ref(v_env_4213_);
v_moduleNames_4239_ = lean_ctor_get(v___x_4238_, 4);
lean_inc_ref(v_moduleNames_4239_);
lean_dec_ref(v___x_4238_);
v_mod_4240_ = lean_array_get(v___x_4211_, v_moduleNames_4239_, v_val_4234_);
lean_dec(v_val_4234_);
lean_dec_ref(v_moduleNames_4239_);
v___x_4241_ = l_Lean_isPrivateName(v_declHint_4208_);
lean_dec(v_declHint_4208_);
if (v___x_4241_ == 0)
{
lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4253_; 
v___x_4242_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10);
v___x_4243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4242_);
lean_ctor_set(v___x_4243_, 1, v_c_4225_);
v___x_4244_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12);
v___x_4245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4243_);
lean_ctor_set(v___x_4245_, 1, v___x_4244_);
v___x_4246_ = l_Lean_MessageData_ofName(v_mod_4240_);
v___x_4247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4247_, 0, v___x_4245_);
lean_ctor_set(v___x_4247_, 1, v___x_4246_);
v___x_4248_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14);
v___x_4249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4249_, 0, v___x_4247_);
lean_ctor_set(v___x_4249_, 1, v___x_4248_);
v___x_4250_ = l_Lean_MessageData_note(v___x_4249_);
v___x_4251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4251_, 0, v_msg_4207_);
lean_ctor_set(v___x_4251_, 1, v___x_4250_);
if (v_isShared_4237_ == 0)
{
lean_ctor_set_tag(v___x_4236_, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4251_);
v___x_4253_ = v___x_4236_;
goto v_reusejp_4252_;
}
else
{
lean_object* v_reuseFailAlloc_4254_; 
v_reuseFailAlloc_4254_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4254_, 0, v___x_4251_);
v___x_4253_ = v_reuseFailAlloc_4254_;
goto v_reusejp_4252_;
}
v_reusejp_4252_:
{
return v___x_4253_;
}
}
else
{
lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4257_; lean_object* v___x_4258_; lean_object* v___x_4259_; lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4266_; 
v___x_4255_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6);
v___x_4256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4256_, 0, v___x_4255_);
lean_ctor_set(v___x_4256_, 1, v_c_4225_);
v___x_4257_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16);
v___x_4258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4258_, 0, v___x_4256_);
lean_ctor_set(v___x_4258_, 1, v___x_4257_);
v___x_4259_ = l_Lean_MessageData_ofName(v_mod_4240_);
v___x_4260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4260_, 0, v___x_4258_);
lean_ctor_set(v___x_4260_, 1, v___x_4259_);
v___x_4261_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18);
v___x_4262_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4262_, 0, v___x_4260_);
lean_ctor_set(v___x_4262_, 1, v___x_4261_);
v___x_4263_ = l_Lean_MessageData_note(v___x_4262_);
v___x_4264_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4264_, 0, v_msg_4207_);
lean_ctor_set(v___x_4264_, 1, v___x_4263_);
if (v_isShared_4237_ == 0)
{
lean_ctor_set_tag(v___x_4236_, 0);
lean_ctor_set(v___x_4236_, 0, v___x_4264_);
v___x_4266_ = v___x_4236_;
goto v_reusejp_4265_;
}
else
{
lean_object* v_reuseFailAlloc_4267_; 
v_reuseFailAlloc_4267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4267_, 0, v___x_4264_);
v___x_4266_ = v_reuseFailAlloc_4267_;
goto v_reusejp_4265_;
}
v_reusejp_4265_:
{
return v___x_4266_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4269_; 
lean_dec_ref(v_env_4213_);
lean_dec(v_declHint_4208_);
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v_msg_4207_);
return v___x_4269_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_4270_, lean_object* v_declHint_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_){
_start:
{
lean_object* v_res_4274_; 
v_res_4274_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4270_, v_declHint_4271_, v___y_4272_);
lean_dec(v___y_4272_);
return v_res_4274_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(lean_object* v_msg_4275_, lean_object* v_declHint_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_, lean_object* v___y_4279_, lean_object* v___y_4280_){
_start:
{
lean_object* v___x_4282_; lean_object* v_a_4283_; lean_object* v___x_4285_; uint8_t v_isShared_4286_; uint8_t v_isSharedCheck_4292_; 
v___x_4282_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4275_, v_declHint_4276_, v___y_4280_);
v_a_4283_ = lean_ctor_get(v___x_4282_, 0);
v_isSharedCheck_4292_ = !lean_is_exclusive(v___x_4282_);
if (v_isSharedCheck_4292_ == 0)
{
v___x_4285_ = v___x_4282_;
v_isShared_4286_ = v_isSharedCheck_4292_;
goto v_resetjp_4284_;
}
else
{
lean_inc(v_a_4283_);
lean_dec(v___x_4282_);
v___x_4285_ = lean_box(0);
v_isShared_4286_ = v_isSharedCheck_4292_;
goto v_resetjp_4284_;
}
v_resetjp_4284_:
{
lean_object* v___x_4287_; lean_object* v___x_4288_; lean_object* v___x_4290_; 
v___x_4287_ = l_Lean_unknownIdentifierMessageTag;
v___x_4288_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4288_, 0, v___x_4287_);
lean_ctor_set(v___x_4288_, 1, v_a_4283_);
if (v_isShared_4286_ == 0)
{
lean_ctor_set(v___x_4285_, 0, v___x_4288_);
v___x_4290_ = v___x_4285_;
goto v_reusejp_4289_;
}
else
{
lean_object* v_reuseFailAlloc_4291_; 
v_reuseFailAlloc_4291_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4291_, 0, v___x_4288_);
v___x_4290_ = v_reuseFailAlloc_4291_;
goto v_reusejp_4289_;
}
v_reusejp_4289_:
{
return v___x_4290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_4293_, lean_object* v_declHint_4294_, lean_object* v___y_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v_res_4300_; 
v_res_4300_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4293_, v_declHint_4294_, v___y_4295_, v___y_4296_, v___y_4297_, v___y_4298_);
lean_dec(v___y_4298_);
lean_dec_ref(v___y_4297_);
lean_dec(v___y_4296_);
lean_dec_ref(v___y_4295_);
return v_res_4300_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_ref_4301_, lean_object* v_msg_4302_, lean_object* v_declHint_4303_, lean_object* v___y_4304_, lean_object* v___y_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_){
_start:
{
lean_object* v___x_4309_; lean_object* v_a_4310_; lean_object* v___x_4311_; 
v___x_4309_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4302_, v_declHint_4303_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
v_a_4310_ = lean_ctor_get(v___x_4309_, 0);
lean_inc(v_a_4310_);
lean_dec_ref(v___x_4309_);
v___x_4311_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4301_, v_a_4310_, v___y_4304_, v___y_4305_, v___y_4306_, v___y_4307_);
return v___x_4311_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_ref_4312_, lean_object* v_msg_4313_, lean_object* v_declHint_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4312_, v_msg_4313_, v_declHint_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
lean_dec(v_ref_4312_);
return v_res_4320_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_4322_; lean_object* v___x_4323_; 
v___x_4322_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_4323_ = l_Lean_stringToMessageData(v___x_4322_);
return v___x_4323_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_4324_, lean_object* v_constName_4325_, lean_object* v___y_4326_, lean_object* v___y_4327_, lean_object* v___y_4328_, lean_object* v___y_4329_){
_start:
{
lean_object* v___x_4331_; uint8_t v___x_4332_; lean_object* v___x_4333_; lean_object* v___x_4334_; lean_object* v___x_4335_; lean_object* v___x_4336_; lean_object* v___x_4337_; 
v___x_4331_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_4332_ = 0;
lean_inc(v_constName_4325_);
v___x_4333_ = l_Lean_MessageData_ofConstName(v_constName_4325_, v___x_4332_);
v___x_4334_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4334_, 0, v___x_4331_);
lean_ctor_set(v___x_4334_, 1, v___x_4333_);
v___x_4335_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4336_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4336_, 0, v___x_4334_);
lean_ctor_set(v___x_4336_, 1, v___x_4335_);
v___x_4337_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4324_, v___x_4336_, v_constName_4325_, v___y_4326_, v___y_4327_, v___y_4328_, v___y_4329_);
return v___x_4337_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_4338_, lean_object* v_constName_4339_, lean_object* v___y_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_){
_start:
{
lean_object* v_res_4345_; 
v_res_4345_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4338_, v_constName_4339_, v___y_4340_, v___y_4341_, v___y_4342_, v___y_4343_);
lean_dec(v___y_4343_);
lean_dec_ref(v___y_4342_);
lean_dec(v___y_4341_);
lean_dec_ref(v___y_4340_);
lean_dec(v_ref_4338_);
return v_res_4345_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_){
_start:
{
lean_object* v_ref_4352_; lean_object* v___x_4353_; 
v_ref_4352_ = lean_ctor_get(v___y_4349_, 2);
v___x_4353_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4352_, v_constName_4346_, v___y_4347_, v___y_4348_, v___y_4349_, v___y_4350_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_4354_, lean_object* v___y_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v_res_4360_; 
v_res_4360_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4354_, v___y_4355_, v___y_4356_, v___y_4357_, v___y_4358_);
lean_dec(v___y_4358_);
lean_dec_ref(v___y_4357_);
lean_dec(v___y_4356_);
lean_dec_ref(v___y_4355_);
return v_res_4360_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v___x_4367_; lean_object* v_env_4368_; uint8_t v___x_4369_; lean_object* v___x_4370_; 
v___x_4367_ = lean_st_ref_get(v___y_4365_);
v_env_4368_ = lean_ctor_get(v___x_4367_, 0);
lean_inc_ref(v_env_4368_);
lean_dec(v___x_4367_);
v___x_4369_ = 0;
lean_inc(v_constName_4361_);
v___x_4370_ = l_Lean_Environment_find_x3f(v_env_4368_, v_constName_4361_, v___x_4369_);
if (lean_obj_tag(v___x_4370_) == 0)
{
lean_object* v___x_4371_; 
v___x_4371_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
return v___x_4371_;
}
else
{
lean_object* v_val_4372_; lean_object* v___x_4374_; uint8_t v_isShared_4375_; uint8_t v_isSharedCheck_4379_; 
lean_dec(v_constName_4361_);
v_val_4372_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4374_ = v___x_4370_;
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
else
{
lean_inc(v_val_4372_);
lean_dec(v___x_4370_);
v___x_4374_ = lean_box(0);
v_isShared_4375_ = v_isSharedCheck_4379_;
goto v_resetjp_4373_;
}
v_resetjp_4373_:
{
lean_object* v___x_4377_; 
if (v_isShared_4375_ == 0)
{
lean_ctor_set_tag(v___x_4374_, 0);
v___x_4377_ = v___x_4374_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v_val_4372_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_4380_, lean_object* v___y_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v_res_4386_; 
v_res_4386_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_4380_, v___y_4381_, v___y_4382_, v___y_4383_, v___y_4384_);
lean_dec(v___y_4384_);
lean_dec_ref(v___y_4383_);
lean_dec(v___y_4382_);
lean_dec_ref(v___y_4381_);
return v_res_4386_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_){
_start:
{
lean_object* v___x_4393_; lean_object* v_env_4394_; uint8_t v___x_4395_; lean_object* v___x_4396_; 
v___x_4393_ = lean_st_ref_get(v___y_4391_);
v_env_4394_ = lean_ctor_get(v___x_4393_, 0);
lean_inc_ref(v_env_4394_);
lean_dec(v___x_4393_);
v___x_4395_ = 0;
lean_inc(v_constName_4387_);
v___x_4396_ = l_Lean_Environment_findConstVal_x3f(v_env_4394_, v_constName_4387_, v___x_4395_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v___x_4397_; 
v___x_4397_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4387_, v___y_4388_, v___y_4389_, v___y_4390_, v___y_4391_);
return v___x_4397_;
}
else
{
lean_object* v_val_4398_; lean_object* v___x_4400_; uint8_t v_isShared_4401_; uint8_t v_isSharedCheck_4405_; 
lean_dec(v_constName_4387_);
v_val_4398_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4405_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4405_ == 0)
{
v___x_4400_ = v___x_4396_;
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
else
{
lean_inc(v_val_4398_);
lean_dec(v___x_4396_);
v___x_4400_ = lean_box(0);
v_isShared_4401_ = v_isSharedCheck_4405_;
goto v_resetjp_4399_;
}
v_resetjp_4399_:
{
lean_object* v___x_4403_; 
if (v_isShared_4401_ == 0)
{
lean_ctor_set_tag(v___x_4400_, 0);
v___x_4403_ = v___x_4400_;
goto v_reusejp_4402_;
}
else
{
lean_object* v_reuseFailAlloc_4404_; 
v_reuseFailAlloc_4404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4404_, 0, v_val_4398_);
v___x_4403_ = v_reuseFailAlloc_4404_;
goto v_reusejp_4402_;
}
v_reusejp_4402_:
{
return v___x_4403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4406_, lean_object* v___y_4407_, lean_object* v___y_4408_, lean_object* v___y_4409_, lean_object* v___y_4410_, lean_object* v___y_4411_){
_start:
{
lean_object* v_res_4412_; 
v_res_4412_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4406_, v___y_4407_, v___y_4408_, v___y_4409_, v___y_4410_);
lean_dec(v___y_4410_);
lean_dec_ref(v___y_4409_);
lean_dec(v___y_4408_);
lean_dec_ref(v___y_4407_);
return v_res_4412_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4413_, lean_object* v_a_4414_){
_start:
{
if (lean_obj_tag(v_a_4413_) == 0)
{
lean_object* v___x_4415_; 
v___x_4415_ = l_List_reverse___redArg(v_a_4414_);
return v___x_4415_;
}
else
{
lean_object* v_head_4416_; lean_object* v_tail_4417_; lean_object* v___x_4419_; uint8_t v_isShared_4420_; uint8_t v_isSharedCheck_4426_; 
v_head_4416_ = lean_ctor_get(v_a_4413_, 0);
v_tail_4417_ = lean_ctor_get(v_a_4413_, 1);
v_isSharedCheck_4426_ = !lean_is_exclusive(v_a_4413_);
if (v_isSharedCheck_4426_ == 0)
{
v___x_4419_ = v_a_4413_;
v_isShared_4420_ = v_isSharedCheck_4426_;
goto v_resetjp_4418_;
}
else
{
lean_inc(v_tail_4417_);
lean_inc(v_head_4416_);
lean_dec(v_a_4413_);
v___x_4419_ = lean_box(0);
v_isShared_4420_ = v_isSharedCheck_4426_;
goto v_resetjp_4418_;
}
v_resetjp_4418_:
{
lean_object* v___x_4421_; lean_object* v___x_4423_; 
v___x_4421_ = l_Lean_mkLevelParam(v_head_4416_);
if (v_isShared_4420_ == 0)
{
lean_ctor_set(v___x_4419_, 1, v_a_4414_);
lean_ctor_set(v___x_4419_, 0, v___x_4421_);
v___x_4423_ = v___x_4419_;
goto v_reusejp_4422_;
}
else
{
lean_object* v_reuseFailAlloc_4425_; 
v_reuseFailAlloc_4425_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4425_, 0, v___x_4421_);
lean_ctor_set(v_reuseFailAlloc_4425_, 1, v_a_4414_);
v___x_4423_ = v_reuseFailAlloc_4425_;
goto v_reusejp_4422_;
}
v_reusejp_4422_:
{
v_a_4413_ = v_tail_4417_;
v_a_4414_ = v___x_4423_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4427_, lean_object* v___y_4428_, lean_object* v___y_4429_, lean_object* v___y_4430_, lean_object* v___y_4431_){
_start:
{
lean_object* v___x_4433_; 
lean_inc(v_constName_4427_);
v___x_4433_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4427_, v___y_4428_, v___y_4429_, v___y_4430_, v___y_4431_);
if (lean_obj_tag(v___x_4433_) == 0)
{
lean_object* v_a_4434_; lean_object* v___x_4436_; uint8_t v_isShared_4437_; uint8_t v_isSharedCheck_4445_; 
v_a_4434_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4445_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4445_ == 0)
{
v___x_4436_ = v___x_4433_;
v_isShared_4437_ = v_isSharedCheck_4445_;
goto v_resetjp_4435_;
}
else
{
lean_inc(v_a_4434_);
lean_dec(v___x_4433_);
v___x_4436_ = lean_box(0);
v_isShared_4437_ = v_isSharedCheck_4445_;
goto v_resetjp_4435_;
}
v_resetjp_4435_:
{
lean_object* v_levelParams_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4443_; 
v_levelParams_4438_ = lean_ctor_get(v_a_4434_, 1);
lean_inc(v_levelParams_4438_);
lean_dec(v_a_4434_);
v___x_4439_ = lean_box(0);
v___x_4440_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4438_, v___x_4439_);
v___x_4441_ = l_Lean_mkConst(v_constName_4427_, v___x_4440_);
if (v_isShared_4437_ == 0)
{
lean_ctor_set(v___x_4436_, 0, v___x_4441_);
v___x_4443_ = v___x_4436_;
goto v_reusejp_4442_;
}
else
{
lean_object* v_reuseFailAlloc_4444_; 
v_reuseFailAlloc_4444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4444_, 0, v___x_4441_);
v___x_4443_ = v_reuseFailAlloc_4444_;
goto v_reusejp_4442_;
}
v_reusejp_4442_:
{
return v___x_4443_;
}
}
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec(v_constName_4427_);
v_a_4446_ = lean_ctor_get(v___x_4433_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4433_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4433_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4433_);
v___x_4448_ = lean_box(0);
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
v_resetjp_4447_:
{
lean_object* v___x_4451_; 
if (v_isShared_4449_ == 0)
{
v___x_4451_ = v___x_4448_;
goto v_reusejp_4450_;
}
else
{
lean_object* v_reuseFailAlloc_4452_; 
v_reuseFailAlloc_4452_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4452_, 0, v_a_4446_);
v___x_4451_ = v_reuseFailAlloc_4452_;
goto v_reusejp_4450_;
}
v_reusejp_4450_:
{
return v___x_4451_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4454_, lean_object* v___y_4455_, lean_object* v___y_4456_, lean_object* v___y_4457_, lean_object* v___y_4458_, lean_object* v___y_4459_){
_start:
{
lean_object* v_res_4460_; 
v_res_4460_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4454_, v___y_4455_, v___y_4456_, v___y_4457_, v___y_4458_);
lean_dec(v___y_4458_);
lean_dec_ref(v___y_4457_);
lean_dec(v___y_4456_);
lean_dec_ref(v___y_4455_);
return v_res_4460_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4462_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4463_ = l_Lean_stringToMessageData(v___x_4462_);
return v___x_4463_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4465_; lean_object* v___x_4466_; 
v___x_4465_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4466_ = l_Lean_stringToMessageData(v___x_4465_);
return v___x_4466_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4468_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_4469_ = l_Lean_stringToMessageData(v___x_4468_);
return v___x_4469_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__7(void){
_start:
{
lean_object* v___x_4471_; lean_object* v___x_4472_; 
v___x_4471_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__6));
v___x_4472_ = l_Lean_stringToMessageData(v___x_4471_);
return v___x_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4473_, uint8_t v_attrKind_4474_, lean_object* v_prio_4475_, lean_object* v_a_4476_, lean_object* v_a_4477_, lean_object* v_a_4478_, lean_object* v_a_4479_){
_start:
{
lean_object* v___x_4481_; 
lean_inc(v_declName_4473_);
v___x_4481_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4473_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
if (lean_obj_tag(v___x_4481_) == 0)
{
lean_object* v_a_4482_; lean_object* v___y_4484_; lean_object* v___y_4485_; lean_object* v___y_4486_; lean_object* v___y_4487_; lean_object* v___y_4488_; lean_object* v___y_4512_; lean_object* v___y_4513_; lean_object* v___y_4514_; lean_object* v___y_4515_; lean_object* v___x_4560_; 
v_a_4482_ = lean_ctor_get(v___x_4481_, 0);
lean_inc(v_a_4482_);
lean_dec_ref_known(v___x_4481_, 1);
lean_inc(v_declName_4473_);
v___x_4560_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4473_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
if (lean_obj_tag(v___x_4560_) == 0)
{
lean_object* v_a_4561_; lean_object* v___x_4562_; uint8_t v___x_4563_; 
v_a_4561_ = lean_ctor_get(v___x_4560_, 0);
lean_inc(v_a_4561_);
lean_dec_ref_known(v___x_4560_, 1);
v___x_4562_ = l_Lean_ConstantInfo_type(v_a_4561_);
v___x_4563_ = l_Lean_Expr_hasSorry(v___x_4562_);
lean_dec_ref(v___x_4562_);
if (v___x_4563_ == 0)
{
lean_object* v___x_4564_; 
lean_inc(v_a_4482_);
v___x_4564_ = l_Lean_Meta_checkNonClassInstance(v_a_4482_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
if (lean_obj_tag(v___x_4564_) == 0)
{
lean_object* v___x_4565_; 
lean_dec_ref_known(v___x_4564_, 1);
v___x_4565_ = l_Lean_Meta_checkImpossibleInstance(v_a_4561_, v_a_4476_, v_a_4477_, v_a_4478_, v_a_4479_);
lean_dec(v_a_4561_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_dec_ref_known(v___x_4565_, 1);
v___y_4512_ = v_a_4476_;
v___y_4513_ = v_a_4477_;
v___y_4514_ = v_a_4478_;
v___y_4515_ = v_a_4479_;
goto v___jp_4511_;
}
else
{
lean_dec(v_a_4482_);
lean_dec(v_prio_4475_);
lean_dec(v_declName_4473_);
return v___x_4565_;
}
}
else
{
lean_dec(v_a_4561_);
lean_dec(v_a_4482_);
lean_dec(v_prio_4475_);
lean_dec(v_declName_4473_);
return v___x_4564_;
}
}
else
{
lean_dec(v_a_4561_);
v___y_4512_ = v_a_4476_;
v___y_4513_ = v_a_4477_;
v___y_4514_ = v_a_4478_;
v___y_4515_ = v_a_4479_;
goto v___jp_4511_;
}
}
else
{
lean_object* v_a_4566_; lean_object* v___x_4568_; uint8_t v_isShared_4569_; uint8_t v_isSharedCheck_4573_; 
lean_dec(v_a_4482_);
lean_dec(v_prio_4475_);
lean_dec(v_declName_4473_);
v_a_4566_ = lean_ctor_get(v___x_4560_, 0);
v_isSharedCheck_4573_ = !lean_is_exclusive(v___x_4560_);
if (v_isSharedCheck_4573_ == 0)
{
v___x_4568_ = v___x_4560_;
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
else
{
lean_inc(v_a_4566_);
lean_dec(v___x_4560_);
v___x_4568_ = lean_box(0);
v_isShared_4569_ = v_isSharedCheck_4573_;
goto v_resetjp_4567_;
}
v_resetjp_4567_:
{
lean_object* v___x_4571_; 
if (v_isShared_4569_ == 0)
{
v___x_4571_ = v___x_4568_;
goto v_reusejp_4570_;
}
else
{
lean_object* v_reuseFailAlloc_4572_; 
v_reuseFailAlloc_4572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4572_, 0, v_a_4566_);
v___x_4571_ = v_reuseFailAlloc_4572_;
goto v_reusejp_4570_;
}
v_reusejp_4570_:
{
return v___x_4571_;
}
}
}
v___jp_4483_:
{
lean_object* v___x_4489_; lean_object* v_a_4490_; lean_object* v___x_4492_; uint8_t v_isShared_4493_; uint8_t v_isSharedCheck_4510_; 
lean_inc(v_declName_4473_);
v___x_4489_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4473_, v___y_4488_);
v_a_4490_ = lean_ctor_get(v___x_4489_, 0);
v_isSharedCheck_4510_ = !lean_is_exclusive(v___x_4489_);
if (v_isSharedCheck_4510_ == 0)
{
v___x_4492_ = v___x_4489_;
v_isShared_4493_ = v_isSharedCheck_4510_;
goto v_resetjp_4491_;
}
else
{
lean_inc(v_a_4490_);
lean_dec(v___x_4489_);
v___x_4492_ = lean_box(0);
v_isShared_4493_ = v_isSharedCheck_4510_;
goto v_resetjp_4491_;
}
v_resetjp_4491_:
{
lean_object* v___x_4494_; 
lean_inc(v_a_4482_);
v___x_4494_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4482_, v_a_4490_, v___y_4485_, v___y_4486_, v___y_4487_, v___y_4488_);
if (lean_obj_tag(v___x_4494_) == 0)
{
lean_object* v_a_4495_; lean_object* v___x_4496_; lean_object* v___x_4498_; 
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
lean_inc(v_a_4495_);
lean_dec_ref_known(v___x_4494_, 1);
v___x_4496_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4493_ == 0)
{
lean_ctor_set_tag(v___x_4492_, 1);
lean_ctor_set(v___x_4492_, 0, v_declName_4473_);
v___x_4498_ = v___x_4492_;
goto v_reusejp_4497_;
}
else
{
lean_object* v_reuseFailAlloc_4501_; 
v_reuseFailAlloc_4501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4501_, 0, v_declName_4473_);
v___x_4498_ = v_reuseFailAlloc_4501_;
goto v_reusejp_4497_;
}
v_reusejp_4497_:
{
lean_object* v___x_4499_; lean_object* v___x_4500_; 
v___x_4499_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4499_, 0, v___y_4484_);
lean_ctor_set(v___x_4499_, 1, v_a_4482_);
lean_ctor_set(v___x_4499_, 2, v_prio_4475_);
lean_ctor_set(v___x_4499_, 3, v___x_4498_);
lean_ctor_set(v___x_4499_, 4, v_a_4495_);
lean_ctor_set_uint8(v___x_4499_, sizeof(void*)*5, v_attrKind_4474_);
v___x_4500_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4496_, v___x_4499_, v_attrKind_4474_, v___y_4486_, v___y_4487_, v___y_4488_);
return v___x_4500_;
}
}
else
{
lean_object* v_a_4502_; lean_object* v___x_4504_; uint8_t v_isShared_4505_; uint8_t v_isSharedCheck_4509_; 
lean_del_object(v___x_4492_);
lean_dec_ref(v___y_4484_);
lean_dec(v_a_4482_);
lean_dec(v_prio_4475_);
lean_dec(v_declName_4473_);
v_a_4502_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4509_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4509_ == 0)
{
v___x_4504_ = v___x_4494_;
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
else
{
lean_inc(v_a_4502_);
lean_dec(v___x_4494_);
v___x_4504_ = lean_box(0);
v_isShared_4505_ = v_isSharedCheck_4509_;
goto v_resetjp_4503_;
}
v_resetjp_4503_:
{
lean_object* v___x_4507_; 
if (v_isShared_4505_ == 0)
{
v___x_4507_ = v___x_4504_;
goto v_reusejp_4506_;
}
else
{
lean_object* v_reuseFailAlloc_4508_; 
v_reuseFailAlloc_4508_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4508_, 0, v_a_4502_);
v___x_4507_ = v_reuseFailAlloc_4508_;
goto v_reusejp_4506_;
}
v_reusejp_4506_:
{
return v___x_4507_;
}
}
}
}
}
v___jp_4511_:
{
lean_object* v___x_4516_; 
lean_inc(v_a_4482_);
v___x_4516_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4482_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4516_) == 0)
{
lean_object* v_a_4517_; lean_object* v___x_4518_; lean_object* v_a_4519_; uint8_t v___x_4520_; uint8_t v___x_4521_; uint8_t v___x_4522_; 
v_a_4517_ = lean_ctor_get(v___x_4516_, 0);
lean_inc(v_a_4517_);
lean_dec_ref_known(v___x_4516_, 1);
lean_inc(v_declName_4473_);
v___x_4518_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4473_, v___y_4515_);
v_a_4519_ = lean_ctor_get(v___x_4518_, 0);
lean_inc(v_a_4519_);
lean_dec_ref(v___x_4518_);
v___x_4520_ = 1;
v___x_4521_ = lean_unbox(v_a_4519_);
lean_dec(v_a_4519_);
v___x_4522_ = l_Lean_instBEqReducibilityStatus_beq(v___x_4521_, v___x_4520_);
if (v___x_4522_ == 0)
{
v___y_4484_ = v_a_4517_;
v___y_4485_ = v___y_4512_;
v___y_4486_ = v___y_4513_;
v___y_4487_ = v___y_4514_;
v___y_4488_ = v___y_4515_;
goto v___jp_4483_;
}
else
{
lean_object* v___x_4523_; 
lean_inc(v_declName_4473_);
v___x_4523_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4473_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4523_) == 0)
{
lean_object* v_a_4524_; uint8_t v___x_4525_; 
v_a_4524_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_a_4524_);
lean_dec_ref_known(v___x_4523_, 1);
v___x_4525_ = l_Lean_ConstantInfo_isDefinition(v_a_4524_);
lean_dec(v_a_4524_);
if (v___x_4525_ == 0)
{
lean_object* v___x_4526_; lean_object* v_env_4527_; uint8_t v___x_4528_; 
v___x_4526_ = lean_st_ref_get(v___y_4515_);
v_env_4527_ = lean_ctor_get(v___x_4526_, 0);
lean_inc_ref(v_env_4527_);
lean_dec(v___x_4526_);
lean_inc(v_declName_4473_);
v___x_4528_ = l_Lean_wasOriginallyDefn(v_env_4527_, v_declName_4473_);
if (v___x_4528_ == 0)
{
v___y_4484_ = v_a_4517_;
v___y_4485_ = v___y_4512_;
v___y_4486_ = v___y_4513_;
v___y_4487_ = v___y_4514_;
v___y_4488_ = v___y_4515_;
goto v___jp_4483_;
}
else
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; lean_object* v___x_4534_; 
v___x_4529_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4473_);
v___x_4530_ = l_Lean_MessageData_ofName(v_declName_4473_);
v___x_4531_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4531_, 0, v___x_4529_);
lean_ctor_set(v___x_4531_, 1, v___x_4530_);
v___x_4532_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4533_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4531_);
lean_ctor_set(v___x_4533_, 1, v___x_4532_);
v___x_4534_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4533_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4534_) == 0)
{
lean_dec_ref_known(v___x_4534_, 1);
v___y_4484_ = v_a_4517_;
v___y_4485_ = v___y_4512_;
v___y_4486_ = v___y_4513_;
v___y_4487_ = v___y_4514_;
v___y_4488_ = v___y_4515_;
goto v___jp_4483_;
}
else
{
lean_dec(v_a_4517_);
lean_dec(v_a_4482_);
lean_dec(v_prio_4475_);
lean_dec(v_declName_4473_);
return v___x_4534_;
}
}
}
else
{
lean_object* v___x_4535_; lean_object* v___x_4536_; uint8_t v___x_4537_; 
v___x_4535_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4514_);
v___x_4536_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility));
v___x_4537_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_4535_, v___x_4536_);
lean_dec_ref(v___x_4535_);
if (v___x_4537_ == 0)
{
v___y_4484_ = v_a_4517_;
v___y_4485_ = v___y_4512_;
v___y_4486_ = v___y_4513_;
v___y_4487_ = v___y_4514_;
v___y_4488_ = v___y_4515_;
goto v___jp_4483_;
}
else
{
lean_object* v___x_4538_; lean_object* v___x_4539_; lean_object* v___x_4540_; lean_object* v___x_4541_; lean_object* v___x_4542_; lean_object* v___x_4543_; 
v___x_4538_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
lean_inc(v_declName_4473_);
v___x_4539_ = l_Lean_MessageData_ofName(v_declName_4473_);
v___x_4540_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4540_, 0, v___x_4538_);
lean_ctor_set(v___x_4540_, 1, v___x_4539_);
v___x_4541_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__7, &l_Lean_Meta_addInstance___closed__7_once, _init_l_Lean_Meta_addInstance___closed__7);
v___x_4542_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4542_, 0, v___x_4540_);
lean_ctor_set(v___x_4542_, 1, v___x_4541_);
v___x_4543_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4542_, v___y_4512_, v___y_4513_, v___y_4514_, v___y_4515_);
if (lean_obj_tag(v___x_4543_) == 0)
{
lean_dec_ref_known(v___x_4543_, 1);
v___y_4484_ = v_a_4517_;
v___y_4485_ = v___y_4512_;
v___y_4486_ = v___y_4513_;
v___y_4487_ = v___y_4514_;
v___y_4488_ = v___y_4515_;
goto v___jp_4483_;
}
else
{
lean_dec(v_a_4517_);
lean_dec(v_a_4482_);
lean_dec(v_prio_4475_);
lean_dec(v_declName_4473_);
return v___x_4543_;
}
}
}
}
else
{
lean_object* v_a_4544_; lean_object* v___x_4546_; uint8_t v_isShared_4547_; uint8_t v_isSharedCheck_4551_; 
lean_dec(v_a_4517_);
lean_dec(v_a_4482_);
lean_dec(v_prio_4475_);
lean_dec(v_declName_4473_);
v_a_4544_ = lean_ctor_get(v___x_4523_, 0);
v_isSharedCheck_4551_ = !lean_is_exclusive(v___x_4523_);
if (v_isSharedCheck_4551_ == 0)
{
v___x_4546_ = v___x_4523_;
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
else
{
lean_inc(v_a_4544_);
lean_dec(v___x_4523_);
v___x_4546_ = lean_box(0);
v_isShared_4547_ = v_isSharedCheck_4551_;
goto v_resetjp_4545_;
}
v_resetjp_4545_:
{
lean_object* v___x_4549_; 
if (v_isShared_4547_ == 0)
{
v___x_4549_ = v___x_4546_;
goto v_reusejp_4548_;
}
else
{
lean_object* v_reuseFailAlloc_4550_; 
v_reuseFailAlloc_4550_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4550_, 0, v_a_4544_);
v___x_4549_ = v_reuseFailAlloc_4550_;
goto v_reusejp_4548_;
}
v_reusejp_4548_:
{
return v___x_4549_;
}
}
}
}
}
else
{
lean_object* v_a_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4559_; 
lean_dec(v_a_4482_);
lean_dec(v_prio_4475_);
lean_dec(v_declName_4473_);
v_a_4552_ = lean_ctor_get(v___x_4516_, 0);
v_isSharedCheck_4559_ = !lean_is_exclusive(v___x_4516_);
if (v_isSharedCheck_4559_ == 0)
{
v___x_4554_ = v___x_4516_;
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_a_4552_);
lean_dec(v___x_4516_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4559_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4557_; 
if (v_isShared_4555_ == 0)
{
v___x_4557_ = v___x_4554_;
goto v_reusejp_4556_;
}
else
{
lean_object* v_reuseFailAlloc_4558_; 
v_reuseFailAlloc_4558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4558_, 0, v_a_4552_);
v___x_4557_ = v_reuseFailAlloc_4558_;
goto v_reusejp_4556_;
}
v_reusejp_4556_:
{
return v___x_4557_;
}
}
}
}
}
else
{
lean_object* v_a_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4581_; 
lean_dec(v_prio_4475_);
lean_dec(v_declName_4473_);
v_a_4574_ = lean_ctor_get(v___x_4481_, 0);
v_isSharedCheck_4581_ = !lean_is_exclusive(v___x_4481_);
if (v_isSharedCheck_4581_ == 0)
{
v___x_4576_ = v___x_4481_;
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_a_4574_);
lean_dec(v___x_4481_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4581_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
lean_object* v___x_4579_; 
if (v_isShared_4577_ == 0)
{
v___x_4579_ = v___x_4576_;
goto v_reusejp_4578_;
}
else
{
lean_object* v_reuseFailAlloc_4580_; 
v_reuseFailAlloc_4580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4580_, 0, v_a_4574_);
v___x_4579_ = v_reuseFailAlloc_4580_;
goto v_reusejp_4578_;
}
v_reusejp_4578_:
{
return v___x_4579_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4582_, lean_object* v_attrKind_4583_, lean_object* v_prio_4584_, lean_object* v_a_4585_, lean_object* v_a_4586_, lean_object* v_a_4587_, lean_object* v_a_4588_, lean_object* v_a_4589_){
_start:
{
uint8_t v_attrKind_boxed_4590_; lean_object* v_res_4591_; 
v_attrKind_boxed_4590_ = lean_unbox(v_attrKind_4583_);
v_res_4591_ = l_Lean_Meta_addInstance(v_declName_4582_, v_attrKind_boxed_4590_, v_prio_4584_, v_a_4585_, v_a_4586_, v_a_4587_, v_a_4588_);
lean_dec(v_a_4588_);
lean_dec_ref(v_a_4587_);
lean_dec(v_a_4586_);
lean_dec_ref(v_a_4585_);
return v_res_4591_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_4592_, lean_object* v_constName_4593_, lean_object* v___y_4594_, lean_object* v___y_4595_, lean_object* v___y_4596_, lean_object* v___y_4597_){
_start:
{
lean_object* v___x_4599_; 
v___x_4599_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4593_, v___y_4594_, v___y_4595_, v___y_4596_, v___y_4597_);
return v___x_4599_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4600_, lean_object* v_constName_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
lean_object* v_res_4607_; 
v_res_4607_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_4600_, v_constName_4601_, v___y_4602_, v___y_4603_, v___y_4604_, v___y_4605_);
lean_dec(v___y_4605_);
lean_dec_ref(v___y_4604_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
return v_res_4607_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_4608_, lean_object* v_ref_4609_, lean_object* v_constName_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v___x_4616_; 
v___x_4616_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4609_, v_constName_4610_, v___y_4611_, v___y_4612_, v___y_4613_, v___y_4614_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4617_, lean_object* v_ref_4618_, lean_object* v_constName_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
lean_object* v_res_4625_; 
v_res_4625_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_4617_, v_ref_4618_, v_constName_4619_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
lean_dec(v_ref_4618_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b1_4626_, lean_object* v_ref_4627_, lean_object* v_msg_4628_, lean_object* v_declHint_4629_, lean_object* v___y_4630_, lean_object* v___y_4631_, lean_object* v___y_4632_, lean_object* v___y_4633_){
_start:
{
lean_object* v___x_4635_; 
v___x_4635_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4627_, v_msg_4628_, v_declHint_4629_, v___y_4630_, v___y_4631_, v___y_4632_, v___y_4633_);
return v___x_4635_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4636_, lean_object* v_ref_4637_, lean_object* v_msg_4638_, lean_object* v_declHint_4639_, lean_object* v___y_4640_, lean_object* v___y_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_){
_start:
{
lean_object* v_res_4645_; 
v_res_4645_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(v_00_u03b1_4636_, v_ref_4637_, v_msg_4638_, v_declHint_4639_, v___y_4640_, v___y_4641_, v___y_4642_, v___y_4643_);
lean_dec(v___y_4643_);
lean_dec_ref(v___y_4642_);
lean_dec(v___y_4641_);
lean_dec_ref(v___y_4640_);
lean_dec(v_ref_4637_);
return v_res_4645_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_4646_, lean_object* v_declHint_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_){
_start:
{
lean_object* v___x_4653_; 
v___x_4653_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4646_, v_declHint_4647_, v___y_4651_);
return v___x_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_4654_, lean_object* v_declHint_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_, lean_object* v___y_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_){
_start:
{
lean_object* v_res_4661_; 
v_res_4661_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(v_msg_4654_, v_declHint_4655_, v___y_4656_, v___y_4657_, v___y_4658_, v___y_4659_);
lean_dec(v___y_4659_);
lean_dec_ref(v___y_4658_);
lean_dec(v___y_4657_);
lean_dec_ref(v___y_4656_);
return v_res_4661_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_4662_, lean_object* v_ref_4663_, lean_object* v_msg_4664_, lean_object* v___y_4665_, lean_object* v___y_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_){
_start:
{
lean_object* v___x_4670_; 
v___x_4670_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4663_, v_msg_4664_, v___y_4665_, v___y_4666_, v___y_4667_, v___y_4668_);
return v___x_4670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4671_, lean_object* v_ref_4672_, lean_object* v_msg_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_, lean_object* v___y_4677_, lean_object* v___y_4678_){
_start:
{
lean_object* v_res_4679_; 
v_res_4679_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_4671_, v_ref_4672_, v_msg_4673_, v___y_4674_, v___y_4675_, v___y_4676_, v___y_4677_);
lean_dec(v___y_4677_);
lean_dec_ref(v___y_4676_);
lean_dec(v___y_4675_);
lean_dec_ref(v___y_4674_);
lean_dec(v_ref_4672_);
return v_res_4679_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4680_, uint8_t v_s_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
lean_object* v___x_4685_; lean_object* v_env_4686_; lean_object* v_nextMacroScope_4687_; lean_object* v_ngen_4688_; lean_object* v_auxDeclNGen_4689_; lean_object* v_traceState_4690_; lean_object* v_recordedDeps_4691_; lean_object* v_messages_4692_; lean_object* v_infoState_4693_; lean_object* v_snapshotTasks_4694_; lean_object* v___x_4696_; uint8_t v_isShared_4697_; uint8_t v_isSharedCheck_4723_; 
v___x_4685_ = lean_st_ref_take(v___y_4683_);
v_env_4686_ = lean_ctor_get(v___x_4685_, 0);
v_nextMacroScope_4687_ = lean_ctor_get(v___x_4685_, 1);
v_ngen_4688_ = lean_ctor_get(v___x_4685_, 2);
v_auxDeclNGen_4689_ = lean_ctor_get(v___x_4685_, 3);
v_traceState_4690_ = lean_ctor_get(v___x_4685_, 4);
v_recordedDeps_4691_ = lean_ctor_get(v___x_4685_, 6);
v_messages_4692_ = lean_ctor_get(v___x_4685_, 7);
v_infoState_4693_ = lean_ctor_get(v___x_4685_, 8);
v_snapshotTasks_4694_ = lean_ctor_get(v___x_4685_, 9);
v_isSharedCheck_4723_ = !lean_is_exclusive(v___x_4685_);
if (v_isSharedCheck_4723_ == 0)
{
lean_object* v_unused_4724_; 
v_unused_4724_ = lean_ctor_get(v___x_4685_, 5);
lean_dec(v_unused_4724_);
v___x_4696_ = v___x_4685_;
v_isShared_4697_ = v_isSharedCheck_4723_;
goto v_resetjp_4695_;
}
else
{
lean_inc(v_snapshotTasks_4694_);
lean_inc(v_infoState_4693_);
lean_inc(v_messages_4692_);
lean_inc(v_recordedDeps_4691_);
lean_inc(v_traceState_4690_);
lean_inc(v_auxDeclNGen_4689_);
lean_inc(v_ngen_4688_);
lean_inc(v_nextMacroScope_4687_);
lean_inc(v_env_4686_);
lean_dec(v___x_4685_);
v___x_4696_ = lean_box(0);
v_isShared_4697_ = v_isSharedCheck_4723_;
goto v_resetjp_4695_;
}
v_resetjp_4695_:
{
uint8_t v___x_4698_; lean_object* v___x_4699_; lean_object* v___x_4700_; lean_object* v___x_4701_; lean_object* v___x_4703_; 
v___x_4698_ = 0;
v___x_4699_ = lean_box(0);
v___x_4700_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4686_, v_declName_4680_, v_s_4681_, v___x_4698_, v___x_4699_);
v___x_4701_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_4697_ == 0)
{
lean_ctor_set(v___x_4696_, 5, v___x_4701_);
lean_ctor_set(v___x_4696_, 0, v___x_4700_);
v___x_4703_ = v___x_4696_;
goto v_reusejp_4702_;
}
else
{
lean_object* v_reuseFailAlloc_4722_; 
v_reuseFailAlloc_4722_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4722_, 0, v___x_4700_);
lean_ctor_set(v_reuseFailAlloc_4722_, 1, v_nextMacroScope_4687_);
lean_ctor_set(v_reuseFailAlloc_4722_, 2, v_ngen_4688_);
lean_ctor_set(v_reuseFailAlloc_4722_, 3, v_auxDeclNGen_4689_);
lean_ctor_set(v_reuseFailAlloc_4722_, 4, v_traceState_4690_);
lean_ctor_set(v_reuseFailAlloc_4722_, 5, v___x_4701_);
lean_ctor_set(v_reuseFailAlloc_4722_, 6, v_recordedDeps_4691_);
lean_ctor_set(v_reuseFailAlloc_4722_, 7, v_messages_4692_);
lean_ctor_set(v_reuseFailAlloc_4722_, 8, v_infoState_4693_);
lean_ctor_set(v_reuseFailAlloc_4722_, 9, v_snapshotTasks_4694_);
v___x_4703_ = v_reuseFailAlloc_4722_;
goto v_reusejp_4702_;
}
v_reusejp_4702_:
{
lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v_mctx_4706_; lean_object* v_zetaDeltaFVarIds_4707_; lean_object* v_postponed_4708_; lean_object* v_diag_4709_; lean_object* v___x_4711_; uint8_t v_isShared_4712_; uint8_t v_isSharedCheck_4720_; 
v___x_4704_ = lean_st_ref_put(v___y_4683_, v___x_4703_);
v___x_4705_ = lean_st_ref_take(v___y_4682_);
v_mctx_4706_ = lean_ctor_get(v___x_4705_, 0);
v_zetaDeltaFVarIds_4707_ = lean_ctor_get(v___x_4705_, 2);
v_postponed_4708_ = lean_ctor_get(v___x_4705_, 3);
v_diag_4709_ = lean_ctor_get(v___x_4705_, 4);
v_isSharedCheck_4720_ = !lean_is_exclusive(v___x_4705_);
if (v_isSharedCheck_4720_ == 0)
{
lean_object* v_unused_4721_; 
v_unused_4721_ = lean_ctor_get(v___x_4705_, 1);
lean_dec(v_unused_4721_);
v___x_4711_ = v___x_4705_;
v_isShared_4712_ = v_isSharedCheck_4720_;
goto v_resetjp_4710_;
}
else
{
lean_inc(v_diag_4709_);
lean_inc(v_postponed_4708_);
lean_inc(v_zetaDeltaFVarIds_4707_);
lean_inc(v_mctx_4706_);
lean_dec(v___x_4705_);
v___x_4711_ = lean_box(0);
v_isShared_4712_ = v_isSharedCheck_4720_;
goto v_resetjp_4710_;
}
v_resetjp_4710_:
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4716_; 
v___x_4713_ = lean_box(0);
v___x_4714_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4712_ == 0)
{
lean_ctor_set(v___x_4711_, 1, v___x_4714_);
v___x_4716_ = v___x_4711_;
goto v_reusejp_4715_;
}
else
{
lean_object* v_reuseFailAlloc_4719_; 
v_reuseFailAlloc_4719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4719_, 0, v_mctx_4706_);
lean_ctor_set(v_reuseFailAlloc_4719_, 1, v___x_4714_);
lean_ctor_set(v_reuseFailAlloc_4719_, 2, v_zetaDeltaFVarIds_4707_);
lean_ctor_set(v_reuseFailAlloc_4719_, 3, v_postponed_4708_);
lean_ctor_set(v_reuseFailAlloc_4719_, 4, v_diag_4709_);
v___x_4716_ = v_reuseFailAlloc_4719_;
goto v_reusejp_4715_;
}
v_reusejp_4715_:
{
lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4717_ = lean_st_ref_put(v___y_4682_, v___x_4716_);
v___x_4718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4718_, 0, v___x_4713_);
return v___x_4718_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4725_, lean_object* v_s_4726_, lean_object* v___y_4727_, lean_object* v___y_4728_, lean_object* v___y_4729_){
_start:
{
uint8_t v_s_boxed_4730_; lean_object* v_res_4731_; 
v_s_boxed_4730_ = lean_unbox(v_s_4726_);
v_res_4731_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4725_, v_s_boxed_4730_, v___y_4727_, v___y_4728_);
lean_dec(v___y_4728_);
lean_dec(v___y_4727_);
return v_res_4731_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4732_, uint8_t v_s_4733_, lean_object* v___y_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
lean_object* v___x_4739_; 
v___x_4739_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4732_, v_s_4733_, v___y_4735_, v___y_4737_);
return v___x_4739_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4740_, lean_object* v_s_4741_, lean_object* v___y_4742_, lean_object* v___y_4743_, lean_object* v___y_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
uint8_t v_s_boxed_4747_; lean_object* v_res_4748_; 
v_s_boxed_4747_ = lean_unbox(v_s_4741_);
v_res_4748_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4740_, v_s_boxed_4747_, v___y_4742_, v___y_4743_, v___y_4744_, v___y_4745_);
lean_dec(v___y_4745_);
lean_dec_ref(v___y_4744_);
lean_dec(v___y_4743_);
lean_dec_ref(v___y_4742_);
return v_res_4748_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4749_, uint8_t v_attrKind_4750_, lean_object* v_prio_4751_, lean_object* v_a_4752_, lean_object* v_a_4753_, lean_object* v_a_4754_, lean_object* v_a_4755_){
_start:
{
uint8_t v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; 
v___x_4757_ = 4;
lean_inc(v_declName_4749_);
v___x_4758_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4749_, v___x_4757_, v_a_4753_, v_a_4755_);
lean_dec_ref(v___x_4758_);
v___x_4759_ = l_Lean_Meta_addInstance(v_declName_4749_, v_attrKind_4750_, v_prio_4751_, v_a_4752_, v_a_4753_, v_a_4754_, v_a_4755_);
return v___x_4759_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4760_, lean_object* v_attrKind_4761_, lean_object* v_prio_4762_, lean_object* v_a_4763_, lean_object* v_a_4764_, lean_object* v_a_4765_, lean_object* v_a_4766_, lean_object* v_a_4767_){
_start:
{
uint8_t v_attrKind_boxed_4768_; lean_object* v_res_4769_; 
v_attrKind_boxed_4768_ = lean_unbox(v_attrKind_4761_);
v_res_4769_ = l_Lean_Meta_registerInstance(v_declName_4760_, v_attrKind_boxed_4768_, v_prio_4762_, v_a_4763_, v_a_4764_, v_a_4765_, v_a_4766_);
lean_dec(v_a_4766_);
lean_dec_ref(v_a_4765_);
lean_dec(v_a_4764_);
lean_dec_ref(v_a_4763_);
return v_res_4769_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4770_, lean_object* v_x_4771_){
_start:
{
lean_inc_ref(v_a_4770_);
return v_a_4770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4772_, lean_object* v_x_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4772_, v_x_4773_);
lean_dec_ref(v_x_4773_);
lean_dec_ref(v_a_4772_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v___x_4779_; lean_object* v_toCold_4780_; lean_object* v_env_4781_; lean_object* v_options_4782_; uint8_t v___x_4783_; lean_object* v_env_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; 
v___x_4779_ = lean_st_ref_get(v___y_4777_);
v_toCold_4780_ = lean_ctor_get(v___y_4776_, 0);
v_env_4781_ = lean_ctor_get(v___x_4779_, 0);
lean_inc_ref(v_env_4781_);
lean_dec(v___x_4779_);
v_options_4782_ = lean_ctor_get(v_toCold_4780_, 2);
v___x_4783_ = 0;
v_env_4784_ = l_Lean_Environment_setRecordingDeps(v_env_4781_, v___x_4783_);
v___x_4785_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4786_ = lean_unsigned_to_nat(32u);
v___x_4787_ = lean_mk_empty_array_with_capacity(v___x_4786_);
lean_dec_ref(v___x_4787_);
v___x_4788_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
lean_inc_ref(v_options_4782_);
v___x_4789_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4789_, 0, v_env_4784_);
lean_ctor_set(v___x_4789_, 1, v___x_4785_);
lean_ctor_set(v___x_4789_, 2, v___x_4788_);
lean_ctor_set(v___x_4789_, 3, v_options_4782_);
v___x_4790_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4790_, 0, v___x_4789_);
lean_ctor_set(v___x_4790_, 1, v_msgData_4775_);
v___x_4791_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4791_, 0, v___x_4790_);
return v___x_4791_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_){
_start:
{
lean_object* v_res_4796_; 
v_res_4796_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4792_, v___y_4793_, v___y_4794_);
lean_dec(v___y_4794_);
lean_dec_ref(v___y_4793_);
return v_res_4796_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4797_, lean_object* v___y_4798_, lean_object* v___y_4799_){
_start:
{
lean_object* v_ref_4801_; lean_object* v___x_4802_; lean_object* v_a_4803_; lean_object* v___x_4805_; uint8_t v_isShared_4806_; uint8_t v_isSharedCheck_4811_; 
v_ref_4801_ = lean_ctor_get(v___y_4798_, 2);
v___x_4802_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4797_, v___y_4798_, v___y_4799_);
v_a_4803_ = lean_ctor_get(v___x_4802_, 0);
v_isSharedCheck_4811_ = !lean_is_exclusive(v___x_4802_);
if (v_isSharedCheck_4811_ == 0)
{
v___x_4805_ = v___x_4802_;
v_isShared_4806_ = v_isSharedCheck_4811_;
goto v_resetjp_4804_;
}
else
{
lean_inc(v_a_4803_);
lean_dec(v___x_4802_);
v___x_4805_ = lean_box(0);
v_isShared_4806_ = v_isSharedCheck_4811_;
goto v_resetjp_4804_;
}
v_resetjp_4804_:
{
lean_object* v___x_4807_; lean_object* v___x_4809_; 
lean_inc(v_ref_4801_);
v___x_4807_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4807_, 0, v_ref_4801_);
lean_ctor_set(v___x_4807_, 1, v_a_4803_);
if (v_isShared_4806_ == 0)
{
lean_ctor_set_tag(v___x_4805_, 1);
lean_ctor_set(v___x_4805_, 0, v___x_4807_);
v___x_4809_ = v___x_4805_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4810_; 
v_reuseFailAlloc_4810_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4810_, 0, v___x_4807_);
v___x_4809_ = v_reuseFailAlloc_4810_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
return v___x_4809_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4812_, lean_object* v___y_4813_, lean_object* v___y_4814_, lean_object* v___y_4815_){
_start:
{
lean_object* v_res_4816_; 
v_res_4816_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4812_, v___y_4813_, v___y_4814_);
lean_dec(v___y_4814_);
lean_dec_ref(v___y_4813_);
return v_res_4816_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4817_, lean_object* v_i_4818_, lean_object* v_k_4819_){
_start:
{
lean_object* v___x_4820_; uint8_t v___x_4821_; 
v___x_4820_ = lean_array_get_size(v_keys_4817_);
v___x_4821_ = lean_nat_dec_lt(v_i_4818_, v___x_4820_);
if (v___x_4821_ == 0)
{
lean_dec(v_i_4818_);
return v___x_4821_;
}
else
{
lean_object* v_k_x27_4822_; uint8_t v___x_4823_; 
v_k_x27_4822_ = lean_array_fget_borrowed(v_keys_4817_, v_i_4818_);
v___x_4823_ = lean_name_eq(v_k_4819_, v_k_x27_4822_);
if (v___x_4823_ == 0)
{
lean_object* v___x_4824_; lean_object* v___x_4825_; 
v___x_4824_ = lean_unsigned_to_nat(1u);
v___x_4825_ = lean_nat_add(v_i_4818_, v___x_4824_);
lean_dec(v_i_4818_);
v_i_4818_ = v___x_4825_;
goto _start;
}
else
{
lean_dec(v_i_4818_);
return v___x_4821_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4827_, lean_object* v_i_4828_, lean_object* v_k_4829_){
_start:
{
uint8_t v_res_4830_; lean_object* v_r_4831_; 
v_res_4830_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4827_, v_i_4828_, v_k_4829_);
lean_dec(v_k_4829_);
lean_dec_ref(v_keys_4827_);
v_r_4831_ = lean_box(v_res_4830_);
return v_r_4831_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4832_, size_t v_x_4833_, lean_object* v_x_4834_){
_start:
{
if (lean_obj_tag(v_x_4832_) == 0)
{
lean_object* v_es_4835_; lean_object* v___x_4836_; size_t v___x_4837_; size_t v___x_4838_; lean_object* v_j_4839_; lean_object* v___x_4840_; 
v_es_4835_ = lean_ctor_get(v_x_4832_, 0);
v___x_4836_ = lean_box(2);
v___x_4837_ = ((size_t)31ULL);
v___x_4838_ = lean_usize_land(v_x_4833_, v___x_4837_);
v_j_4839_ = lean_usize_to_nat(v___x_4838_);
v___x_4840_ = lean_array_get_borrowed(v___x_4836_, v_es_4835_, v_j_4839_);
lean_dec(v_j_4839_);
switch(lean_obj_tag(v___x_4840_))
{
case 0:
{
lean_object* v_key_4841_; uint8_t v___x_4842_; 
v_key_4841_ = lean_ctor_get(v___x_4840_, 0);
v___x_4842_ = lean_name_eq(v_x_4834_, v_key_4841_);
return v___x_4842_;
}
case 1:
{
lean_object* v_node_4843_; size_t v___x_4844_; size_t v___x_4845_; 
v_node_4843_ = lean_ctor_get(v___x_4840_, 0);
v___x_4844_ = ((size_t)5ULL);
v___x_4845_ = lean_usize_shift_right(v_x_4833_, v___x_4844_);
v_x_4832_ = v_node_4843_;
v_x_4833_ = v___x_4845_;
goto _start;
}
default: 
{
uint8_t v___x_4847_; 
v___x_4847_ = 0;
return v___x_4847_;
}
}
}
else
{
lean_object* v_ks_4848_; lean_object* v___x_4849_; uint8_t v___x_4850_; 
v_ks_4848_ = lean_ctor_get(v_x_4832_, 0);
v___x_4849_ = lean_unsigned_to_nat(0u);
v___x_4850_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4848_, v___x_4849_, v_x_4834_);
return v___x_4850_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4851_, lean_object* v_x_4852_, lean_object* v_x_4853_){
_start:
{
size_t v_x_2405__boxed_4854_; uint8_t v_res_4855_; lean_object* v_r_4856_; 
v_x_2405__boxed_4854_ = lean_unbox_usize(v_x_4852_);
lean_dec(v_x_4852_);
v_res_4855_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4851_, v_x_2405__boxed_4854_, v_x_4853_);
lean_dec(v_x_4853_);
lean_dec_ref(v_x_4851_);
v_r_4856_ = lean_box(v_res_4855_);
return v_r_4856_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4857_, lean_object* v_x_4858_){
_start:
{
uint64_t v___y_4860_; 
if (lean_obj_tag(v_x_4858_) == 0)
{
uint64_t v___x_4863_; 
v___x_4863_ = 1723ULL;
v___y_4860_ = v___x_4863_;
goto v___jp_4859_;
}
else
{
uint64_t v_hash_4864_; 
v_hash_4864_ = lean_ctor_get_uint64(v_x_4858_, sizeof(void*)*2);
v___y_4860_ = v_hash_4864_;
goto v___jp_4859_;
}
v___jp_4859_:
{
size_t v___x_4861_; uint8_t v___x_4862_; 
v___x_4861_ = lean_uint64_to_usize(v___y_4860_);
v___x_4862_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4857_, v___x_4861_, v_x_4858_);
return v___x_4862_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4865_, lean_object* v_x_4866_){
_start:
{
uint8_t v_res_4867_; lean_object* v_r_4868_; 
v_res_4867_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4865_, v_x_4866_);
lean_dec(v_x_4866_);
lean_dec_ref(v_x_4865_);
v_r_4868_ = lean_box(v_res_4867_);
return v_r_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4869_, lean_object* v_declName_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_){
_start:
{
lean_object* v_instanceNames_4877_; uint8_t v___x_4878_; 
v_instanceNames_4877_ = lean_ctor_get(v_d_4869_, 1);
v___x_4878_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4877_, v_declName_4870_);
if (v___x_4878_ == 0)
{
lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v_a_4885_; lean_object* v___x_4887_; uint8_t v_isShared_4888_; uint8_t v_isSharedCheck_4892_; 
lean_dec_ref(v_d_4869_);
v___x_4879_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4880_ = l_Lean_MessageData_ofConstName(v_declName_4870_, v___x_4878_);
v___x_4881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4881_, 0, v___x_4879_);
lean_ctor_set(v___x_4881_, 1, v___x_4880_);
v___x_4882_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4883_, 0, v___x_4881_);
lean_ctor_set(v___x_4883_, 1, v___x_4882_);
v___x_4884_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4883_, v___y_4871_, v___y_4872_);
v_a_4885_ = lean_ctor_get(v___x_4884_, 0);
v_isSharedCheck_4892_ = !lean_is_exclusive(v___x_4884_);
if (v_isSharedCheck_4892_ == 0)
{
v___x_4887_ = v___x_4884_;
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
else
{
lean_inc(v_a_4885_);
lean_dec(v___x_4884_);
v___x_4887_ = lean_box(0);
v_isShared_4888_ = v_isSharedCheck_4892_;
goto v_resetjp_4886_;
}
v_resetjp_4886_:
{
lean_object* v___x_4890_; 
if (v_isShared_4888_ == 0)
{
v___x_4890_ = v___x_4887_;
goto v_reusejp_4889_;
}
else
{
lean_object* v_reuseFailAlloc_4891_; 
v_reuseFailAlloc_4891_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4891_, 0, v_a_4885_);
v___x_4890_ = v_reuseFailAlloc_4891_;
goto v_reusejp_4889_;
}
v_reusejp_4889_:
{
return v___x_4890_;
}
}
}
else
{
goto v___jp_4874_;
}
v___jp_4874_:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = l_Lean_Meta_Instances_eraseCore(v_d_4869_, v_declName_4870_);
v___x_4876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4875_);
return v___x_4876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4893_, lean_object* v_declName_4894_, lean_object* v___y_4895_, lean_object* v___y_4896_, lean_object* v___y_4897_){
_start:
{
lean_object* v_res_4898_; 
v_res_4898_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4893_, v_declName_4894_, v___y_4895_, v___y_4896_);
lean_dec(v___y_4896_);
lean_dec_ref(v___y_4895_);
return v_res_4898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4899_, lean_object* v_declName_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_){
_start:
{
lean_object* v___x_4904_; lean_object* v_env_4905_; lean_object* v___x_4906_; lean_object* v_ext_4907_; lean_object* v_toEnvExtension_4908_; lean_object* v_asyncMode_4909_; uint8_t v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; 
v___x_4904_ = lean_st_ref_get(v___y_4902_);
v_env_4905_ = lean_ctor_get(v___x_4904_, 0);
lean_inc_ref(v_env_4905_);
lean_dec(v___x_4904_);
v___x_4906_ = l_Lean_Meta_instanceExtension;
v_ext_4907_ = lean_ctor_get(v___x_4906_, 1);
v_toEnvExtension_4908_ = lean_ctor_get(v_ext_4907_, 0);
v_asyncMode_4909_ = lean_ctor_get(v_toEnvExtension_4908_, 2);
v___x_4910_ = 0;
v___x_4911_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4899_, v___x_4906_, v_env_4905_, v_asyncMode_4909_, v___x_4910_);
v___x_4912_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4911_, v_declName_4900_, v___y_4901_, v___y_4902_);
if (lean_obj_tag(v___x_4912_) == 0)
{
lean_object* v_a_4913_; lean_object* v___x_4915_; uint8_t v_isShared_4916_; uint8_t v_isSharedCheck_4943_; 
v_a_4913_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4943_ == 0)
{
v___x_4915_ = v___x_4912_;
v_isShared_4916_ = v_isSharedCheck_4943_;
goto v_resetjp_4914_;
}
else
{
lean_inc(v_a_4913_);
lean_dec(v___x_4912_);
v___x_4915_ = lean_box(0);
v_isShared_4916_ = v_isSharedCheck_4943_;
goto v_resetjp_4914_;
}
v_resetjp_4914_:
{
lean_object* v___f_4917_; lean_object* v___x_4918_; lean_object* v_env_4919_; lean_object* v_nextMacroScope_4920_; lean_object* v_ngen_4921_; lean_object* v_auxDeclNGen_4922_; lean_object* v_traceState_4923_; lean_object* v_recordedDeps_4924_; lean_object* v_messages_4925_; lean_object* v_infoState_4926_; lean_object* v_snapshotTasks_4927_; lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4941_; 
v___f_4917_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4917_, 0, v_a_4913_);
v___x_4918_ = lean_st_ref_take(v___y_4902_);
v_env_4919_ = lean_ctor_get(v___x_4918_, 0);
v_nextMacroScope_4920_ = lean_ctor_get(v___x_4918_, 1);
v_ngen_4921_ = lean_ctor_get(v___x_4918_, 2);
v_auxDeclNGen_4922_ = lean_ctor_get(v___x_4918_, 3);
v_traceState_4923_ = lean_ctor_get(v___x_4918_, 4);
v_recordedDeps_4924_ = lean_ctor_get(v___x_4918_, 6);
v_messages_4925_ = lean_ctor_get(v___x_4918_, 7);
v_infoState_4926_ = lean_ctor_get(v___x_4918_, 8);
v_snapshotTasks_4927_ = lean_ctor_get(v___x_4918_, 9);
v_isSharedCheck_4941_ = !lean_is_exclusive(v___x_4918_);
if (v_isSharedCheck_4941_ == 0)
{
lean_object* v_unused_4942_; 
v_unused_4942_ = lean_ctor_get(v___x_4918_, 5);
lean_dec(v_unused_4942_);
v___x_4929_ = v___x_4918_;
v_isShared_4930_ = v_isSharedCheck_4941_;
goto v_resetjp_4928_;
}
else
{
lean_inc(v_snapshotTasks_4927_);
lean_inc(v_infoState_4926_);
lean_inc(v_messages_4925_);
lean_inc(v_recordedDeps_4924_);
lean_inc(v_traceState_4923_);
lean_inc(v_auxDeclNGen_4922_);
lean_inc(v_ngen_4921_);
lean_inc(v_nextMacroScope_4920_);
lean_inc(v_env_4919_);
lean_dec(v___x_4918_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4941_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4933_; lean_object* v___x_4935_; 
v___x_4931_ = lean_box(0);
v___x_4932_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4906_, v_env_4919_, v___f_4917_);
v___x_4933_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_4930_ == 0)
{
lean_ctor_set(v___x_4929_, 5, v___x_4933_);
lean_ctor_set(v___x_4929_, 0, v___x_4932_);
v___x_4935_ = v___x_4929_;
goto v_reusejp_4934_;
}
else
{
lean_object* v_reuseFailAlloc_4940_; 
v_reuseFailAlloc_4940_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4940_, 0, v___x_4932_);
lean_ctor_set(v_reuseFailAlloc_4940_, 1, v_nextMacroScope_4920_);
lean_ctor_set(v_reuseFailAlloc_4940_, 2, v_ngen_4921_);
lean_ctor_set(v_reuseFailAlloc_4940_, 3, v_auxDeclNGen_4922_);
lean_ctor_set(v_reuseFailAlloc_4940_, 4, v_traceState_4923_);
lean_ctor_set(v_reuseFailAlloc_4940_, 5, v___x_4933_);
lean_ctor_set(v_reuseFailAlloc_4940_, 6, v_recordedDeps_4924_);
lean_ctor_set(v_reuseFailAlloc_4940_, 7, v_messages_4925_);
lean_ctor_set(v_reuseFailAlloc_4940_, 8, v_infoState_4926_);
lean_ctor_set(v_reuseFailAlloc_4940_, 9, v_snapshotTasks_4927_);
v___x_4935_ = v_reuseFailAlloc_4940_;
goto v_reusejp_4934_;
}
v_reusejp_4934_:
{
lean_object* v___x_4936_; lean_object* v___x_4938_; 
v___x_4936_ = lean_st_ref_put(v___y_4902_, v___x_4935_);
if (v_isShared_4916_ == 0)
{
lean_ctor_set(v___x_4915_, 0, v___x_4931_);
v___x_4938_ = v___x_4915_;
goto v_reusejp_4937_;
}
else
{
lean_object* v_reuseFailAlloc_4939_; 
v_reuseFailAlloc_4939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4939_, 0, v___x_4931_);
v___x_4938_ = v_reuseFailAlloc_4939_;
goto v_reusejp_4937_;
}
v_reusejp_4937_:
{
return v___x_4938_;
}
}
}
}
}
else
{
lean_object* v_a_4944_; lean_object* v___x_4946_; uint8_t v_isShared_4947_; uint8_t v_isSharedCheck_4951_; 
v_a_4944_ = lean_ctor_get(v___x_4912_, 0);
v_isSharedCheck_4951_ = !lean_is_exclusive(v___x_4912_);
if (v_isSharedCheck_4951_ == 0)
{
v___x_4946_ = v___x_4912_;
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
else
{
lean_inc(v_a_4944_);
lean_dec(v___x_4912_);
v___x_4946_ = lean_box(0);
v_isShared_4947_ = v_isSharedCheck_4951_;
goto v_resetjp_4945_;
}
v_resetjp_4945_:
{
lean_object* v___x_4949_; 
if (v_isShared_4947_ == 0)
{
v___x_4949_ = v___x_4946_;
goto v_reusejp_4948_;
}
else
{
lean_object* v_reuseFailAlloc_4950_; 
v_reuseFailAlloc_4950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4950_, 0, v_a_4944_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4952_, lean_object* v_declName_4953_, lean_object* v___y_4954_, lean_object* v___y_4955_, lean_object* v___y_4956_){
_start:
{
lean_object* v_res_4957_; 
v_res_4957_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4952_, v_declName_4953_, v___y_4954_, v___y_4955_);
lean_dec(v___y_4955_);
lean_dec_ref(v___y_4954_);
lean_dec_ref(v___x_4952_);
return v_res_4957_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4964_; uint64_t v___x_4965_; 
v___x_4964_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4965_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4964_);
return v___x_4965_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4966_; lean_object* v___x_4967_; lean_object* v___x_4968_; 
v___x_4966_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4967_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4968_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4968_, 0, v___x_4967_);
lean_ctor_set_uint64(v___x_4968_, sizeof(void*)*1, v___x_4966_);
return v___x_4968_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4969_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4970_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4970_, 0, v___x_4969_);
return v___x_4970_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4971_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4972_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4971_);
lean_ctor_set(v___x_4972_, 1, v___x_4971_);
lean_ctor_set(v___x_4972_, 2, v___x_4971_);
lean_ctor_set(v___x_4972_, 3, v___x_4971_);
lean_ctor_set(v___x_4972_, 4, v___x_4971_);
lean_ctor_set(v___x_4972_, 5, v___x_4971_);
return v___x_4972_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___x_4973_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4974_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4974_, 0, v___x_4973_);
lean_ctor_set(v___x_4974_, 1, v___x_4973_);
lean_ctor_set(v___x_4974_, 2, v___x_4973_);
lean_ctor_set(v___x_4974_, 3, v___x_4973_);
lean_ctor_set(v___x_4974_, 4, v___x_4973_);
return v___x_4974_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4975_, lean_object* v___x_4976_, lean_object* v_declName_4977_, lean_object* v_stx_4978_, uint8_t v_attrKind_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_){
_start:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4983_ = lean_unsigned_to_nat(1u);
v___x_4984_ = l_Lean_Syntax_getArg(v_stx_4978_, v___x_4983_);
v___x_4985_ = l_Lean_getAttrParamOptPrio(v___x_4984_, v___y_4980_, v___y_4981_);
if (lean_obj_tag(v___x_4985_) == 0)
{
lean_object* v_a_4986_; uint8_t v___x_4987_; uint8_t v___x_4988_; lean_object* v___x_4989_; lean_object* v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; size_t v___x_4994_; lean_object* v___x_4995_; lean_object* v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; 
v_a_4986_ = lean_ctor_get(v___x_4985_, 0);
lean_inc(v_a_4986_);
lean_dec_ref_known(v___x_4985_, 1);
v___x_4987_ = 0;
v___x_4988_ = 1;
v___x_4989_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4990_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4991_ = lean_unsigned_to_nat(32u);
v___x_4992_ = lean_mk_empty_array_with_capacity(v___x_4991_);
v___x_4993_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4994_ = ((size_t)5ULL);
lean_inc_n(v___x_4975_, 6);
v___x_4995_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4995_, 0, v___x_4993_);
lean_ctor_set(v___x_4995_, 1, v___x_4992_);
lean_ctor_set(v___x_4995_, 2, v___x_4975_);
lean_ctor_set(v___x_4995_, 3, v___x_4975_);
lean_ctor_set_usize(v___x_4995_, 4, v___x_4994_);
v___x_4996_ = lean_box(1);
lean_inc_ref(v___x_4995_);
v___x_4997_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4997_, 0, v___x_4990_);
lean_ctor_set(v___x_4997_, 1, v___x_4995_);
lean_ctor_set(v___x_4997_, 2, v___x_4996_);
v___x_4998_ = lean_mk_empty_array_with_capacity(v___x_4975_);
v___x_4999_ = lean_box(0);
lean_inc(v___x_4976_);
v___x_5000_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5000_, 0, v___x_4989_);
lean_ctor_set(v___x_5000_, 1, v___x_4976_);
lean_ctor_set(v___x_5000_, 2, v___x_4997_);
lean_ctor_set(v___x_5000_, 3, v___x_4998_);
lean_ctor_set(v___x_5000_, 4, v___x_4999_);
lean_ctor_set(v___x_5000_, 5, v___x_4975_);
lean_ctor_set(v___x_5000_, 6, v___x_4999_);
lean_ctor_set_uint8(v___x_5000_, sizeof(void*)*7, v___x_4987_);
lean_ctor_set_uint8(v___x_5000_, sizeof(void*)*7 + 1, v___x_4987_);
lean_ctor_set_uint8(v___x_5000_, sizeof(void*)*7 + 2, v___x_4987_);
lean_ctor_set_uint8(v___x_5000_, sizeof(void*)*7 + 3, v___x_4988_);
v___x_5001_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_5002_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5002_, 0, v___x_4975_);
lean_ctor_set(v___x_5002_, 1, v___x_4975_);
lean_ctor_set(v___x_5002_, 2, v___x_4975_);
lean_ctor_set(v___x_5002_, 3, v___x_4975_);
lean_ctor_set(v___x_5002_, 4, v___x_4990_);
lean_ctor_set(v___x_5002_, 5, v___x_4990_);
lean_ctor_set(v___x_5002_, 6, v___x_4990_);
lean_ctor_set(v___x_5002_, 7, v___x_4990_);
lean_ctor_set(v___x_5002_, 8, v___x_4990_);
lean_ctor_set(v___x_5002_, 9, v___x_4990_);
lean_ctor_set(v___x_5002_, 10, v___x_5001_);
v___x_5003_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5004_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5005_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5005_, 0, v___x_5002_);
lean_ctor_set(v___x_5005_, 1, v___x_5003_);
lean_ctor_set(v___x_5005_, 2, v___x_4976_);
lean_ctor_set(v___x_5005_, 3, v___x_4995_);
lean_ctor_set(v___x_5005_, 4, v___x_5004_);
v___x_5006_ = lean_box(0);
v___x_5007_ = lean_st_mk_ref(v___x_5005_);
v___x_5008_ = l_Lean_Meta_addInstance(v_declName_4977_, v_attrKind_4979_, v_a_4986_, v___x_5000_, v___x_5007_, v___y_4980_, v___y_4981_);
lean_dec_ref_known(v___x_5000_, 7);
if (lean_obj_tag(v___x_5008_) == 0)
{
lean_object* v___x_5010_; uint8_t v_isShared_5011_; uint8_t v_isSharedCheck_5016_; 
v_isSharedCheck_5016_ = !lean_is_exclusive(v___x_5008_);
if (v_isSharedCheck_5016_ == 0)
{
lean_object* v_unused_5017_; 
v_unused_5017_ = lean_ctor_get(v___x_5008_, 0);
lean_dec(v_unused_5017_);
v___x_5010_ = v___x_5008_;
v_isShared_5011_ = v_isSharedCheck_5016_;
goto v_resetjp_5009_;
}
else
{
lean_dec(v___x_5008_);
v___x_5010_ = lean_box(0);
v_isShared_5011_ = v_isSharedCheck_5016_;
goto v_resetjp_5009_;
}
v_resetjp_5009_:
{
lean_object* v___x_5012_; lean_object* v___x_5014_; 
v___x_5012_ = lean_st_ref_get(v___x_5007_);
lean_dec(v___x_5007_);
lean_dec(v___x_5012_);
if (v_isShared_5011_ == 0)
{
lean_ctor_set(v___x_5010_, 0, v___x_5006_);
v___x_5014_ = v___x_5010_;
goto v_reusejp_5013_;
}
else
{
lean_object* v_reuseFailAlloc_5015_; 
v_reuseFailAlloc_5015_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5015_, 0, v___x_5006_);
v___x_5014_ = v_reuseFailAlloc_5015_;
goto v_reusejp_5013_;
}
v_reusejp_5013_:
{
return v___x_5014_;
}
}
}
else
{
lean_dec(v___x_5007_);
return v___x_5008_;
}
}
else
{
lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5025_; 
lean_dec(v_declName_4977_);
lean_dec(v___x_4976_);
lean_dec(v___x_4975_);
v_a_5018_ = lean_ctor_get(v___x_4985_, 0);
v_isSharedCheck_5025_ = !lean_is_exclusive(v___x_4985_);
if (v_isSharedCheck_5025_ == 0)
{
v___x_5020_ = v___x_4985_;
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_4985_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5025_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5023_; 
if (v_isShared_5021_ == 0)
{
v___x_5023_ = v___x_5020_;
goto v_reusejp_5022_;
}
else
{
lean_object* v_reuseFailAlloc_5024_; 
v_reuseFailAlloc_5024_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5024_, 0, v_a_5018_);
v___x_5023_ = v_reuseFailAlloc_5024_;
goto v_reusejp_5022_;
}
v_reusejp_5022_:
{
return v___x_5023_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_5026_, lean_object* v___x_5027_, lean_object* v_declName_5028_, lean_object* v_stx_5029_, lean_object* v_attrKind_5030_, lean_object* v___y_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_){
_start:
{
uint8_t v_attrKind_boxed_5034_; lean_object* v_res_5035_; 
v_attrKind_boxed_5034_ = lean_unbox(v_attrKind_5030_);
v_res_5035_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_5026_, v___x_5027_, v_declName_5028_, v_stx_5029_, v_attrKind_boxed_5034_, v___y_5031_, v___y_5032_);
lean_dec(v___y_5032_);
lean_dec_ref(v___y_5031_);
lean_dec(v_stx_5029_);
return v_res_5035_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5036_; lean_object* v___f_5037_; 
v___x_5036_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_5037_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_5037_, 0, v___x_5036_);
return v___f_5037_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_5104_; lean_object* v___f_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___f_5104_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_5105_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5106_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5107_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5106_);
lean_ctor_set(v___x_5107_, 1, v___f_5105_);
lean_ctor_set(v___x_5107_, 2, v___f_5104_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5109_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5110_ = l_Lean_registerBuiltinAttribute(v___x_5109_);
return v___x_5110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5112_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_5113_, lean_object* v_x_5114_, lean_object* v_x_5115_){
_start:
{
uint8_t v___x_5116_; 
v___x_5116_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_5114_, v_x_5115_);
return v___x_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_5117_, lean_object* v_x_5118_, lean_object* v_x_5119_){
_start:
{
uint8_t v_res_5120_; lean_object* v_r_5121_; 
v_res_5120_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_5117_, v_x_5118_, v_x_5119_);
lean_dec(v_x_5119_);
lean_dec_ref(v_x_5118_);
v_r_5121_ = lean_box(v_res_5120_);
return v_r_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_5122_, lean_object* v_msg_5123_, lean_object* v___y_5124_, lean_object* v___y_5125_){
_start:
{
lean_object* v___x_5127_; 
v___x_5127_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_5123_, v___y_5124_, v___y_5125_);
return v___x_5127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_5128_, lean_object* v_msg_5129_, lean_object* v___y_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_){
_start:
{
lean_object* v_res_5133_; 
v_res_5133_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_5128_, v_msg_5129_, v___y_5130_, v___y_5131_);
lean_dec(v___y_5131_);
lean_dec_ref(v___y_5130_);
return v_res_5133_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5134_, lean_object* v_x_5135_, size_t v_x_5136_, lean_object* v_x_5137_){
_start:
{
uint8_t v___x_5138_; 
v___x_5138_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5135_, v_x_5136_, v_x_5137_);
return v___x_5138_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5139_, lean_object* v_x_5140_, lean_object* v_x_5141_, lean_object* v_x_5142_){
_start:
{
size_t v_x_3056__boxed_5143_; uint8_t v_res_5144_; lean_object* v_r_5145_; 
v_x_3056__boxed_5143_ = lean_unbox_usize(v_x_5141_);
lean_dec(v_x_5141_);
v_res_5144_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_5139_, v_x_5140_, v_x_3056__boxed_5143_, v_x_5142_);
lean_dec(v_x_5142_);
lean_dec_ref(v_x_5140_);
v_r_5145_ = lean_box(v_res_5144_);
return v_r_5145_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5146_, lean_object* v_keys_5147_, lean_object* v_vals_5148_, lean_object* v_heq_5149_, lean_object* v_i_5150_, lean_object* v_k_5151_){
_start:
{
uint8_t v___x_5152_; 
v___x_5152_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_5147_, v_i_5150_, v_k_5151_);
return v___x_5152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5153_, lean_object* v_keys_5154_, lean_object* v_vals_5155_, lean_object* v_heq_5156_, lean_object* v_i_5157_, lean_object* v_k_5158_){
_start:
{
uint8_t v_res_5159_; lean_object* v_r_5160_; 
v_res_5159_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_5153_, v_keys_5154_, v_vals_5155_, v_heq_5156_, v_i_5157_, v_k_5158_);
lean_dec(v_k_5158_);
lean_dec_ref(v_vals_5155_);
lean_dec_ref(v_keys_5154_);
v_r_5160_ = lean_box(v_res_5159_);
return v_r_5160_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; 
v___x_5163_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5164_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5165_ = l_Lean_addBuiltinDocString(v___x_5163_, v___x_5164_);
return v___x_5165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5166_){
_start:
{
lean_object* v_res_5167_; 
v_res_5167_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_5168_){
_start:
{
lean_object* v___x_5170_; lean_object* v___x_5171_; lean_object* v_env_5172_; lean_object* v___x_5173_; lean_object* v_ext_5174_; lean_object* v_toEnvExtension_5175_; lean_object* v_asyncMode_5176_; uint8_t v___x_5177_; lean_object* v___x_5178_; lean_object* v_discrTree_5179_; lean_object* v___x_5180_; 
v___x_5170_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5171_ = lean_st_ref_get(v_a_5168_);
v_env_5172_ = lean_ctor_get(v___x_5171_, 0);
lean_inc_ref(v_env_5172_);
lean_dec(v___x_5171_);
v___x_5173_ = l_Lean_Meta_instanceExtension;
v_ext_5174_ = lean_ctor_get(v___x_5173_, 1);
v_toEnvExtension_5175_ = lean_ctor_get(v_ext_5174_, 0);
v_asyncMode_5176_ = lean_ctor_get(v_toEnvExtension_5175_, 2);
v___x_5177_ = 1;
v___x_5178_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5170_, v___x_5173_, v_env_5172_, v_asyncMode_5176_, v___x_5177_);
v_discrTree_5179_ = lean_ctor_get(v___x_5178_, 0);
lean_inc_ref(v_discrTree_5179_);
lean_dec(v___x_5178_);
v___x_5180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5180_, 0, v_discrTree_5179_);
return v___x_5180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_5181_, lean_object* v_a_5182_){
_start:
{
lean_object* v_res_5183_; 
v_res_5183_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5181_);
lean_dec(v_a_5181_);
return v_res_5183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_5184_, lean_object* v_a_5185_){
_start:
{
lean_object* v___x_5187_; 
v___x_5187_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5185_);
return v___x_5187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_5188_, lean_object* v_a_5189_, lean_object* v_a_5190_){
_start:
{
lean_object* v_res_5191_; 
v_res_5191_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_5188_, v_a_5189_);
lean_dec(v_a_5189_);
lean_dec_ref(v_a_5188_);
return v_res_5191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_5192_){
_start:
{
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v_env_5196_; lean_object* v___x_5197_; lean_object* v_ext_5198_; lean_object* v_toEnvExtension_5199_; lean_object* v_asyncMode_5200_; uint8_t v___x_5201_; lean_object* v___x_5202_; lean_object* v_erased_5203_; lean_object* v___x_5204_; 
v___x_5194_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5195_ = lean_st_ref_get(v_a_5192_);
v_env_5196_ = lean_ctor_get(v___x_5195_, 0);
lean_inc_ref(v_env_5196_);
lean_dec(v___x_5195_);
v___x_5197_ = l_Lean_Meta_instanceExtension;
v_ext_5198_ = lean_ctor_get(v___x_5197_, 1);
v_toEnvExtension_5199_ = lean_ctor_get(v_ext_5198_, 0);
v_asyncMode_5200_ = lean_ctor_get(v_toEnvExtension_5199_, 2);
v___x_5201_ = 1;
v___x_5202_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5194_, v___x_5197_, v_env_5196_, v_asyncMode_5200_, v___x_5201_);
v_erased_5203_ = lean_ctor_get(v___x_5202_, 2);
lean_inc_ref(v_erased_5203_);
lean_dec(v___x_5202_);
v___x_5204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5204_, 0, v_erased_5203_);
return v___x_5204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_5205_, lean_object* v_a_5206_){
_start:
{
lean_object* v_res_5207_; 
v_res_5207_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5205_);
lean_dec(v_a_5205_);
return v_res_5207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_5208_, lean_object* v_a_5209_){
_start:
{
lean_object* v___x_5211_; 
v___x_5211_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5209_);
return v___x_5211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_){
_start:
{
lean_object* v_res_5215_; 
v_res_5215_ = l_Lean_Meta_getErasedInstances(v_a_5212_, v_a_5213_);
lean_dec(v_a_5213_);
lean_dec_ref(v_a_5212_);
return v_res_5215_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_5216_, lean_object* v_declName_5217_){
_start:
{
lean_object* v___x_5218_; lean_object* v_ext_5219_; lean_object* v_toEnvExtension_5220_; lean_object* v_asyncMode_5221_; lean_object* v___x_5222_; uint8_t v___x_5223_; lean_object* v___x_5224_; lean_object* v_instanceNames_5225_; uint8_t v___x_5226_; 
v___x_5218_ = l_Lean_Meta_instanceExtension;
v_ext_5219_ = lean_ctor_get(v___x_5218_, 1);
v_toEnvExtension_5220_ = lean_ctor_get(v_ext_5219_, 0);
v_asyncMode_5221_ = lean_ctor_get(v_toEnvExtension_5220_, 2);
v___x_5222_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5223_ = 1;
v___x_5224_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5222_, v___x_5218_, v_env_5216_, v_asyncMode_5221_, v___x_5223_);
v_instanceNames_5225_ = lean_ctor_get(v___x_5224_, 1);
lean_inc_ref(v_instanceNames_5225_);
lean_dec(v___x_5224_);
v___x_5226_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_5225_, v_declName_5217_);
lean_dec_ref(v_instanceNames_5225_);
return v___x_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_5227_, lean_object* v_declName_5228_){
_start:
{
uint8_t v_res_5229_; lean_object* v_r_5230_; 
v_res_5229_ = l_Lean_Meta_isInstanceCore(v_env_5227_, v_declName_5228_);
lean_dec(v_declName_5228_);
v_r_5230_ = lean_box(v_res_5229_);
return v_r_5230_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_5231_, lean_object* v_a_5232_){
_start:
{
lean_object* v___x_5234_; lean_object* v_env_5235_; uint8_t v___x_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; 
v___x_5234_ = lean_st_ref_get(v_a_5232_);
v_env_5235_ = lean_ctor_get(v___x_5234_, 0);
lean_inc_ref(v_env_5235_);
lean_dec(v___x_5234_);
v___x_5236_ = l_Lean_Meta_isInstanceCore(v_env_5235_, v_declName_5231_);
v___x_5237_ = lean_box(v___x_5236_);
v___x_5238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5238_, 0, v___x_5237_);
return v___x_5238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_5239_, lean_object* v_a_5240_, lean_object* v_a_5241_){
_start:
{
lean_object* v_res_5242_; 
v_res_5242_ = l_Lean_Meta_isInstance___redArg(v_declName_5239_, v_a_5240_);
lean_dec(v_a_5240_);
lean_dec(v_declName_5239_);
return v_res_5242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_5243_, lean_object* v_a_5244_, lean_object* v_a_5245_){
_start:
{
lean_object* v___x_5247_; 
v___x_5247_ = l_Lean_Meta_isInstance___redArg(v_declName_5243_, v_a_5245_);
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_5248_, lean_object* v_a_5249_, lean_object* v_a_5250_, lean_object* v_a_5251_){
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l_Lean_Meta_isInstance(v_declName_5248_, v_a_5249_, v_a_5250_);
lean_dec(v_a_5250_);
lean_dec_ref(v_a_5249_);
lean_dec(v_declName_5248_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5253_, lean_object* v_vals_5254_, lean_object* v_i_5255_, lean_object* v_k_5256_){
_start:
{
lean_object* v___x_5257_; uint8_t v___x_5258_; 
v___x_5257_ = lean_array_get_size(v_keys_5253_);
v___x_5258_ = lean_nat_dec_lt(v_i_5255_, v___x_5257_);
if (v___x_5258_ == 0)
{
lean_object* v___x_5259_; 
lean_dec(v_i_5255_);
v___x_5259_ = lean_box(0);
return v___x_5259_;
}
else
{
lean_object* v_k_x27_5260_; uint8_t v___x_5261_; 
v_k_x27_5260_ = lean_array_fget_borrowed(v_keys_5253_, v_i_5255_);
v___x_5261_ = lean_name_eq(v_k_5256_, v_k_x27_5260_);
if (v___x_5261_ == 0)
{
lean_object* v___x_5262_; lean_object* v___x_5263_; 
v___x_5262_ = lean_unsigned_to_nat(1u);
v___x_5263_ = lean_nat_add(v_i_5255_, v___x_5262_);
lean_dec(v_i_5255_);
v_i_5255_ = v___x_5263_;
goto _start;
}
else
{
lean_object* v___x_5265_; lean_object* v___x_5266_; 
v___x_5265_ = lean_array_fget_borrowed(v_vals_5254_, v_i_5255_);
lean_dec(v_i_5255_);
lean_inc(v___x_5265_);
v___x_5266_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5266_, 0, v___x_5265_);
return v___x_5266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5267_, lean_object* v_vals_5268_, lean_object* v_i_5269_, lean_object* v_k_5270_){
_start:
{
lean_object* v_res_5271_; 
v_res_5271_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5267_, v_vals_5268_, v_i_5269_, v_k_5270_);
lean_dec(v_k_5270_);
lean_dec_ref(v_vals_5268_);
lean_dec_ref(v_keys_5267_);
return v_res_5271_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_5272_, size_t v_x_5273_, lean_object* v_x_5274_){
_start:
{
if (lean_obj_tag(v_x_5272_) == 0)
{
lean_object* v_es_5275_; lean_object* v___x_5276_; size_t v___x_5277_; size_t v___x_5278_; lean_object* v_j_5279_; lean_object* v___x_5280_; 
v_es_5275_ = lean_ctor_get(v_x_5272_, 0);
v___x_5276_ = lean_box(2);
v___x_5277_ = ((size_t)31ULL);
v___x_5278_ = lean_usize_land(v_x_5273_, v___x_5277_);
v_j_5279_ = lean_usize_to_nat(v___x_5278_);
v___x_5280_ = lean_array_get_borrowed(v___x_5276_, v_es_5275_, v_j_5279_);
lean_dec(v_j_5279_);
switch(lean_obj_tag(v___x_5280_))
{
case 0:
{
lean_object* v_key_5281_; lean_object* v_val_5282_; uint8_t v___x_5283_; 
v_key_5281_ = lean_ctor_get(v___x_5280_, 0);
v_val_5282_ = lean_ctor_get(v___x_5280_, 1);
v___x_5283_ = lean_name_eq(v_x_5274_, v_key_5281_);
if (v___x_5283_ == 0)
{
lean_object* v___x_5284_; 
v___x_5284_ = lean_box(0);
return v___x_5284_;
}
else
{
lean_object* v___x_5285_; 
lean_inc(v_val_5282_);
v___x_5285_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5285_, 0, v_val_5282_);
return v___x_5285_;
}
}
case 1:
{
lean_object* v_node_5286_; size_t v___x_5287_; size_t v___x_5288_; 
v_node_5286_ = lean_ctor_get(v___x_5280_, 0);
v___x_5287_ = ((size_t)5ULL);
v___x_5288_ = lean_usize_shift_right(v_x_5273_, v___x_5287_);
v_x_5272_ = v_node_5286_;
v_x_5273_ = v___x_5288_;
goto _start;
}
default: 
{
lean_object* v___x_5290_; 
v___x_5290_ = lean_box(0);
return v___x_5290_;
}
}
}
else
{
lean_object* v_ks_5291_; lean_object* v_vs_5292_; lean_object* v___x_5293_; lean_object* v___x_5294_; 
v_ks_5291_ = lean_ctor_get(v_x_5272_, 0);
v_vs_5292_ = lean_ctor_get(v_x_5272_, 1);
v___x_5293_ = lean_unsigned_to_nat(0u);
v___x_5294_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5291_, v_vs_5292_, v___x_5293_, v_x_5274_);
return v___x_5294_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5295_, lean_object* v_x_5296_, lean_object* v_x_5297_){
_start:
{
size_t v_x_481__boxed_5298_; lean_object* v_res_5299_; 
v_x_481__boxed_5298_ = lean_unbox_usize(v_x_5296_);
lean_dec(v_x_5296_);
v_res_5299_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5295_, v_x_481__boxed_5298_, v_x_5297_);
lean_dec(v_x_5297_);
lean_dec_ref(v_x_5295_);
return v_res_5299_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_5300_, lean_object* v_x_5301_){
_start:
{
uint64_t v___y_5303_; 
if (lean_obj_tag(v_x_5301_) == 0)
{
uint64_t v___x_5306_; 
v___x_5306_ = 1723ULL;
v___y_5303_ = v___x_5306_;
goto v___jp_5302_;
}
else
{
uint64_t v_hash_5307_; 
v_hash_5307_ = lean_ctor_get_uint64(v_x_5301_, sizeof(void*)*2);
v___y_5303_ = v_hash_5307_;
goto v___jp_5302_;
}
v___jp_5302_:
{
size_t v___x_5304_; lean_object* v___x_5305_; 
v___x_5304_ = lean_uint64_to_usize(v___y_5303_);
v___x_5305_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5300_, v___x_5304_, v_x_5301_);
return v___x_5305_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_5308_, lean_object* v_x_5309_){
_start:
{
lean_object* v_res_5310_; 
v_res_5310_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5308_, v_x_5309_);
lean_dec(v_x_5309_);
lean_dec_ref(v_x_5308_);
return v_res_5310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_5311_, lean_object* v_a_5312_){
_start:
{
lean_object* v___x_5314_; lean_object* v___x_5315_; lean_object* v_env_5316_; lean_object* v___x_5317_; lean_object* v_ext_5318_; lean_object* v_toEnvExtension_5319_; lean_object* v_asyncMode_5320_; uint8_t v___x_5321_; lean_object* v___x_5322_; lean_object* v_instanceNames_5323_; lean_object* v___x_5324_; 
v___x_5314_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5315_ = lean_st_ref_get(v_a_5312_);
v_env_5316_ = lean_ctor_get(v___x_5315_, 0);
lean_inc_ref(v_env_5316_);
lean_dec(v___x_5315_);
v___x_5317_ = l_Lean_Meta_instanceExtension;
v_ext_5318_ = lean_ctor_get(v___x_5317_, 1);
v_toEnvExtension_5319_ = lean_ctor_get(v_ext_5318_, 0);
v_asyncMode_5320_ = lean_ctor_get(v_toEnvExtension_5319_, 2);
v___x_5321_ = 1;
v___x_5322_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5314_, v___x_5317_, v_env_5316_, v_asyncMode_5320_, v___x_5321_);
v_instanceNames_5323_ = lean_ctor_get(v___x_5322_, 1);
lean_inc_ref(v_instanceNames_5323_);
lean_dec(v___x_5322_);
v___x_5324_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5323_, v_declName_5311_);
lean_dec_ref(v_instanceNames_5323_);
if (lean_obj_tag(v___x_5324_) == 1)
{
lean_object* v_val_5325_; lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5334_; 
v_val_5325_ = lean_ctor_get(v___x_5324_, 0);
v_isSharedCheck_5334_ = !lean_is_exclusive(v___x_5324_);
if (v_isSharedCheck_5334_ == 0)
{
v___x_5327_ = v___x_5324_;
v_isShared_5328_ = v_isSharedCheck_5334_;
goto v_resetjp_5326_;
}
else
{
lean_inc(v_val_5325_);
lean_dec(v___x_5324_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5334_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v_priority_5329_; lean_object* v___x_5331_; 
v_priority_5329_ = lean_ctor_get(v_val_5325_, 2);
lean_inc(v_priority_5329_);
lean_dec(v_val_5325_);
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 0, v_priority_5329_);
v___x_5331_ = v___x_5327_;
goto v_reusejp_5330_;
}
else
{
lean_object* v_reuseFailAlloc_5333_; 
v_reuseFailAlloc_5333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5333_, 0, v_priority_5329_);
v___x_5331_ = v_reuseFailAlloc_5333_;
goto v_reusejp_5330_;
}
v_reusejp_5330_:
{
lean_object* v___x_5332_; 
v___x_5332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5332_, 0, v___x_5331_);
return v___x_5332_;
}
}
}
else
{
lean_object* v___x_5335_; lean_object* v___x_5336_; 
lean_dec(v___x_5324_);
v___x_5335_ = lean_box(0);
v___x_5336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5336_, 0, v___x_5335_);
return v___x_5336_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_5337_, lean_object* v_a_5338_, lean_object* v_a_5339_){
_start:
{
lean_object* v_res_5340_; 
v_res_5340_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5337_, v_a_5338_);
lean_dec(v_a_5338_);
lean_dec(v_declName_5337_);
return v_res_5340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_5341_, lean_object* v_a_5342_, lean_object* v_a_5343_){
_start:
{
lean_object* v___x_5345_; 
v___x_5345_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5341_, v_a_5343_);
return v___x_5345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_5346_, lean_object* v_a_5347_, lean_object* v_a_5348_, lean_object* v_a_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_5346_, v_a_5347_, v_a_5348_);
lean_dec(v_a_5348_);
lean_dec_ref(v_a_5347_);
lean_dec(v_declName_5346_);
return v_res_5350_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_5351_, lean_object* v_x_5352_, lean_object* v_x_5353_){
_start:
{
lean_object* v___x_5354_; 
v___x_5354_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5352_, v_x_5353_);
return v___x_5354_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_5355_, lean_object* v_x_5356_, lean_object* v_x_5357_){
_start:
{
lean_object* v_res_5358_; 
v_res_5358_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_5355_, v_x_5356_, v_x_5357_);
lean_dec(v_x_5357_);
lean_dec_ref(v_x_5356_);
return v_res_5358_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5359_, lean_object* v_x_5360_, size_t v_x_5361_, lean_object* v_x_5362_){
_start:
{
lean_object* v___x_5363_; 
v___x_5363_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5360_, v_x_5361_, v_x_5362_);
return v___x_5363_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5364_, lean_object* v_x_5365_, lean_object* v_x_5366_, lean_object* v_x_5367_){
_start:
{
size_t v_x_594__boxed_5368_; lean_object* v_res_5369_; 
v_x_594__boxed_5368_ = lean_unbox_usize(v_x_5366_);
lean_dec(v_x_5366_);
v_res_5369_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_5364_, v_x_5365_, v_x_594__boxed_5368_, v_x_5367_);
lean_dec(v_x_5367_);
lean_dec_ref(v_x_5365_);
return v_res_5369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5370_, lean_object* v_keys_5371_, lean_object* v_vals_5372_, lean_object* v_heq_5373_, lean_object* v_i_5374_, lean_object* v_k_5375_){
_start:
{
lean_object* v___x_5376_; 
v___x_5376_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5371_, v_vals_5372_, v_i_5374_, v_k_5375_);
return v___x_5376_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5377_, lean_object* v_keys_5378_, lean_object* v_vals_5379_, lean_object* v_heq_5380_, lean_object* v_i_5381_, lean_object* v_k_5382_){
_start:
{
lean_object* v_res_5383_; 
v_res_5383_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5377_, v_keys_5378_, v_vals_5379_, v_heq_5380_, v_i_5381_, v_k_5382_);
lean_dec(v_k_5382_);
lean_dec_ref(v_vals_5379_);
lean_dec_ref(v_keys_5378_);
return v_res_5383_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_5384_, lean_object* v_a_5385_){
_start:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v_env_5389_; lean_object* v___x_5390_; lean_object* v_ext_5391_; lean_object* v_toEnvExtension_5392_; lean_object* v_asyncMode_5393_; uint8_t v___x_5394_; lean_object* v___x_5395_; lean_object* v_instanceNames_5396_; lean_object* v___x_5397_; 
v___x_5387_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5388_ = lean_st_ref_get(v_a_5385_);
v_env_5389_ = lean_ctor_get(v___x_5388_, 0);
lean_inc_ref(v_env_5389_);
lean_dec(v___x_5388_);
v___x_5390_ = l_Lean_Meta_instanceExtension;
v_ext_5391_ = lean_ctor_get(v___x_5390_, 1);
v_toEnvExtension_5392_ = lean_ctor_get(v_ext_5391_, 0);
v_asyncMode_5393_ = lean_ctor_get(v_toEnvExtension_5392_, 2);
v___x_5394_ = 1;
v___x_5395_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5387_, v___x_5390_, v_env_5389_, v_asyncMode_5393_, v___x_5394_);
v_instanceNames_5396_ = lean_ctor_get(v___x_5395_, 1);
lean_inc_ref(v_instanceNames_5396_);
lean_dec(v___x_5395_);
v___x_5397_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5396_, v_declName_5384_);
lean_dec_ref(v_instanceNames_5396_);
if (lean_obj_tag(v___x_5397_) == 1)
{
lean_object* v_val_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5408_; 
v_val_5398_ = lean_ctor_get(v___x_5397_, 0);
v_isSharedCheck_5408_ = !lean_is_exclusive(v___x_5397_);
if (v_isSharedCheck_5408_ == 0)
{
v___x_5400_ = v___x_5397_;
v_isShared_5401_ = v_isSharedCheck_5408_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_val_5398_);
lean_dec(v___x_5397_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5408_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
uint8_t v_attrKind_5402_; lean_object* v___x_5403_; lean_object* v___x_5405_; 
v_attrKind_5402_ = lean_ctor_get_uint8(v_val_5398_, sizeof(void*)*5);
lean_dec(v_val_5398_);
v___x_5403_ = lean_box(v_attrKind_5402_);
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 0, v___x_5403_);
v___x_5405_ = v___x_5400_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5407_; 
v_reuseFailAlloc_5407_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5407_, 0, v___x_5403_);
v___x_5405_ = v_reuseFailAlloc_5407_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
lean_object* v___x_5406_; 
v___x_5406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5406_, 0, v___x_5405_);
return v___x_5406_;
}
}
}
else
{
lean_object* v___x_5409_; lean_object* v___x_5410_; 
lean_dec(v___x_5397_);
v___x_5409_ = lean_box(0);
v___x_5410_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5410_, 0, v___x_5409_);
return v___x_5410_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_){
_start:
{
lean_object* v_res_5414_; 
v_res_5414_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5411_, v_a_5412_);
lean_dec(v_a_5412_);
lean_dec(v_declName_5411_);
return v_res_5414_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_5415_, lean_object* v_a_5416_, lean_object* v_a_5417_){
_start:
{
lean_object* v___x_5419_; 
v___x_5419_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5415_, v_a_5417_);
return v___x_5419_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_5420_, lean_object* v_a_5421_, lean_object* v_a_5422_, lean_object* v_a_5423_){
_start:
{
lean_object* v_res_5424_; 
v_res_5424_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_5420_, v_a_5421_, v_a_5422_);
lean_dec(v_a_5422_);
lean_dec_ref(v_a_5421_);
lean_dec(v_declName_5420_);
return v_res_5424_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5429_, lean_object* v_v_5430_, lean_object* v_t_5431_){
_start:
{
if (lean_obj_tag(v_t_5431_) == 0)
{
lean_object* v_size_5432_; lean_object* v_k_5433_; lean_object* v_v_5434_; lean_object* v_l_5435_; lean_object* v_r_5436_; lean_object* v___x_5438_; uint8_t v_isShared_5439_; uint8_t v_isSharedCheck_5717_; 
v_size_5432_ = lean_ctor_get(v_t_5431_, 0);
v_k_5433_ = lean_ctor_get(v_t_5431_, 1);
v_v_5434_ = lean_ctor_get(v_t_5431_, 2);
v_l_5435_ = lean_ctor_get(v_t_5431_, 3);
v_r_5436_ = lean_ctor_get(v_t_5431_, 4);
v_isSharedCheck_5717_ = !lean_is_exclusive(v_t_5431_);
if (v_isSharedCheck_5717_ == 0)
{
v___x_5438_ = v_t_5431_;
v_isShared_5439_ = v_isSharedCheck_5717_;
goto v_resetjp_5437_;
}
else
{
lean_inc(v_r_5436_);
lean_inc(v_l_5435_);
lean_inc(v_v_5434_);
lean_inc(v_k_5433_);
lean_inc(v_size_5432_);
lean_dec(v_t_5431_);
v___x_5438_ = lean_box(0);
v_isShared_5439_ = v_isSharedCheck_5717_;
goto v_resetjp_5437_;
}
v_resetjp_5437_:
{
uint8_t v___x_5440_; 
v___x_5440_ = lean_nat_dec_lt(v_k_5433_, v_k_5429_);
if (v___x_5440_ == 0)
{
uint8_t v___x_5441_; 
v___x_5441_ = lean_nat_dec_eq(v_k_5433_, v_k_5429_);
if (v___x_5441_ == 0)
{
lean_object* v_impl_5442_; lean_object* v___x_5443_; 
lean_dec(v_size_5432_);
v_impl_5442_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5429_, v_v_5430_, v_r_5436_);
v___x_5443_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5435_) == 0)
{
lean_object* v_size_5444_; lean_object* v_size_5445_; lean_object* v_k_5446_; lean_object* v_v_5447_; lean_object* v_l_5448_; lean_object* v_r_5449_; lean_object* v___x_5450_; lean_object* v___x_5451_; uint8_t v___x_5452_; 
v_size_5444_ = lean_ctor_get(v_l_5435_, 0);
v_size_5445_ = lean_ctor_get(v_impl_5442_, 0);
v_k_5446_ = lean_ctor_get(v_impl_5442_, 1);
v_v_5447_ = lean_ctor_get(v_impl_5442_, 2);
v_l_5448_ = lean_ctor_get(v_impl_5442_, 3);
lean_inc(v_l_5448_);
v_r_5449_ = lean_ctor_get(v_impl_5442_, 4);
v___x_5450_ = lean_unsigned_to_nat(3u);
v___x_5451_ = lean_nat_mul(v___x_5450_, v_size_5444_);
v___x_5452_ = lean_nat_dec_lt(v___x_5451_, v_size_5445_);
lean_dec(v___x_5451_);
if (v___x_5452_ == 0)
{
lean_object* v___x_5453_; lean_object* v___x_5454_; lean_object* v___x_5456_; 
lean_dec(v_l_5448_);
v___x_5453_ = lean_nat_add(v___x_5443_, v_size_5444_);
v___x_5454_ = lean_nat_add(v___x_5453_, v_size_5445_);
lean_dec(v___x_5453_);
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 4, v_impl_5442_);
lean_ctor_set(v___x_5438_, 0, v___x_5454_);
v___x_5456_ = v___x_5438_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5457_; 
v_reuseFailAlloc_5457_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5457_, 0, v___x_5454_);
lean_ctor_set(v_reuseFailAlloc_5457_, 1, v_k_5433_);
lean_ctor_set(v_reuseFailAlloc_5457_, 2, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5457_, 3, v_l_5435_);
lean_ctor_set(v_reuseFailAlloc_5457_, 4, v_impl_5442_);
v___x_5456_ = v_reuseFailAlloc_5457_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
return v___x_5456_;
}
}
else
{
lean_object* v___x_5459_; uint8_t v_isShared_5460_; uint8_t v_isSharedCheck_5521_; 
lean_inc(v_r_5449_);
lean_inc(v_v_5447_);
lean_inc(v_k_5446_);
lean_inc(v_size_5445_);
v_isSharedCheck_5521_ = !lean_is_exclusive(v_impl_5442_);
if (v_isSharedCheck_5521_ == 0)
{
lean_object* v_unused_5522_; lean_object* v_unused_5523_; lean_object* v_unused_5524_; lean_object* v_unused_5525_; lean_object* v_unused_5526_; 
v_unused_5522_ = lean_ctor_get(v_impl_5442_, 4);
lean_dec(v_unused_5522_);
v_unused_5523_ = lean_ctor_get(v_impl_5442_, 3);
lean_dec(v_unused_5523_);
v_unused_5524_ = lean_ctor_get(v_impl_5442_, 2);
lean_dec(v_unused_5524_);
v_unused_5525_ = lean_ctor_get(v_impl_5442_, 1);
lean_dec(v_unused_5525_);
v_unused_5526_ = lean_ctor_get(v_impl_5442_, 0);
lean_dec(v_unused_5526_);
v___x_5459_ = v_impl_5442_;
v_isShared_5460_ = v_isSharedCheck_5521_;
goto v_resetjp_5458_;
}
else
{
lean_dec(v_impl_5442_);
v___x_5459_ = lean_box(0);
v_isShared_5460_ = v_isSharedCheck_5521_;
goto v_resetjp_5458_;
}
v_resetjp_5458_:
{
lean_object* v_size_5461_; lean_object* v_k_5462_; lean_object* v_v_5463_; lean_object* v_l_5464_; lean_object* v_r_5465_; lean_object* v_size_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; uint8_t v___x_5469_; 
v_size_5461_ = lean_ctor_get(v_l_5448_, 0);
v_k_5462_ = lean_ctor_get(v_l_5448_, 1);
v_v_5463_ = lean_ctor_get(v_l_5448_, 2);
v_l_5464_ = lean_ctor_get(v_l_5448_, 3);
v_r_5465_ = lean_ctor_get(v_l_5448_, 4);
v_size_5466_ = lean_ctor_get(v_r_5449_, 0);
v___x_5467_ = lean_unsigned_to_nat(2u);
v___x_5468_ = lean_nat_mul(v___x_5467_, v_size_5466_);
v___x_5469_ = lean_nat_dec_lt(v_size_5461_, v___x_5468_);
lean_dec(v___x_5468_);
if (v___x_5469_ == 0)
{
lean_object* v___x_5471_; uint8_t v_isShared_5472_; uint8_t v_isSharedCheck_5497_; 
lean_inc(v_r_5465_);
lean_inc(v_l_5464_);
lean_inc(v_v_5463_);
lean_inc(v_k_5462_);
v_isSharedCheck_5497_ = !lean_is_exclusive(v_l_5448_);
if (v_isSharedCheck_5497_ == 0)
{
lean_object* v_unused_5498_; lean_object* v_unused_5499_; lean_object* v_unused_5500_; lean_object* v_unused_5501_; lean_object* v_unused_5502_; 
v_unused_5498_ = lean_ctor_get(v_l_5448_, 4);
lean_dec(v_unused_5498_);
v_unused_5499_ = lean_ctor_get(v_l_5448_, 3);
lean_dec(v_unused_5499_);
v_unused_5500_ = lean_ctor_get(v_l_5448_, 2);
lean_dec(v_unused_5500_);
v_unused_5501_ = lean_ctor_get(v_l_5448_, 1);
lean_dec(v_unused_5501_);
v_unused_5502_ = lean_ctor_get(v_l_5448_, 0);
lean_dec(v_unused_5502_);
v___x_5471_ = v_l_5448_;
v_isShared_5472_ = v_isSharedCheck_5497_;
goto v_resetjp_5470_;
}
else
{
lean_dec(v_l_5448_);
v___x_5471_ = lean_box(0);
v_isShared_5472_ = v_isSharedCheck_5497_;
goto v_resetjp_5470_;
}
v_resetjp_5470_:
{
lean_object* v___x_5473_; lean_object* v___x_5474_; lean_object* v___y_5476_; lean_object* v___y_5477_; lean_object* v___y_5478_; lean_object* v___y_5487_; 
v___x_5473_ = lean_nat_add(v___x_5443_, v_size_5444_);
v___x_5474_ = lean_nat_add(v___x_5473_, v_size_5445_);
lean_dec(v_size_5445_);
if (lean_obj_tag(v_l_5464_) == 0)
{
lean_object* v_size_5495_; 
v_size_5495_ = lean_ctor_get(v_l_5464_, 0);
lean_inc(v_size_5495_);
v___y_5487_ = v_size_5495_;
goto v___jp_5486_;
}
else
{
lean_object* v___x_5496_; 
v___x_5496_ = lean_unsigned_to_nat(0u);
v___y_5487_ = v___x_5496_;
goto v___jp_5486_;
}
v___jp_5475_:
{
lean_object* v___x_5479_; lean_object* v___x_5481_; 
v___x_5479_ = lean_nat_add(v___y_5476_, v___y_5478_);
lean_dec(v___y_5478_);
lean_dec(v___y_5476_);
if (v_isShared_5472_ == 0)
{
lean_ctor_set(v___x_5471_, 4, v_r_5449_);
lean_ctor_set(v___x_5471_, 3, v_r_5465_);
lean_ctor_set(v___x_5471_, 2, v_v_5447_);
lean_ctor_set(v___x_5471_, 1, v_k_5446_);
lean_ctor_set(v___x_5471_, 0, v___x_5479_);
v___x_5481_ = v___x_5471_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5485_; 
v_reuseFailAlloc_5485_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5485_, 0, v___x_5479_);
lean_ctor_set(v_reuseFailAlloc_5485_, 1, v_k_5446_);
lean_ctor_set(v_reuseFailAlloc_5485_, 2, v_v_5447_);
lean_ctor_set(v_reuseFailAlloc_5485_, 3, v_r_5465_);
lean_ctor_set(v_reuseFailAlloc_5485_, 4, v_r_5449_);
v___x_5481_ = v_reuseFailAlloc_5485_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
lean_object* v___x_5483_; 
if (v_isShared_5460_ == 0)
{
lean_ctor_set(v___x_5459_, 4, v___x_5481_);
lean_ctor_set(v___x_5459_, 3, v___y_5477_);
lean_ctor_set(v___x_5459_, 2, v_v_5463_);
lean_ctor_set(v___x_5459_, 1, v_k_5462_);
lean_ctor_set(v___x_5459_, 0, v___x_5474_);
v___x_5483_ = v___x_5459_;
goto v_reusejp_5482_;
}
else
{
lean_object* v_reuseFailAlloc_5484_; 
v_reuseFailAlloc_5484_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5484_, 0, v___x_5474_);
lean_ctor_set(v_reuseFailAlloc_5484_, 1, v_k_5462_);
lean_ctor_set(v_reuseFailAlloc_5484_, 2, v_v_5463_);
lean_ctor_set(v_reuseFailAlloc_5484_, 3, v___y_5477_);
lean_ctor_set(v_reuseFailAlloc_5484_, 4, v___x_5481_);
v___x_5483_ = v_reuseFailAlloc_5484_;
goto v_reusejp_5482_;
}
v_reusejp_5482_:
{
return v___x_5483_;
}
}
}
v___jp_5486_:
{
lean_object* v___x_5488_; lean_object* v___x_5490_; 
v___x_5488_ = lean_nat_add(v___x_5473_, v___y_5487_);
lean_dec(v___y_5487_);
lean_dec(v___x_5473_);
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 4, v_l_5464_);
lean_ctor_set(v___x_5438_, 0, v___x_5488_);
v___x_5490_ = v___x_5438_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5494_; 
v_reuseFailAlloc_5494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5494_, 0, v___x_5488_);
lean_ctor_set(v_reuseFailAlloc_5494_, 1, v_k_5433_);
lean_ctor_set(v_reuseFailAlloc_5494_, 2, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5494_, 3, v_l_5435_);
lean_ctor_set(v_reuseFailAlloc_5494_, 4, v_l_5464_);
v___x_5490_ = v_reuseFailAlloc_5494_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
lean_object* v___x_5491_; 
v___x_5491_ = lean_nat_add(v___x_5443_, v_size_5466_);
if (lean_obj_tag(v_r_5465_) == 0)
{
lean_object* v_size_5492_; 
v_size_5492_ = lean_ctor_get(v_r_5465_, 0);
lean_inc(v_size_5492_);
v___y_5476_ = v___x_5491_;
v___y_5477_ = v___x_5490_;
v___y_5478_ = v_size_5492_;
goto v___jp_5475_;
}
else
{
lean_object* v___x_5493_; 
v___x_5493_ = lean_unsigned_to_nat(0u);
v___y_5476_ = v___x_5491_;
v___y_5477_ = v___x_5490_;
v___y_5478_ = v___x_5493_;
goto v___jp_5475_;
}
}
}
}
}
else
{
lean_object* v___x_5503_; lean_object* v___x_5504_; lean_object* v___x_5505_; lean_object* v___x_5507_; 
lean_del_object(v___x_5438_);
v___x_5503_ = lean_nat_add(v___x_5443_, v_size_5444_);
v___x_5504_ = lean_nat_add(v___x_5503_, v_size_5445_);
lean_dec(v_size_5445_);
v___x_5505_ = lean_nat_add(v___x_5503_, v_size_5461_);
lean_dec(v___x_5503_);
lean_inc_ref(v_l_5435_);
if (v_isShared_5460_ == 0)
{
lean_ctor_set(v___x_5459_, 4, v_l_5448_);
lean_ctor_set(v___x_5459_, 3, v_l_5435_);
lean_ctor_set(v___x_5459_, 2, v_v_5434_);
lean_ctor_set(v___x_5459_, 1, v_k_5433_);
lean_ctor_set(v___x_5459_, 0, v___x_5505_);
v___x_5507_ = v___x_5459_;
goto v_reusejp_5506_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v___x_5505_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v_k_5433_);
lean_ctor_set(v_reuseFailAlloc_5520_, 2, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5520_, 3, v_l_5435_);
lean_ctor_set(v_reuseFailAlloc_5520_, 4, v_l_5448_);
v___x_5507_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5506_;
}
v_reusejp_5506_:
{
lean_object* v___x_5509_; uint8_t v_isShared_5510_; uint8_t v_isSharedCheck_5514_; 
v_isSharedCheck_5514_ = !lean_is_exclusive(v_l_5435_);
if (v_isSharedCheck_5514_ == 0)
{
lean_object* v_unused_5515_; lean_object* v_unused_5516_; lean_object* v_unused_5517_; lean_object* v_unused_5518_; lean_object* v_unused_5519_; 
v_unused_5515_ = lean_ctor_get(v_l_5435_, 4);
lean_dec(v_unused_5515_);
v_unused_5516_ = lean_ctor_get(v_l_5435_, 3);
lean_dec(v_unused_5516_);
v_unused_5517_ = lean_ctor_get(v_l_5435_, 2);
lean_dec(v_unused_5517_);
v_unused_5518_ = lean_ctor_get(v_l_5435_, 1);
lean_dec(v_unused_5518_);
v_unused_5519_ = lean_ctor_get(v_l_5435_, 0);
lean_dec(v_unused_5519_);
v___x_5509_ = v_l_5435_;
v_isShared_5510_ = v_isSharedCheck_5514_;
goto v_resetjp_5508_;
}
else
{
lean_dec(v_l_5435_);
v___x_5509_ = lean_box(0);
v_isShared_5510_ = v_isSharedCheck_5514_;
goto v_resetjp_5508_;
}
v_resetjp_5508_:
{
lean_object* v___x_5512_; 
if (v_isShared_5510_ == 0)
{
lean_ctor_set(v___x_5509_, 4, v_r_5449_);
lean_ctor_set(v___x_5509_, 3, v___x_5507_);
lean_ctor_set(v___x_5509_, 2, v_v_5447_);
lean_ctor_set(v___x_5509_, 1, v_k_5446_);
lean_ctor_set(v___x_5509_, 0, v___x_5504_);
v___x_5512_ = v___x_5509_;
goto v_reusejp_5511_;
}
else
{
lean_object* v_reuseFailAlloc_5513_; 
v_reuseFailAlloc_5513_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5513_, 0, v___x_5504_);
lean_ctor_set(v_reuseFailAlloc_5513_, 1, v_k_5446_);
lean_ctor_set(v_reuseFailAlloc_5513_, 2, v_v_5447_);
lean_ctor_set(v_reuseFailAlloc_5513_, 3, v___x_5507_);
lean_ctor_set(v_reuseFailAlloc_5513_, 4, v_r_5449_);
v___x_5512_ = v_reuseFailAlloc_5513_;
goto v_reusejp_5511_;
}
v_reusejp_5511_:
{
return v___x_5512_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5527_; 
v_l_5527_ = lean_ctor_get(v_impl_5442_, 3);
lean_inc(v_l_5527_);
if (lean_obj_tag(v_l_5527_) == 0)
{
lean_object* v_r_5528_; lean_object* v_k_5529_; lean_object* v_v_5530_; lean_object* v___x_5532_; uint8_t v_isShared_5533_; uint8_t v_isSharedCheck_5553_; 
v_r_5528_ = lean_ctor_get(v_impl_5442_, 4);
v_k_5529_ = lean_ctor_get(v_impl_5442_, 1);
v_v_5530_ = lean_ctor_get(v_impl_5442_, 2);
v_isSharedCheck_5553_ = !lean_is_exclusive(v_impl_5442_);
if (v_isSharedCheck_5553_ == 0)
{
lean_object* v_unused_5554_; lean_object* v_unused_5555_; 
v_unused_5554_ = lean_ctor_get(v_impl_5442_, 3);
lean_dec(v_unused_5554_);
v_unused_5555_ = lean_ctor_get(v_impl_5442_, 0);
lean_dec(v_unused_5555_);
v___x_5532_ = v_impl_5442_;
v_isShared_5533_ = v_isSharedCheck_5553_;
goto v_resetjp_5531_;
}
else
{
lean_inc(v_r_5528_);
lean_inc(v_v_5530_);
lean_inc(v_k_5529_);
lean_dec(v_impl_5442_);
v___x_5532_ = lean_box(0);
v_isShared_5533_ = v_isSharedCheck_5553_;
goto v_resetjp_5531_;
}
v_resetjp_5531_:
{
lean_object* v_k_5534_; lean_object* v_v_5535_; lean_object* v___x_5537_; uint8_t v_isShared_5538_; uint8_t v_isSharedCheck_5549_; 
v_k_5534_ = lean_ctor_get(v_l_5527_, 1);
v_v_5535_ = lean_ctor_get(v_l_5527_, 2);
v_isSharedCheck_5549_ = !lean_is_exclusive(v_l_5527_);
if (v_isSharedCheck_5549_ == 0)
{
lean_object* v_unused_5550_; lean_object* v_unused_5551_; lean_object* v_unused_5552_; 
v_unused_5550_ = lean_ctor_get(v_l_5527_, 4);
lean_dec(v_unused_5550_);
v_unused_5551_ = lean_ctor_get(v_l_5527_, 3);
lean_dec(v_unused_5551_);
v_unused_5552_ = lean_ctor_get(v_l_5527_, 0);
lean_dec(v_unused_5552_);
v___x_5537_ = v_l_5527_;
v_isShared_5538_ = v_isSharedCheck_5549_;
goto v_resetjp_5536_;
}
else
{
lean_inc(v_v_5535_);
lean_inc(v_k_5534_);
lean_dec(v_l_5527_);
v___x_5537_ = lean_box(0);
v_isShared_5538_ = v_isSharedCheck_5549_;
goto v_resetjp_5536_;
}
v_resetjp_5536_:
{
lean_object* v___x_5539_; lean_object* v___x_5541_; 
v___x_5539_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5528_, 2);
if (v_isShared_5538_ == 0)
{
lean_ctor_set(v___x_5537_, 4, v_r_5528_);
lean_ctor_set(v___x_5537_, 3, v_r_5528_);
lean_ctor_set(v___x_5537_, 2, v_v_5434_);
lean_ctor_set(v___x_5537_, 1, v_k_5433_);
lean_ctor_set(v___x_5537_, 0, v___x_5443_);
v___x_5541_ = v___x_5537_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v___x_5443_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v_k_5433_);
lean_ctor_set(v_reuseFailAlloc_5548_, 2, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5548_, 3, v_r_5528_);
lean_ctor_set(v_reuseFailAlloc_5548_, 4, v_r_5528_);
v___x_5541_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
lean_object* v___x_5543_; 
lean_inc(v_r_5528_);
if (v_isShared_5533_ == 0)
{
lean_ctor_set(v___x_5532_, 3, v_r_5528_);
lean_ctor_set(v___x_5532_, 0, v___x_5443_);
v___x_5543_ = v___x_5532_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v___x_5443_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v_k_5529_);
lean_ctor_set(v_reuseFailAlloc_5547_, 2, v_v_5530_);
lean_ctor_set(v_reuseFailAlloc_5547_, 3, v_r_5528_);
lean_ctor_set(v_reuseFailAlloc_5547_, 4, v_r_5528_);
v___x_5543_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
lean_object* v___x_5545_; 
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 4, v___x_5543_);
lean_ctor_set(v___x_5438_, 3, v___x_5541_);
lean_ctor_set(v___x_5438_, 2, v_v_5535_);
lean_ctor_set(v___x_5438_, 1, v_k_5534_);
lean_ctor_set(v___x_5438_, 0, v___x_5539_);
v___x_5545_ = v___x_5438_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v___x_5539_);
lean_ctor_set(v_reuseFailAlloc_5546_, 1, v_k_5534_);
lean_ctor_set(v_reuseFailAlloc_5546_, 2, v_v_5535_);
lean_ctor_set(v_reuseFailAlloc_5546_, 3, v___x_5541_);
lean_ctor_set(v_reuseFailAlloc_5546_, 4, v___x_5543_);
v___x_5545_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
return v___x_5545_;
}
}
}
}
}
}
else
{
lean_object* v_r_5556_; 
v_r_5556_ = lean_ctor_get(v_impl_5442_, 4);
lean_inc(v_r_5556_);
if (lean_obj_tag(v_r_5556_) == 0)
{
lean_object* v_k_5557_; lean_object* v_v_5558_; lean_object* v___x_5560_; uint8_t v_isShared_5561_; uint8_t v_isSharedCheck_5569_; 
v_k_5557_ = lean_ctor_get(v_impl_5442_, 1);
v_v_5558_ = lean_ctor_get(v_impl_5442_, 2);
v_isSharedCheck_5569_ = !lean_is_exclusive(v_impl_5442_);
if (v_isSharedCheck_5569_ == 0)
{
lean_object* v_unused_5570_; lean_object* v_unused_5571_; lean_object* v_unused_5572_; 
v_unused_5570_ = lean_ctor_get(v_impl_5442_, 4);
lean_dec(v_unused_5570_);
v_unused_5571_ = lean_ctor_get(v_impl_5442_, 3);
lean_dec(v_unused_5571_);
v_unused_5572_ = lean_ctor_get(v_impl_5442_, 0);
lean_dec(v_unused_5572_);
v___x_5560_ = v_impl_5442_;
v_isShared_5561_ = v_isSharedCheck_5569_;
goto v_resetjp_5559_;
}
else
{
lean_inc(v_v_5558_);
lean_inc(v_k_5557_);
lean_dec(v_impl_5442_);
v___x_5560_ = lean_box(0);
v_isShared_5561_ = v_isSharedCheck_5569_;
goto v_resetjp_5559_;
}
v_resetjp_5559_:
{
lean_object* v___x_5562_; lean_object* v___x_5564_; 
v___x_5562_ = lean_unsigned_to_nat(3u);
if (v_isShared_5561_ == 0)
{
lean_ctor_set(v___x_5560_, 4, v_l_5527_);
lean_ctor_set(v___x_5560_, 2, v_v_5434_);
lean_ctor_set(v___x_5560_, 1, v_k_5433_);
lean_ctor_set(v___x_5560_, 0, v___x_5443_);
v___x_5564_ = v___x_5560_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5443_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v_k_5433_);
lean_ctor_set(v_reuseFailAlloc_5568_, 2, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5568_, 3, v_l_5527_);
lean_ctor_set(v_reuseFailAlloc_5568_, 4, v_l_5527_);
v___x_5564_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
lean_object* v___x_5566_; 
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 4, v_r_5556_);
lean_ctor_set(v___x_5438_, 3, v___x_5564_);
lean_ctor_set(v___x_5438_, 2, v_v_5558_);
lean_ctor_set(v___x_5438_, 1, v_k_5557_);
lean_ctor_set(v___x_5438_, 0, v___x_5562_);
v___x_5566_ = v___x_5438_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5567_; 
v_reuseFailAlloc_5567_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5567_, 0, v___x_5562_);
lean_ctor_set(v_reuseFailAlloc_5567_, 1, v_k_5557_);
lean_ctor_set(v_reuseFailAlloc_5567_, 2, v_v_5558_);
lean_ctor_set(v_reuseFailAlloc_5567_, 3, v___x_5564_);
lean_ctor_set(v_reuseFailAlloc_5567_, 4, v_r_5556_);
v___x_5566_ = v_reuseFailAlloc_5567_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
return v___x_5566_;
}
}
}
}
else
{
lean_object* v___x_5573_; lean_object* v___x_5575_; 
v___x_5573_ = lean_unsigned_to_nat(2u);
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 4, v_impl_5442_);
lean_ctor_set(v___x_5438_, 3, v_r_5556_);
lean_ctor_set(v___x_5438_, 0, v___x_5573_);
v___x_5575_ = v___x_5438_;
goto v_reusejp_5574_;
}
else
{
lean_object* v_reuseFailAlloc_5576_; 
v_reuseFailAlloc_5576_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5576_, 0, v___x_5573_);
lean_ctor_set(v_reuseFailAlloc_5576_, 1, v_k_5433_);
lean_ctor_set(v_reuseFailAlloc_5576_, 2, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5576_, 3, v_r_5556_);
lean_ctor_set(v_reuseFailAlloc_5576_, 4, v_impl_5442_);
v___x_5575_ = v_reuseFailAlloc_5576_;
goto v_reusejp_5574_;
}
v_reusejp_5574_:
{
return v___x_5575_;
}
}
}
}
}
else
{
lean_object* v___x_5578_; 
lean_dec(v_v_5434_);
lean_dec(v_k_5433_);
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 2, v_v_5430_);
lean_ctor_set(v___x_5438_, 1, v_k_5429_);
v___x_5578_ = v___x_5438_;
goto v_reusejp_5577_;
}
else
{
lean_object* v_reuseFailAlloc_5579_; 
v_reuseFailAlloc_5579_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5579_, 0, v_size_5432_);
lean_ctor_set(v_reuseFailAlloc_5579_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5579_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5579_, 3, v_l_5435_);
lean_ctor_set(v_reuseFailAlloc_5579_, 4, v_r_5436_);
v___x_5578_ = v_reuseFailAlloc_5579_;
goto v_reusejp_5577_;
}
v_reusejp_5577_:
{
return v___x_5578_;
}
}
}
else
{
lean_object* v_impl_5580_; lean_object* v___x_5581_; 
lean_dec(v_size_5432_);
v_impl_5580_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5429_, v_v_5430_, v_l_5435_);
v___x_5581_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5436_) == 0)
{
lean_object* v_size_5582_; lean_object* v_size_5583_; lean_object* v_k_5584_; lean_object* v_v_5585_; lean_object* v_l_5586_; lean_object* v_r_5587_; lean_object* v___x_5588_; lean_object* v___x_5589_; uint8_t v___x_5590_; 
v_size_5582_ = lean_ctor_get(v_r_5436_, 0);
v_size_5583_ = lean_ctor_get(v_impl_5580_, 0);
v_k_5584_ = lean_ctor_get(v_impl_5580_, 1);
v_v_5585_ = lean_ctor_get(v_impl_5580_, 2);
v_l_5586_ = lean_ctor_get(v_impl_5580_, 3);
v_r_5587_ = lean_ctor_get(v_impl_5580_, 4);
lean_inc(v_r_5587_);
v___x_5588_ = lean_unsigned_to_nat(3u);
v___x_5589_ = lean_nat_mul(v___x_5588_, v_size_5582_);
v___x_5590_ = lean_nat_dec_lt(v___x_5589_, v_size_5583_);
lean_dec(v___x_5589_);
if (v___x_5590_ == 0)
{
lean_object* v___x_5591_; lean_object* v___x_5592_; lean_object* v___x_5594_; 
lean_dec(v_r_5587_);
v___x_5591_ = lean_nat_add(v___x_5581_, v_size_5583_);
v___x_5592_ = lean_nat_add(v___x_5591_, v_size_5582_);
lean_dec(v___x_5591_);
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 3, v_impl_5580_);
lean_ctor_set(v___x_5438_, 0, v___x_5592_);
v___x_5594_ = v___x_5438_;
goto v_reusejp_5593_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v___x_5592_);
lean_ctor_set(v_reuseFailAlloc_5595_, 1, v_k_5433_);
lean_ctor_set(v_reuseFailAlloc_5595_, 2, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5595_, 3, v_impl_5580_);
lean_ctor_set(v_reuseFailAlloc_5595_, 4, v_r_5436_);
v___x_5594_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5593_;
}
v_reusejp_5593_:
{
return v___x_5594_;
}
}
else
{
lean_object* v___x_5597_; uint8_t v_isShared_5598_; uint8_t v_isSharedCheck_5661_; 
lean_inc(v_l_5586_);
lean_inc(v_v_5585_);
lean_inc(v_k_5584_);
lean_inc(v_size_5583_);
v_isSharedCheck_5661_ = !lean_is_exclusive(v_impl_5580_);
if (v_isSharedCheck_5661_ == 0)
{
lean_object* v_unused_5662_; lean_object* v_unused_5663_; lean_object* v_unused_5664_; lean_object* v_unused_5665_; lean_object* v_unused_5666_; 
v_unused_5662_ = lean_ctor_get(v_impl_5580_, 4);
lean_dec(v_unused_5662_);
v_unused_5663_ = lean_ctor_get(v_impl_5580_, 3);
lean_dec(v_unused_5663_);
v_unused_5664_ = lean_ctor_get(v_impl_5580_, 2);
lean_dec(v_unused_5664_);
v_unused_5665_ = lean_ctor_get(v_impl_5580_, 1);
lean_dec(v_unused_5665_);
v_unused_5666_ = lean_ctor_get(v_impl_5580_, 0);
lean_dec(v_unused_5666_);
v___x_5597_ = v_impl_5580_;
v_isShared_5598_ = v_isSharedCheck_5661_;
goto v_resetjp_5596_;
}
else
{
lean_dec(v_impl_5580_);
v___x_5597_ = lean_box(0);
v_isShared_5598_ = v_isSharedCheck_5661_;
goto v_resetjp_5596_;
}
v_resetjp_5596_:
{
lean_object* v_size_5599_; lean_object* v_size_5600_; lean_object* v_k_5601_; lean_object* v_v_5602_; lean_object* v_l_5603_; lean_object* v_r_5604_; lean_object* v___x_5605_; lean_object* v___x_5606_; uint8_t v___x_5607_; 
v_size_5599_ = lean_ctor_get(v_l_5586_, 0);
v_size_5600_ = lean_ctor_get(v_r_5587_, 0);
v_k_5601_ = lean_ctor_get(v_r_5587_, 1);
v_v_5602_ = lean_ctor_get(v_r_5587_, 2);
v_l_5603_ = lean_ctor_get(v_r_5587_, 3);
v_r_5604_ = lean_ctor_get(v_r_5587_, 4);
v___x_5605_ = lean_unsigned_to_nat(2u);
v___x_5606_ = lean_nat_mul(v___x_5605_, v_size_5599_);
v___x_5607_ = lean_nat_dec_lt(v_size_5600_, v___x_5606_);
lean_dec(v___x_5606_);
if (v___x_5607_ == 0)
{
lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5636_; 
lean_inc(v_r_5604_);
lean_inc(v_l_5603_);
lean_inc(v_v_5602_);
lean_inc(v_k_5601_);
v_isSharedCheck_5636_ = !lean_is_exclusive(v_r_5587_);
if (v_isSharedCheck_5636_ == 0)
{
lean_object* v_unused_5637_; lean_object* v_unused_5638_; lean_object* v_unused_5639_; lean_object* v_unused_5640_; lean_object* v_unused_5641_; 
v_unused_5637_ = lean_ctor_get(v_r_5587_, 4);
lean_dec(v_unused_5637_);
v_unused_5638_ = lean_ctor_get(v_r_5587_, 3);
lean_dec(v_unused_5638_);
v_unused_5639_ = lean_ctor_get(v_r_5587_, 2);
lean_dec(v_unused_5639_);
v_unused_5640_ = lean_ctor_get(v_r_5587_, 1);
lean_dec(v_unused_5640_);
v_unused_5641_ = lean_ctor_get(v_r_5587_, 0);
lean_dec(v_unused_5641_);
v___x_5609_ = v_r_5587_;
v_isShared_5610_ = v_isSharedCheck_5636_;
goto v_resetjp_5608_;
}
else
{
lean_dec(v_r_5587_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5636_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v___x_5611_; lean_object* v___x_5612_; lean_object* v___y_5614_; lean_object* v___y_5615_; lean_object* v___y_5616_; lean_object* v___x_5624_; lean_object* v___y_5626_; 
v___x_5611_ = lean_nat_add(v___x_5581_, v_size_5583_);
lean_dec(v_size_5583_);
v___x_5612_ = lean_nat_add(v___x_5611_, v_size_5582_);
lean_dec(v___x_5611_);
v___x_5624_ = lean_nat_add(v___x_5581_, v_size_5599_);
if (lean_obj_tag(v_l_5603_) == 0)
{
lean_object* v_size_5634_; 
v_size_5634_ = lean_ctor_get(v_l_5603_, 0);
lean_inc(v_size_5634_);
v___y_5626_ = v_size_5634_;
goto v___jp_5625_;
}
else
{
lean_object* v___x_5635_; 
v___x_5635_ = lean_unsigned_to_nat(0u);
v___y_5626_ = v___x_5635_;
goto v___jp_5625_;
}
v___jp_5613_:
{
lean_object* v___x_5617_; lean_object* v___x_5619_; 
v___x_5617_ = lean_nat_add(v___y_5614_, v___y_5616_);
lean_dec(v___y_5616_);
lean_dec(v___y_5614_);
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 4, v_r_5436_);
lean_ctor_set(v___x_5609_, 3, v_r_5604_);
lean_ctor_set(v___x_5609_, 2, v_v_5434_);
lean_ctor_set(v___x_5609_, 1, v_k_5433_);
lean_ctor_set(v___x_5609_, 0, v___x_5617_);
v___x_5619_ = v___x_5609_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v___x_5617_);
lean_ctor_set(v_reuseFailAlloc_5623_, 1, v_k_5433_);
lean_ctor_set(v_reuseFailAlloc_5623_, 2, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5623_, 3, v_r_5604_);
lean_ctor_set(v_reuseFailAlloc_5623_, 4, v_r_5436_);
v___x_5619_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
lean_object* v___x_5621_; 
if (v_isShared_5598_ == 0)
{
lean_ctor_set(v___x_5597_, 4, v___x_5619_);
lean_ctor_set(v___x_5597_, 3, v___y_5615_);
lean_ctor_set(v___x_5597_, 2, v_v_5602_);
lean_ctor_set(v___x_5597_, 1, v_k_5601_);
lean_ctor_set(v___x_5597_, 0, v___x_5612_);
v___x_5621_ = v___x_5597_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5612_);
lean_ctor_set(v_reuseFailAlloc_5622_, 1, v_k_5601_);
lean_ctor_set(v_reuseFailAlloc_5622_, 2, v_v_5602_);
lean_ctor_set(v_reuseFailAlloc_5622_, 3, v___y_5615_);
lean_ctor_set(v_reuseFailAlloc_5622_, 4, v___x_5619_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
}
v___jp_5625_:
{
lean_object* v___x_5627_; lean_object* v___x_5629_; 
v___x_5627_ = lean_nat_add(v___x_5624_, v___y_5626_);
lean_dec(v___y_5626_);
lean_dec(v___x_5624_);
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 4, v_l_5603_);
lean_ctor_set(v___x_5438_, 3, v_l_5586_);
lean_ctor_set(v___x_5438_, 2, v_v_5585_);
lean_ctor_set(v___x_5438_, 1, v_k_5584_);
lean_ctor_set(v___x_5438_, 0, v___x_5627_);
v___x_5629_ = v___x_5438_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v___x_5627_);
lean_ctor_set(v_reuseFailAlloc_5633_, 1, v_k_5584_);
lean_ctor_set(v_reuseFailAlloc_5633_, 2, v_v_5585_);
lean_ctor_set(v_reuseFailAlloc_5633_, 3, v_l_5586_);
lean_ctor_set(v_reuseFailAlloc_5633_, 4, v_l_5603_);
v___x_5629_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
lean_object* v___x_5630_; 
v___x_5630_ = lean_nat_add(v___x_5581_, v_size_5582_);
if (lean_obj_tag(v_r_5604_) == 0)
{
lean_object* v_size_5631_; 
v_size_5631_ = lean_ctor_get(v_r_5604_, 0);
lean_inc(v_size_5631_);
v___y_5614_ = v___x_5630_;
v___y_5615_ = v___x_5629_;
v___y_5616_ = v_size_5631_;
goto v___jp_5613_;
}
else
{
lean_object* v___x_5632_; 
v___x_5632_ = lean_unsigned_to_nat(0u);
v___y_5614_ = v___x_5630_;
v___y_5615_ = v___x_5629_;
v___y_5616_ = v___x_5632_;
goto v___jp_5613_;
}
}
}
}
}
else
{
lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5645_; lean_object* v___x_5647_; 
lean_del_object(v___x_5438_);
v___x_5642_ = lean_nat_add(v___x_5581_, v_size_5583_);
lean_dec(v_size_5583_);
v___x_5643_ = lean_nat_add(v___x_5642_, v_size_5582_);
lean_dec(v___x_5642_);
v___x_5644_ = lean_nat_add(v___x_5581_, v_size_5582_);
v___x_5645_ = lean_nat_add(v___x_5644_, v_size_5600_);
lean_dec(v___x_5644_);
lean_inc_ref(v_r_5436_);
if (v_isShared_5598_ == 0)
{
lean_ctor_set(v___x_5597_, 4, v_r_5436_);
lean_ctor_set(v___x_5597_, 3, v_r_5587_);
lean_ctor_set(v___x_5597_, 2, v_v_5434_);
lean_ctor_set(v___x_5597_, 1, v_k_5433_);
lean_ctor_set(v___x_5597_, 0, v___x_5645_);
v___x_5647_ = v___x_5597_;
goto v_reusejp_5646_;
}
else
{
lean_object* v_reuseFailAlloc_5660_; 
v_reuseFailAlloc_5660_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5660_, 0, v___x_5645_);
lean_ctor_set(v_reuseFailAlloc_5660_, 1, v_k_5433_);
lean_ctor_set(v_reuseFailAlloc_5660_, 2, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5660_, 3, v_r_5587_);
lean_ctor_set(v_reuseFailAlloc_5660_, 4, v_r_5436_);
v___x_5647_ = v_reuseFailAlloc_5660_;
goto v_reusejp_5646_;
}
v_reusejp_5646_:
{
lean_object* v___x_5649_; uint8_t v_isShared_5650_; uint8_t v_isSharedCheck_5654_; 
v_isSharedCheck_5654_ = !lean_is_exclusive(v_r_5436_);
if (v_isSharedCheck_5654_ == 0)
{
lean_object* v_unused_5655_; lean_object* v_unused_5656_; lean_object* v_unused_5657_; lean_object* v_unused_5658_; lean_object* v_unused_5659_; 
v_unused_5655_ = lean_ctor_get(v_r_5436_, 4);
lean_dec(v_unused_5655_);
v_unused_5656_ = lean_ctor_get(v_r_5436_, 3);
lean_dec(v_unused_5656_);
v_unused_5657_ = lean_ctor_get(v_r_5436_, 2);
lean_dec(v_unused_5657_);
v_unused_5658_ = lean_ctor_get(v_r_5436_, 1);
lean_dec(v_unused_5658_);
v_unused_5659_ = lean_ctor_get(v_r_5436_, 0);
lean_dec(v_unused_5659_);
v___x_5649_ = v_r_5436_;
v_isShared_5650_ = v_isSharedCheck_5654_;
goto v_resetjp_5648_;
}
else
{
lean_dec(v_r_5436_);
v___x_5649_ = lean_box(0);
v_isShared_5650_ = v_isSharedCheck_5654_;
goto v_resetjp_5648_;
}
v_resetjp_5648_:
{
lean_object* v___x_5652_; 
if (v_isShared_5650_ == 0)
{
lean_ctor_set(v___x_5649_, 4, v___x_5647_);
lean_ctor_set(v___x_5649_, 3, v_l_5586_);
lean_ctor_set(v___x_5649_, 2, v_v_5585_);
lean_ctor_set(v___x_5649_, 1, v_k_5584_);
lean_ctor_set(v___x_5649_, 0, v___x_5643_);
v___x_5652_ = v___x_5649_;
goto v_reusejp_5651_;
}
else
{
lean_object* v_reuseFailAlloc_5653_; 
v_reuseFailAlloc_5653_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5653_, 0, v___x_5643_);
lean_ctor_set(v_reuseFailAlloc_5653_, 1, v_k_5584_);
lean_ctor_set(v_reuseFailAlloc_5653_, 2, v_v_5585_);
lean_ctor_set(v_reuseFailAlloc_5653_, 3, v_l_5586_);
lean_ctor_set(v_reuseFailAlloc_5653_, 4, v___x_5647_);
v___x_5652_ = v_reuseFailAlloc_5653_;
goto v_reusejp_5651_;
}
v_reusejp_5651_:
{
return v___x_5652_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5667_; 
v_l_5667_ = lean_ctor_get(v_impl_5580_, 3);
if (lean_obj_tag(v_l_5667_) == 0)
{
lean_object* v_r_5668_; lean_object* v_k_5669_; lean_object* v_v_5670_; lean_object* v___x_5672_; uint8_t v_isShared_5673_; uint8_t v_isSharedCheck_5681_; 
lean_inc_ref(v_l_5667_);
v_r_5668_ = lean_ctor_get(v_impl_5580_, 4);
v_k_5669_ = lean_ctor_get(v_impl_5580_, 1);
v_v_5670_ = lean_ctor_get(v_impl_5580_, 2);
v_isSharedCheck_5681_ = !lean_is_exclusive(v_impl_5580_);
if (v_isSharedCheck_5681_ == 0)
{
lean_object* v_unused_5682_; lean_object* v_unused_5683_; 
v_unused_5682_ = lean_ctor_get(v_impl_5580_, 3);
lean_dec(v_unused_5682_);
v_unused_5683_ = lean_ctor_get(v_impl_5580_, 0);
lean_dec(v_unused_5683_);
v___x_5672_ = v_impl_5580_;
v_isShared_5673_ = v_isSharedCheck_5681_;
goto v_resetjp_5671_;
}
else
{
lean_inc(v_r_5668_);
lean_inc(v_v_5670_);
lean_inc(v_k_5669_);
lean_dec(v_impl_5580_);
v___x_5672_ = lean_box(0);
v_isShared_5673_ = v_isSharedCheck_5681_;
goto v_resetjp_5671_;
}
v_resetjp_5671_:
{
lean_object* v___x_5674_; lean_object* v___x_5676_; 
v___x_5674_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5668_);
if (v_isShared_5673_ == 0)
{
lean_ctor_set(v___x_5672_, 3, v_r_5668_);
lean_ctor_set(v___x_5672_, 2, v_v_5434_);
lean_ctor_set(v___x_5672_, 1, v_k_5433_);
lean_ctor_set(v___x_5672_, 0, v___x_5581_);
v___x_5676_ = v___x_5672_;
goto v_reusejp_5675_;
}
else
{
lean_object* v_reuseFailAlloc_5680_; 
v_reuseFailAlloc_5680_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5680_, 0, v___x_5581_);
lean_ctor_set(v_reuseFailAlloc_5680_, 1, v_k_5433_);
lean_ctor_set(v_reuseFailAlloc_5680_, 2, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5680_, 3, v_r_5668_);
lean_ctor_set(v_reuseFailAlloc_5680_, 4, v_r_5668_);
v___x_5676_ = v_reuseFailAlloc_5680_;
goto v_reusejp_5675_;
}
v_reusejp_5675_:
{
lean_object* v___x_5678_; 
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 4, v___x_5676_);
lean_ctor_set(v___x_5438_, 3, v_l_5667_);
lean_ctor_set(v___x_5438_, 2, v_v_5670_);
lean_ctor_set(v___x_5438_, 1, v_k_5669_);
lean_ctor_set(v___x_5438_, 0, v___x_5674_);
v___x_5678_ = v___x_5438_;
goto v_reusejp_5677_;
}
else
{
lean_object* v_reuseFailAlloc_5679_; 
v_reuseFailAlloc_5679_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5679_, 0, v___x_5674_);
lean_ctor_set(v_reuseFailAlloc_5679_, 1, v_k_5669_);
lean_ctor_set(v_reuseFailAlloc_5679_, 2, v_v_5670_);
lean_ctor_set(v_reuseFailAlloc_5679_, 3, v_l_5667_);
lean_ctor_set(v_reuseFailAlloc_5679_, 4, v___x_5676_);
v___x_5678_ = v_reuseFailAlloc_5679_;
goto v_reusejp_5677_;
}
v_reusejp_5677_:
{
return v___x_5678_;
}
}
}
}
else
{
lean_object* v_r_5684_; 
v_r_5684_ = lean_ctor_get(v_impl_5580_, 4);
lean_inc(v_r_5684_);
if (lean_obj_tag(v_r_5684_) == 0)
{
lean_object* v_k_5685_; lean_object* v_v_5686_; lean_object* v___x_5688_; uint8_t v_isShared_5689_; uint8_t v_isSharedCheck_5709_; 
lean_inc(v_l_5667_);
v_k_5685_ = lean_ctor_get(v_impl_5580_, 1);
v_v_5686_ = lean_ctor_get(v_impl_5580_, 2);
v_isSharedCheck_5709_ = !lean_is_exclusive(v_impl_5580_);
if (v_isSharedCheck_5709_ == 0)
{
lean_object* v_unused_5710_; lean_object* v_unused_5711_; lean_object* v_unused_5712_; 
v_unused_5710_ = lean_ctor_get(v_impl_5580_, 4);
lean_dec(v_unused_5710_);
v_unused_5711_ = lean_ctor_get(v_impl_5580_, 3);
lean_dec(v_unused_5711_);
v_unused_5712_ = lean_ctor_get(v_impl_5580_, 0);
lean_dec(v_unused_5712_);
v___x_5688_ = v_impl_5580_;
v_isShared_5689_ = v_isSharedCheck_5709_;
goto v_resetjp_5687_;
}
else
{
lean_inc(v_v_5686_);
lean_inc(v_k_5685_);
lean_dec(v_impl_5580_);
v___x_5688_ = lean_box(0);
v_isShared_5689_ = v_isSharedCheck_5709_;
goto v_resetjp_5687_;
}
v_resetjp_5687_:
{
lean_object* v_k_5690_; lean_object* v_v_5691_; lean_object* v___x_5693_; uint8_t v_isShared_5694_; uint8_t v_isSharedCheck_5705_; 
v_k_5690_ = lean_ctor_get(v_r_5684_, 1);
v_v_5691_ = lean_ctor_get(v_r_5684_, 2);
v_isSharedCheck_5705_ = !lean_is_exclusive(v_r_5684_);
if (v_isSharedCheck_5705_ == 0)
{
lean_object* v_unused_5706_; lean_object* v_unused_5707_; lean_object* v_unused_5708_; 
v_unused_5706_ = lean_ctor_get(v_r_5684_, 4);
lean_dec(v_unused_5706_);
v_unused_5707_ = lean_ctor_get(v_r_5684_, 3);
lean_dec(v_unused_5707_);
v_unused_5708_ = lean_ctor_get(v_r_5684_, 0);
lean_dec(v_unused_5708_);
v___x_5693_ = v_r_5684_;
v_isShared_5694_ = v_isSharedCheck_5705_;
goto v_resetjp_5692_;
}
else
{
lean_inc(v_v_5691_);
lean_inc(v_k_5690_);
lean_dec(v_r_5684_);
v___x_5693_ = lean_box(0);
v_isShared_5694_ = v_isSharedCheck_5705_;
goto v_resetjp_5692_;
}
v_resetjp_5692_:
{
lean_object* v___x_5695_; lean_object* v___x_5697_; 
v___x_5695_ = lean_unsigned_to_nat(3u);
if (v_isShared_5694_ == 0)
{
lean_ctor_set(v___x_5693_, 4, v_l_5667_);
lean_ctor_set(v___x_5693_, 3, v_l_5667_);
lean_ctor_set(v___x_5693_, 2, v_v_5686_);
lean_ctor_set(v___x_5693_, 1, v_k_5685_);
lean_ctor_set(v___x_5693_, 0, v___x_5581_);
v___x_5697_ = v___x_5693_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5704_; 
v_reuseFailAlloc_5704_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5704_, 0, v___x_5581_);
lean_ctor_set(v_reuseFailAlloc_5704_, 1, v_k_5685_);
lean_ctor_set(v_reuseFailAlloc_5704_, 2, v_v_5686_);
lean_ctor_set(v_reuseFailAlloc_5704_, 3, v_l_5667_);
lean_ctor_set(v_reuseFailAlloc_5704_, 4, v_l_5667_);
v___x_5697_ = v_reuseFailAlloc_5704_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
lean_object* v___x_5699_; 
if (v_isShared_5689_ == 0)
{
lean_ctor_set(v___x_5688_, 4, v_l_5667_);
lean_ctor_set(v___x_5688_, 2, v_v_5434_);
lean_ctor_set(v___x_5688_, 1, v_k_5433_);
lean_ctor_set(v___x_5688_, 0, v___x_5581_);
v___x_5699_ = v___x_5688_;
goto v_reusejp_5698_;
}
else
{
lean_object* v_reuseFailAlloc_5703_; 
v_reuseFailAlloc_5703_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5703_, 0, v___x_5581_);
lean_ctor_set(v_reuseFailAlloc_5703_, 1, v_k_5433_);
lean_ctor_set(v_reuseFailAlloc_5703_, 2, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5703_, 3, v_l_5667_);
lean_ctor_set(v_reuseFailAlloc_5703_, 4, v_l_5667_);
v___x_5699_ = v_reuseFailAlloc_5703_;
goto v_reusejp_5698_;
}
v_reusejp_5698_:
{
lean_object* v___x_5701_; 
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 4, v___x_5699_);
lean_ctor_set(v___x_5438_, 3, v___x_5697_);
lean_ctor_set(v___x_5438_, 2, v_v_5691_);
lean_ctor_set(v___x_5438_, 1, v_k_5690_);
lean_ctor_set(v___x_5438_, 0, v___x_5695_);
v___x_5701_ = v___x_5438_;
goto v_reusejp_5700_;
}
else
{
lean_object* v_reuseFailAlloc_5702_; 
v_reuseFailAlloc_5702_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5702_, 0, v___x_5695_);
lean_ctor_set(v_reuseFailAlloc_5702_, 1, v_k_5690_);
lean_ctor_set(v_reuseFailAlloc_5702_, 2, v_v_5691_);
lean_ctor_set(v_reuseFailAlloc_5702_, 3, v___x_5697_);
lean_ctor_set(v_reuseFailAlloc_5702_, 4, v___x_5699_);
v___x_5701_ = v_reuseFailAlloc_5702_;
goto v_reusejp_5700_;
}
v_reusejp_5700_:
{
return v___x_5701_;
}
}
}
}
}
}
else
{
lean_object* v___x_5713_; lean_object* v___x_5715_; 
v___x_5713_ = lean_unsigned_to_nat(2u);
if (v_isShared_5439_ == 0)
{
lean_ctor_set(v___x_5438_, 4, v_r_5684_);
lean_ctor_set(v___x_5438_, 3, v_impl_5580_);
lean_ctor_set(v___x_5438_, 0, v___x_5713_);
v___x_5715_ = v___x_5438_;
goto v_reusejp_5714_;
}
else
{
lean_object* v_reuseFailAlloc_5716_; 
v_reuseFailAlloc_5716_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5716_, 0, v___x_5713_);
lean_ctor_set(v_reuseFailAlloc_5716_, 1, v_k_5433_);
lean_ctor_set(v_reuseFailAlloc_5716_, 2, v_v_5434_);
lean_ctor_set(v_reuseFailAlloc_5716_, 3, v_impl_5580_);
lean_ctor_set(v_reuseFailAlloc_5716_, 4, v_r_5684_);
v___x_5715_ = v_reuseFailAlloc_5716_;
goto v_reusejp_5714_;
}
v_reusejp_5714_:
{
return v___x_5715_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5718_; lean_object* v___x_5719_; 
v___x_5718_ = lean_unsigned_to_nat(1u);
v___x_5719_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5718_);
lean_ctor_set(v___x_5719_, 1, v_k_5429_);
lean_ctor_set(v___x_5719_, 2, v_v_5430_);
lean_ctor_set(v___x_5719_, 3, v_t_5431_);
lean_ctor_set(v___x_5719_, 4, v_t_5431_);
return v___x_5719_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5720_, lean_object* v_t_5721_){
_start:
{
if (lean_obj_tag(v_t_5721_) == 0)
{
lean_object* v_k_5722_; lean_object* v_l_5723_; lean_object* v_r_5724_; uint8_t v___x_5725_; 
v_k_5722_ = lean_ctor_get(v_t_5721_, 1);
v_l_5723_ = lean_ctor_get(v_t_5721_, 3);
v_r_5724_ = lean_ctor_get(v_t_5721_, 4);
v___x_5725_ = lean_nat_dec_lt(v_k_5722_, v_k_5720_);
if (v___x_5725_ == 0)
{
uint8_t v___x_5726_; 
v___x_5726_ = lean_nat_dec_eq(v_k_5722_, v_k_5720_);
if (v___x_5726_ == 0)
{
v_t_5721_ = v_r_5724_;
goto _start;
}
else
{
return v___x_5726_;
}
}
else
{
v_t_5721_ = v_l_5723_;
goto _start;
}
}
else
{
uint8_t v___x_5729_; 
v___x_5729_ = 0;
return v___x_5729_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5730_, lean_object* v_t_5731_){
_start:
{
uint8_t v_res_5732_; lean_object* v_r_5733_; 
v_res_5732_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5730_, v_t_5731_);
lean_dec(v_t_5731_);
lean_dec(v_k_5730_);
v_r_5733_ = lean_box(v_res_5732_);
return v_r_5733_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5734_, lean_object* v_e_5735_){
_start:
{
lean_object* v_defaultInstances_5736_; lean_object* v_priorities_5737_; lean_object* v___x_5739_; uint8_t v_isShared_5740_; uint8_t v_isSharedCheck_5764_; 
v_defaultInstances_5736_ = lean_ctor_get(v_d_5734_, 0);
v_priorities_5737_ = lean_ctor_get(v_d_5734_, 1);
v_isSharedCheck_5764_ = !lean_is_exclusive(v_d_5734_);
if (v_isSharedCheck_5764_ == 0)
{
v___x_5739_ = v_d_5734_;
v_isShared_5740_ = v_isSharedCheck_5764_;
goto v_resetjp_5738_;
}
else
{
lean_inc(v_priorities_5737_);
lean_inc(v_defaultInstances_5736_);
lean_dec(v_d_5734_);
v___x_5739_ = lean_box(0);
v_isShared_5740_ = v_isSharedCheck_5764_;
goto v_resetjp_5738_;
}
v_resetjp_5738_:
{
lean_object* v_className_5741_; lean_object* v_instanceName_5742_; lean_object* v_priority_5743_; lean_object* v___y_5745_; uint8_t v___x_5761_; 
v_className_5741_ = lean_ctor_get(v_e_5735_, 0);
lean_inc(v_className_5741_);
v_instanceName_5742_ = lean_ctor_get(v_e_5735_, 1);
lean_inc(v_instanceName_5742_);
v_priority_5743_ = lean_ctor_get(v_e_5735_, 2);
lean_inc(v_priority_5743_);
lean_dec_ref(v_e_5735_);
v___x_5761_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5743_, v_priorities_5737_);
if (v___x_5761_ == 0)
{
lean_object* v___x_5762_; lean_object* v___x_5763_; 
v___x_5762_ = lean_box(0);
lean_inc(v_priority_5743_);
v___x_5763_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5743_, v___x_5762_, v_priorities_5737_);
v___y_5745_ = v___x_5763_;
goto v___jp_5744_;
}
else
{
v___y_5745_ = v_priorities_5737_;
goto v___jp_5744_;
}
v___jp_5744_:
{
lean_object* v___x_5746_; 
v___x_5746_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5736_, v_className_5741_);
if (lean_obj_tag(v___x_5746_) == 0)
{
lean_object* v___x_5747_; lean_object* v___x_5748_; lean_object* v___x_5749_; lean_object* v___x_5750_; lean_object* v___x_5752_; 
v___x_5747_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5747_, 0, v_instanceName_5742_);
lean_ctor_set(v___x_5747_, 1, v_priority_5743_);
v___x_5748_ = lean_box(0);
v___x_5749_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5749_, 0, v___x_5747_);
lean_ctor_set(v___x_5749_, 1, v___x_5748_);
v___x_5750_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5741_, v___x_5749_, v_defaultInstances_5736_);
if (v_isShared_5740_ == 0)
{
lean_ctor_set(v___x_5739_, 1, v___y_5745_);
lean_ctor_set(v___x_5739_, 0, v___x_5750_);
v___x_5752_ = v___x_5739_;
goto v_reusejp_5751_;
}
else
{
lean_object* v_reuseFailAlloc_5753_; 
v_reuseFailAlloc_5753_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5753_, 0, v___x_5750_);
lean_ctor_set(v_reuseFailAlloc_5753_, 1, v___y_5745_);
v___x_5752_ = v_reuseFailAlloc_5753_;
goto v_reusejp_5751_;
}
v_reusejp_5751_:
{
return v___x_5752_;
}
}
else
{
lean_object* v_val_5754_; lean_object* v___x_5755_; lean_object* v___x_5756_; lean_object* v___x_5757_; lean_object* v___x_5759_; 
v_val_5754_ = lean_ctor_get(v___x_5746_, 0);
lean_inc(v_val_5754_);
lean_dec_ref_known(v___x_5746_, 1);
v___x_5755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5755_, 0, v_instanceName_5742_);
lean_ctor_set(v___x_5755_, 1, v_priority_5743_);
v___x_5756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5756_, 0, v___x_5755_);
lean_ctor_set(v___x_5756_, 1, v_val_5754_);
v___x_5757_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5741_, v___x_5756_, v_defaultInstances_5736_);
if (v_isShared_5740_ == 0)
{
lean_ctor_set(v___x_5739_, 1, v___y_5745_);
lean_ctor_set(v___x_5739_, 0, v___x_5757_);
v___x_5759_ = v___x_5739_;
goto v_reusejp_5758_;
}
else
{
lean_object* v_reuseFailAlloc_5760_; 
v_reuseFailAlloc_5760_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5760_, 0, v___x_5757_);
lean_ctor_set(v_reuseFailAlloc_5760_, 1, v___y_5745_);
v___x_5759_ = v_reuseFailAlloc_5760_;
goto v_reusejp_5758_;
}
v_reusejp_5758_:
{
return v___x_5759_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5765_, lean_object* v_k_5766_, lean_object* v_t_5767_){
_start:
{
uint8_t v___x_5768_; 
v___x_5768_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5766_, v_t_5767_);
return v___x_5768_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5769_, lean_object* v_k_5770_, lean_object* v_t_5771_){
_start:
{
uint8_t v_res_5772_; lean_object* v_r_5773_; 
v_res_5772_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5769_, v_k_5770_, v_t_5771_);
lean_dec(v_t_5771_);
lean_dec(v_k_5770_);
v_r_5773_ = lean_box(v_res_5772_);
return v_r_5773_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5774_, lean_object* v_k_5775_, lean_object* v_v_5776_, lean_object* v_t_5777_, lean_object* v_hl_5778_){
_start:
{
lean_object* v___x_5779_; 
v___x_5779_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5775_, v_v_5776_, v_t_5777_);
return v___x_5779_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object* v_env_5780_, lean_object* v_as_5781_, size_t v_i_5782_, size_t v_stop_5783_, lean_object* v_b_5784_){
_start:
{
lean_object* v___y_5786_; uint8_t v___x_5790_; 
v___x_5790_ = lean_usize_dec_eq(v_i_5782_, v_stop_5783_);
if (v___x_5790_ == 0)
{
lean_object* v___x_5791_; lean_object* v_instanceName_5792_; uint8_t v___x_5793_; lean_object* v___x_5794_; uint8_t v___x_5795_; 
v___x_5791_ = lean_array_uget_borrowed(v_as_5781_, v_i_5782_);
v_instanceName_5792_ = lean_ctor_get(v___x_5791_, 1);
v___x_5793_ = 1;
lean_inc_ref(v_env_5780_);
v___x_5794_ = l_Lean_Environment_setExporting(v_env_5780_, v___x_5793_);
lean_inc(v_instanceName_5792_);
v___x_5795_ = l_Lean_Environment_contains(v___x_5794_, v_instanceName_5792_, v___x_5790_);
if (v___x_5795_ == 0)
{
v___y_5786_ = v_b_5784_;
goto v___jp_5785_;
}
else
{
lean_object* v___x_5796_; 
lean_inc(v___x_5791_);
v___x_5796_ = lean_array_push(v_b_5784_, v___x_5791_);
v___y_5786_ = v___x_5796_;
goto v___jp_5785_;
}
}
else
{
lean_dec_ref(v_env_5780_);
return v_b_5784_;
}
v___jp_5785_:
{
size_t v___x_5787_; size_t v___x_5788_; 
v___x_5787_ = ((size_t)1ULL);
v___x_5788_ = lean_usize_add(v_i_5782_, v___x_5787_);
v_i_5782_ = v___x_5788_;
v_b_5784_ = v___y_5786_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_5797_, lean_object* v_as_5798_, lean_object* v_i_5799_, lean_object* v_stop_5800_, lean_object* v_b_5801_){
_start:
{
size_t v_i_boxed_5802_; size_t v_stop_boxed_5803_; lean_object* v_res_5804_; 
v_i_boxed_5802_ = lean_unbox_usize(v_i_5799_);
lean_dec(v_i_5799_);
v_stop_boxed_5803_ = lean_unbox_usize(v_stop_5800_);
lean_dec(v_stop_5800_);
v_res_5804_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5797_, v_as_5798_, v_i_boxed_5802_, v_stop_boxed_5803_, v_b_5801_);
lean_dec_ref(v_as_5798_);
return v_res_5804_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_env_5807_, lean_object* v_x_5808_, lean_object* v_entries_5809_){
_start:
{
lean_object* v_all_5810_; lean_object* v___x_5811_; lean_object* v___x_5812_; lean_object* v___x_5813_; uint8_t v___x_5814_; 
v_all_5810_ = lean_array_mk(v_entries_5809_);
v___x_5811_ = lean_unsigned_to_nat(0u);
v___x_5812_ = lean_array_get_size(v_all_5810_);
v___x_5813_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5814_ = lean_nat_dec_lt(v___x_5811_, v___x_5812_);
if (v___x_5814_ == 0)
{
lean_object* v___x_5815_; 
lean_dec_ref(v_env_5807_);
v___x_5815_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5815_, 0, v___x_5813_);
lean_ctor_set(v___x_5815_, 1, v___x_5813_);
lean_ctor_set(v___x_5815_, 2, v_all_5810_);
return v___x_5815_;
}
else
{
size_t v___x_5816_; size_t v___x_5817_; lean_object* v___x_5818_; lean_object* v___x_5819_; 
v___x_5816_ = ((size_t)0ULL);
v___x_5817_ = lean_usize_of_nat(v___x_5812_);
v___x_5818_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5807_, v_all_5810_, v___x_5816_, v___x_5817_, v___x_5813_);
lean_inc_ref(v___x_5818_);
v___x_5819_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5819_, 0, v___x_5818_);
lean_ctor_set(v___x_5819_, 1, v___x_5818_);
lean_ctor_set(v___x_5819_, 2, v_all_5810_);
return v___x_5819_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5820_, lean_object* v_x_5821_, lean_object* v_entries_5822_){
_start:
{
lean_object* v_res_5823_; 
v_res_5823_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5820_, v_x_5821_, v_entries_5822_);
lean_dec_ref(v_x_5821_);
return v_res_5823_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5824_){
_start:
{
lean_object* v___x_5825_; 
v___x_5825_ = lean_array_mk(v_es_5824_);
return v___x_5825_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5826_, size_t v_i_5827_, size_t v_stop_5828_, lean_object* v_b_5829_){
_start:
{
uint8_t v___x_5830_; 
v___x_5830_ = lean_usize_dec_eq(v_i_5827_, v_stop_5828_);
if (v___x_5830_ == 0)
{
lean_object* v___x_5831_; lean_object* v___x_5832_; size_t v___x_5833_; size_t v___x_5834_; 
v___x_5831_ = lean_array_uget_borrowed(v_as_5826_, v_i_5827_);
lean_inc(v___x_5831_);
v___x_5832_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5829_, v___x_5831_);
v___x_5833_ = ((size_t)1ULL);
v___x_5834_ = lean_usize_add(v_i_5827_, v___x_5833_);
v_i_5827_ = v___x_5834_;
v_b_5829_ = v___x_5832_;
goto _start;
}
else
{
return v_b_5829_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5836_, lean_object* v_i_5837_, lean_object* v_stop_5838_, lean_object* v_b_5839_){
_start:
{
size_t v_i_boxed_5840_; size_t v_stop_boxed_5841_; lean_object* v_res_5842_; 
v_i_boxed_5840_ = lean_unbox_usize(v_i_5837_);
lean_dec(v_i_5837_);
v_stop_boxed_5841_ = lean_unbox_usize(v_stop_5838_);
lean_dec(v_stop_5838_);
v_res_5842_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5836_, v_i_boxed_5840_, v_stop_boxed_5841_, v_b_5839_);
lean_dec_ref(v_as_5836_);
return v_res_5842_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5843_, size_t v_i_5844_, size_t v_stop_5845_, lean_object* v_b_5846_){
_start:
{
lean_object* v___y_5848_; uint8_t v___x_5852_; 
v___x_5852_ = lean_usize_dec_eq(v_i_5844_, v_stop_5845_);
if (v___x_5852_ == 0)
{
lean_object* v___x_5853_; lean_object* v___x_5854_; lean_object* v___x_5855_; uint8_t v___x_5856_; 
v___x_5853_ = lean_array_uget_borrowed(v_as_5843_, v_i_5844_);
v___x_5854_ = lean_unsigned_to_nat(0u);
v___x_5855_ = lean_array_get_size(v___x_5853_);
v___x_5856_ = lean_nat_dec_lt(v___x_5854_, v___x_5855_);
if (v___x_5856_ == 0)
{
v___y_5848_ = v_b_5846_;
goto v___jp_5847_;
}
else
{
size_t v___x_5857_; size_t v___x_5858_; lean_object* v___x_5859_; 
v___x_5857_ = ((size_t)0ULL);
v___x_5858_ = lean_usize_of_nat(v___x_5855_);
v___x_5859_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5853_, v___x_5857_, v___x_5858_, v_b_5846_);
v___y_5848_ = v___x_5859_;
goto v___jp_5847_;
}
}
else
{
return v_b_5846_;
}
v___jp_5847_:
{
size_t v___x_5849_; size_t v___x_5850_; 
v___x_5849_ = ((size_t)1ULL);
v___x_5850_ = lean_usize_add(v_i_5844_, v___x_5849_);
v_i_5844_ = v___x_5850_;
v_b_5846_ = v___y_5848_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5860_, lean_object* v_i_5861_, lean_object* v_stop_5862_, lean_object* v_b_5863_){
_start:
{
size_t v_i_boxed_5864_; size_t v_stop_boxed_5865_; lean_object* v_res_5866_; 
v_i_boxed_5864_ = lean_unbox_usize(v_i_5861_);
lean_dec(v_i_5861_);
v_stop_boxed_5865_ = lean_unbox_usize(v_stop_5862_);
lean_dec(v_stop_5862_);
v_res_5866_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5860_, v_i_boxed_5864_, v_stop_boxed_5865_, v_b_5863_);
lean_dec_ref(v_as_5860_);
return v_res_5866_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_5867_, lean_object* v_as_5868_){
_start:
{
lean_object* v___x_5869_; lean_object* v___x_5870_; uint8_t v___x_5871_; 
v___x_5869_ = lean_unsigned_to_nat(0u);
v___x_5870_ = lean_array_get_size(v_as_5868_);
v___x_5871_ = lean_nat_dec_lt(v___x_5869_, v___x_5870_);
if (v___x_5871_ == 0)
{
return v_initState_5867_;
}
else
{
size_t v___x_5872_; size_t v___x_5873_; lean_object* v___x_5874_; 
v___x_5872_ = ((size_t)0ULL);
v___x_5873_ = lean_usize_of_nat(v___x_5870_);
v___x_5874_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5868_, v___x_5872_, v___x_5873_, v_initState_5867_);
return v___x_5874_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_5875_, lean_object* v_as_5876_){
_start:
{
lean_object* v_res_5877_; 
v_res_5877_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_5875_, v_as_5876_);
lean_dec_ref(v_as_5876_);
return v_res_5877_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5878_){
_start:
{
lean_object* v___x_5879_; lean_object* v___x_5880_; 
v___x_5879_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5880_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_5879_, v_es_5878_);
return v___x_5880_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_5881_){
_start:
{
lean_object* v_res_5882_; 
v_res_5882_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_5881_);
lean_dec_ref(v_es_5881_);
return v_res_5882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5904_; lean_object* v___x_5905_; 
v___x_5904_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5905_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5904_);
return v___x_5905_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_5906_){
_start:
{
lean_object* v_res_5907_; 
v_res_5907_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_5907_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5908_, lean_object* v___y_5909_, lean_object* v___y_5910_){
_start:
{
lean_object* v___x_5912_; lean_object* v_nextMacroScope_5913_; lean_object* v_ngen_5914_; lean_object* v_auxDeclNGen_5915_; lean_object* v_traceState_5916_; lean_object* v_recordedDeps_5917_; lean_object* v_messages_5918_; lean_object* v_infoState_5919_; lean_object* v_snapshotTasks_5920_; lean_object* v___x_5922_; uint8_t v_isShared_5923_; uint8_t v_isSharedCheck_5946_; 
v___x_5912_ = lean_st_ref_take(v___y_5910_);
v_nextMacroScope_5913_ = lean_ctor_get(v___x_5912_, 1);
v_ngen_5914_ = lean_ctor_get(v___x_5912_, 2);
v_auxDeclNGen_5915_ = lean_ctor_get(v___x_5912_, 3);
v_traceState_5916_ = lean_ctor_get(v___x_5912_, 4);
v_recordedDeps_5917_ = lean_ctor_get(v___x_5912_, 6);
v_messages_5918_ = lean_ctor_get(v___x_5912_, 7);
v_infoState_5919_ = lean_ctor_get(v___x_5912_, 8);
v_snapshotTasks_5920_ = lean_ctor_get(v___x_5912_, 9);
v_isSharedCheck_5946_ = !lean_is_exclusive(v___x_5912_);
if (v_isSharedCheck_5946_ == 0)
{
lean_object* v_unused_5947_; lean_object* v_unused_5948_; 
v_unused_5947_ = lean_ctor_get(v___x_5912_, 5);
lean_dec(v_unused_5947_);
v_unused_5948_ = lean_ctor_get(v___x_5912_, 0);
lean_dec(v_unused_5948_);
v___x_5922_ = v___x_5912_;
v_isShared_5923_ = v_isSharedCheck_5946_;
goto v_resetjp_5921_;
}
else
{
lean_inc(v_snapshotTasks_5920_);
lean_inc(v_infoState_5919_);
lean_inc(v_messages_5918_);
lean_inc(v_recordedDeps_5917_);
lean_inc(v_traceState_5916_);
lean_inc(v_auxDeclNGen_5915_);
lean_inc(v_ngen_5914_);
lean_inc(v_nextMacroScope_5913_);
lean_dec(v___x_5912_);
v___x_5922_ = lean_box(0);
v_isShared_5923_ = v_isSharedCheck_5946_;
goto v_resetjp_5921_;
}
v_resetjp_5921_:
{
lean_object* v___x_5924_; lean_object* v___x_5926_; 
v___x_5924_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_5923_ == 0)
{
lean_ctor_set(v___x_5922_, 5, v___x_5924_);
lean_ctor_set(v___x_5922_, 0, v_env_5908_);
v___x_5926_ = v___x_5922_;
goto v_reusejp_5925_;
}
else
{
lean_object* v_reuseFailAlloc_5945_; 
v_reuseFailAlloc_5945_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5945_, 0, v_env_5908_);
lean_ctor_set(v_reuseFailAlloc_5945_, 1, v_nextMacroScope_5913_);
lean_ctor_set(v_reuseFailAlloc_5945_, 2, v_ngen_5914_);
lean_ctor_set(v_reuseFailAlloc_5945_, 3, v_auxDeclNGen_5915_);
lean_ctor_set(v_reuseFailAlloc_5945_, 4, v_traceState_5916_);
lean_ctor_set(v_reuseFailAlloc_5945_, 5, v___x_5924_);
lean_ctor_set(v_reuseFailAlloc_5945_, 6, v_recordedDeps_5917_);
lean_ctor_set(v_reuseFailAlloc_5945_, 7, v_messages_5918_);
lean_ctor_set(v_reuseFailAlloc_5945_, 8, v_infoState_5919_);
lean_ctor_set(v_reuseFailAlloc_5945_, 9, v_snapshotTasks_5920_);
v___x_5926_ = v_reuseFailAlloc_5945_;
goto v_reusejp_5925_;
}
v_reusejp_5925_:
{
lean_object* v___x_5927_; lean_object* v___x_5928_; lean_object* v_mctx_5929_; lean_object* v_zetaDeltaFVarIds_5930_; lean_object* v_postponed_5931_; lean_object* v_diag_5932_; lean_object* v___x_5934_; uint8_t v_isShared_5935_; uint8_t v_isSharedCheck_5943_; 
v___x_5927_ = lean_st_ref_put(v___y_5910_, v___x_5926_);
v___x_5928_ = lean_st_ref_take(v___y_5909_);
v_mctx_5929_ = lean_ctor_get(v___x_5928_, 0);
v_zetaDeltaFVarIds_5930_ = lean_ctor_get(v___x_5928_, 2);
v_postponed_5931_ = lean_ctor_get(v___x_5928_, 3);
v_diag_5932_ = lean_ctor_get(v___x_5928_, 4);
v_isSharedCheck_5943_ = !lean_is_exclusive(v___x_5928_);
if (v_isSharedCheck_5943_ == 0)
{
lean_object* v_unused_5944_; 
v_unused_5944_ = lean_ctor_get(v___x_5928_, 1);
lean_dec(v_unused_5944_);
v___x_5934_ = v___x_5928_;
v_isShared_5935_ = v_isSharedCheck_5943_;
goto v_resetjp_5933_;
}
else
{
lean_inc(v_diag_5932_);
lean_inc(v_postponed_5931_);
lean_inc(v_zetaDeltaFVarIds_5930_);
lean_inc(v_mctx_5929_);
lean_dec(v___x_5928_);
v___x_5934_ = lean_box(0);
v_isShared_5935_ = v_isSharedCheck_5943_;
goto v_resetjp_5933_;
}
v_resetjp_5933_:
{
lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5939_; 
v___x_5936_ = lean_box(0);
v___x_5937_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5935_ == 0)
{
lean_ctor_set(v___x_5934_, 1, v___x_5937_);
v___x_5939_ = v___x_5934_;
goto v_reusejp_5938_;
}
else
{
lean_object* v_reuseFailAlloc_5942_; 
v_reuseFailAlloc_5942_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5942_, 0, v_mctx_5929_);
lean_ctor_set(v_reuseFailAlloc_5942_, 1, v___x_5937_);
lean_ctor_set(v_reuseFailAlloc_5942_, 2, v_zetaDeltaFVarIds_5930_);
lean_ctor_set(v_reuseFailAlloc_5942_, 3, v_postponed_5931_);
lean_ctor_set(v_reuseFailAlloc_5942_, 4, v_diag_5932_);
v___x_5939_ = v_reuseFailAlloc_5942_;
goto v_reusejp_5938_;
}
v_reusejp_5938_:
{
lean_object* v___x_5940_; lean_object* v___x_5941_; 
v___x_5940_ = lean_st_ref_put(v___y_5909_, v___x_5939_);
v___x_5941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5941_, 0, v___x_5936_);
return v___x_5941_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5949_, lean_object* v___y_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_){
_start:
{
lean_object* v_res_5953_; 
v_res_5953_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5949_, v___y_5950_, v___y_5951_);
lean_dec(v___y_5951_);
lean_dec(v___y_5950_);
return v_res_5953_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5954_, lean_object* v___y_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_){
_start:
{
lean_object* v___x_5960_; 
v___x_5960_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5954_, v___y_5956_, v___y_5958_);
return v___x_5960_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_){
_start:
{
lean_object* v_res_5967_; 
v_res_5967_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5961_, v___y_5962_, v___y_5963_, v___y_5964_, v___y_5965_);
lean_dec(v___y_5965_);
lean_dec_ref(v___y_5964_);
lean_dec(v___y_5963_);
lean_dec_ref(v___y_5962_);
return v_res_5967_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_addEntryFn_5968_, lean_object* v___x_5969_, lean_object* v_s_5970_){
_start:
{
lean_object* v_importedEntries_5971_; lean_object* v_state_5972_; lean_object* v___x_5974_; uint8_t v_isShared_5975_; uint8_t v_isSharedCheck_5980_; 
v_importedEntries_5971_ = lean_ctor_get(v_s_5970_, 0);
v_state_5972_ = lean_ctor_get(v_s_5970_, 1);
v_isSharedCheck_5980_ = !lean_is_exclusive(v_s_5970_);
if (v_isSharedCheck_5980_ == 0)
{
v___x_5974_ = v_s_5970_;
v_isShared_5975_ = v_isSharedCheck_5980_;
goto v_resetjp_5973_;
}
else
{
lean_inc(v_state_5972_);
lean_inc(v_importedEntries_5971_);
lean_dec(v_s_5970_);
v___x_5974_ = lean_box(0);
v_isShared_5975_ = v_isSharedCheck_5980_;
goto v_resetjp_5973_;
}
v_resetjp_5973_:
{
lean_object* v_state_5976_; lean_object* v___x_5978_; 
v_state_5976_ = lean_apply_2(v_addEntryFn_5968_, v_state_5972_, v___x_5969_);
if (v_isShared_5975_ == 0)
{
lean_ctor_set(v___x_5974_, 1, v_state_5976_);
v___x_5978_ = v___x_5974_;
goto v_reusejp_5977_;
}
else
{
lean_object* v_reuseFailAlloc_5979_; 
v_reuseFailAlloc_5979_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5979_, 0, v_importedEntries_5971_);
lean_ctor_set(v_reuseFailAlloc_5979_, 1, v_state_5976_);
v___x_5978_ = v_reuseFailAlloc_5979_;
goto v_reusejp_5977_;
}
v_reusejp_5977_:
{
return v___x_5978_;
}
}
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; 
v___x_5982_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__0));
v___x_5983_ = l_Lean_stringToMessageData(v___x_5982_);
return v___x_5983_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__3(void){
_start:
{
lean_object* v___x_5985_; lean_object* v___x_5986_; 
v___x_5985_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__2));
v___x_5986_ = l_Lean_stringToMessageData(v___x_5985_);
return v___x_5986_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__5(void){
_start:
{
lean_object* v___x_5988_; lean_object* v___x_5989_; 
v___x_5988_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__4));
v___x_5989_ = l_Lean_stringToMessageData(v___x_5988_);
return v___x_5989_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__7(void){
_start:
{
lean_object* v___x_5991_; lean_object* v___x_5992_; 
v___x_5991_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__6));
v___x_5992_ = l_Lean_stringToMessageData(v___x_5991_);
return v___x_5992_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__9(void){
_start:
{
lean_object* v___x_5994_; lean_object* v___x_5995_; 
v___x_5994_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__8));
v___x_5995_ = l_Lean_stringToMessageData(v___x_5994_);
return v___x_5995_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__1(lean_object* v_declName_5996_, lean_object* v_prio_5997_, lean_object* v_x_5998_, lean_object* v_type_5999_, lean_object* v___y_6000_, lean_object* v___y_6001_, lean_object* v___y_6002_, lean_object* v___y_6003_){
_start:
{
lean_object* v___x_6005_; 
v___x_6005_ = l_Lean_Expr_getAppFn(v_type_5999_);
if (lean_obj_tag(v___x_6005_) == 4)
{
lean_object* v_declName_6006_; lean_object* v___y_6008_; lean_object* v___y_6009_; lean_object* v___y_6010_; lean_object* v___y_6011_; lean_object* v___x_6028_; lean_object* v_env_6029_; uint8_t v___x_6030_; 
v_declName_6006_ = lean_ctor_get(v___x_6005_, 0);
lean_inc(v_declName_6006_);
lean_dec_ref_known(v___x_6005_, 2);
v___x_6028_ = lean_st_ref_get(v___y_6003_);
v_env_6029_ = lean_ctor_get(v___x_6028_, 0);
lean_inc_ref(v_env_6029_);
lean_dec(v___x_6028_);
v___x_6030_ = l_Lean_isClass(v_env_6029_, v_declName_6006_);
if (v___x_6030_ == 0)
{
lean_object* v___x_6031_; lean_object* v___x_6032_; lean_object* v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; 
lean_dec(v_prio_5997_);
v___x_6031_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__1, &l_Lean_Meta_addDefaultInstance___lam__1___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__1);
v___x_6032_ = l_Lean_MessageData_ofConstName(v_declName_5996_, v___x_6030_);
v___x_6033_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6033_, 0, v___x_6031_);
lean_ctor_set(v___x_6033_, 1, v___x_6032_);
v___x_6034_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__3, &l_Lean_Meta_addDefaultInstance___lam__1___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__3);
v___x_6035_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6035_, 0, v___x_6033_);
lean_ctor_set(v___x_6035_, 1, v___x_6034_);
lean_inc(v_declName_6006_);
v___x_6036_ = l_Lean_MessageData_ofName(v_declName_6006_);
v___x_6037_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6037_, 0, v___x_6035_);
lean_ctor_set(v___x_6037_, 1, v___x_6036_);
v___x_6038_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__5, &l_Lean_Meta_addDefaultInstance___lam__1___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__5);
v___x_6039_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6039_, 0, v___x_6037_);
lean_ctor_set(v___x_6039_, 1, v___x_6038_);
v___x_6040_ = l_Lean_MessageData_ofConstName(v_declName_6006_, v___x_6030_);
v___x_6041_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6041_, 0, v___x_6039_);
lean_ctor_set(v___x_6041_, 1, v___x_6040_);
v___x_6042_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__7, &l_Lean_Meta_addDefaultInstance___lam__1___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__7);
v___x_6043_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6043_, 0, v___x_6041_);
lean_ctor_set(v___x_6043_, 1, v___x_6042_);
v___x_6044_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6043_, v___y_6000_, v___y_6001_, v___y_6002_, v___y_6003_);
return v___x_6044_;
}
else
{
v___y_6008_ = v___y_6000_;
v___y_6009_ = v___y_6001_;
v___y_6010_ = v___y_6002_;
v___y_6011_ = v___y_6003_;
goto v___jp_6007_;
}
v___jp_6007_:
{
lean_object* v___x_6012_; lean_object* v_env_6013_; lean_object* v___x_6014_; lean_object* v_toEnvExtension_6015_; lean_object* v_addEntryFn_6016_; lean_object* v_asyncMode_6017_; uint8_t v_logWrites_6018_; lean_object* v___x_6019_; lean_object* v___f_6020_; lean_object* v___x_6021_; uint8_t v___x_6022_; 
v___x_6012_ = lean_st_ref_get(v___y_6011_);
v_env_6013_ = lean_ctor_get(v___x_6012_, 0);
lean_inc_ref(v_env_6013_);
lean_dec(v___x_6012_);
v___x_6014_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6015_ = lean_ctor_get(v___x_6014_, 0);
v_addEntryFn_6016_ = lean_ctor_get(v___x_6014_, 3);
v_asyncMode_6017_ = lean_ctor_get(v_toEnvExtension_6015_, 2);
v_logWrites_6018_ = lean_ctor_get_uint8(v_toEnvExtension_6015_, sizeof(void*)*6);
v___x_6019_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6019_, 0, v_declName_6006_);
lean_ctor_set(v___x_6019_, 1, v_declName_5996_);
lean_ctor_set(v___x_6019_, 2, v_prio_5997_);
lean_inc(v_addEntryFn_6016_);
v___f_6020_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0), 3, 2);
lean_closure_set(v___f_6020_, 0, v_addEntryFn_6016_);
lean_closure_set(v___f_6020_, 1, v___x_6019_);
v___x_6021_ = lean_box(0);
v___x_6022_ = 1;
if (v_logWrites_6018_ == 0)
{
lean_object* v___x_6023_; lean_object* v___x_6024_; 
lean_inc_ref(v_toEnvExtension_6015_);
v___x_6023_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_6015_, v_env_6013_, v___f_6020_, v_asyncMode_6017_, v___x_6021_, v___x_6022_);
v___x_6024_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_6023_, v___y_6009_, v___y_6011_);
return v___x_6024_;
}
else
{
lean_object* v___x_6025_; lean_object* v___x_6026_; lean_object* v___x_6027_; 
lean_inc_ref_n(v_toEnvExtension_6015_, 2);
v___x_6025_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_6015_, v_env_6013_);
lean_dec_ref(v_env_6013_);
v___x_6026_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_6015_, v___x_6025_, v___f_6020_, v_asyncMode_6017_, v___x_6021_, v___x_6022_);
v___x_6027_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_6026_, v___y_6009_, v___y_6011_);
return v___x_6027_;
}
}
}
else
{
lean_object* v___x_6045_; uint8_t v___x_6046_; lean_object* v___x_6047_; lean_object* v___x_6048_; lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6051_; 
lean_dec_ref(v___x_6005_);
lean_dec(v_prio_5997_);
v___x_6045_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__1, &l_Lean_Meta_addDefaultInstance___lam__1___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__1);
v___x_6046_ = 0;
v___x_6047_ = l_Lean_MessageData_ofConstName(v_declName_5996_, v___x_6046_);
v___x_6048_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6048_, 0, v___x_6045_);
lean_ctor_set(v___x_6048_, 1, v___x_6047_);
v___x_6049_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__9, &l_Lean_Meta_addDefaultInstance___lam__1___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__9);
v___x_6050_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6050_, 0, v___x_6048_);
lean_ctor_set(v___x_6050_, 1, v___x_6049_);
v___x_6051_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6050_, v___y_6000_, v___y_6001_, v___y_6002_, v___y_6003_);
return v___x_6051_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__1___boxed(lean_object* v_declName_6052_, lean_object* v_prio_6053_, lean_object* v_x_6054_, lean_object* v_type_6055_, lean_object* v___y_6056_, lean_object* v___y_6057_, lean_object* v___y_6058_, lean_object* v___y_6059_, lean_object* v___y_6060_){
_start:
{
lean_object* v_res_6061_; 
v_res_6061_ = l_Lean_Meta_addDefaultInstance___lam__1(v_declName_6052_, v_prio_6053_, v_x_6054_, v_type_6055_, v___y_6056_, v___y_6057_, v___y_6058_, v___y_6059_);
lean_dec(v___y_6059_);
lean_dec_ref(v___y_6058_);
lean_dec(v___y_6057_);
lean_dec_ref(v___y_6056_);
lean_dec_ref(v_type_6055_);
lean_dec_ref(v_x_6054_);
return v_res_6061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_6062_, lean_object* v_prio_6063_, lean_object* v_a_6064_, lean_object* v_a_6065_, lean_object* v_a_6066_, lean_object* v_a_6067_){
_start:
{
lean_object* v___f_6069_; lean_object* v___x_6070_; lean_object* v_env_6071_; uint8_t v___x_6072_; lean_object* v___x_6073_; 
lean_inc_n(v_declName_6062_, 2);
v___f_6069_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__1___boxed), 9, 2);
lean_closure_set(v___f_6069_, 0, v_declName_6062_);
lean_closure_set(v___f_6069_, 1, v_prio_6063_);
v___x_6070_ = lean_st_ref_get(v_a_6067_);
v_env_6071_ = lean_ctor_get(v___x_6070_, 0);
lean_inc_ref(v_env_6071_);
lean_dec(v___x_6070_);
v___x_6072_ = 0;
v___x_6073_ = l_Lean_Environment_find_x3f(v_env_6071_, v_declName_6062_, v___x_6072_);
if (lean_obj_tag(v___x_6073_) == 0)
{
lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6076_; lean_object* v___x_6077_; lean_object* v___x_6078_; lean_object* v___x_6079_; 
lean_dec_ref(v___f_6069_);
v___x_6074_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_6075_ = l_Lean_MessageData_ofConstName(v_declName_6062_, v___x_6072_);
v___x_6076_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6076_, 0, v___x_6074_);
lean_ctor_set(v___x_6076_, 1, v___x_6075_);
v___x_6077_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_6078_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6078_, 0, v___x_6076_);
lean_ctor_set(v___x_6078_, 1, v___x_6077_);
v___x_6079_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6078_, v_a_6064_, v_a_6065_, v_a_6066_, v_a_6067_);
return v___x_6079_;
}
else
{
lean_object* v_val_6080_; lean_object* v___x_6081_; lean_object* v___x_6082_; 
lean_dec(v_declName_6062_);
v_val_6080_ = lean_ctor_get(v___x_6073_, 0);
lean_inc(v_val_6080_);
lean_dec_ref_known(v___x_6073_, 1);
v___x_6081_ = l_Lean_ConstantInfo_type(v_val_6080_);
lean_dec(v_val_6080_);
v___x_6082_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_6081_, v___f_6069_, v___x_6072_, v___x_6072_, v_a_6064_, v_a_6065_, v_a_6066_, v_a_6067_);
return v___x_6082_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_6083_, lean_object* v_prio_6084_, lean_object* v_a_6085_, lean_object* v_a_6086_, lean_object* v_a_6087_, lean_object* v_a_6088_, lean_object* v_a_6089_){
_start:
{
lean_object* v_res_6090_; 
v_res_6090_ = l_Lean_Meta_addDefaultInstance(v_declName_6083_, v_prio_6084_, v_a_6085_, v_a_6086_, v_a_6087_, v_a_6088_);
lean_dec(v_a_6088_);
lean_dec_ref(v_a_6087_);
lean_dec(v_a_6086_);
lean_dec_ref(v_a_6085_);
return v_res_6090_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6092_; lean_object* v___x_6093_; 
v___x_6092_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_6093_ = l_Lean_stringToMessageData(v___x_6092_);
return v___x_6093_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_6095_; lean_object* v___x_6096_; 
v___x_6095_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_6096_ = l_Lean_stringToMessageData(v___x_6095_);
return v___x_6096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_6100_, uint8_t v_kind_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_){
_start:
{
lean_object* v___x_6105_; lean_object* v___x_6106_; lean_object* v___x_6107_; lean_object* v___x_6108_; lean_object* v___x_6109_; lean_object* v___y_6111_; 
v___x_6105_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_6106_ = l_Lean_MessageData_ofName(v_name_6100_);
v___x_6107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6107_, 0, v___x_6105_);
lean_ctor_set(v___x_6107_, 1, v___x_6106_);
v___x_6108_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_6109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6109_, 0, v___x_6107_);
lean_ctor_set(v___x_6109_, 1, v___x_6108_);
switch(v_kind_6101_)
{
case 0:
{
lean_object* v___x_6118_; 
v___x_6118_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_6111_ = v___x_6118_;
goto v___jp_6110_;
}
case 1:
{
lean_object* v___x_6119_; 
v___x_6119_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_6111_ = v___x_6119_;
goto v___jp_6110_;
}
default: 
{
lean_object* v___x_6120_; 
v___x_6120_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_6111_ = v___x_6120_;
goto v___jp_6110_;
}
}
v___jp_6110_:
{
lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; 
lean_inc_ref(v___y_6111_);
v___x_6112_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6112_, 0, v___y_6111_);
v___x_6113_ = l_Lean_MessageData_ofFormat(v___x_6112_);
v___x_6114_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6114_, 0, v___x_6109_);
lean_ctor_set(v___x_6114_, 1, v___x_6113_);
v___x_6115_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_6116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6114_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
v___x_6117_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6116_, v___y_6102_, v___y_6103_);
return v___x_6117_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_6121_, lean_object* v_kind_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_){
_start:
{
uint8_t v_kind_boxed_6126_; lean_object* v_res_6127_; 
v_kind_boxed_6126_ = lean_unbox(v_kind_6122_);
v_res_6127_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6121_, v_kind_boxed_6126_, v___y_6123_, v___y_6124_);
lean_dec(v___y_6124_);
lean_dec_ref(v___y_6123_);
return v_res_6127_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6128_, lean_object* v___x_6129_, lean_object* v___x_6130_, lean_object* v_declName_6131_, lean_object* v_stx_6132_, uint8_t v_kind_6133_, lean_object* v___y_6134_, lean_object* v___y_6135_){
_start:
{
lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; 
v___x_6137_ = lean_unsigned_to_nat(1u);
v___x_6138_ = l_Lean_Syntax_getArg(v_stx_6132_, v___x_6137_);
v___x_6139_ = l_Lean_getAttrParamOptPrio(v___x_6138_, v___y_6134_, v___y_6135_);
if (lean_obj_tag(v___x_6139_) == 0)
{
lean_object* v_a_6140_; lean_object* v___y_6142_; lean_object* v___y_6143_; uint8_t v___x_6175_; uint8_t v___x_6176_; 
v_a_6140_ = lean_ctor_get(v___x_6139_, 0);
lean_inc(v_a_6140_);
lean_dec_ref_known(v___x_6139_, 1);
v___x_6175_ = 0;
v___x_6176_ = l_Lean_instBEqAttributeKind_beq(v_kind_6133_, v___x_6175_);
if (v___x_6176_ == 0)
{
lean_object* v___x_6177_; 
lean_dec(v_a_6140_);
lean_dec(v_declName_6131_);
lean_dec(v___x_6129_);
lean_dec(v___x_6128_);
v___x_6177_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_6130_, v_kind_6133_, v___y_6134_, v___y_6135_);
return v___x_6177_;
}
else
{
lean_dec(v___x_6130_);
v___y_6142_ = v___y_6134_;
v___y_6143_ = v___y_6135_;
goto v___jp_6141_;
}
v___jp_6141_:
{
uint8_t v___x_6144_; uint8_t v___x_6145_; lean_object* v___x_6146_; lean_object* v___x_6147_; lean_object* v___x_6148_; lean_object* v___x_6149_; lean_object* v___x_6150_; size_t v___x_6151_; lean_object* v___x_6152_; lean_object* v___x_6153_; lean_object* v___x_6154_; lean_object* v___x_6155_; lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; 
v___x_6144_ = 0;
v___x_6145_ = 1;
v___x_6146_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6147_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6148_ = lean_unsigned_to_nat(32u);
v___x_6149_ = lean_mk_empty_array_with_capacity(v___x_6148_);
v___x_6150_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_6151_ = ((size_t)5ULL);
lean_inc_n(v___x_6128_, 6);
v___x_6152_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6152_, 0, v___x_6150_);
lean_ctor_set(v___x_6152_, 1, v___x_6149_);
lean_ctor_set(v___x_6152_, 2, v___x_6128_);
lean_ctor_set(v___x_6152_, 3, v___x_6128_);
lean_ctor_set_usize(v___x_6152_, 4, v___x_6151_);
v___x_6153_ = lean_box(1);
lean_inc_ref(v___x_6152_);
v___x_6154_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6154_, 0, v___x_6147_);
lean_ctor_set(v___x_6154_, 1, v___x_6152_);
lean_ctor_set(v___x_6154_, 2, v___x_6153_);
v___x_6155_ = lean_mk_empty_array_with_capacity(v___x_6128_);
v___x_6156_ = lean_box(0);
lean_inc(v___x_6129_);
v___x_6157_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6157_, 0, v___x_6146_);
lean_ctor_set(v___x_6157_, 1, v___x_6129_);
lean_ctor_set(v___x_6157_, 2, v___x_6154_);
lean_ctor_set(v___x_6157_, 3, v___x_6155_);
lean_ctor_set(v___x_6157_, 4, v___x_6156_);
lean_ctor_set(v___x_6157_, 5, v___x_6128_);
lean_ctor_set(v___x_6157_, 6, v___x_6156_);
lean_ctor_set_uint8(v___x_6157_, sizeof(void*)*7, v___x_6144_);
lean_ctor_set_uint8(v___x_6157_, sizeof(void*)*7 + 1, v___x_6144_);
lean_ctor_set_uint8(v___x_6157_, sizeof(void*)*7 + 2, v___x_6144_);
lean_ctor_set_uint8(v___x_6157_, sizeof(void*)*7 + 3, v___x_6145_);
v___x_6158_ = l_Lean_instInhabitedSynthNormMemoSlot_default;
v___x_6159_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6159_, 0, v___x_6128_);
lean_ctor_set(v___x_6159_, 1, v___x_6128_);
lean_ctor_set(v___x_6159_, 2, v___x_6128_);
lean_ctor_set(v___x_6159_, 3, v___x_6128_);
lean_ctor_set(v___x_6159_, 4, v___x_6147_);
lean_ctor_set(v___x_6159_, 5, v___x_6147_);
lean_ctor_set(v___x_6159_, 6, v___x_6147_);
lean_ctor_set(v___x_6159_, 7, v___x_6147_);
lean_ctor_set(v___x_6159_, 8, v___x_6147_);
lean_ctor_set(v___x_6159_, 9, v___x_6147_);
lean_ctor_set(v___x_6159_, 10, v___x_6158_);
v___x_6160_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6161_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6162_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6162_, 0, v___x_6159_);
lean_ctor_set(v___x_6162_, 1, v___x_6160_);
lean_ctor_set(v___x_6162_, 2, v___x_6129_);
lean_ctor_set(v___x_6162_, 3, v___x_6152_);
lean_ctor_set(v___x_6162_, 4, v___x_6161_);
v___x_6163_ = lean_box(0);
v___x_6164_ = lean_st_mk_ref(v___x_6162_);
v___x_6165_ = l_Lean_Meta_addDefaultInstance(v_declName_6131_, v_a_6140_, v___x_6157_, v___x_6164_, v___y_6142_, v___y_6143_);
lean_dec_ref_known(v___x_6157_, 7);
if (lean_obj_tag(v___x_6165_) == 0)
{
lean_object* v___x_6167_; uint8_t v_isShared_6168_; uint8_t v_isSharedCheck_6173_; 
v_isSharedCheck_6173_ = !lean_is_exclusive(v___x_6165_);
if (v_isSharedCheck_6173_ == 0)
{
lean_object* v_unused_6174_; 
v_unused_6174_ = lean_ctor_get(v___x_6165_, 0);
lean_dec(v_unused_6174_);
v___x_6167_ = v___x_6165_;
v_isShared_6168_ = v_isSharedCheck_6173_;
goto v_resetjp_6166_;
}
else
{
lean_dec(v___x_6165_);
v___x_6167_ = lean_box(0);
v_isShared_6168_ = v_isSharedCheck_6173_;
goto v_resetjp_6166_;
}
v_resetjp_6166_:
{
lean_object* v___x_6169_; lean_object* v___x_6171_; 
v___x_6169_ = lean_st_ref_get(v___x_6164_);
lean_dec(v___x_6164_);
lean_dec(v___x_6169_);
if (v_isShared_6168_ == 0)
{
lean_ctor_set(v___x_6167_, 0, v___x_6163_);
v___x_6171_ = v___x_6167_;
goto v_reusejp_6170_;
}
else
{
lean_object* v_reuseFailAlloc_6172_; 
v_reuseFailAlloc_6172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6172_, 0, v___x_6163_);
v___x_6171_ = v_reuseFailAlloc_6172_;
goto v_reusejp_6170_;
}
v_reusejp_6170_:
{
return v___x_6171_;
}
}
}
else
{
lean_dec(v___x_6164_);
return v___x_6165_;
}
}
}
else
{
lean_object* v_a_6178_; lean_object* v___x_6180_; uint8_t v_isShared_6181_; uint8_t v_isSharedCheck_6185_; 
lean_dec(v_declName_6131_);
lean_dec(v___x_6130_);
lean_dec(v___x_6129_);
lean_dec(v___x_6128_);
v_a_6178_ = lean_ctor_get(v___x_6139_, 0);
v_isSharedCheck_6185_ = !lean_is_exclusive(v___x_6139_);
if (v_isSharedCheck_6185_ == 0)
{
v___x_6180_ = v___x_6139_;
v_isShared_6181_ = v_isSharedCheck_6185_;
goto v_resetjp_6179_;
}
else
{
lean_inc(v_a_6178_);
lean_dec(v___x_6139_);
v___x_6180_ = lean_box(0);
v_isShared_6181_ = v_isSharedCheck_6185_;
goto v_resetjp_6179_;
}
v_resetjp_6179_:
{
lean_object* v___x_6183_; 
if (v_isShared_6181_ == 0)
{
v___x_6183_ = v___x_6180_;
goto v_reusejp_6182_;
}
else
{
lean_object* v_reuseFailAlloc_6184_; 
v_reuseFailAlloc_6184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6184_, 0, v_a_6178_);
v___x_6183_ = v_reuseFailAlloc_6184_;
goto v_reusejp_6182_;
}
v_reusejp_6182_:
{
return v___x_6183_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6186_, lean_object* v___x_6187_, lean_object* v___x_6188_, lean_object* v_declName_6189_, lean_object* v_stx_6190_, lean_object* v_kind_6191_, lean_object* v___y_6192_, lean_object* v___y_6193_, lean_object* v___y_6194_){
_start:
{
uint8_t v_kind_boxed_6195_; lean_object* v_res_6196_; 
v_kind_boxed_6195_ = lean_unbox(v_kind_6191_);
v_res_6196_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6186_, v___x_6187_, v___x_6188_, v_declName_6189_, v_stx_6190_, v_kind_boxed_6195_, v___y_6192_, v___y_6193_);
lean_dec(v___y_6193_);
lean_dec_ref(v___y_6192_);
lean_dec(v_stx_6190_);
return v_res_6196_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6198_; lean_object* v___x_6199_; 
v___x_6198_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6199_ = l_Lean_stringToMessageData(v___x_6198_);
return v___x_6199_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6201_; lean_object* v___x_6202_; 
v___x_6201_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6202_ = l_Lean_stringToMessageData(v___x_6201_);
return v___x_6202_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6203_, lean_object* v_decl_6204_, lean_object* v___y_6205_, lean_object* v___y_6206_){
_start:
{
lean_object* v___x_6208_; lean_object* v___x_6209_; lean_object* v___x_6210_; lean_object* v___x_6211_; lean_object* v___x_6212_; lean_object* v___x_6213_; 
v___x_6208_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6209_ = l_Lean_MessageData_ofName(v___x_6203_);
v___x_6210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6210_, 0, v___x_6208_);
lean_ctor_set(v___x_6210_, 1, v___x_6209_);
v___x_6211_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6212_, 0, v___x_6210_);
lean_ctor_set(v___x_6212_, 1, v___x_6211_);
v___x_6213_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6212_, v___y_6205_, v___y_6206_);
return v___x_6213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6214_, lean_object* v_decl_6215_, lean_object* v___y_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_){
_start:
{
lean_object* v_res_6219_; 
v_res_6219_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6214_, v_decl_6215_, v___y_6216_, v___y_6217_);
lean_dec(v___y_6217_);
lean_dec_ref(v___y_6216_);
lean_dec(v_decl_6215_);
return v_res_6219_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; 
v___x_6252_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6253_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6254_ = l_Lean_registerBuiltinAttribute(v___x_6253_);
if (lean_obj_tag(v___x_6254_) == 0)
{
lean_object* v___x_6255_; uint8_t v___x_6256_; lean_object* v___x_6257_; 
lean_dec_ref_known(v___x_6254_, 1);
v___x_6255_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_6256_ = 0;
v___x_6257_ = l_Lean_registerTraceClass(v___x_6255_, v___x_6256_, v___x_6252_);
return v___x_6257_;
}
else
{
return v___x_6254_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_6258_){
_start:
{
lean_object* v_res_6259_; 
v_res_6259_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_6259_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_6260_, lean_object* v_name_6261_, uint8_t v_kind_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_){
_start:
{
lean_object* v___x_6266_; 
v___x_6266_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6261_, v_kind_6262_, v___y_6263_, v___y_6264_);
return v___x_6266_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_6267_, lean_object* v_name_6268_, lean_object* v_kind_6269_, lean_object* v___y_6270_, lean_object* v___y_6271_, lean_object* v___y_6272_){
_start:
{
uint8_t v_kind_boxed_6273_; lean_object* v_res_6274_; 
v_kind_boxed_6273_ = lean_unbox(v_kind_6269_);
v_res_6274_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_6267_, v_name_6268_, v_kind_boxed_6273_, v___y_6270_, v___y_6271_);
lean_dec(v___y_6271_);
lean_dec_ref(v___y_6270_);
return v_res_6274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_6275_, lean_object* v_toPure_6276_, lean_object* v_____do__lift_6277_){
_start:
{
lean_object* v___x_6278_; lean_object* v_toEnvExtension_6279_; lean_object* v_asyncMode_6280_; lean_object* v___x_6281_; lean_object* v___x_6282_; lean_object* v_priorities_6283_; lean_object* v___x_6284_; 
v___x_6278_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6279_ = lean_ctor_get(v___x_6278_, 0);
v_asyncMode_6280_ = lean_ctor_get(v_toEnvExtension_6279_, 2);
v___x_6281_ = lean_box(0);
v___x_6282_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6275_, v___x_6278_, v_____do__lift_6277_, v_asyncMode_6280_, v___x_6281_);
v_priorities_6283_ = lean_ctor_get(v___x_6282_, 1);
lean_inc(v_priorities_6283_);
lean_dec(v___x_6282_);
v___x_6284_ = lean_apply_2(v_toPure_6276_, lean_box(0), v_priorities_6283_);
return v___x_6284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_6285_, lean_object* v_inst_6286_){
_start:
{
lean_object* v_toApplicative_6287_; lean_object* v_toBind_6288_; lean_object* v_getEnv_6289_; lean_object* v_toPure_6290_; lean_object* v___x_6291_; lean_object* v___f_6292_; lean_object* v___x_6293_; 
v_toApplicative_6287_ = lean_ctor_get(v_inst_6285_, 0);
lean_inc_ref(v_toApplicative_6287_);
v_toBind_6288_ = lean_ctor_get(v_inst_6285_, 1);
lean_inc(v_toBind_6288_);
lean_dec_ref(v_inst_6285_);
v_getEnv_6289_ = lean_ctor_get(v_inst_6286_, 0);
lean_inc(v_getEnv_6289_);
lean_dec_ref(v_inst_6286_);
v_toPure_6290_ = lean_ctor_get(v_toApplicative_6287_, 1);
lean_inc(v_toPure_6290_);
lean_dec_ref(v_toApplicative_6287_);
v___x_6291_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6292_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6292_, 0, v___x_6291_);
lean_closure_set(v___f_6292_, 1, v_toPure_6290_);
v___x_6293_ = lean_apply_4(v_toBind_6288_, lean_box(0), lean_box(0), v_getEnv_6289_, v___f_6292_);
return v___x_6293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_6294_, lean_object* v_inst_6295_, lean_object* v_inst_6296_){
_start:
{
lean_object* v___x_6297_; 
v___x_6297_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_6295_, v_inst_6296_);
return v___x_6297_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_6298_, uint8_t v_isExporting_6299_, lean_object* v_x_6300_){
_start:
{
lean_object* v_fst_6301_; uint8_t v___x_6302_; 
v_fst_6301_ = lean_ctor_get(v_x_6300_, 0);
lean_inc(v_fst_6301_);
lean_dec_ref(v_x_6300_);
v___x_6302_ = l_Lean_Environment_contains(v_env_6298_, v_fst_6301_, v_isExporting_6299_);
return v___x_6302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_6303_, lean_object* v_isExporting_6304_, lean_object* v_x_6305_){
_start:
{
uint8_t v_isExporting_boxed_6306_; uint8_t v_res_6307_; lean_object* v_r_6308_; 
v_isExporting_boxed_6306_ = lean_unbox(v_isExporting_6304_);
v_res_6307_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_6303_, v_isExporting_boxed_6306_, v_x_6305_);
v_r_6308_ = lean_box(v_res_6307_);
return v_r_6308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_6309_, lean_object* v_toPure_6310_, lean_object* v_className_6311_, lean_object* v_env_6312_){
_start:
{
lean_object* v___y_6314_; lean_object* v___x_6322_; lean_object* v_toEnvExtension_6323_; lean_object* v_asyncMode_6324_; lean_object* v___x_6325_; lean_object* v___x_6326_; lean_object* v_defaultInstances_6327_; lean_object* v___x_6328_; 
v___x_6322_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6323_ = lean_ctor_get(v___x_6322_, 0);
v_asyncMode_6324_ = lean_ctor_get(v_toEnvExtension_6323_, 2);
v___x_6325_ = lean_box(0);
lean_inc_ref(v_env_6312_);
v___x_6326_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6309_, v___x_6322_, v_env_6312_, v_asyncMode_6324_, v___x_6325_);
v_defaultInstances_6327_ = lean_ctor_get(v___x_6326_, 0);
lean_inc(v_defaultInstances_6327_);
lean_dec(v___x_6326_);
v___x_6328_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_6327_, v_className_6311_);
lean_dec(v_defaultInstances_6327_);
if (lean_obj_tag(v___x_6328_) == 0)
{
lean_object* v___x_6329_; 
v___x_6329_ = lean_box(0);
v___y_6314_ = v___x_6329_;
goto v___jp_6313_;
}
else
{
lean_object* v_val_6330_; 
v_val_6330_ = lean_ctor_get(v___x_6328_, 0);
lean_inc(v_val_6330_);
lean_dec_ref_known(v___x_6328_, 1);
v___y_6314_ = v_val_6330_;
goto v___jp_6313_;
}
v___jp_6313_:
{
uint8_t v_isExporting_6315_; 
v_isExporting_6315_ = lean_ctor_get_uint8(v_env_6312_, sizeof(void*)*13);
if (v_isExporting_6315_ == 0)
{
lean_object* v___x_6316_; 
lean_dec_ref(v_env_6312_);
v___x_6316_ = lean_apply_2(v_toPure_6310_, lean_box(0), v___y_6314_);
return v___x_6316_;
}
else
{
lean_object* v___x_6317_; lean_object* v___f_6318_; lean_object* v___x_6319_; lean_object* v___x_6320_; lean_object* v___x_6321_; 
v___x_6317_ = lean_box(v_isExporting_6315_);
v___f_6318_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6318_, 0, v_env_6312_);
lean_closure_set(v___f_6318_, 1, v___x_6317_);
v___x_6319_ = lean_box(0);
v___x_6320_ = l_List_filterTR_loop___redArg(v___f_6318_, v___y_6314_, v___x_6319_);
v___x_6321_ = lean_apply_2(v_toPure_6310_, lean_box(0), v___x_6320_);
return v___x_6321_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_6331_, lean_object* v_toPure_6332_, lean_object* v_className_6333_, lean_object* v_env_6334_){
_start:
{
lean_object* v_res_6335_; 
v_res_6335_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_6331_, v_toPure_6332_, v_className_6333_, v_env_6334_);
lean_dec(v_className_6333_);
return v_res_6335_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_6336_, lean_object* v_inst_6337_, lean_object* v_className_6338_){
_start:
{
lean_object* v_toApplicative_6339_; lean_object* v_toBind_6340_; lean_object* v_getEnv_6341_; lean_object* v_toPure_6342_; lean_object* v___x_6343_; lean_object* v___f_6344_; lean_object* v___x_6345_; 
v_toApplicative_6339_ = lean_ctor_get(v_inst_6336_, 0);
lean_inc_ref(v_toApplicative_6339_);
v_toBind_6340_ = lean_ctor_get(v_inst_6336_, 1);
lean_inc(v_toBind_6340_);
lean_dec_ref(v_inst_6336_);
v_getEnv_6341_ = lean_ctor_get(v_inst_6337_, 0);
lean_inc(v_getEnv_6341_);
lean_dec_ref(v_inst_6337_);
v_toPure_6342_ = lean_ctor_get(v_toApplicative_6339_, 1);
lean_inc(v_toPure_6342_);
lean_dec_ref(v_toApplicative_6339_);
v___x_6343_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6344_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_6344_, 0, v___x_6343_);
lean_closure_set(v___f_6344_, 1, v_toPure_6342_);
lean_closure_set(v___f_6344_, 2, v_className_6338_);
v___x_6345_ = lean_apply_4(v_toBind_6340_, lean_box(0), lean_box(0), v_getEnv_6341_, v___f_6344_);
return v___x_6345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6346_, lean_object* v_inst_6347_, lean_object* v_inst_6348_, lean_object* v_className_6349_){
_start:
{
lean_object* v___x_6350_; 
v___x_6350_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6347_, v_inst_6348_, v_className_6349_);
return v___x_6350_;
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
