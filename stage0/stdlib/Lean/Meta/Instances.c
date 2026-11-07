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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* l_Lean_Environment_setRecordingDeps(lean_object*, uint8_t);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_borrowed(lean_object*, lean_object*, lean_object*);
lean_object* lean_infer_type(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_getMVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Expr_mvar___override(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Expr_mvarId_x21(lean_object*);
uint8_t l_Lean_instBEqMVarId_beq(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty___redArg();
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited___redArg();
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_getAttrParamOptPrio(lean_object*, lean_object*, lean_object*);
uint64_t l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(lean_object*);
lean_object* lean_st_mk_ref(lean_object*);
lean_object* l_Lean_Environment_findConstVal_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
extern lean_object* l_Lean_unknownIdentifierMessageTag;
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* l_Lean_mkLevelParam(lean_object*);
lean_object* l_Lean_mkConst(lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_addCore___redArg(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_ConstantInfo_type(lean_object*);
lean_object* l_Lean_indentExpr(lean_object*);
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
lean_object* l_Lean_Meta_DiscrTree_mkPath(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_getReducibilityStatusCore(lean_object*, lean_object*);
uint8_t l_Lean_instBEqReducibilityStatus_beq(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_InstanceEntry_keyClass_spec__0(lean_object*);
static const lean_string_object l_Lean_Meta_InstanceEntry_keyClass___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "Lean.Meta.Instances"};
static const lean_object* l_Lean_Meta_InstanceEntry_keyClass___closed__0 = (const lean_object*)&l_Lean_Meta_InstanceEntry_keyClass___closed__0_value;
static const lean_string_object l_Lean_Meta_InstanceEntry_keyClass___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "Lean.Meta.InstanceEntry.keyClass"};
static const lean_object* l_Lean_Meta_InstanceEntry_keyClass___closed__1 = (const lean_object*)&l_Lean_Meta_InstanceEntry_keyClass___closed__1_value;
static const lean_string_object l_Lean_Meta_InstanceEntry_keyClass___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 67, .m_capacity = 67, .m_length = 66, .m_data = "instance key not rooted at a constant, which `addInstance` rejects"};
static const lean_object* l_Lean_Meta_InstanceEntry_keyClass___closed__2 = (const lean_object*)&l_Lean_Meta_InstanceEntry_keyClass___closed__2_value;
static lean_once_cell_t l_Lean_Meta_InstanceEntry_keyClass___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_InstanceEntry_keyClass___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_InstanceEntry_keyClass(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_InstanceEntry_keyClass___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_getClassChanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_getClassChanges___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__1___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__2___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__2(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4_spec__10_spec__17(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4_spec__10_spec__17___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4_spec__10(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__13_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__13___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__14___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__14___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__5_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__5_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__5(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__2_spec__6(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__2(lean_object*);
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 26, .m_capacity = 26, .m_length = 25, .m_data = "Lean.Meta.DiscrTree.Basic"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__0 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__0_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 35, .m_capacity = 35, .m_length = 34, .m_data = "Lean.Meta.DiscrTree.insertKeyValue"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__1 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__1_value;
static const lean_string_object l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "invalid key sequence"};
static const lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__2 = (const lean_object*)&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__3;
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addImportedInstanceEntry(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__13(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__14(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__13_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instanceExtension"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 253, 187, 89, 234, 162, 232, 19)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addInstanceEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addImportedInstanceEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__4___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__0;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__1;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__2;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__3;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__4;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__5 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__5_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__6;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__7 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__7_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__8;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__9 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__9_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__10;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__11 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__11_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__12;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__13 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__13_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__14;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__15 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__15_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__16;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__17 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__17_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__18_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__18;
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__12___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Unknown constant `"};
static const lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__0 = (const lean_object*)&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__0_value;
static lean_once_cell_t l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9___redArg();
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9___redArg___boxed(lean_object*);
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__3;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__4;
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_addInstance___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "invalid instance `"};
static const lean_object* l_Lean_Meta_addInstance___closed__0 = (const lean_object*)&l_Lean_Meta_addInstance___closed__0_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__1;
static const lean_string_object l_Lean_Meta_addInstance___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 86, .m_capacity = 86, .m_length = 85, .m_data = "`, its type does not reduce to an application of a constant at reducible transparency"};
static const lean_object* l_Lean_Meta_addInstance___closed__2 = (const lean_object*)&l_Lean_Meta_addInstance___closed__2_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__3;
static const lean_string_object l_Lean_Meta_addInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "instance `"};
static const lean_object* l_Lean_Meta_addInstance___closed__4 = (const lean_object*)&l_Lean_Meta_addInstance___closed__4_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__5;
static const lean_string_object l_Lean_Meta_addInstance___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 34, .m_capacity = 34, .m_length = 33, .m_data = "` must be marked with `@[expose]`"};
static const lean_object* l_Lean_Meta_addInstance___closed__6 = (const lean_object*)&l_Lean_Meta_addInstance___closed__6_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__7;
static const lean_string_object l_Lean_Meta_addInstance___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Definition `"};
static const lean_object* l_Lean_Meta_addInstance___closed__8 = (const lean_object*)&l_Lean_Meta_addInstance___closed__8_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__9;
static const lean_string_object l_Lean_Meta_addInstance___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 274, .m_capacity = 274, .m_length = 273, .m_data = "` of class type is semireducible. Most type class instances should be instance-reducible, so consider marking this\ndefinition with `@[instance_reducible]`. If it is intentionally semireducible, this warning can be disabled with `set_option warn.classDefReducibility false`."};
static const lean_object* l_Lean_Meta_addInstance___closed__10 = (const lean_object*)&l_Lean_Meta_addInstance___closed__10_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__11;
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6___redArg();
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceClassChanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceClassChanges___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
v___x_120_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_120_, 0, v___x_119_);
lean_ctor_set(v___x_120_, 1, v___x_118_);
lean_ctor_set(v___x_120_, 2, v___x_117_);
lean_ctor_set(v___x_120_, 3, v___x_118_);
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
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_InstanceEntry_keyClass_spec__0(lean_object* v_msg_123_){
_start:
{
lean_object* v___x_124_; lean_object* v___x_125_; 
v___x_124_ = lean_box(0);
v___x_125_ = lean_panic_fn_borrowed(v___x_124_, v_msg_123_);
return v___x_125_;
}
}
static lean_object* _init_l_Lean_Meta_InstanceEntry_keyClass___closed__3(void){
_start:
{
lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; 
v___x_129_ = ((lean_object*)(l_Lean_Meta_InstanceEntry_keyClass___closed__2));
v___x_130_ = lean_unsigned_to_nat(9u);
v___x_131_ = lean_unsigned_to_nat(95u);
v___x_132_ = ((lean_object*)(l_Lean_Meta_InstanceEntry_keyClass___closed__1));
v___x_133_ = ((lean_object*)(l_Lean_Meta_InstanceEntry_keyClass___closed__0));
v___x_134_ = l_mkPanicMessageWithDecl(v___x_133_, v___x_132_, v___x_131_, v___x_130_, v___x_129_);
return v___x_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InstanceEntry_keyClass(lean_object* v_e_135_){
_start:
{
lean_object* v_keys_139_; lean_object* v___x_140_; lean_object* v___x_141_; uint8_t v___x_142_; 
v_keys_139_ = lean_ctor_get(v_e_135_, 0);
v___x_140_ = lean_unsigned_to_nat(0u);
v___x_141_ = lean_array_get_size(v_keys_139_);
v___x_142_ = lean_nat_dec_lt(v___x_140_, v___x_141_);
if (v___x_142_ == 0)
{
goto v___jp_136_;
}
else
{
lean_object* v___x_143_; 
v___x_143_ = lean_array_fget_borrowed(v_keys_139_, v___x_140_);
if (lean_obj_tag(v___x_143_) == 4)
{
lean_object* v_a_144_; 
v_a_144_ = lean_ctor_get(v___x_143_, 0);
lean_inc(v_a_144_);
return v_a_144_;
}
else
{
goto v___jp_136_;
}
}
v___jp_136_:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = lean_obj_once(&l_Lean_Meta_InstanceEntry_keyClass___closed__3, &l_Lean_Meta_InstanceEntry_keyClass___closed__3_once, _init_l_Lean_Meta_InstanceEntry_keyClass___closed__3);
v___x_138_ = l_panic___at___00Lean_Meta_InstanceEntry_keyClass_spec__0(v___x_137_);
return v___x_138_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_InstanceEntry_keyClass___boxed(lean_object* v_e_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Lean_Meta_InstanceEntry_keyClass(v_e_145_);
lean_dec_ref(v_e_145_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_147_, lean_object* v_vals_148_, lean_object* v_i_149_, lean_object* v_k_150_){
_start:
{
lean_object* v___x_151_; uint8_t v___x_152_; 
v___x_151_ = lean_array_get_size(v_keys_147_);
v___x_152_ = lean_nat_dec_lt(v_i_149_, v___x_151_);
if (v___x_152_ == 0)
{
lean_object* v___x_153_; 
lean_dec(v_i_149_);
v___x_153_ = lean_box(0);
return v___x_153_;
}
else
{
lean_object* v_k_x27_154_; uint8_t v___x_155_; 
v_k_x27_154_ = lean_array_fget_borrowed(v_keys_147_, v_i_149_);
v___x_155_ = lean_name_eq(v_k_150_, v_k_x27_154_);
if (v___x_155_ == 0)
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = lean_unsigned_to_nat(1u);
v___x_157_ = lean_nat_add(v_i_149_, v___x_156_);
lean_dec(v_i_149_);
v_i_149_ = v___x_157_;
goto _start;
}
else
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_array_fget_borrowed(v_vals_148_, v_i_149_);
lean_dec(v_i_149_);
lean_inc(v___x_159_);
v___x_160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_160_, 0, v___x_159_);
return v___x_160_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_161_, lean_object* v_vals_162_, lean_object* v_i_163_, lean_object* v_k_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0_spec__1___redArg(v_keys_161_, v_vals_162_, v_i_163_, v_k_164_);
lean_dec(v_k_164_);
lean_dec_ref(v_vals_162_);
lean_dec_ref(v_keys_161_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0___redArg(lean_object* v_x_166_, size_t v_x_167_, lean_object* v_x_168_){
_start:
{
if (lean_obj_tag(v_x_166_) == 0)
{
lean_object* v_es_169_; lean_object* v___x_170_; size_t v___x_171_; size_t v___x_172_; lean_object* v_j_173_; lean_object* v___x_174_; 
v_es_169_ = lean_ctor_get(v_x_166_, 0);
v___x_170_ = lean_box(2);
v___x_171_ = ((size_t)31ULL);
v___x_172_ = lean_usize_land(v_x_167_, v___x_171_);
v_j_173_ = lean_usize_to_nat(v___x_172_);
v___x_174_ = lean_array_get_borrowed(v___x_170_, v_es_169_, v_j_173_);
lean_dec(v_j_173_);
switch(lean_obj_tag(v___x_174_))
{
case 0:
{
lean_object* v_key_175_; lean_object* v_val_176_; uint8_t v___x_177_; 
v_key_175_ = lean_ctor_get(v___x_174_, 0);
v_val_176_ = lean_ctor_get(v___x_174_, 1);
v___x_177_ = lean_name_eq(v_x_168_, v_key_175_);
if (v___x_177_ == 0)
{
lean_object* v___x_178_; 
v___x_178_ = lean_box(0);
return v___x_178_;
}
else
{
lean_object* v___x_179_; 
lean_inc(v_val_176_);
v___x_179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_179_, 0, v_val_176_);
return v___x_179_;
}
}
case 1:
{
lean_object* v_node_180_; size_t v___x_181_; size_t v___x_182_; 
v_node_180_ = lean_ctor_get(v___x_174_, 0);
v___x_181_ = ((size_t)5ULL);
v___x_182_ = lean_usize_shift_right(v_x_167_, v___x_181_);
v_x_166_ = v_node_180_;
v_x_167_ = v___x_182_;
goto _start;
}
default: 
{
lean_object* v___x_184_; 
v___x_184_ = lean_box(0);
return v___x_184_;
}
}
}
else
{
lean_object* v_ks_185_; lean_object* v_vs_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v_ks_185_ = lean_ctor_get(v_x_166_, 0);
v_vs_186_ = lean_ctor_get(v_x_166_, 1);
v___x_187_ = lean_unsigned_to_nat(0u);
v___x_188_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0_spec__1___redArg(v_ks_185_, v_vs_186_, v___x_187_, v_x_168_);
return v___x_188_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0___redArg___boxed(lean_object* v_x_189_, lean_object* v_x_190_, lean_object* v_x_191_){
_start:
{
size_t v_x_141__boxed_192_; lean_object* v_res_193_; 
v_x_141__boxed_192_ = lean_unbox_usize(v_x_190_);
lean_dec(v_x_190_);
v_res_193_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0___redArg(v_x_189_, v_x_141__boxed_192_, v_x_191_);
lean_dec(v_x_191_);
lean_dec_ref(v_x_189_);
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0___redArg(lean_object* v_x_194_, lean_object* v_x_195_){
_start:
{
uint64_t v___y_197_; 
if (lean_obj_tag(v_x_195_) == 0)
{
uint64_t v___x_200_; 
v___x_200_ = 1723ULL;
v___y_197_ = v___x_200_;
goto v___jp_196_;
}
else
{
uint64_t v_hash_201_; 
v_hash_201_ = lean_ctor_get_uint64(v_x_195_, sizeof(void*)*2);
v___y_197_ = v_hash_201_;
goto v___jp_196_;
}
v___jp_196_:
{
size_t v___x_198_; lean_object* v___x_199_; 
v___x_198_ = lean_uint64_to_usize(v___y_197_);
v___x_199_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0___redArg(v_x_194_, v___x_198_, v_x_195_);
return v___x_199_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0___redArg___boxed(lean_object* v_x_202_, lean_object* v_x_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0___redArg(v_x_202_, v_x_203_);
lean_dec(v_x_203_);
lean_dec_ref(v_x_202_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_getClassChanges(lean_object* v_d_205_, lean_object* v_className_206_){
_start:
{
lean_object* v_classChanges_207_; lean_object* v___x_208_; 
v_classChanges_207_ = lean_ctor_get(v_d_205_, 3);
v___x_208_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0___redArg(v_classChanges_207_, v_className_206_);
if (lean_obj_tag(v___x_208_) == 0)
{
lean_object* v___x_209_; 
v___x_209_ = lean_box(0);
return v___x_209_;
}
else
{
lean_object* v_val_210_; 
v_val_210_ = lean_ctor_get(v___x_208_, 0);
lean_inc(v_val_210_);
lean_dec_ref_known(v___x_208_, 1);
return v_val_210_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_getClassChanges___boxed(lean_object* v_d_211_, lean_object* v_className_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_Lean_Meta_Instances_getClassChanges(v_d_211_, v_className_212_);
lean_dec(v_className_212_);
lean_dec_ref(v_d_211_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0(lean_object* v_00_u03b2_214_, lean_object* v_x_215_, lean_object* v_x_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0___redArg(v_x_215_, v_x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0___boxed(lean_object* v_00_u03b2_218_, lean_object* v_x_219_, lean_object* v_x_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0(v_00_u03b2_218_, v_x_219_, v_x_220_);
lean_dec(v_x_220_);
lean_dec_ref(v_x_219_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0(lean_object* v_00_u03b2_222_, lean_object* v_x_223_, size_t v_x_224_, lean_object* v_x_225_){
_start:
{
lean_object* v___x_226_; 
v___x_226_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0___redArg(v_x_223_, v_x_224_, v_x_225_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0___boxed(lean_object* v_00_u03b2_227_, lean_object* v_x_228_, lean_object* v_x_229_, lean_object* v_x_230_){
_start:
{
size_t v_x_218__boxed_231_; lean_object* v_res_232_; 
v_x_218__boxed_231_ = lean_unbox_usize(v_x_229_);
lean_dec(v_x_229_);
v_res_232_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0(v_00_u03b2_227_, v_x_228_, v_x_218__boxed_231_, v_x_230_);
lean_dec(v_x_230_);
lean_dec_ref(v_x_228_);
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_233_, lean_object* v_keys_234_, lean_object* v_vals_235_, lean_object* v_heq_236_, lean_object* v_i_237_, lean_object* v_k_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0_spec__1___redArg(v_keys_234_, v_vals_235_, v_i_237_, v_k_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_240_, lean_object* v_keys_241_, lean_object* v_vals_242_, lean_object* v_heq_243_, lean_object* v_i_244_, lean_object* v_k_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0_spec__0_spec__1(v_00_u03b2_240_, v_keys_241_, v_vals_242_, v_heq_243_, v_i_244_, v_k_245_);
lean_dec(v_k_245_);
lean_dec_ref(v_vals_242_);
lean_dec_ref(v_keys_241_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_x_247_, lean_object* v_x_248_, lean_object* v_x_249_, lean_object* v_x_250_){
_start:
{
lean_object* v_ks_251_; lean_object* v_vs_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_276_; 
v_ks_251_ = lean_ctor_get(v_x_247_, 0);
v_vs_252_ = lean_ctor_get(v_x_247_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_x_247_);
if (v_isSharedCheck_276_ == 0)
{
v___x_254_ = v_x_247_;
v_isShared_255_ = v_isSharedCheck_276_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_vs_252_);
lean_inc(v_ks_251_);
lean_dec(v_x_247_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_276_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v___x_256_; uint8_t v___x_257_; 
v___x_256_ = lean_array_get_size(v_ks_251_);
v___x_257_ = lean_nat_dec_lt(v_x_248_, v___x_256_);
if (v___x_257_ == 0)
{
lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_261_; 
lean_dec(v_x_248_);
v___x_258_ = lean_array_push(v_ks_251_, v_x_249_);
v___x_259_ = lean_array_push(v_vs_252_, v_x_250_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_259_);
lean_ctor_set(v___x_254_, 0, v___x_258_);
v___x_261_ = v___x_254_;
goto v_reusejp_260_;
}
else
{
lean_object* v_reuseFailAlloc_262_; 
v_reuseFailAlloc_262_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_262_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_262_, 1, v___x_259_);
v___x_261_ = v_reuseFailAlloc_262_;
goto v_reusejp_260_;
}
v_reusejp_260_:
{
return v___x_261_;
}
}
else
{
lean_object* v_k_x27_263_; uint8_t v___x_264_; 
v_k_x27_263_ = lean_array_fget_borrowed(v_ks_251_, v_x_248_);
v___x_264_ = lean_name_eq(v_x_249_, v_k_x27_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_266_; 
if (v_isShared_255_ == 0)
{
v___x_266_ = v___x_254_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_ks_251_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_vs_252_);
v___x_266_ = v_reuseFailAlloc_270_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_267_ = lean_unsigned_to_nat(1u);
v___x_268_ = lean_nat_add(v_x_248_, v___x_267_);
lean_dec(v_x_248_);
v_x_247_ = v___x_266_;
v_x_248_ = v___x_268_;
goto _start;
}
}
else
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_271_ = lean_array_fset(v_ks_251_, v_x_248_, v_x_249_);
v___x_272_ = lean_array_fset(v_vs_252_, v_x_248_, v_x_250_);
lean_dec(v_x_248_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v___x_272_);
lean_ctor_set(v___x_254_, 0, v___x_271_);
v___x_274_ = v___x_254_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__1___redArg(lean_object* v_n_277_, lean_object* v_k_278_, lean_object* v_v_279_){
_start:
{
lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_280_ = lean_unsigned_to_nat(0u);
v___x_281_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__1_spec__2___redArg(v_n_277_, v___x_280_, v_k_278_, v_v_279_);
return v___x_281_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_PersistentHashMap_mkEmptyEntries___redArg();
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg(lean_object* v_x_283_, size_t v_x_284_, size_t v_x_285_, lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
if (lean_obj_tag(v_x_283_) == 0)
{
lean_object* v_es_288_; size_t v___x_289_; size_t v___x_290_; lean_object* v_j_291_; lean_object* v___x_292_; uint8_t v___x_293_; 
v_es_288_ = lean_ctor_get(v_x_283_, 0);
v___x_289_ = ((size_t)31ULL);
v___x_290_ = lean_usize_land(v_x_284_, v___x_289_);
v_j_291_ = lean_usize_to_nat(v___x_290_);
v___x_292_ = lean_array_get_size(v_es_288_);
v___x_293_ = lean_nat_dec_lt(v_j_291_, v___x_292_);
if (v___x_293_ == 0)
{
lean_dec(v_j_291_);
lean_dec(v_x_287_);
lean_dec(v_x_286_);
return v_x_283_;
}
else
{
lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_332_; 
lean_inc_ref(v_es_288_);
v_isSharedCheck_332_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_332_ == 0)
{
lean_object* v_unused_333_; 
v_unused_333_ = lean_ctor_get(v_x_283_, 0);
lean_dec(v_unused_333_);
v___x_295_ = v_x_283_;
v_isShared_296_ = v_isSharedCheck_332_;
goto v_resetjp_294_;
}
else
{
lean_dec(v_x_283_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_332_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v_v_297_; lean_object* v___x_298_; lean_object* v_xs_x27_299_; lean_object* v___y_301_; 
v_v_297_ = lean_array_fget(v_es_288_, v_j_291_);
v___x_298_ = lean_box(0);
v_xs_x27_299_ = lean_array_fset(v_es_288_, v_j_291_, v___x_298_);
switch(lean_obj_tag(v_v_297_))
{
case 0:
{
lean_object* v_key_306_; lean_object* v_val_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_317_; 
v_key_306_ = lean_ctor_get(v_v_297_, 0);
v_val_307_ = lean_ctor_get(v_v_297_, 1);
v_isSharedCheck_317_ = !lean_is_exclusive(v_v_297_);
if (v_isSharedCheck_317_ == 0)
{
v___x_309_ = v_v_297_;
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_val_307_);
lean_inc(v_key_306_);
lean_dec(v_v_297_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_317_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
uint8_t v___x_311_; 
v___x_311_ = lean_name_eq(v_x_286_, v_key_306_);
if (v___x_311_ == 0)
{
lean_object* v___x_312_; lean_object* v___x_313_; 
lean_del_object(v___x_309_);
v___x_312_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_306_, v_val_307_, v_x_286_, v_x_287_);
v___x_313_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_313_, 0, v___x_312_);
v___y_301_ = v___x_313_;
goto v___jp_300_;
}
else
{
lean_object* v___x_315_; 
lean_dec(v_val_307_);
lean_dec(v_key_306_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v_x_287_);
lean_ctor_set(v___x_309_, 0, v_x_286_);
v___x_315_ = v___x_309_;
goto v_reusejp_314_;
}
else
{
lean_object* v_reuseFailAlloc_316_; 
v_reuseFailAlloc_316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_316_, 0, v_x_286_);
lean_ctor_set(v_reuseFailAlloc_316_, 1, v_x_287_);
v___x_315_ = v_reuseFailAlloc_316_;
goto v_reusejp_314_;
}
v_reusejp_314_:
{
v___y_301_ = v___x_315_;
goto v___jp_300_;
}
}
}
}
case 1:
{
lean_object* v_node_318_; lean_object* v___x_320_; uint8_t v_isShared_321_; uint8_t v_isSharedCheck_330_; 
v_node_318_ = lean_ctor_get(v_v_297_, 0);
v_isSharedCheck_330_ = !lean_is_exclusive(v_v_297_);
if (v_isSharedCheck_330_ == 0)
{
v___x_320_ = v_v_297_;
v_isShared_321_ = v_isSharedCheck_330_;
goto v_resetjp_319_;
}
else
{
lean_inc(v_node_318_);
lean_dec(v_v_297_);
v___x_320_ = lean_box(0);
v_isShared_321_ = v_isSharedCheck_330_;
goto v_resetjp_319_;
}
v_resetjp_319_:
{
size_t v___x_322_; size_t v___x_323_; size_t v___x_324_; size_t v___x_325_; lean_object* v___x_326_; lean_object* v___x_328_; 
v___x_322_ = ((size_t)5ULL);
v___x_323_ = lean_usize_shift_right(v_x_284_, v___x_322_);
v___x_324_ = ((size_t)1ULL);
v___x_325_ = lean_usize_add(v_x_285_, v___x_324_);
v___x_326_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg(v_node_318_, v___x_323_, v___x_325_, v_x_286_, v_x_287_);
if (v_isShared_321_ == 0)
{
lean_ctor_set(v___x_320_, 0, v___x_326_);
v___x_328_ = v___x_320_;
goto v_reusejp_327_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v___x_326_);
v___x_328_ = v_reuseFailAlloc_329_;
goto v_reusejp_327_;
}
v_reusejp_327_:
{
v___y_301_ = v___x_328_;
goto v___jp_300_;
}
}
}
default: 
{
lean_object* v___x_331_; 
v___x_331_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_331_, 0, v_x_286_);
lean_ctor_set(v___x_331_, 1, v_x_287_);
v___y_301_ = v___x_331_;
goto v___jp_300_;
}
}
v___jp_300_:
{
lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_302_ = lean_array_fset(v_xs_x27_299_, v_j_291_, v___y_301_);
lean_dec(v_j_291_);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 0, v___x_302_);
v___x_304_ = v___x_295_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_302_);
v___x_304_ = v_reuseFailAlloc_305_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
return v___x_304_;
}
}
}
}
}
else
{
lean_object* v_ks_334_; lean_object* v_vs_335_; lean_object* v___x_337_; uint8_t v_isShared_338_; uint8_t v_isSharedCheck_353_; 
v_ks_334_ = lean_ctor_get(v_x_283_, 0);
v_vs_335_ = lean_ctor_get(v_x_283_, 1);
v_isSharedCheck_353_ = !lean_is_exclusive(v_x_283_);
if (v_isSharedCheck_353_ == 0)
{
v___x_337_ = v_x_283_;
v_isShared_338_ = v_isSharedCheck_353_;
goto v_resetjp_336_;
}
else
{
lean_inc(v_vs_335_);
lean_inc(v_ks_334_);
lean_dec(v_x_283_);
v___x_337_ = lean_box(0);
v_isShared_338_ = v_isSharedCheck_353_;
goto v_resetjp_336_;
}
v_resetjp_336_:
{
lean_object* v___x_340_; 
if (v_isShared_338_ == 0)
{
v___x_340_ = v___x_337_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_352_; 
v_reuseFailAlloc_352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_352_, 0, v_ks_334_);
lean_ctor_set(v_reuseFailAlloc_352_, 1, v_vs_335_);
v___x_340_ = v_reuseFailAlloc_352_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
lean_object* v_newNode_341_; size_t v___x_342_; uint8_t v___x_343_; 
v_newNode_341_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__1___redArg(v___x_340_, v_x_286_, v_x_287_);
v___x_342_ = ((size_t)7ULL);
v___x_343_ = lean_usize_dec_le(v___x_342_, v_x_285_);
if (v___x_343_ == 0)
{
lean_object* v___x_344_; lean_object* v___x_345_; uint8_t v___x_346_; 
v___x_344_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_341_);
v___x_345_ = lean_unsigned_to_nat(4u);
v___x_346_ = lean_nat_dec_lt(v___x_344_, v___x_345_);
lean_dec(v___x_344_);
if (v___x_346_ == 0)
{
lean_object* v_ks_347_; lean_object* v_vs_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v_ks_347_ = lean_ctor_get(v_newNode_341_, 0);
lean_inc_ref(v_ks_347_);
v_vs_348_ = lean_ctor_get(v_newNode_341_, 1);
lean_inc_ref(v_vs_348_);
lean_dec_ref(v_newNode_341_);
v___x_349_ = lean_unsigned_to_nat(0u);
v___x_350_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___closed__0);
v___x_351_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__2___redArg(v_x_285_, v_ks_347_, v_vs_348_, v___x_349_, v___x_350_);
lean_dec_ref(v_vs_348_);
lean_dec_ref(v_ks_347_);
return v___x_351_;
}
else
{
return v_newNode_341_;
}
}
else
{
return v_newNode_341_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__2___redArg(size_t v_depth_354_, lean_object* v_keys_355_, lean_object* v_vals_356_, lean_object* v_i_357_, lean_object* v_entries_358_){
_start:
{
lean_object* v___x_359_; uint8_t v___x_360_; 
v___x_359_ = lean_array_get_size(v_keys_355_);
v___x_360_ = lean_nat_dec_lt(v_i_357_, v___x_359_);
if (v___x_360_ == 0)
{
lean_dec(v_i_357_);
return v_entries_358_;
}
else
{
lean_object* v_k_361_; lean_object* v_v_362_; uint64_t v___y_364_; 
v_k_361_ = lean_array_fget_borrowed(v_keys_355_, v_i_357_);
v_v_362_ = lean_array_fget_borrowed(v_vals_356_, v_i_357_);
if (lean_obj_tag(v_k_361_) == 0)
{
uint64_t v___x_375_; 
v___x_375_ = 1723ULL;
v___y_364_ = v___x_375_;
goto v___jp_363_;
}
else
{
uint64_t v_hash_376_; 
v_hash_376_ = lean_ctor_get_uint64(v_k_361_, sizeof(void*)*2);
v___y_364_ = v_hash_376_;
goto v___jp_363_;
}
v___jp_363_:
{
size_t v_h_365_; size_t v___x_366_; lean_object* v___x_367_; size_t v___x_368_; size_t v___x_369_; size_t v___x_370_; size_t v_h_371_; lean_object* v___x_372_; lean_object* v___x_373_; 
v_h_365_ = lean_uint64_to_usize(v___y_364_);
v___x_366_ = ((size_t)5ULL);
v___x_367_ = lean_unsigned_to_nat(1u);
v___x_368_ = ((size_t)1ULL);
v___x_369_ = lean_usize_sub(v_depth_354_, v___x_368_);
v___x_370_ = lean_usize_mul(v___x_366_, v___x_369_);
v_h_371_ = lean_usize_shift_right(v_h_365_, v___x_370_);
v___x_372_ = lean_nat_add(v_i_357_, v___x_367_);
lean_dec(v_i_357_);
lean_inc(v_v_362_);
lean_inc(v_k_361_);
v___x_373_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg(v_entries_358_, v_h_371_, v_depth_354_, v_k_361_, v_v_362_);
v_i_357_ = v___x_372_;
v_entries_358_ = v___x_373_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__2___redArg___boxed(lean_object* v_depth_377_, lean_object* v_keys_378_, lean_object* v_vals_379_, lean_object* v_i_380_, lean_object* v_entries_381_){
_start:
{
size_t v_depth_boxed_382_; lean_object* v_res_383_; 
v_depth_boxed_382_ = lean_unbox_usize(v_depth_377_);
lean_dec(v_depth_377_);
v_res_383_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__2___redArg(v_depth_boxed_382_, v_keys_378_, v_vals_379_, v_i_380_, v_entries_381_);
lean_dec_ref(v_vals_379_);
lean_dec_ref(v_keys_378_);
return v_res_383_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___boxed(lean_object* v_x_384_, lean_object* v_x_385_, lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_x_388_){
_start:
{
size_t v_x_363__boxed_389_; size_t v_x_364__boxed_390_; lean_object* v_res_391_; 
v_x_363__boxed_389_ = lean_unbox_usize(v_x_385_);
lean_dec(v_x_385_);
v_x_364__boxed_390_ = lean_unbox_usize(v_x_386_);
lean_dec(v_x_386_);
v_res_391_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg(v_x_384_, v_x_363__boxed_389_, v_x_364__boxed_390_, v_x_387_, v_x_388_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0___redArg(lean_object* v_x_392_, lean_object* v_x_393_, lean_object* v_x_394_){
_start:
{
uint64_t v___y_396_; 
if (lean_obj_tag(v_x_393_) == 0)
{
uint64_t v___x_400_; 
v___x_400_ = 1723ULL;
v___y_396_ = v___x_400_;
goto v___jp_395_;
}
else
{
uint64_t v_hash_401_; 
v_hash_401_ = lean_ctor_get_uint64(v_x_393_, sizeof(void*)*2);
v___y_396_ = v_hash_401_;
goto v___jp_395_;
}
v___jp_395_:
{
size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; 
v___x_397_ = lean_uint64_to_usize(v___y_396_);
v___x_398_ = ((size_t)1ULL);
v___x_399_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg(v_x_392_, v___x_397_, v___x_398_, v_x_393_, v_x_394_);
return v___x_399_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange(lean_object* v_d_402_, lean_object* v_className_403_, lean_object* v_c_404_){
_start:
{
lean_object* v_discrTree_405_; lean_object* v_instanceNames_406_; lean_object* v_erased_407_; lean_object* v_classChanges_408_; lean_object* v___x_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_418_; 
v_discrTree_405_ = lean_ctor_get(v_d_402_, 0);
lean_inc_ref(v_discrTree_405_);
v_instanceNames_406_ = lean_ctor_get(v_d_402_, 1);
lean_inc_ref(v_instanceNames_406_);
v_erased_407_ = lean_ctor_get(v_d_402_, 2);
lean_inc_ref(v_erased_407_);
v_classChanges_408_ = lean_ctor_get(v_d_402_, 3);
lean_inc_ref(v_classChanges_408_);
v___x_409_ = l_Lean_Meta_Instances_getClassChanges(v_d_402_, v_className_403_);
v_isSharedCheck_418_ = !lean_is_exclusive(v_d_402_);
if (v_isSharedCheck_418_ == 0)
{
lean_object* v_unused_419_; lean_object* v_unused_420_; lean_object* v_unused_421_; lean_object* v_unused_422_; 
v_unused_419_ = lean_ctor_get(v_d_402_, 3);
lean_dec(v_unused_419_);
v_unused_420_ = lean_ctor_get(v_d_402_, 2);
lean_dec(v_unused_420_);
v_unused_421_ = lean_ctor_get(v_d_402_, 1);
lean_dec(v_unused_421_);
v_unused_422_ = lean_ctor_get(v_d_402_, 0);
lean_dec(v_unused_422_);
v___x_411_ = v_d_402_;
v_isShared_412_ = v_isSharedCheck_418_;
goto v_resetjp_410_;
}
else
{
lean_dec(v_d_402_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_418_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_416_; 
v___x_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_413_, 0, v_c_404_);
lean_ctor_set(v___x_413_, 1, v___x_409_);
v___x_414_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0___redArg(v_classChanges_408_, v_className_403_, v___x_413_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 3, v___x_414_);
v___x_416_ = v___x_411_;
goto v_reusejp_415_;
}
else
{
lean_object* v_reuseFailAlloc_417_; 
v_reuseFailAlloc_417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_417_, 0, v_discrTree_405_);
lean_ctor_set(v_reuseFailAlloc_417_, 1, v_instanceNames_406_);
lean_ctor_set(v_reuseFailAlloc_417_, 2, v_erased_407_);
lean_ctor_set(v_reuseFailAlloc_417_, 3, v___x_414_);
v___x_416_ = v_reuseFailAlloc_417_;
goto v_reusejp_415_;
}
v_reusejp_415_:
{
return v___x_416_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0(lean_object* v_00_u03b2_423_, lean_object* v_x_424_, lean_object* v_x_425_, lean_object* v_x_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0___redArg(v_x_424_, v_x_425_, v_x_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0(lean_object* v_00_u03b2_428_, lean_object* v_x_429_, size_t v_x_430_, size_t v_x_431_, lean_object* v_x_432_, lean_object* v_x_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg(v_x_429_, v_x_430_, v_x_431_, v_x_432_, v_x_433_);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___boxed(lean_object* v_00_u03b2_435_, lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
size_t v_x_571__boxed_441_; size_t v_x_572__boxed_442_; lean_object* v_res_443_; 
v_x_571__boxed_441_ = lean_unbox_usize(v_x_437_);
lean_dec(v_x_437_);
v_x_572__boxed_442_ = lean_unbox_usize(v_x_438_);
lean_dec(v_x_438_);
v_res_443_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0(v_00_u03b2_435_, v_x_436_, v_x_571__boxed_441_, v_x_572__boxed_442_, v_x_439_, v_x_440_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_444_, lean_object* v_n_445_, lean_object* v_k_446_, lean_object* v_v_447_){
_start:
{
lean_object* v___x_448_; 
v___x_448_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__1___redArg(v_n_445_, v_k_446_, v_v_447_);
return v___x_448_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__2(lean_object* v_00_u03b2_449_, size_t v_depth_450_, lean_object* v_keys_451_, lean_object* v_vals_452_, lean_object* v_heq_453_, lean_object* v_i_454_, lean_object* v_entries_455_){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__2___redArg(v_depth_450_, v_keys_451_, v_vals_452_, v_i_454_, v_entries_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__2___boxed(lean_object* v_00_u03b2_457_, lean_object* v_depth_458_, lean_object* v_keys_459_, lean_object* v_vals_460_, lean_object* v_heq_461_, lean_object* v_i_462_, lean_object* v_entries_463_){
_start:
{
size_t v_depth_boxed_464_; lean_object* v_res_465_; 
v_depth_boxed_464_ = lean_unbox_usize(v_depth_458_);
lean_dec(v_depth_458_);
v_res_465_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__2(v_00_u03b2_457_, v_depth_boxed_464_, v_keys_459_, v_vals_460_, v_heq_461_, v_i_462_, v_entries_463_);
lean_dec_ref(v_vals_460_);
lean_dec_ref(v_keys_459_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_466_, lean_object* v_x_467_, lean_object* v_x_468_, lean_object* v_x_469_, lean_object* v_x_470_){
_start:
{
lean_object* v___x_471_; 
v___x_471_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0_spec__1_spec__2___redArg(v_x_467_, v_x_468_, v_x_469_, v_x_470_);
return v___x_471_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4_spec__10_spec__17(lean_object* v_xs_472_, lean_object* v_v_473_, lean_object* v_i_474_){
_start:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_array_get_size(v_xs_472_);
v___x_476_ = lean_nat_dec_lt(v_i_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
lean_dec(v_i_474_);
v___x_477_ = lean_box(0);
return v___x_477_;
}
else
{
lean_object* v___x_478_; uint8_t v___x_479_; 
v___x_478_ = lean_array_fget_borrowed(v_xs_472_, v_i_474_);
v___x_479_ = lean_name_eq(v___x_478_, v_v_473_);
if (v___x_479_ == 0)
{
lean_object* v___x_480_; lean_object* v___x_481_; 
v___x_480_ = lean_unsigned_to_nat(1u);
v___x_481_ = lean_nat_add(v_i_474_, v___x_480_);
lean_dec(v_i_474_);
v_i_474_ = v___x_481_;
goto _start;
}
else
{
lean_object* v___x_483_; 
v___x_483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_483_, 0, v_i_474_);
return v___x_483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4_spec__10_spec__17___boxed(lean_object* v_xs_484_, lean_object* v_v_485_, lean_object* v_i_486_){
_start:
{
lean_object* v_res_487_; 
v_res_487_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4_spec__10_spec__17(v_xs_484_, v_v_485_, v_i_486_);
lean_dec(v_v_485_);
lean_dec_ref(v_xs_484_);
return v_res_487_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4_spec__10(lean_object* v_xs_488_, lean_object* v_v_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4_spec__10_spec__17(v_xs_488_, v_v_489_, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4_spec__10___boxed(lean_object* v_xs_492_, lean_object* v_v_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4_spec__10(v_xs_492_, v_v_493_);
lean_dec(v_v_493_);
lean_dec_ref(v_xs_492_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4___redArg(lean_object* v_x_495_, size_t v_x_496_, lean_object* v_x_497_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_object* v_es_498_; lean_object* v___x_499_; size_t v___x_500_; size_t v___x_501_; lean_object* v_j_502_; lean_object* v_entry_503_; 
v_es_498_ = lean_ctor_get(v_x_495_, 0);
v___x_499_ = lean_box(2);
v___x_500_ = ((size_t)31ULL);
v___x_501_ = lean_usize_land(v_x_496_, v___x_500_);
v_j_502_ = lean_usize_to_nat(v___x_501_);
v_entry_503_ = lean_array_get(v___x_499_, v_es_498_, v_j_502_);
switch(lean_obj_tag(v_entry_503_))
{
case 0:
{
lean_object* v_key_504_; uint8_t v___x_505_; 
v_key_504_ = lean_ctor_get(v_entry_503_, 0);
lean_inc(v_key_504_);
lean_dec_ref_known(v_entry_503_, 2);
v___x_505_ = lean_name_eq(v_x_497_, v_key_504_);
lean_dec(v_key_504_);
if (v___x_505_ == 0)
{
lean_dec(v_j_502_);
return v_x_495_;
}
else
{
lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_513_; 
lean_inc_ref(v_es_498_);
v_isSharedCheck_513_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_513_ == 0)
{
lean_object* v_unused_514_; 
v_unused_514_ = lean_ctor_get(v_x_495_, 0);
lean_dec(v_unused_514_);
v___x_507_ = v_x_495_;
v_isShared_508_ = v_isSharedCheck_513_;
goto v_resetjp_506_;
}
else
{
lean_dec(v_x_495_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_513_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_509_; lean_object* v___x_511_; 
v___x_509_ = lean_array_set(v_es_498_, v_j_502_, v___x_499_);
lean_dec(v_j_502_);
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_509_);
v___x_511_ = v___x_507_;
goto v_reusejp_510_;
}
else
{
lean_object* v_reuseFailAlloc_512_; 
v_reuseFailAlloc_512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_512_, 0, v___x_509_);
v___x_511_ = v_reuseFailAlloc_512_;
goto v_reusejp_510_;
}
v_reusejp_510_:
{
return v___x_511_;
}
}
}
}
case 1:
{
lean_object* v___x_516_; uint8_t v_isShared_517_; uint8_t v_isSharedCheck_549_; 
lean_inc_ref(v_es_498_);
v_isSharedCheck_549_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v_x_495_, 0);
lean_dec(v_unused_550_);
v___x_516_ = v_x_495_;
v_isShared_517_ = v_isSharedCheck_549_;
goto v_resetjp_515_;
}
else
{
lean_dec(v_x_495_);
v___x_516_ = lean_box(0);
v_isShared_517_ = v_isSharedCheck_549_;
goto v_resetjp_515_;
}
v_resetjp_515_:
{
lean_object* v_node_518_; lean_object* v___x_520_; uint8_t v_isShared_521_; uint8_t v_isSharedCheck_548_; 
v_node_518_ = lean_ctor_get(v_entry_503_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v_entry_503_);
if (v_isSharedCheck_548_ == 0)
{
v___x_520_ = v_entry_503_;
v_isShared_521_ = v_isSharedCheck_548_;
goto v_resetjp_519_;
}
else
{
lean_inc(v_node_518_);
lean_dec(v_entry_503_);
v___x_520_ = lean_box(0);
v_isShared_521_ = v_isSharedCheck_548_;
goto v_resetjp_519_;
}
v_resetjp_519_:
{
size_t v___x_522_; lean_object* v_entries_523_; size_t v___x_524_; lean_object* v_newNode_525_; lean_object* v___x_526_; 
v___x_522_ = ((size_t)5ULL);
v_entries_523_ = lean_array_set(v_es_498_, v_j_502_, v___x_499_);
v___x_524_ = lean_usize_shift_right(v_x_496_, v___x_522_);
v_newNode_525_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4___redArg(v_node_518_, v___x_524_, v_x_497_);
lean_inc_ref(v_newNode_525_);
v___x_526_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_525_);
if (lean_obj_tag(v___x_526_) == 0)
{
lean_object* v___x_528_; 
if (v_isShared_521_ == 0)
{
lean_ctor_set(v___x_520_, 0, v_newNode_525_);
v___x_528_ = v___x_520_;
goto v_reusejp_527_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_newNode_525_);
v___x_528_ = v_reuseFailAlloc_533_;
goto v_reusejp_527_;
}
v_reusejp_527_:
{
lean_object* v___x_529_; lean_object* v___x_531_; 
v___x_529_ = lean_array_set(v_entries_523_, v_j_502_, v___x_528_);
lean_dec(v_j_502_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_529_);
v___x_531_ = v___x_516_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_532_; 
v_reuseFailAlloc_532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_532_, 0, v___x_529_);
v___x_531_ = v_reuseFailAlloc_532_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
return v___x_531_;
}
}
}
else
{
lean_object* v_val_534_; lean_object* v_fst_535_; lean_object* v_snd_536_; lean_object* v___x_538_; uint8_t v_isShared_539_; uint8_t v_isSharedCheck_547_; 
lean_dec_ref(v_newNode_525_);
lean_del_object(v___x_520_);
v_val_534_ = lean_ctor_get(v___x_526_, 0);
lean_inc(v_val_534_);
lean_dec_ref_known(v___x_526_, 1);
v_fst_535_ = lean_ctor_get(v_val_534_, 0);
v_snd_536_ = lean_ctor_get(v_val_534_, 1);
v_isSharedCheck_547_ = !lean_is_exclusive(v_val_534_);
if (v_isSharedCheck_547_ == 0)
{
v___x_538_ = v_val_534_;
v_isShared_539_ = v_isSharedCheck_547_;
goto v_resetjp_537_;
}
else
{
lean_inc(v_snd_536_);
lean_inc(v_fst_535_);
lean_dec(v_val_534_);
v___x_538_ = lean_box(0);
v_isShared_539_ = v_isSharedCheck_547_;
goto v_resetjp_537_;
}
v_resetjp_537_:
{
lean_object* v___x_541_; 
if (v_isShared_539_ == 0)
{
v___x_541_ = v___x_538_;
goto v_reusejp_540_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v_fst_535_);
lean_ctor_set(v_reuseFailAlloc_546_, 1, v_snd_536_);
v___x_541_ = v_reuseFailAlloc_546_;
goto v_reusejp_540_;
}
v_reusejp_540_:
{
lean_object* v___x_542_; lean_object* v___x_544_; 
v___x_542_ = lean_array_set(v_entries_523_, v_j_502_, v___x_541_);
lean_dec(v_j_502_);
if (v_isShared_517_ == 0)
{
lean_ctor_set(v___x_516_, 0, v___x_542_);
v___x_544_ = v___x_516_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_545_; 
v_reuseFailAlloc_545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_545_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_545_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
return v___x_544_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_502_);
return v_x_495_;
}
}
}
else
{
lean_object* v_ks_551_; lean_object* v_vs_552_; lean_object* v___x_554_; uint8_t v_isShared_555_; uint8_t v_isSharedCheck_566_; 
v_ks_551_ = lean_ctor_get(v_x_495_, 0);
v_vs_552_ = lean_ctor_get(v_x_495_, 1);
v_isSharedCheck_566_ = !lean_is_exclusive(v_x_495_);
if (v_isSharedCheck_566_ == 0)
{
v___x_554_ = v_x_495_;
v_isShared_555_ = v_isSharedCheck_566_;
goto v_resetjp_553_;
}
else
{
lean_inc(v_vs_552_);
lean_inc(v_ks_551_);
lean_dec(v_x_495_);
v___x_554_ = lean_box(0);
v_isShared_555_ = v_isSharedCheck_566_;
goto v_resetjp_553_;
}
v_resetjp_553_:
{
lean_object* v___x_556_; 
v___x_556_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4_spec__10(v_ks_551_, v_x_497_);
if (lean_obj_tag(v___x_556_) == 0)
{
lean_object* v___x_558_; 
if (v_isShared_555_ == 0)
{
v___x_558_ = v___x_554_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_559_; 
v_reuseFailAlloc_559_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_559_, 0, v_ks_551_);
lean_ctor_set(v_reuseFailAlloc_559_, 1, v_vs_552_);
v___x_558_ = v_reuseFailAlloc_559_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
return v___x_558_;
}
}
else
{
lean_object* v_val_560_; lean_object* v_keys_x27_561_; lean_object* v_vals_x27_562_; lean_object* v___x_564_; 
v_val_560_ = lean_ctor_get(v___x_556_, 0);
lean_inc_n(v_val_560_, 2);
lean_dec_ref_known(v___x_556_, 1);
v_keys_x27_561_ = l_Array_eraseIdx___redArg(v_ks_551_, v_val_560_);
v_vals_x27_562_ = l_Array_eraseIdx___redArg(v_vs_552_, v_val_560_);
if (v_isShared_555_ == 0)
{
lean_ctor_set(v___x_554_, 1, v_vals_x27_562_);
lean_ctor_set(v___x_554_, 0, v_keys_x27_561_);
v___x_564_ = v___x_554_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_keys_x27_561_);
lean_ctor_set(v_reuseFailAlloc_565_, 1, v_vals_x27_562_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
return v___x_564_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4___redArg___boxed(lean_object* v_x_567_, lean_object* v_x_568_, lean_object* v_x_569_){
_start:
{
size_t v_x_2778__boxed_570_; lean_object* v_res_571_; 
v_x_2778__boxed_570_ = lean_unbox_usize(v_x_568_);
lean_dec(v_x_568_);
v_res_571_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4___redArg(v_x_567_, v_x_2778__boxed_570_, v_x_569_);
lean_dec(v_x_569_);
return v_res_571_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1___redArg(lean_object* v_x_572_, lean_object* v_x_573_){
_start:
{
uint64_t v___y_575_; 
if (lean_obj_tag(v_x_573_) == 0)
{
uint64_t v___x_578_; 
v___x_578_ = 1723ULL;
v___y_575_ = v___x_578_;
goto v___jp_574_;
}
else
{
uint64_t v_hash_579_; 
v_hash_579_ = lean_ctor_get_uint64(v_x_573_, sizeof(void*)*2);
v___y_575_ = v_hash_579_;
goto v___jp_574_;
}
v___jp_574_:
{
size_t v_h_576_; lean_object* v___x_577_; 
v_h_576_ = lean_uint64_to_usize(v___y_575_);
v___x_577_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4___redArg(v_x_572_, v_h_576_, v_x_573_);
return v___x_577_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1___redArg___boxed(lean_object* v_x_580_, lean_object* v_x_581_){
_start:
{
lean_object* v_res_582_; 
v_res_582_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1___redArg(v_x_580_, v_x_581_);
lean_dec(v_x_581_);
return v_res_582_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__13_spec__15___redArg(lean_object* v_x_583_, lean_object* v_x_584_, lean_object* v_x_585_, lean_object* v_x_586_){
_start:
{
lean_object* v_ks_587_; lean_object* v_vs_588_; lean_object* v___x_590_; uint8_t v_isShared_591_; uint8_t v_isSharedCheck_612_; 
v_ks_587_ = lean_ctor_get(v_x_583_, 0);
v_vs_588_ = lean_ctor_get(v_x_583_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_x_583_);
if (v_isSharedCheck_612_ == 0)
{
v___x_590_ = v_x_583_;
v_isShared_591_ = v_isSharedCheck_612_;
goto v_resetjp_589_;
}
else
{
lean_inc(v_vs_588_);
lean_inc(v_ks_587_);
lean_dec(v_x_583_);
v___x_590_ = lean_box(0);
v_isShared_591_ = v_isSharedCheck_612_;
goto v_resetjp_589_;
}
v_resetjp_589_:
{
lean_object* v___x_592_; uint8_t v___x_593_; 
v___x_592_ = lean_array_get_size(v_ks_587_);
v___x_593_ = lean_nat_dec_lt(v_x_584_, v___x_592_);
if (v___x_593_ == 0)
{
lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_597_; 
lean_dec(v_x_584_);
v___x_594_ = lean_array_push(v_ks_587_, v_x_585_);
v___x_595_ = lean_array_push(v_vs_588_, v_x_586_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_595_);
lean_ctor_set(v___x_590_, 0, v___x_594_);
v___x_597_ = v___x_590_;
goto v_reusejp_596_;
}
else
{
lean_object* v_reuseFailAlloc_598_; 
v_reuseFailAlloc_598_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_598_, 0, v___x_594_);
lean_ctor_set(v_reuseFailAlloc_598_, 1, v___x_595_);
v___x_597_ = v_reuseFailAlloc_598_;
goto v_reusejp_596_;
}
v_reusejp_596_:
{
return v___x_597_;
}
}
else
{
lean_object* v_k_x27_599_; uint8_t v___x_600_; 
v_k_x27_599_ = lean_array_fget_borrowed(v_ks_587_, v_x_584_);
v___x_600_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_585_, v_k_x27_599_);
if (v___x_600_ == 0)
{
lean_object* v___x_602_; 
if (v_isShared_591_ == 0)
{
v___x_602_ = v___x_590_;
goto v_reusejp_601_;
}
else
{
lean_object* v_reuseFailAlloc_606_; 
v_reuseFailAlloc_606_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_606_, 0, v_ks_587_);
lean_ctor_set(v_reuseFailAlloc_606_, 1, v_vs_588_);
v___x_602_ = v_reuseFailAlloc_606_;
goto v_reusejp_601_;
}
v_reusejp_601_:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = lean_unsigned_to_nat(1u);
v___x_604_ = lean_nat_add(v_x_584_, v___x_603_);
lean_dec(v_x_584_);
v_x_583_ = v___x_602_;
v_x_584_ = v___x_604_;
goto _start;
}
}
else
{
lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_610_; 
v___x_607_ = lean_array_fset(v_ks_587_, v_x_584_, v_x_585_);
v___x_608_ = lean_array_fset(v_vs_588_, v_x_584_, v_x_586_);
lean_dec(v_x_584_);
if (v_isShared_591_ == 0)
{
lean_ctor_set(v___x_590_, 1, v___x_608_);
lean_ctor_set(v___x_590_, 0, v___x_607_);
v___x_610_ = v___x_590_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v___x_607_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v___x_608_);
v___x_610_ = v_reuseFailAlloc_611_;
goto v_reusejp_609_;
}
v_reusejp_609_:
{
return v___x_610_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__13___redArg(lean_object* v_n_613_, lean_object* v_k_614_, lean_object* v_v_615_){
_start:
{
lean_object* v___x_616_; lean_object* v___x_617_; 
v___x_616_ = lean_unsigned_to_nat(0u);
v___x_617_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__13_spec__15___redArg(v_n_613_, v___x_616_, v_k_614_, v_v_615_);
return v___x_617_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6___redArg(lean_object* v_x_618_, size_t v_x_619_, size_t v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_){
_start:
{
if (lean_obj_tag(v_x_618_) == 0)
{
lean_object* v_es_623_; size_t v___x_624_; size_t v___x_625_; lean_object* v_j_626_; lean_object* v___x_627_; uint8_t v___x_628_; 
v_es_623_ = lean_ctor_get(v_x_618_, 0);
v___x_624_ = ((size_t)31ULL);
v___x_625_ = lean_usize_land(v_x_619_, v___x_624_);
v_j_626_ = lean_usize_to_nat(v___x_625_);
v___x_627_ = lean_array_get_size(v_es_623_);
v___x_628_ = lean_nat_dec_lt(v_j_626_, v___x_627_);
if (v___x_628_ == 0)
{
lean_dec(v_j_626_);
lean_dec(v_x_622_);
lean_dec(v_x_621_);
return v_x_618_;
}
else
{
lean_object* v___x_630_; uint8_t v_isShared_631_; uint8_t v_isSharedCheck_667_; 
lean_inc_ref(v_es_623_);
v_isSharedCheck_667_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v_x_618_, 0);
lean_dec(v_unused_668_);
v___x_630_ = v_x_618_;
v_isShared_631_ = v_isSharedCheck_667_;
goto v_resetjp_629_;
}
else
{
lean_dec(v_x_618_);
v___x_630_ = lean_box(0);
v_isShared_631_ = v_isSharedCheck_667_;
goto v_resetjp_629_;
}
v_resetjp_629_:
{
lean_object* v_v_632_; lean_object* v___x_633_; lean_object* v_xs_x27_634_; lean_object* v___y_636_; 
v_v_632_ = lean_array_fget(v_es_623_, v_j_626_);
v___x_633_ = lean_box(0);
v_xs_x27_634_ = lean_array_fset(v_es_623_, v_j_626_, v___x_633_);
switch(lean_obj_tag(v_v_632_))
{
case 0:
{
lean_object* v_key_641_; lean_object* v_val_642_; lean_object* v___x_644_; uint8_t v_isShared_645_; uint8_t v_isSharedCheck_652_; 
v_key_641_ = lean_ctor_get(v_v_632_, 0);
v_val_642_ = lean_ctor_get(v_v_632_, 1);
v_isSharedCheck_652_ = !lean_is_exclusive(v_v_632_);
if (v_isSharedCheck_652_ == 0)
{
v___x_644_ = v_v_632_;
v_isShared_645_ = v_isSharedCheck_652_;
goto v_resetjp_643_;
}
else
{
lean_inc(v_val_642_);
lean_inc(v_key_641_);
lean_dec(v_v_632_);
v___x_644_ = lean_box(0);
v_isShared_645_ = v_isSharedCheck_652_;
goto v_resetjp_643_;
}
v_resetjp_643_:
{
uint8_t v___x_646_; 
v___x_646_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_621_, v_key_641_);
if (v___x_646_ == 0)
{
lean_object* v___x_647_; lean_object* v___x_648_; 
lean_del_object(v___x_644_);
v___x_647_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_641_, v_val_642_, v_x_621_, v_x_622_);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
v___y_636_ = v___x_648_;
goto v___jp_635_;
}
else
{
lean_object* v___x_650_; 
lean_dec(v_val_642_);
lean_dec(v_key_641_);
if (v_isShared_645_ == 0)
{
lean_ctor_set(v___x_644_, 1, v_x_622_);
lean_ctor_set(v___x_644_, 0, v_x_621_);
v___x_650_ = v___x_644_;
goto v_reusejp_649_;
}
else
{
lean_object* v_reuseFailAlloc_651_; 
v_reuseFailAlloc_651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_651_, 0, v_x_621_);
lean_ctor_set(v_reuseFailAlloc_651_, 1, v_x_622_);
v___x_650_ = v_reuseFailAlloc_651_;
goto v_reusejp_649_;
}
v_reusejp_649_:
{
v___y_636_ = v___x_650_;
goto v___jp_635_;
}
}
}
}
case 1:
{
lean_object* v_node_653_; lean_object* v___x_655_; uint8_t v_isShared_656_; uint8_t v_isSharedCheck_665_; 
v_node_653_ = lean_ctor_get(v_v_632_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_v_632_);
if (v_isSharedCheck_665_ == 0)
{
v___x_655_ = v_v_632_;
v_isShared_656_ = v_isSharedCheck_665_;
goto v_resetjp_654_;
}
else
{
lean_inc(v_node_653_);
lean_dec(v_v_632_);
v___x_655_ = lean_box(0);
v_isShared_656_ = v_isSharedCheck_665_;
goto v_resetjp_654_;
}
v_resetjp_654_:
{
size_t v___x_657_; size_t v___x_658_; size_t v___x_659_; size_t v___x_660_; lean_object* v___x_661_; lean_object* v___x_663_; 
v___x_657_ = ((size_t)5ULL);
v___x_658_ = lean_usize_shift_right(v_x_619_, v___x_657_);
v___x_659_ = ((size_t)1ULL);
v___x_660_ = lean_usize_add(v_x_620_, v___x_659_);
v___x_661_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6___redArg(v_node_653_, v___x_658_, v___x_660_, v_x_621_, v_x_622_);
if (v_isShared_656_ == 0)
{
lean_ctor_set(v___x_655_, 0, v___x_661_);
v___x_663_ = v___x_655_;
goto v_reusejp_662_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_661_);
v___x_663_ = v_reuseFailAlloc_664_;
goto v_reusejp_662_;
}
v_reusejp_662_:
{
v___y_636_ = v___x_663_;
goto v___jp_635_;
}
}
}
default: 
{
lean_object* v___x_666_; 
v___x_666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_666_, 0, v_x_621_);
lean_ctor_set(v___x_666_, 1, v_x_622_);
v___y_636_ = v___x_666_;
goto v___jp_635_;
}
}
v___jp_635_:
{
lean_object* v___x_637_; lean_object* v___x_639_; 
v___x_637_ = lean_array_fset(v_xs_x27_634_, v_j_626_, v___y_636_);
lean_dec(v_j_626_);
if (v_isShared_631_ == 0)
{
lean_ctor_set(v___x_630_, 0, v___x_637_);
v___x_639_ = v___x_630_;
goto v_reusejp_638_;
}
else
{
lean_object* v_reuseFailAlloc_640_; 
v_reuseFailAlloc_640_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_640_, 0, v___x_637_);
v___x_639_ = v_reuseFailAlloc_640_;
goto v_reusejp_638_;
}
v_reusejp_638_:
{
return v___x_639_;
}
}
}
}
}
else
{
lean_object* v_ks_669_; lean_object* v_vs_670_; lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_688_; 
v_ks_669_ = lean_ctor_get(v_x_618_, 0);
v_vs_670_ = lean_ctor_get(v_x_618_, 1);
v_isSharedCheck_688_ = !lean_is_exclusive(v_x_618_);
if (v_isSharedCheck_688_ == 0)
{
v___x_672_ = v_x_618_;
v_isShared_673_ = v_isSharedCheck_688_;
goto v_resetjp_671_;
}
else
{
lean_inc(v_vs_670_);
lean_inc(v_ks_669_);
lean_dec(v_x_618_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_688_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v___x_675_; 
if (v_isShared_673_ == 0)
{
v___x_675_ = v___x_672_;
goto v_reusejp_674_;
}
else
{
lean_object* v_reuseFailAlloc_687_; 
v_reuseFailAlloc_687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_687_, 0, v_ks_669_);
lean_ctor_set(v_reuseFailAlloc_687_, 1, v_vs_670_);
v___x_675_ = v_reuseFailAlloc_687_;
goto v_reusejp_674_;
}
v_reusejp_674_:
{
lean_object* v_newNode_676_; size_t v___x_677_; uint8_t v___x_678_; 
v_newNode_676_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__13___redArg(v___x_675_, v_x_621_, v_x_622_);
v___x_677_ = ((size_t)7ULL);
v___x_678_ = lean_usize_dec_le(v___x_677_, v_x_620_);
if (v___x_678_ == 0)
{
lean_object* v___x_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v___x_679_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_676_);
v___x_680_ = lean_unsigned_to_nat(4u);
v___x_681_ = lean_nat_dec_lt(v___x_679_, v___x_680_);
lean_dec(v___x_679_);
if (v___x_681_ == 0)
{
lean_object* v_ks_682_; lean_object* v_vs_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; 
v_ks_682_ = lean_ctor_get(v_newNode_676_, 0);
lean_inc_ref(v_ks_682_);
v_vs_683_ = lean_ctor_get(v_newNode_676_, 1);
lean_inc_ref(v_vs_683_);
lean_dec_ref(v_newNode_676_);
v___x_684_ = lean_unsigned_to_nat(0u);
v___x_685_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___closed__0);
v___x_686_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__14___redArg(v_x_620_, v_ks_682_, v_vs_683_, v___x_684_, v___x_685_);
lean_dec_ref(v_vs_683_);
lean_dec_ref(v_ks_682_);
return v___x_686_;
}
else
{
return v_newNode_676_;
}
}
else
{
return v_newNode_676_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__14___redArg(size_t v_depth_689_, lean_object* v_keys_690_, lean_object* v_vals_691_, lean_object* v_i_692_, lean_object* v_entries_693_){
_start:
{
lean_object* v___x_694_; uint8_t v___x_695_; 
v___x_694_ = lean_array_get_size(v_keys_690_);
v___x_695_ = lean_nat_dec_lt(v_i_692_, v___x_694_);
if (v___x_695_ == 0)
{
lean_dec(v_i_692_);
return v_entries_693_;
}
else
{
lean_object* v_k_696_; lean_object* v_v_697_; uint64_t v___x_698_; size_t v_h_699_; size_t v___x_700_; lean_object* v___x_701_; size_t v___x_702_; size_t v___x_703_; size_t v___x_704_; size_t v_h_705_; lean_object* v___x_706_; lean_object* v___x_707_; 
v_k_696_ = lean_array_fget_borrowed(v_keys_690_, v_i_692_);
v_v_697_ = lean_array_fget_borrowed(v_vals_691_, v_i_692_);
v___x_698_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_696_);
v_h_699_ = lean_uint64_to_usize(v___x_698_);
v___x_700_ = ((size_t)5ULL);
v___x_701_ = lean_unsigned_to_nat(1u);
v___x_702_ = ((size_t)1ULL);
v___x_703_ = lean_usize_sub(v_depth_689_, v___x_702_);
v___x_704_ = lean_usize_mul(v___x_700_, v___x_703_);
v_h_705_ = lean_usize_shift_right(v_h_699_, v___x_704_);
v___x_706_ = lean_nat_add(v_i_692_, v___x_701_);
lean_dec(v_i_692_);
lean_inc(v_v_697_);
lean_inc(v_k_696_);
v___x_707_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6___redArg(v_entries_693_, v_h_705_, v_depth_689_, v_k_696_, v_v_697_);
v_i_692_ = v___x_706_;
v_entries_693_ = v___x_707_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__14___redArg___boxed(lean_object* v_depth_709_, lean_object* v_keys_710_, lean_object* v_vals_711_, lean_object* v_i_712_, lean_object* v_entries_713_){
_start:
{
size_t v_depth_boxed_714_; lean_object* v_res_715_; 
v_depth_boxed_714_ = lean_unbox_usize(v_depth_709_);
lean_dec(v_depth_709_);
v_res_715_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__14___redArg(v_depth_boxed_714_, v_keys_710_, v_vals_711_, v_i_712_, v_entries_713_);
lean_dec_ref(v_vals_711_);
lean_dec_ref(v_keys_710_);
return v_res_715_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6___redArg___boxed(lean_object* v_x_716_, lean_object* v_x_717_, lean_object* v_x_718_, lean_object* v_x_719_, lean_object* v_x_720_){
_start:
{
size_t v_x_3003__boxed_721_; size_t v_x_3004__boxed_722_; lean_object* v_res_723_; 
v_x_3003__boxed_721_ = lean_unbox_usize(v_x_717_);
lean_dec(v_x_717_);
v_x_3004__boxed_722_ = lean_unbox_usize(v_x_718_);
lean_dec(v_x_718_);
v_res_723_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6___redArg(v_x_716_, v_x_3003__boxed_721_, v_x_3004__boxed_722_, v_x_719_, v_x_720_);
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__5_spec__11(lean_object* v_xs_724_, lean_object* v_v_725_, lean_object* v_i_726_){
_start:
{
lean_object* v___x_727_; uint8_t v___x_728_; 
v___x_727_ = lean_array_get_size(v_xs_724_);
v___x_728_ = lean_nat_dec_lt(v_i_726_, v___x_727_);
if (v___x_728_ == 0)
{
lean_object* v___x_729_; 
lean_dec(v_i_726_);
v___x_729_ = lean_box(0);
return v___x_729_;
}
else
{
lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_730_ = lean_array_fget_borrowed(v_xs_724_, v_i_726_);
v___x_731_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_730_, v_v_725_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = lean_unsigned_to_nat(1u);
v___x_733_ = lean_nat_add(v_i_726_, v___x_732_);
lean_dec(v_i_726_);
v_i_726_ = v___x_733_;
goto _start;
}
else
{
lean_object* v___x_735_; 
v___x_735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_735_, 0, v_i_726_);
return v___x_735_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__5_spec__11___boxed(lean_object* v_xs_736_, lean_object* v_v_737_, lean_object* v_i_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__5_spec__11(v_xs_736_, v_v_737_, v_i_738_);
lean_dec(v_v_737_);
lean_dec_ref(v_xs_736_);
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__5(lean_object* v_xs_740_, lean_object* v_v_741_){
_start:
{
lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__5_spec__11(v_xs_740_, v_v_741_, v___x_742_);
return v___x_743_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__5___boxed(lean_object* v_xs_744_, lean_object* v_v_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__5(v_xs_744_, v_v_745_);
lean_dec(v_v_745_);
lean_dec_ref(v_xs_744_);
return v_res_746_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(lean_object* v_a_747_, lean_object* v_b_748_){
_start:
{
lean_object* v_fst_749_; lean_object* v_fst_750_; uint8_t v___x_751_; 
v_fst_749_ = lean_ctor_get(v_a_747_, 0);
v_fst_750_ = lean_ctor_get(v_b_748_, 0);
v___x_751_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_749_, v_fst_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0___boxed(lean_object* v_a_752_, lean_object* v_b_753_){
_start:
{
uint8_t v_res_754_; lean_object* v_r_755_; 
v_res_754_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_a_752_, v_b_753_);
lean_dec_ref(v_b_753_);
lean_dec_ref(v_a_752_);
v_r_755_ = lean_box(v_res_754_);
return v_r_755_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__0(lean_object* v_x_756_, lean_object* v_keys_757_, lean_object* v_v_758_, lean_object* v_k_759_, lean_object* v_x_760_){
_start:
{
lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v_c_763_; lean_object* v___x_764_; 
v___x_761_ = lean_unsigned_to_nat(1u);
v___x_762_ = lean_nat_add(v_x_756_, v___x_761_);
v_c_763_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_757_, v_v_758_, v___x_762_);
lean_dec(v___x_762_);
v___x_764_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_764_, 0, v_k_759_);
lean_ctor_set(v___x_764_, 1, v_c_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__0___boxed(lean_object* v_x_765_, lean_object* v_keys_766_, lean_object* v_v_767_, lean_object* v_k_768_, lean_object* v_x_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__0(v_x_765_, v_keys_766_, v_v_767_, v_k_768_, v_x_769_);
lean_dec_ref(v_keys_766_);
lean_dec(v_x_765_);
return v_res_770_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__2_spec__6(lean_object* v_vs_771_, lean_object* v_v_772_, lean_object* v_i_773_){
_start:
{
lean_object* v___x_774_; uint8_t v___x_775_; 
v___x_774_ = lean_array_get_size(v_vs_771_);
v___x_775_ = lean_nat_dec_lt(v_i_773_, v___x_774_);
if (v___x_775_ == 0)
{
lean_object* v___x_776_; 
lean_dec(v_i_773_);
v___x_776_ = lean_array_push(v_vs_771_, v_v_772_);
return v___x_776_;
}
else
{
lean_object* v_val_777_; lean_object* v___x_778_; lean_object* v_val_779_; uint8_t v___x_780_; 
v_val_777_ = lean_ctor_get(v_v_772_, 1);
v___x_778_ = lean_array_fget_borrowed(v_vs_771_, v_i_773_);
v_val_779_ = lean_ctor_get(v___x_778_, 1);
v___x_780_ = lean_expr_eqv(v_val_777_, v_val_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; lean_object* v___x_782_; 
v___x_781_ = lean_unsigned_to_nat(1u);
v___x_782_ = lean_nat_add(v_i_773_, v___x_781_);
lean_dec(v_i_773_);
v_i_773_ = v___x_782_;
goto _start;
}
else
{
lean_object* v___x_784_; 
v___x_784_ = lean_array_fset(v_vs_771_, v_i_773_, v_v_772_);
lean_dec(v_i_773_);
return v___x_784_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__2(lean_object* v_vs_785_, lean_object* v_v_786_){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__2_spec__6(v_vs_785_, v_v_786_, v___x_787_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1_spec__4___redArg(lean_object* v___x_789_, lean_object* v_as_790_, lean_object* v_k_791_, lean_object* v_x_792_, lean_object* v_x_793_){
_start:
{
lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v_mid_796_; lean_object* v_midVal_797_; uint8_t v___x_798_; 
v___x_794_ = lean_nat_add(v_x_792_, v_x_793_);
v___x_795_ = lean_unsigned_to_nat(1u);
v_mid_796_ = lean_nat_shiftr(v___x_794_, v___x_795_);
lean_dec(v___x_794_);
v_midVal_797_ = lean_array_fget_borrowed(v_as_790_, v_mid_796_);
v___x_798_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_midVal_797_, v_k_791_);
if (v___x_798_ == 0)
{
uint8_t v___x_799_; 
lean_dec(v_x_793_);
v___x_799_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_k_791_, v_midVal_797_);
if (v___x_799_ == 0)
{
lean_object* v___x_800_; uint8_t v___x_801_; 
lean_dec(v_x_792_);
v___x_800_ = lean_array_get_size(v_as_790_);
v___x_801_ = lean_nat_dec_lt(v_mid_796_, v___x_800_);
if (v___x_801_ == 0)
{
lean_dec(v_mid_796_);
lean_dec_ref(v___x_789_);
return v_as_790_;
}
else
{
lean_object* v___x_802_; lean_object* v_xs_x27_803_; lean_object* v___x_804_; 
v___x_802_ = lean_box(0);
v_xs_x27_803_ = lean_array_fset(v_as_790_, v_mid_796_, v___x_802_);
v___x_804_ = lean_array_fset(v_xs_x27_803_, v_mid_796_, v___x_789_);
lean_dec(v_mid_796_);
return v___x_804_;
}
}
else
{
v_x_793_ = v_mid_796_;
goto _start;
}
}
else
{
uint8_t v___x_806_; 
v___x_806_ = lean_nat_dec_eq(v_mid_796_, v_x_792_);
if (v___x_806_ == 0)
{
lean_dec(v_x_792_);
v_x_792_ = v_mid_796_;
goto _start;
}
else
{
lean_object* v___x_808_; lean_object* v_j_809_; lean_object* v_as_810_; lean_object* v___x_811_; 
lean_dec(v_mid_796_);
lean_dec(v_x_793_);
v___x_808_ = lean_nat_add(v_x_792_, v___x_795_);
lean_dec(v_x_792_);
v_j_809_ = lean_array_get_size(v_as_790_);
v_as_810_ = lean_array_push(v_as_790_, v___x_789_);
v___x_811_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_808_, v_as_810_, v_j_809_);
lean_dec(v___x_808_);
return v___x_811_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1_spec__4___redArg___boxed(lean_object* v___x_812_, lean_object* v_as_813_, lean_object* v_k_814_, lean_object* v_x_815_, lean_object* v_x_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1_spec__4___redArg(v___x_812_, v_as_813_, v_k_814_, v_x_815_, v_x_816_);
lean_dec_ref(v_k_814_);
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1(lean_object* v___x_818_, lean_object* v_as_819_, lean_object* v_k_820_){
_start:
{
lean_object* v___x_821_; lean_object* v___x_822_; uint8_t v___x_823_; 
v___x_821_ = lean_array_get_size(v_as_819_);
v___x_822_ = lean_unsigned_to_nat(0u);
v___x_823_ = lean_nat_dec_eq(v___x_821_, v___x_822_);
if (v___x_823_ == 0)
{
lean_object* v___x_824_; uint8_t v___x_825_; 
v___x_824_ = lean_array_fget_borrowed(v_as_819_, v___x_822_);
v___x_825_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_k_820_, v___x_824_);
if (v___x_825_ == 0)
{
uint8_t v___x_826_; 
v___x_826_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v___x_824_, v_k_820_);
if (v___x_826_ == 0)
{
uint8_t v___x_827_; 
v___x_827_ = lean_nat_dec_lt(v___x_822_, v___x_821_);
if (v___x_827_ == 0)
{
lean_dec_ref(v___x_818_);
return v_as_819_;
}
else
{
lean_object* v___x_828_; lean_object* v_xs_x27_829_; lean_object* v___x_830_; 
v___x_828_ = lean_box(0);
v_xs_x27_829_ = lean_array_fset(v_as_819_, v___x_822_, v___x_828_);
v___x_830_ = lean_array_fset(v_xs_x27_829_, v___x_822_, v___x_818_);
return v___x_830_;
}
}
else
{
lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_831_ = lean_unsigned_to_nat(1u);
v___x_832_ = lean_nat_sub(v___x_821_, v___x_831_);
v___x_833_ = lean_array_fget_borrowed(v_as_819_, v___x_832_);
v___x_834_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v___x_833_, v_k_820_);
if (v___x_834_ == 0)
{
uint8_t v___x_835_; 
v___x_835_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_k_820_, v___x_833_);
if (v___x_835_ == 0)
{
uint8_t v___x_836_; 
v___x_836_ = lean_nat_dec_lt(v___x_832_, v___x_821_);
if (v___x_836_ == 0)
{
lean_dec(v___x_832_);
lean_dec_ref(v___x_818_);
return v_as_819_;
}
else
{
lean_object* v___x_837_; lean_object* v_xs_x27_838_; lean_object* v___x_839_; 
v___x_837_ = lean_box(0);
v_xs_x27_838_ = lean_array_fset(v_as_819_, v___x_832_, v___x_837_);
v___x_839_ = lean_array_fset(v_xs_x27_838_, v___x_832_, v___x_818_);
lean_dec(v___x_832_);
return v___x_839_;
}
}
else
{
lean_object* v___x_840_; 
v___x_840_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1_spec__4___redArg(v___x_818_, v_as_819_, v_k_820_, v___x_822_, v___x_832_);
return v___x_840_;
}
}
else
{
lean_object* v___x_841_; 
lean_dec(v___x_832_);
v___x_841_ = lean_array_push(v_as_819_, v___x_818_);
return v___x_841_;
}
}
}
else
{
lean_object* v_as_842_; lean_object* v___x_843_; 
v_as_842_ = lean_array_push(v_as_819_, v___x_818_);
v___x_843_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_822_, v_as_842_, v___x_821_);
return v___x_843_;
}
}
else
{
lean_object* v___x_844_; 
v___x_844_ = lean_array_push(v_as_819_, v___x_818_);
return v___x_844_;
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___boxed(lean_object* v___x_845_, lean_object* v_as_846_, lean_object* v_k_847_){
_start:
{
lean_object* v_res_848_; 
v_res_848_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1(v___x_845_, v_as_846_, v_k_847_);
lean_dec_ref(v_k_847_);
return v_res_848_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3_spec__8___redArg(lean_object* v_x_853_, lean_object* v_keys_854_, lean_object* v_v_855_, lean_object* v_k_856_, lean_object* v_as_857_, lean_object* v_k_858_, lean_object* v_x_859_, lean_object* v_x_860_){
_start:
{
lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v_mid_863_; lean_object* v_midVal_864_; uint8_t v___x_865_; 
v___x_861_ = lean_nat_add(v_x_859_, v_x_860_);
v___x_862_ = lean_unsigned_to_nat(1u);
v_mid_863_ = lean_nat_shiftr(v___x_861_, v___x_862_);
lean_dec(v___x_861_);
v_midVal_864_ = lean_array_fget(v_as_857_, v_mid_863_);
v___x_865_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_midVal_864_, v_k_858_);
if (v___x_865_ == 0)
{
uint8_t v___x_866_; 
lean_dec(v_x_860_);
v___x_866_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_k_858_, v_midVal_864_);
if (v___x_866_ == 0)
{
lean_object* v___x_867_; uint8_t v___x_868_; 
lean_dec(v_x_859_);
v___x_867_ = lean_array_get_size(v_as_857_);
v___x_868_ = lean_nat_dec_lt(v_mid_863_, v___x_867_);
if (v___x_868_ == 0)
{
lean_dec(v_midVal_864_);
lean_dec(v_mid_863_);
lean_dec(v_k_856_);
lean_dec_ref(v_v_855_);
return v_as_857_;
}
else
{
lean_object* v_snd_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_881_; 
v_snd_869_ = lean_ctor_get(v_midVal_864_, 1);
v_isSharedCheck_881_ = !lean_is_exclusive(v_midVal_864_);
if (v_isSharedCheck_881_ == 0)
{
lean_object* v_unused_882_; 
v_unused_882_ = lean_ctor_get(v_midVal_864_, 0);
lean_dec(v_unused_882_);
v___x_871_ = v_midVal_864_;
v_isShared_872_ = v_isSharedCheck_881_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_snd_869_);
lean_dec(v_midVal_864_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_881_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; lean_object* v_xs_x27_874_; lean_object* v___x_875_; lean_object* v_c_876_; lean_object* v___x_878_; 
v___x_873_ = lean_box(0);
v_xs_x27_874_ = lean_array_fset(v_as_857_, v_mid_863_, v___x_873_);
v___x_875_ = lean_nat_add(v_x_853_, v___x_862_);
v_c_876_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0(v_keys_854_, v_v_855_, v___x_875_, v_snd_869_);
lean_dec(v___x_875_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v_c_876_);
lean_ctor_set(v___x_871_, 0, v_k_856_);
v___x_878_ = v___x_871_;
goto v_reusejp_877_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_k_856_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v_c_876_);
v___x_878_ = v_reuseFailAlloc_880_;
goto v_reusejp_877_;
}
v_reusejp_877_:
{
lean_object* v___x_879_; 
v___x_879_ = lean_array_fset(v_xs_x27_874_, v_mid_863_, v___x_878_);
lean_dec(v_mid_863_);
return v___x_879_;
}
}
}
}
else
{
lean_dec(v_midVal_864_);
v_x_860_ = v_mid_863_;
goto _start;
}
}
else
{
uint8_t v___x_884_; 
lean_dec(v_midVal_864_);
v___x_884_ = lean_nat_dec_eq(v_mid_863_, v_x_859_);
if (v___x_884_ == 0)
{
lean_dec(v_x_859_);
v_x_859_ = v_mid_863_;
goto _start;
}
else
{
lean_object* v___x_886_; lean_object* v_c_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v_j_890_; lean_object* v_as_891_; lean_object* v___x_892_; 
lean_dec(v_mid_863_);
lean_dec(v_x_860_);
v___x_886_ = lean_nat_add(v_x_853_, v___x_862_);
v_c_887_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_854_, v_v_855_, v___x_886_);
lean_dec(v___x_886_);
v___x_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_888_, 0, v_k_856_);
lean_ctor_set(v___x_888_, 1, v_c_887_);
v___x_889_ = lean_nat_add(v_x_859_, v___x_862_);
lean_dec(v_x_859_);
v_j_890_ = lean_array_get_size(v_as_857_);
v_as_891_ = lean_array_push(v_as_857_, v___x_888_);
v___x_892_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_889_, v_as_891_, v_j_890_);
lean_dec(v___x_889_);
return v___x_892_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3(lean_object* v_x_893_, lean_object* v_keys_894_, lean_object* v_v_895_, lean_object* v_k_896_, lean_object* v_as_897_, lean_object* v_k_898_){
_start:
{
lean_object* v___x_899_; lean_object* v___x_900_; uint8_t v___x_901_; 
v___x_899_ = lean_array_get_size(v_as_897_);
v___x_900_ = lean_unsigned_to_nat(0u);
v___x_901_ = lean_nat_dec_eq(v___x_899_, v___x_900_);
if (v___x_901_ == 0)
{
lean_object* v___x_902_; uint8_t v___x_903_; 
v___x_902_ = lean_array_fget_borrowed(v_as_897_, v___x_900_);
v___x_903_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_k_898_, v___x_902_);
if (v___x_903_ == 0)
{
uint8_t v___x_904_; 
v___x_904_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v___x_902_, v_k_898_);
if (v___x_904_ == 0)
{
uint8_t v___x_905_; 
v___x_905_ = lean_nat_dec_lt(v___x_900_, v___x_899_);
if (v___x_905_ == 0)
{
lean_dec(v_k_896_);
lean_dec_ref(v_v_895_);
return v_as_897_;
}
else
{
lean_object* v___x_906_; lean_object* v_xs_x27_907_; lean_object* v___x_908_; lean_object* v___x_909_; 
lean_inc(v___x_902_);
v___x_906_ = lean_box(0);
v_xs_x27_907_ = lean_array_fset(v_as_897_, v___x_900_, v___x_906_);
v___x_908_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__2(v_x_893_, v_keys_894_, v_v_895_, v_k_896_, v___x_902_);
v___x_909_ = lean_array_fset(v_xs_x27_907_, v___x_900_, v___x_908_);
return v___x_909_;
}
}
else
{
lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; uint8_t v___x_913_; 
v___x_910_ = lean_unsigned_to_nat(1u);
v___x_911_ = lean_nat_sub(v___x_899_, v___x_910_);
v___x_912_ = lean_array_fget_borrowed(v_as_897_, v___x_911_);
v___x_913_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v___x_912_, v_k_898_);
if (v___x_913_ == 0)
{
uint8_t v___x_914_; 
v___x_914_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1___lam__0(v_k_898_, v___x_912_);
if (v___x_914_ == 0)
{
uint8_t v___x_915_; 
v___x_915_ = lean_nat_dec_lt(v___x_911_, v___x_899_);
if (v___x_915_ == 0)
{
lean_dec(v___x_911_);
lean_dec(v_k_896_);
lean_dec_ref(v_v_895_);
return v_as_897_;
}
else
{
lean_object* v___x_916_; lean_object* v_xs_x27_917_; lean_object* v___x_918_; lean_object* v___x_919_; 
lean_inc(v___x_912_);
v___x_916_ = lean_box(0);
v_xs_x27_917_ = lean_array_fset(v_as_897_, v___x_911_, v___x_916_);
v___x_918_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__2(v_x_893_, v_keys_894_, v_v_895_, v_k_896_, v___x_912_);
v___x_919_ = lean_array_fset(v_xs_x27_917_, v___x_911_, v___x_918_);
lean_dec(v___x_911_);
return v___x_919_;
}
}
else
{
lean_object* v___x_920_; 
v___x_920_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3_spec__8___redArg(v_x_893_, v_keys_894_, v_v_895_, v_k_896_, v_as_897_, v_k_898_, v___x_900_, v___x_911_);
return v___x_920_;
}
}
else
{
lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec(v___x_911_);
v___x_921_ = lean_box(0);
v___x_922_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__0(v_x_893_, v_keys_894_, v_v_895_, v_k_896_, v___x_921_);
v___x_923_ = lean_array_push(v_as_897_, v___x_922_);
return v___x_923_;
}
}
}
else
{
lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_as_926_; lean_object* v___x_927_; 
v___x_924_ = lean_box(0);
v___x_925_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__0(v_x_893_, v_keys_894_, v_v_895_, v_k_896_, v___x_924_);
v_as_926_ = lean_array_push(v_as_897_, v___x_925_);
v___x_927_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_900_, v_as_926_, v___x_899_);
return v___x_927_;
}
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; 
v___x_928_ = lean_box(0);
v___x_929_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__0(v_x_893_, v_keys_894_, v_v_895_, v_k_896_, v___x_928_);
v___x_930_ = lean_array_push(v_as_897_, v___x_929_);
return v___x_930_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0(lean_object* v_keys_931_, lean_object* v_v_932_, lean_object* v_x_933_, lean_object* v_x_934_){
_start:
{
if (lean_obj_tag(v_x_934_) == 0)
{
lean_object* v_key_935_; lean_object* v_child_936_; lean_object* v___x_938_; uint8_t v_isShared_939_; uint8_t v_isSharedCheck_970_; 
v_key_935_ = lean_ctor_get(v_x_934_, 0);
v_child_936_ = lean_ctor_get(v_x_934_, 1);
v_isSharedCheck_970_ = !lean_is_exclusive(v_x_934_);
if (v_isSharedCheck_970_ == 0)
{
v___x_938_ = v_x_934_;
v_isShared_939_ = v_isSharedCheck_970_;
goto v_resetjp_937_;
}
else
{
lean_inc(v_child_936_);
lean_inc(v_key_935_);
lean_dec(v_x_934_);
v___x_938_ = lean_box(0);
v_isShared_939_ = v_isSharedCheck_970_;
goto v_resetjp_937_;
}
v_resetjp_937_:
{
lean_object* v___x_940_; uint8_t v___x_941_; 
v___x_940_ = lean_array_get_size(v_keys_931_);
v___x_941_ = lean_nat_dec_lt(v_x_933_, v___x_940_);
if (v___x_941_ == 0)
{
lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_948_; 
v___x_942_ = lean_unsigned_to_nat(1u);
v___x_943_ = lean_mk_empty_array_with_capacity(v___x_942_);
lean_inc_ref(v___x_943_);
v___x_944_ = lean_array_push(v___x_943_, v_v_932_);
v___x_945_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_945_, 0, v_key_935_);
lean_ctor_set(v___x_945_, 1, v_child_936_);
v___x_946_ = lean_array_push(v___x_943_, v___x_945_);
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 1);
lean_ctor_set(v___x_938_, 1, v___x_946_);
lean_ctor_set(v___x_938_, 0, v___x_944_);
v___x_948_ = v___x_938_;
goto v_reusejp_947_;
}
else
{
lean_object* v_reuseFailAlloc_949_; 
v_reuseFailAlloc_949_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_949_, 0, v___x_944_);
lean_ctor_set(v_reuseFailAlloc_949_, 1, v___x_946_);
v___x_948_ = v_reuseFailAlloc_949_;
goto v_reusejp_947_;
}
v_reusejp_947_:
{
return v___x_948_;
}
}
else
{
lean_object* v___x_950_; uint8_t v___x_951_; 
v___x_950_ = lean_array_fget_borrowed(v_keys_931_, v_x_933_);
v___x_951_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_950_, v_key_935_);
if (v___x_951_ == 0)
{
lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_962_; 
v___x_952_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0___closed__0));
v___x_953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_953_, 0, v_key_935_);
lean_ctor_set(v___x_953_, 1, v_child_936_);
v___x_954_ = lean_unsigned_to_nat(1u);
v___x_955_ = lean_mk_empty_array_with_capacity(v___x_954_);
v___x_956_ = lean_array_push(v___x_955_, v___x_953_);
v___x_957_ = lean_nat_add(v_x_933_, v___x_954_);
v___x_958_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_931_, v_v_932_, v___x_957_);
lean_dec(v___x_957_);
lean_inc(v___x_950_);
v___x_959_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_959_, 0, v___x_950_);
lean_ctor_set(v___x_959_, 1, v___x_958_);
lean_inc_ref(v___x_959_);
v___x_960_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1(v___x_959_, v___x_956_, v___x_959_);
lean_dec_ref_known(v___x_959_, 2);
if (v_isShared_939_ == 0)
{
lean_ctor_set_tag(v___x_938_, 1);
lean_ctor_set(v___x_938_, 1, v___x_960_);
lean_ctor_set(v___x_938_, 0, v___x_952_);
v___x_962_ = v___x_938_;
goto v_reusejp_961_;
}
else
{
lean_object* v_reuseFailAlloc_963_; 
v_reuseFailAlloc_963_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_963_, 0, v___x_952_);
lean_ctor_set(v_reuseFailAlloc_963_, 1, v___x_960_);
v___x_962_ = v_reuseFailAlloc_963_;
goto v_reusejp_961_;
}
v_reusejp_961_:
{
return v___x_962_;
}
}
else
{
lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_968_; 
v___x_964_ = lean_unsigned_to_nat(1u);
v___x_965_ = lean_nat_add(v_x_933_, v___x_964_);
v___x_966_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0(v_keys_931_, v_v_932_, v___x_965_, v_child_936_);
lean_dec(v___x_965_);
if (v_isShared_939_ == 0)
{
lean_ctor_set(v___x_938_, 1, v___x_966_);
v___x_968_ = v___x_938_;
goto v_reusejp_967_;
}
else
{
lean_object* v_reuseFailAlloc_969_; 
v_reuseFailAlloc_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_969_, 0, v_key_935_);
lean_ctor_set(v_reuseFailAlloc_969_, 1, v___x_966_);
v___x_968_ = v_reuseFailAlloc_969_;
goto v_reusejp_967_;
}
v_reusejp_967_:
{
return v___x_968_;
}
}
}
}
}
else
{
lean_object* v_vs_971_; lean_object* v_children_972_; lean_object* v___x_974_; uint8_t v_isShared_975_; uint8_t v_isSharedCheck_989_; 
v_vs_971_ = lean_ctor_get(v_x_934_, 0);
v_children_972_ = lean_ctor_get(v_x_934_, 1);
v_isSharedCheck_989_ = !lean_is_exclusive(v_x_934_);
if (v_isSharedCheck_989_ == 0)
{
v___x_974_ = v_x_934_;
v_isShared_975_ = v_isSharedCheck_989_;
goto v_resetjp_973_;
}
else
{
lean_inc(v_children_972_);
lean_inc(v_vs_971_);
lean_dec(v_x_934_);
v___x_974_ = lean_box(0);
v_isShared_975_ = v_isSharedCheck_989_;
goto v_resetjp_973_;
}
v_resetjp_973_:
{
lean_object* v___x_976_; uint8_t v___x_977_; 
v___x_976_ = lean_array_get_size(v_keys_931_);
v___x_977_ = lean_nat_dec_lt(v_x_933_, v___x_976_);
if (v___x_977_ == 0)
{
lean_object* v___x_978_; lean_object* v___x_980_; 
v___x_978_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__2(v_vs_971_, v_v_932_);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 0, v___x_978_);
v___x_980_ = v___x_974_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_children_972_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
else
{
lean_object* v_k_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v_c_985_; lean_object* v___x_987_; 
v_k_982_ = lean_array_fget_borrowed(v_keys_931_, v_x_933_);
v___x_983_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0___closed__1));
lean_inc_n(v_k_982_, 2);
v___x_984_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_984_, 0, v_k_982_);
lean_ctor_set(v___x_984_, 1, v___x_983_);
v_c_985_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3(v_x_933_, v_keys_931_, v_v_932_, v_k_982_, v_children_972_, v___x_984_);
lean_dec_ref_known(v___x_984_, 2);
if (v_isShared_975_ == 0)
{
lean_ctor_set(v___x_974_, 1, v_c_985_);
v___x_987_ = v___x_974_;
goto v_reusejp_986_;
}
else
{
lean_object* v_reuseFailAlloc_988_; 
v_reuseFailAlloc_988_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_988_, 0, v_vs_971_);
lean_ctor_set(v_reuseFailAlloc_988_, 1, v_c_985_);
v___x_987_ = v_reuseFailAlloc_988_;
goto v_reusejp_986_;
}
v_reusejp_986_:
{
return v___x_987_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__2(lean_object* v_x_990_, lean_object* v_keys_991_, lean_object* v_v_992_, lean_object* v_k_993_, lean_object* v_x_994_){
_start:
{
lean_object* v_snd_995_; lean_object* v___x_997_; uint8_t v_isShared_998_; uint8_t v_isSharedCheck_1005_; 
v_snd_995_ = lean_ctor_get(v_x_994_, 1);
v_isSharedCheck_1005_ = !lean_is_exclusive(v_x_994_);
if (v_isSharedCheck_1005_ == 0)
{
lean_object* v_unused_1006_; 
v_unused_1006_ = lean_ctor_get(v_x_994_, 0);
lean_dec(v_unused_1006_);
v___x_997_ = v_x_994_;
v_isShared_998_ = v_isSharedCheck_1005_;
goto v_resetjp_996_;
}
else
{
lean_inc(v_snd_995_);
lean_dec(v_x_994_);
v___x_997_ = lean_box(0);
v_isShared_998_ = v_isSharedCheck_1005_;
goto v_resetjp_996_;
}
v_resetjp_996_:
{
lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v_c_1001_; lean_object* v___x_1003_; 
v___x_999_ = lean_unsigned_to_nat(1u);
v___x_1000_ = lean_nat_add(v_x_990_, v___x_999_);
v_c_1001_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0(v_keys_991_, v_v_992_, v___x_1000_, v_snd_995_);
lean_dec(v___x_1000_);
if (v_isShared_998_ == 0)
{
lean_ctor_set(v___x_997_, 1, v_c_1001_);
lean_ctor_set(v___x_997_, 0, v_k_993_);
v___x_1003_ = v___x_997_;
goto v_reusejp_1002_;
}
else
{
lean_object* v_reuseFailAlloc_1004_; 
v_reuseFailAlloc_1004_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1004_, 0, v_k_993_);
lean_ctor_set(v_reuseFailAlloc_1004_, 1, v_c_1001_);
v___x_1003_ = v_reuseFailAlloc_1004_;
goto v_reusejp_1002_;
}
v_reusejp_1002_:
{
return v___x_1003_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__2___boxed(lean_object* v_x_1007_, lean_object* v_keys_1008_, lean_object* v_v_1009_, lean_object* v_k_1010_, lean_object* v_x_1011_){
_start:
{
lean_object* v_res_1012_; 
v_res_1012_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___lam__2(v_x_1007_, v_keys_1008_, v_v_1009_, v_k_1010_, v_x_1011_);
lean_dec_ref(v_keys_1008_);
lean_dec(v_x_1007_);
return v_res_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3_spec__8___redArg___boxed(lean_object* v_x_1013_, lean_object* v_keys_1014_, lean_object* v_v_1015_, lean_object* v_k_1016_, lean_object* v_as_1017_, lean_object* v_k_1018_, lean_object* v_x_1019_, lean_object* v_x_1020_){
_start:
{
lean_object* v_res_1021_; 
v_res_1021_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3_spec__8___redArg(v_x_1013_, v_keys_1014_, v_v_1015_, v_k_1016_, v_as_1017_, v_k_1018_, v_x_1019_, v_x_1020_);
lean_dec_ref(v_k_1018_);
lean_dec_ref(v_keys_1014_);
lean_dec(v_x_1013_);
return v_res_1021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0___boxed(lean_object* v_keys_1022_, lean_object* v_v_1023_, lean_object* v_x_1024_, lean_object* v_x_1025_){
_start:
{
lean_object* v_res_1026_; 
v_res_1026_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0(v_keys_1022_, v_v_1023_, v_x_1024_, v_x_1025_);
lean_dec(v_x_1024_);
lean_dec_ref(v_keys_1022_);
return v_res_1026_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3___boxed(lean_object* v_x_1027_, lean_object* v_keys_1028_, lean_object* v_v_1029_, lean_object* v_k_1030_, lean_object* v_as_1031_, lean_object* v_k_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3(v_x_1027_, v_keys_1028_, v_v_1029_, v_k_1030_, v_as_1031_, v_k_1032_);
lean_dec_ref(v_k_1032_);
lean_dec_ref(v_keys_1028_);
lean_dec(v_x_1027_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1___lam__0(lean_object* v_keys_1034_, lean_object* v_v_1035_, lean_object* v_x_1036_){
_start:
{
if (lean_obj_tag(v_x_1036_) == 0)
{
lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; 
v___x_1037_ = lean_unsigned_to_nat(1u);
v___x_1038_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_1034_, v_v_1035_, v___x_1037_);
v___x_1039_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1039_, 0, v___x_1038_);
return v___x_1039_;
}
else
{
lean_object* v_val_1040_; lean_object* v___x_1042_; uint8_t v_isShared_1043_; uint8_t v_isSharedCheck_1049_; 
v_val_1040_ = lean_ctor_get(v_x_1036_, 0);
v_isSharedCheck_1049_ = !lean_is_exclusive(v_x_1036_);
if (v_isSharedCheck_1049_ == 0)
{
v___x_1042_ = v_x_1036_;
v_isShared_1043_ = v_isSharedCheck_1049_;
goto v_resetjp_1041_;
}
else
{
lean_inc(v_val_1040_);
lean_dec(v_x_1036_);
v___x_1042_ = lean_box(0);
v_isShared_1043_ = v_isSharedCheck_1049_;
goto v_resetjp_1041_;
}
v_resetjp_1041_:
{
lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1047_; 
v___x_1044_ = lean_unsigned_to_nat(1u);
v___x_1045_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0(v_keys_1034_, v_v_1035_, v___x_1044_, v_val_1040_);
if (v_isShared_1043_ == 0)
{
lean_ctor_set(v___x_1042_, 0, v___x_1045_);
v___x_1047_ = v___x_1042_;
goto v_reusejp_1046_;
}
else
{
lean_object* v_reuseFailAlloc_1048_; 
v_reuseFailAlloc_1048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1048_, 0, v___x_1045_);
v___x_1047_ = v_reuseFailAlloc_1048_;
goto v_reusejp_1046_;
}
v_reusejp_1046_:
{
return v___x_1047_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1___lam__0___boxed(lean_object* v_keys_1050_, lean_object* v_v_1051_, lean_object* v_x_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1___lam__0(v_keys_1050_, v_v_1051_, v_x_1052_);
lean_dec_ref(v_keys_1050_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1(lean_object* v_keys_1054_, lean_object* v_v_1055_, lean_object* v_x_1056_, size_t v_x_1057_, size_t v_x_1058_, lean_object* v_x_1059_){
_start:
{
if (lean_obj_tag(v_x_1056_) == 0)
{
lean_object* v_es_1060_; size_t v___x_1061_; size_t v___x_1062_; lean_object* v_j_1063_; lean_object* v___x_1064_; uint8_t v___x_1065_; 
v_es_1060_ = lean_ctor_get(v_x_1056_, 0);
v___x_1061_ = ((size_t)31ULL);
v___x_1062_ = lean_usize_land(v_x_1057_, v___x_1061_);
v_j_1063_ = lean_usize_to_nat(v___x_1062_);
v___x_1064_ = lean_array_get_size(v_es_1060_);
v___x_1065_ = lean_nat_dec_lt(v_j_1063_, v___x_1064_);
if (v___x_1065_ == 0)
{
lean_dec(v_j_1063_);
lean_dec(v_x_1059_);
lean_dec_ref(v_v_1055_);
return v_x_1056_;
}
else
{
lean_object* v___x_1067_; uint8_t v_isShared_1068_; uint8_t v_isSharedCheck_1133_; 
lean_inc_ref(v_es_1060_);
v_isSharedCheck_1133_ = !lean_is_exclusive(v_x_1056_);
if (v_isSharedCheck_1133_ == 0)
{
lean_object* v_unused_1134_; 
v_unused_1134_ = lean_ctor_get(v_x_1056_, 0);
lean_dec(v_unused_1134_);
v___x_1067_ = v_x_1056_;
v_isShared_1068_ = v_isSharedCheck_1133_;
goto v_resetjp_1066_;
}
else
{
lean_dec(v_x_1056_);
v___x_1067_ = lean_box(0);
v_isShared_1068_ = v_isSharedCheck_1133_;
goto v_resetjp_1066_;
}
v_resetjp_1066_:
{
lean_object* v_v_1069_; lean_object* v___x_1070_; lean_object* v_xs_x27_1071_; lean_object* v___y_1073_; 
v_v_1069_ = lean_array_fget(v_es_1060_, v_j_1063_);
v___x_1070_ = lean_box(0);
v_xs_x27_1071_ = lean_array_fset(v_es_1060_, v_j_1063_, v___x_1070_);
switch(lean_obj_tag(v_v_1069_))
{
case 0:
{
lean_object* v_key_1078_; lean_object* v_val_1079_; uint8_t v___x_1080_; 
v_key_1078_ = lean_ctor_get(v_v_1069_, 0);
v_val_1079_ = lean_ctor_get(v_v_1069_, 1);
v___x_1080_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_1059_, v_key_1078_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v___x_1082_; 
v___x_1081_ = lean_box(0);
v___x_1082_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1___lam__0(v_keys_1054_, v_v_1055_, v___x_1081_);
if (lean_obj_tag(v___x_1082_) == 0)
{
lean_dec(v_x_1059_);
v___y_1073_ = v_v_1069_;
goto v___jp_1072_;
}
else
{
lean_object* v_val_1083_; lean_object* v___x_1085_; uint8_t v_isShared_1086_; uint8_t v_isSharedCheck_1091_; 
lean_inc(v_val_1079_);
lean_inc(v_key_1078_);
lean_dec_ref_known(v_v_1069_, 2);
v_val_1083_ = lean_ctor_get(v___x_1082_, 0);
v_isSharedCheck_1091_ = !lean_is_exclusive(v___x_1082_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1085_ = v___x_1082_;
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
else
{
lean_inc(v_val_1083_);
lean_dec(v___x_1082_);
v___x_1085_ = lean_box(0);
v_isShared_1086_ = v_isSharedCheck_1091_;
goto v_resetjp_1084_;
}
v_resetjp_1084_:
{
lean_object* v___x_1087_; lean_object* v___x_1089_; 
v___x_1087_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1078_, v_val_1079_, v_x_1059_, v_val_1083_);
if (v_isShared_1086_ == 0)
{
lean_ctor_set(v___x_1085_, 0, v___x_1087_);
v___x_1089_ = v___x_1085_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1090_; 
v_reuseFailAlloc_1090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1090_, 0, v___x_1087_);
v___x_1089_ = v_reuseFailAlloc_1090_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
v___y_1073_ = v___x_1089_;
goto v___jp_1072_;
}
}
}
}
else
{
lean_object* v___x_1093_; uint8_t v_isShared_1094_; uint8_t v_isSharedCheck_1102_; 
lean_inc(v_val_1079_);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_v_1069_);
if (v_isSharedCheck_1102_ == 0)
{
lean_object* v_unused_1103_; lean_object* v_unused_1104_; 
v_unused_1103_ = lean_ctor_get(v_v_1069_, 1);
lean_dec(v_unused_1103_);
v_unused_1104_ = lean_ctor_get(v_v_1069_, 0);
lean_dec(v_unused_1104_);
v___x_1093_ = v_v_1069_;
v_isShared_1094_ = v_isSharedCheck_1102_;
goto v_resetjp_1092_;
}
else
{
lean_dec(v_v_1069_);
v___x_1093_ = lean_box(0);
v_isShared_1094_ = v_isSharedCheck_1102_;
goto v_resetjp_1092_;
}
v_resetjp_1092_:
{
lean_object* v___x_1095_; lean_object* v___x_1096_; 
v___x_1095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1095_, 0, v_val_1079_);
v___x_1096_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1___lam__0(v_keys_1054_, v_v_1055_, v___x_1095_);
if (lean_obj_tag(v___x_1096_) == 0)
{
lean_object* v___x_1097_; 
lean_del_object(v___x_1093_);
lean_dec(v_x_1059_);
v___x_1097_ = lean_box(2);
v___y_1073_ = v___x_1097_;
goto v___jp_1072_;
}
else
{
lean_object* v_val_1098_; lean_object* v___x_1100_; 
v_val_1098_ = lean_ctor_get(v___x_1096_, 0);
lean_inc(v_val_1098_);
lean_dec_ref_known(v___x_1096_, 1);
if (v_isShared_1094_ == 0)
{
lean_ctor_set(v___x_1093_, 1, v_val_1098_);
lean_ctor_set(v___x_1093_, 0, v_x_1059_);
v___x_1100_ = v___x_1093_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_x_1059_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v_val_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
v___y_1073_ = v___x_1100_;
goto v___jp_1072_;
}
}
}
}
}
case 1:
{
lean_object* v_node_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1128_; 
v_node_1105_ = lean_ctor_get(v_v_1069_, 0);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_v_1069_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1107_ = v_v_1069_;
v_isShared_1108_ = v_isSharedCheck_1128_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_node_1105_);
lean_dec(v_v_1069_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1128_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
size_t v___x_1109_; size_t v___x_1110_; size_t v___x_1111_; size_t v___x_1112_; lean_object* v_newNode_1113_; lean_object* v___x_1114_; 
v___x_1109_ = ((size_t)5ULL);
v___x_1110_ = lean_usize_shift_right(v_x_1057_, v___x_1109_);
v___x_1111_ = ((size_t)1ULL);
v___x_1112_ = lean_usize_add(v_x_1058_, v___x_1111_);
v_newNode_1113_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1(v_keys_1054_, v_v_1055_, v_node_1105_, v___x_1110_, v___x_1112_, v_x_1059_);
lean_inc_ref(v_newNode_1113_);
v___x_1114_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_1113_);
if (lean_obj_tag(v___x_1114_) == 0)
{
lean_object* v___x_1116_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 0, v_newNode_1113_);
v___x_1116_ = v___x_1107_;
goto v_reusejp_1115_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_newNode_1113_);
v___x_1116_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1115_;
}
v_reusejp_1115_:
{
v___y_1073_ = v___x_1116_;
goto v___jp_1072_;
}
}
else
{
lean_object* v_val_1118_; lean_object* v_fst_1119_; lean_object* v_snd_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1127_; 
lean_dec_ref(v_newNode_1113_);
lean_del_object(v___x_1107_);
v_val_1118_ = lean_ctor_get(v___x_1114_, 0);
lean_inc(v_val_1118_);
lean_dec_ref_known(v___x_1114_, 1);
v_fst_1119_ = lean_ctor_get(v_val_1118_, 0);
v_snd_1120_ = lean_ctor_get(v_val_1118_, 1);
v_isSharedCheck_1127_ = !lean_is_exclusive(v_val_1118_);
if (v_isSharedCheck_1127_ == 0)
{
v___x_1122_ = v_val_1118_;
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_snd_1120_);
lean_inc(v_fst_1119_);
lean_dec(v_val_1118_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1127_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1123_ == 0)
{
v___x_1125_ = v___x_1122_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1126_; 
v_reuseFailAlloc_1126_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1126_, 0, v_fst_1119_);
lean_ctor_set(v_reuseFailAlloc_1126_, 1, v_snd_1120_);
v___x_1125_ = v_reuseFailAlloc_1126_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
v___y_1073_ = v___x_1125_;
goto v___jp_1072_;
}
}
}
}
}
default: 
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_box(0);
v___x_1130_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1___lam__0(v_keys_1054_, v_v_1055_, v___x_1129_);
if (lean_obj_tag(v___x_1130_) == 0)
{
lean_dec(v_x_1059_);
v___y_1073_ = v_v_1069_;
goto v___jp_1072_;
}
else
{
lean_object* v_val_1131_; lean_object* v___x_1132_; 
v_val_1131_ = lean_ctor_get(v___x_1130_, 0);
lean_inc(v_val_1131_);
lean_dec_ref_known(v___x_1130_, 1);
v___x_1132_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1132_, 0, v_x_1059_);
lean_ctor_set(v___x_1132_, 1, v_val_1131_);
v___y_1073_ = v___x_1132_;
goto v___jp_1072_;
}
}
}
v___jp_1072_:
{
lean_object* v___x_1074_; lean_object* v___x_1076_; 
v___x_1074_ = lean_array_fset(v_xs_x27_1071_, v_j_1063_, v___y_1073_);
lean_dec(v_j_1063_);
if (v_isShared_1068_ == 0)
{
lean_ctor_set(v___x_1067_, 0, v___x_1074_);
v___x_1076_ = v___x_1067_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1077_; 
v_reuseFailAlloc_1077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1077_, 0, v___x_1074_);
v___x_1076_ = v_reuseFailAlloc_1077_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
return v___x_1076_;
}
}
}
}
}
else
{
lean_object* v_ks_1135_; lean_object* v_vs_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1169_; 
v_ks_1135_ = lean_ctor_get(v_x_1056_, 0);
v_vs_1136_ = lean_ctor_get(v_x_1056_, 1);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_x_1056_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1138_ = v_x_1056_;
v_isShared_1139_ = v_isSharedCheck_1169_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_vs_1136_);
lean_inc(v_ks_1135_);
lean_dec(v_x_1056_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1169_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__5(v_ks_1135_, v_x_1059_);
if (lean_obj_tag(v___x_1140_) == 0)
{
lean_object* v___x_1142_; 
if (v_isShared_1139_ == 0)
{
v___x_1142_ = v___x_1138_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1147_; 
v_reuseFailAlloc_1147_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1147_, 0, v_ks_1135_);
lean_ctor_set(v_reuseFailAlloc_1147_, 1, v_vs_1136_);
v___x_1142_ = v_reuseFailAlloc_1147_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; 
v___x_1143_ = lean_box(0);
v___x_1144_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1___lam__0(v_keys_1054_, v_v_1055_, v___x_1143_);
if (lean_obj_tag(v___x_1144_) == 0)
{
lean_dec(v_x_1059_);
return v___x_1142_;
}
else
{
lean_object* v_val_1145_; lean_object* v___x_1146_; 
v_val_1145_ = lean_ctor_get(v___x_1144_, 0);
lean_inc(v_val_1145_);
lean_dec_ref_known(v___x_1144_, 1);
v___x_1146_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6___redArg(v___x_1142_, v_x_1057_, v_x_1058_, v_x_1059_, v_val_1145_);
return v___x_1146_;
}
}
}
else
{
lean_object* v_val_1148_; lean_object* v___x_1150_; uint8_t v_isShared_1151_; uint8_t v_isSharedCheck_1168_; 
v_val_1148_ = lean_ctor_get(v___x_1140_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1140_);
if (v_isSharedCheck_1168_ == 0)
{
v___x_1150_ = v___x_1140_;
v_isShared_1151_ = v_isSharedCheck_1168_;
goto v_resetjp_1149_;
}
else
{
lean_inc(v_val_1148_);
lean_dec(v___x_1140_);
v___x_1150_ = lean_box(0);
v_isShared_1151_ = v_isSharedCheck_1168_;
goto v_resetjp_1149_;
}
v_resetjp_1149_:
{
lean_object* v_v_x27_1152_; lean_object* v_keys_1153_; lean_object* v_vals_1154_; lean_object* v___x_1156_; 
v_v_x27_1152_ = lean_array_fget(v_vs_1136_, v_val_1148_);
lean_inc(v_val_1148_);
v_keys_1153_ = l_Array_eraseIdx___redArg(v_ks_1135_, v_val_1148_);
v_vals_1154_ = l_Array_eraseIdx___redArg(v_vs_1136_, v_val_1148_);
if (v_isShared_1151_ == 0)
{
lean_ctor_set(v___x_1150_, 0, v_v_x27_1152_);
v___x_1156_ = v___x_1150_;
goto v_reusejp_1155_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_v_x27_1152_);
v___x_1156_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1155_;
}
v_reusejp_1155_:
{
lean_object* v___x_1157_; 
v___x_1157_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1___lam__0(v_keys_1054_, v_v_1055_, v___x_1156_);
if (lean_obj_tag(v___x_1157_) == 0)
{
lean_object* v___x_1159_; 
lean_dec(v_x_1059_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v_vals_1154_);
lean_ctor_set(v___x_1138_, 0, v_keys_1153_);
v___x_1159_ = v___x_1138_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1160_; 
v_reuseFailAlloc_1160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1160_, 0, v_keys_1153_);
lean_ctor_set(v_reuseFailAlloc_1160_, 1, v_vals_1154_);
v___x_1159_ = v_reuseFailAlloc_1160_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
return v___x_1159_;
}
}
else
{
lean_object* v_val_1161_; lean_object* v_keys_1162_; lean_object* v_vals_1163_; lean_object* v___x_1165_; 
v_val_1161_ = lean_ctor_get(v___x_1157_, 0);
lean_inc(v_val_1161_);
lean_dec_ref_known(v___x_1157_, 1);
v_keys_1162_ = lean_array_push(v_keys_1153_, v_x_1059_);
v_vals_1163_ = lean_array_push(v_vals_1154_, v_val_1161_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v_vals_1163_);
lean_ctor_set(v___x_1138_, 0, v_keys_1162_);
v___x_1165_ = v___x_1138_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_keys_1162_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_vals_1163_);
v___x_1165_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
return v___x_1165_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1___boxed(lean_object* v_keys_1170_, lean_object* v_v_1171_, lean_object* v_x_1172_, lean_object* v_x_1173_, lean_object* v_x_1174_, lean_object* v_x_1175_){
_start:
{
size_t v_x_3599__boxed_1176_; size_t v_x_3600__boxed_1177_; lean_object* v_res_1178_; 
v_x_3599__boxed_1176_ = lean_unbox_usize(v_x_1173_);
lean_dec(v_x_1173_);
v_x_3600__boxed_1177_ = lean_unbox_usize(v_x_1174_);
lean_dec(v_x_1174_);
v_res_1178_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1(v_keys_1170_, v_v_1171_, v_x_1172_, v_x_3599__boxed_1176_, v_x_3600__boxed_1177_, v_x_1175_);
lean_dec_ref(v_keys_1170_);
return v_res_1178_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_1179_; 
v___x_1179_ = l_Lean_Meta_DiscrTree_instInhabited___redArg();
return v___x_1179_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__2(lean_object* v_msg_1180_){
_start:
{
lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___x_1181_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__2___closed__0);
v___x_1182_ = lean_panic_fn_borrowed(v___x_1181_, v_msg_1180_);
return v___x_1182_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; 
v___x_1186_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__2));
v___x_1187_ = lean_unsigned_to_nat(23u);
v___x_1188_ = lean_unsigned_to_nat(179u);
v___x_1189_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__1));
v___x_1190_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__0));
v___x_1191_ = l_mkPanicMessageWithDecl(v___x_1190_, v___x_1189_, v___x_1188_, v___x_1187_, v___x_1186_);
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0(lean_object* v_d_1192_, lean_object* v_keys_1193_, lean_object* v_v_1194_){
_start:
{
lean_object* v___x_1195_; lean_object* v___x_1196_; uint8_t v___x_1197_; 
v___x_1195_ = lean_array_get_size(v_keys_1193_);
v___x_1196_ = lean_unsigned_to_nat(0u);
v___x_1197_ = lean_nat_dec_eq(v___x_1195_, v___x_1196_);
if (v___x_1197_ == 0)
{
lean_object* v___x_1198_; lean_object* v_k_1199_; uint64_t v___x_1200_; size_t v_h_1201_; size_t v___x_1202_; lean_object* v___x_1203_; 
v___x_1198_ = lean_box(0);
v_k_1199_ = lean_array_get_borrowed(v___x_1198_, v_keys_1193_, v___x_1196_);
v___x_1200_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_1199_);
v_h_1201_ = lean_uint64_to_usize(v___x_1200_);
v___x_1202_ = ((size_t)1ULL);
lean_inc(v_k_1199_);
v___x_1203_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1(v_keys_1193_, v_v_1194_, v_d_1192_, v_h_1201_, v___x_1202_, v_k_1199_);
return v___x_1203_;
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec_ref(v_v_1194_);
lean_dec_ref(v_d_1192_);
v___x_1204_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___closed__3);
v___x_1205_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__2(v___x_1204_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0___boxed(lean_object* v_d_1206_, lean_object* v_keys_1207_, lean_object* v_v_1208_){
_start:
{
lean_object* v_res_1209_; 
v_res_1209_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0(v_d_1206_, v_keys_1207_, v_v_1208_);
lean_dec_ref(v_keys_1207_);
return v_res_1209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addImportedInstanceEntry(lean_object* v_d_1210_, lean_object* v_e_1211_){
_start:
{
lean_object* v_globalName_x3f_1212_; 
v_globalName_x3f_1212_ = lean_ctor_get(v_e_1211_, 3);
if (lean_obj_tag(v_globalName_x3f_1212_) == 0)
{
lean_object* v_keys_1213_; lean_object* v_discrTree_1214_; lean_object* v_instanceNames_1215_; lean_object* v_erased_1216_; lean_object* v_classChanges_1217_; lean_object* v___x_1219_; uint8_t v_isShared_1220_; uint8_t v_isSharedCheck_1225_; 
v_keys_1213_ = lean_ctor_get(v_e_1211_, 0);
lean_inc_ref(v_keys_1213_);
v_discrTree_1214_ = lean_ctor_get(v_d_1210_, 0);
v_instanceNames_1215_ = lean_ctor_get(v_d_1210_, 1);
v_erased_1216_ = lean_ctor_get(v_d_1210_, 2);
v_classChanges_1217_ = lean_ctor_get(v_d_1210_, 3);
v_isSharedCheck_1225_ = !lean_is_exclusive(v_d_1210_);
if (v_isSharedCheck_1225_ == 0)
{
v___x_1219_ = v_d_1210_;
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
else
{
lean_inc(v_classChanges_1217_);
lean_inc(v_erased_1216_);
lean_inc(v_instanceNames_1215_);
lean_inc(v_discrTree_1214_);
lean_dec(v_d_1210_);
v___x_1219_ = lean_box(0);
v_isShared_1220_ = v_isSharedCheck_1225_;
goto v_resetjp_1218_;
}
v_resetjp_1218_:
{
lean_object* v___x_1221_; lean_object* v___x_1223_; 
v___x_1221_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0(v_discrTree_1214_, v_keys_1213_, v_e_1211_);
lean_dec_ref(v_keys_1213_);
if (v_isShared_1220_ == 0)
{
lean_ctor_set(v___x_1219_, 0, v___x_1221_);
v___x_1223_ = v___x_1219_;
goto v_reusejp_1222_;
}
else
{
lean_object* v_reuseFailAlloc_1224_; 
v_reuseFailAlloc_1224_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1224_, 0, v___x_1221_);
lean_ctor_set(v_reuseFailAlloc_1224_, 1, v_instanceNames_1215_);
lean_ctor_set(v_reuseFailAlloc_1224_, 2, v_erased_1216_);
lean_ctor_set(v_reuseFailAlloc_1224_, 3, v_classChanges_1217_);
v___x_1223_ = v_reuseFailAlloc_1224_;
goto v_reusejp_1222_;
}
v_reusejp_1222_:
{
return v___x_1223_;
}
}
}
else
{
lean_object* v_keys_1226_; lean_object* v_val_1227_; lean_object* v_discrTree_1228_; lean_object* v_instanceNames_1229_; lean_object* v_erased_1230_; lean_object* v_classChanges_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1241_; 
v_keys_1226_ = lean_ctor_get(v_e_1211_, 0);
v_val_1227_ = lean_ctor_get(v_globalName_x3f_1212_, 0);
lean_inc(v_val_1227_);
v_discrTree_1228_ = lean_ctor_get(v_d_1210_, 0);
v_instanceNames_1229_ = lean_ctor_get(v_d_1210_, 1);
v_erased_1230_ = lean_ctor_get(v_d_1210_, 2);
v_classChanges_1231_ = lean_ctor_get(v_d_1210_, 3);
v_isSharedCheck_1241_ = !lean_is_exclusive(v_d_1210_);
if (v_isSharedCheck_1241_ == 0)
{
v___x_1233_ = v_d_1210_;
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_classChanges_1231_);
lean_inc(v_erased_1230_);
lean_inc(v_instanceNames_1229_);
lean_inc(v_discrTree_1228_);
lean_dec(v_d_1210_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1241_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
lean_inc_ref(v_e_1211_);
v___x_1235_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0(v_discrTree_1228_, v_keys_1226_, v_e_1211_);
lean_inc(v_val_1227_);
v___x_1236_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0___redArg(v_instanceNames_1229_, v_val_1227_, v_e_1211_);
v___x_1237_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1___redArg(v_erased_1230_, v_val_1227_);
lean_dec(v_val_1227_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 2, v___x_1237_);
lean_ctor_set(v___x_1233_, 1, v___x_1236_);
lean_ctor_set(v___x_1233_, 0, v___x_1235_);
v___x_1239_ = v___x_1233_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1240_, 1, v___x_1236_);
lean_ctor_set(v_reuseFailAlloc_1240_, 2, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1240_, 3, v_classChanges_1231_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1(lean_object* v_00_u03b2_1242_, lean_object* v_x_1243_, lean_object* v_x_1244_){
_start:
{
lean_object* v___x_1245_; 
v___x_1245_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1___redArg(v_x_1243_, v_x_1244_);
return v___x_1245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1___boxed(lean_object* v_00_u03b2_1246_, lean_object* v_x_1247_, lean_object* v_x_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1(v_00_u03b2_1246_, v_x_1247_, v_x_1248_);
lean_dec(v_x_1248_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4(lean_object* v_00_u03b2_1250_, lean_object* v_x_1251_, size_t v_x_1252_, lean_object* v_x_1253_){
_start:
{
lean_object* v___x_1254_; 
v___x_1254_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4___redArg(v_x_1251_, v_x_1252_, v_x_1253_);
return v___x_1254_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4___boxed(lean_object* v_00_u03b2_1255_, lean_object* v_x_1256_, lean_object* v_x_1257_, lean_object* v_x_1258_){
_start:
{
size_t v_x_3911__boxed_1259_; lean_object* v_res_1260_; 
v_x_3911__boxed_1259_ = lean_unbox_usize(v_x_1257_);
lean_dec(v_x_1257_);
v_res_1260_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1_spec__4(v_00_u03b2_1255_, v_x_1256_, v_x_3911__boxed_1259_, v_x_1258_);
lean_dec(v_x_1258_);
return v_res_1260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6(lean_object* v_00_u03b2_1261_, lean_object* v_x_1262_, size_t v_x_1263_, size_t v_x_1264_, lean_object* v_x_1265_, lean_object* v_x_1266_){
_start:
{
lean_object* v___x_1267_; 
v___x_1267_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6___redArg(v_x_1262_, v_x_1263_, v_x_1264_, v_x_1265_, v_x_1266_);
return v___x_1267_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6___boxed(lean_object* v_00_u03b2_1268_, lean_object* v_x_1269_, lean_object* v_x_1270_, lean_object* v_x_1271_, lean_object* v_x_1272_, lean_object* v_x_1273_){
_start:
{
size_t v_x_3922__boxed_1274_; size_t v_x_3923__boxed_1275_; lean_object* v_res_1276_; 
v_x_3922__boxed_1274_ = lean_unbox_usize(v_x_1270_);
lean_dec(v_x_1270_);
v_x_3923__boxed_1275_ = lean_unbox_usize(v_x_1271_);
lean_dec(v_x_1271_);
v_res_1276_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6(v_00_u03b2_1268_, v_x_1269_, v_x_3922__boxed_1274_, v_x_3923__boxed_1275_, v_x_1272_, v_x_1273_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1_spec__4(lean_object* v___x_1277_, lean_object* v_as_1278_, lean_object* v_k_1279_, lean_object* v_x_1280_, lean_object* v_x_1281_, lean_object* v_x_1282_, lean_object* v_x_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1_spec__4___redArg(v___x_1277_, v_as_1278_, v_k_1279_, v_x_1280_, v_x_1281_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1_spec__4___boxed(lean_object* v___x_1285_, lean_object* v_as_1286_, lean_object* v_k_1287_, lean_object* v_x_1288_, lean_object* v_x_1289_, lean_object* v_x_1290_, lean_object* v_x_1291_){
_start:
{
lean_object* v_res_1292_; 
v_res_1292_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__1_spec__4(v___x_1285_, v_as_1286_, v_k_1287_, v_x_1288_, v_x_1289_, v_x_1290_, v_x_1291_);
lean_dec_ref(v_k_1287_);
return v_res_1292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3_spec__8(lean_object* v_x_1293_, lean_object* v_keys_1294_, lean_object* v_v_1295_, lean_object* v_k_1296_, lean_object* v_as_1297_, lean_object* v_k_1298_, lean_object* v_x_1299_, lean_object* v_x_1300_, lean_object* v_x_1301_, lean_object* v_x_1302_){
_start:
{
lean_object* v___x_1303_; 
v___x_1303_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3_spec__8___redArg(v_x_1293_, v_keys_1294_, v_v_1295_, v_k_1296_, v_as_1297_, v_k_1298_, v_x_1299_, v_x_1300_);
return v___x_1303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3_spec__8___boxed(lean_object* v_x_1304_, lean_object* v_keys_1305_, lean_object* v_v_1306_, lean_object* v_k_1307_, lean_object* v_as_1308_, lean_object* v_k_1309_, lean_object* v_x_1310_, lean_object* v_x_1311_, lean_object* v_x_1312_, lean_object* v_x_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__0_spec__3_spec__8(v_x_1304_, v_keys_1305_, v_v_1306_, v_k_1307_, v_as_1308_, v_k_1309_, v_x_1310_, v_x_1311_, v_x_1312_, v_x_1313_);
lean_dec_ref(v_k_1309_);
lean_dec_ref(v_keys_1305_);
lean_dec(v_x_1304_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__13(lean_object* v_00_u03b2_1315_, lean_object* v_n_1316_, lean_object* v_k_1317_, lean_object* v_v_1318_){
_start:
{
lean_object* v___x_1319_; 
v___x_1319_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__13___redArg(v_n_1316_, v_k_1317_, v_v_1318_);
return v___x_1319_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__14(lean_object* v_00_u03b2_1320_, size_t v_depth_1321_, lean_object* v_keys_1322_, lean_object* v_vals_1323_, lean_object* v_heq_1324_, lean_object* v_i_1325_, lean_object* v_entries_1326_){
_start:
{
lean_object* v___x_1327_; 
v___x_1327_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__14___redArg(v_depth_1321_, v_keys_1322_, v_vals_1323_, v_i_1325_, v_entries_1326_);
return v___x_1327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__14___boxed(lean_object* v_00_u03b2_1328_, lean_object* v_depth_1329_, lean_object* v_keys_1330_, lean_object* v_vals_1331_, lean_object* v_heq_1332_, lean_object* v_i_1333_, lean_object* v_entries_1334_){
_start:
{
size_t v_depth_boxed_1335_; lean_object* v_res_1336_; 
v_depth_boxed_1335_ = lean_unbox_usize(v_depth_1329_);
lean_dec(v_depth_1329_);
v_res_1336_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__14(v_00_u03b2_1328_, v_depth_boxed_1335_, v_keys_1330_, v_vals_1331_, v_heq_1332_, v_i_1333_, v_entries_1334_);
lean_dec_ref(v_vals_1331_);
lean_dec_ref(v_keys_1330_);
return v_res_1336_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__13_spec__15(lean_object* v_00_u03b2_1337_, lean_object* v_x_1338_, lean_object* v_x_1339_, lean_object* v_x_1340_, lean_object* v_x_1341_){
_start:
{
lean_object* v___x_1342_; 
v___x_1342_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addImportedInstanceEntry_spec__0_spec__1_spec__6_spec__13_spec__15___redArg(v_x_1338_, v_x_1339_, v_x_1340_, v_x_1341_);
return v___x_1342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object* v_d_1343_, lean_object* v_e_1344_){
_start:
{
lean_object* v_val_1345_; lean_object* v_priority_1346_; lean_object* v_synthOrder_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; 
v_val_1345_ = lean_ctor_get(v_e_1344_, 1);
v_priority_1346_ = lean_ctor_get(v_e_1344_, 2);
v_synthOrder_1347_ = lean_ctor_get(v_e_1344_, 4);
v___x_1348_ = l_Lean_Meta_InstanceEntry_keyClass(v_e_1344_);
lean_inc_ref(v_synthOrder_1347_);
lean_inc(v_priority_1346_);
lean_inc_ref(v_val_1345_);
v___x_1349_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1349_, 0, v_val_1345_);
lean_ctor_set(v___x_1349_, 1, v_priority_1346_);
lean_ctor_set(v___x_1349_, 2, v_synthOrder_1347_);
v___x_1350_ = l___private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange(v_d_1343_, v___x_1348_, v___x_1349_);
v___x_1351_ = l_Lean_Meta_addImportedInstanceEntry(v___x_1350_, v_e_1344_);
return v___x_1351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_eraseCore(lean_object* v_d_1352_, lean_object* v_declName_1353_){
_start:
{
lean_object* v_discrTree_1355_; lean_object* v_instanceNames_1356_; lean_object* v_erased_1357_; lean_object* v_classChanges_1358_; lean_object* v_discrTree_1363_; lean_object* v_instanceNames_1364_; lean_object* v_erased_1365_; lean_object* v_classChanges_1366_; lean_object* v___x_1367_; 
v_discrTree_1363_ = lean_ctor_get(v_d_1352_, 0);
v_instanceNames_1364_ = lean_ctor_get(v_d_1352_, 1);
v_erased_1365_ = lean_ctor_get(v_d_1352_, 2);
v_classChanges_1366_ = lean_ctor_get(v_d_1352_, 3);
v___x_1367_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0___redArg(v_instanceNames_1364_, v_declName_1353_);
if (lean_obj_tag(v___x_1367_) == 0)
{
lean_inc_ref(v_classChanges_1366_);
lean_inc_ref(v_erased_1365_);
lean_inc_ref(v_instanceNames_1364_);
lean_inc_ref(v_discrTree_1363_);
lean_dec_ref(v_d_1352_);
v_discrTree_1355_ = v_discrTree_1363_;
v_instanceNames_1356_ = v_instanceNames_1364_;
v_erased_1357_ = v_erased_1365_;
v_classChanges_1358_ = v_classChanges_1366_;
goto v___jp_1354_;
}
else
{
lean_object* v_val_1368_; lean_object* v___x_1370_; uint8_t v_isShared_1371_; uint8_t v_isSharedCheck_1381_; 
v_val_1368_ = lean_ctor_get(v___x_1367_, 0);
v_isSharedCheck_1381_ = !lean_is_exclusive(v___x_1367_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1370_ = v___x_1367_;
v_isShared_1371_ = v_isSharedCheck_1381_;
goto v_resetjp_1369_;
}
else
{
lean_inc(v_val_1368_);
lean_dec(v___x_1367_);
v___x_1370_ = lean_box(0);
v_isShared_1371_ = v_isSharedCheck_1381_;
goto v_resetjp_1369_;
}
v_resetjp_1369_:
{
lean_object* v___x_1372_; lean_object* v___x_1374_; 
v___x_1372_ = l_Lean_Meta_InstanceEntry_keyClass(v_val_1368_);
lean_dec(v_val_1368_);
lean_inc(v_declName_1353_);
if (v_isShared_1371_ == 0)
{
lean_ctor_set(v___x_1370_, 0, v_declName_1353_);
v___x_1374_ = v___x_1370_;
goto v_reusejp_1373_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_declName_1353_);
v___x_1374_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1373_;
}
v_reusejp_1373_:
{
lean_object* v___x_1375_; lean_object* v_discrTree_1376_; lean_object* v_instanceNames_1377_; lean_object* v_erased_1378_; lean_object* v_classChanges_1379_; 
v___x_1375_ = l___private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange(v_d_1352_, v___x_1372_, v___x_1374_);
v_discrTree_1376_ = lean_ctor_get(v___x_1375_, 0);
lean_inc_ref(v_discrTree_1376_);
v_instanceNames_1377_ = lean_ctor_get(v___x_1375_, 1);
lean_inc_ref(v_instanceNames_1377_);
v_erased_1378_ = lean_ctor_get(v___x_1375_, 2);
lean_inc_ref(v_erased_1378_);
v_classChanges_1379_ = lean_ctor_get(v___x_1375_, 3);
lean_inc_ref(v_classChanges_1379_);
lean_dec_ref(v___x_1375_);
v_discrTree_1355_ = v_discrTree_1376_;
v_instanceNames_1356_ = v_instanceNames_1377_;
v_erased_1357_ = v_erased_1378_;
v_classChanges_1358_ = v_classChanges_1379_;
goto v___jp_1354_;
}
}
}
v___jp_1354_:
{
lean_object* v___x_1359_; lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; 
v___x_1359_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addImportedInstanceEntry_spec__1___redArg(v_instanceNames_1356_, v_declName_1353_);
v___x_1360_ = lean_box(0);
v___x_1361_ = l_Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0___redArg(v_erased_1357_, v_declName_1353_, v___x_1360_);
v___x_1362_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_1362_, 0, v_discrTree_1355_);
lean_ctor_set(v___x_1362_, 1, v___x_1359_);
lean_ctor_set(v___x_1362_, 2, v___x_1361_);
lean_ctor_set(v___x_1362_, 3, v_classChanges_1358_);
return v___x_1362_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__0(lean_object* v_d_1382_, lean_object* v_declName_1383_, lean_object* v_toPure_1384_, lean_object* v_____r_1385_){
_start:
{
lean_object* v___x_1386_; lean_object* v___x_1387_; 
v___x_1386_ = l_Lean_Meta_Instances_eraseCore(v_d_1382_, v_declName_1383_);
v___x_1387_ = lean_apply_2(v_toPure_1384_, lean_box(0), v___x_1386_);
return v___x_1387_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__1(lean_object* v___f_1388_, lean_object* v_____r_1389_){
_start:
{
lean_object* v___x_1390_; 
v___x_1390_ = lean_apply_1(v___f_1388_, v_____r_1389_);
return v___x_1390_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1394_; lean_object* v___x_1395_; 
v___x_1394_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__2));
v___x_1395_ = l_Lean_stringToMessageData(v___x_1394_);
return v___x_1395_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__5(void){
_start:
{
lean_object* v___x_1397_; lean_object* v___x_1398_; 
v___x_1397_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__4));
v___x_1398_ = l_Lean_stringToMessageData(v___x_1397_);
return v___x_1398_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg(lean_object* v_inst_1399_, lean_object* v_inst_1400_, lean_object* v_d_1401_, lean_object* v_declName_1402_){
_start:
{
lean_object* v_toApplicative_1403_; lean_object* v_toBind_1404_; lean_object* v_toPure_1405_; lean_object* v_instanceNames_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___f_1409_; uint8_t v___x_1410_; 
v_toApplicative_1403_ = lean_ctor_get(v_inst_1399_, 0);
v_toBind_1404_ = lean_ctor_get(v_inst_1399_, 1);
lean_inc(v_toBind_1404_);
v_toPure_1405_ = lean_ctor_get(v_toApplicative_1403_, 1);
v_instanceNames_1406_ = lean_ctor_get(v_d_1401_, 1);
v___x_1407_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__0));
v___x_1408_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__1));
lean_inc(v_toPure_1405_);
lean_inc_n(v_declName_1402_, 2);
lean_inc_ref(v_d_1401_);
v___f_1409_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1409_, 0, v_d_1401_);
lean_closure_set(v___f_1409_, 1, v_declName_1402_);
lean_closure_set(v___f_1409_, 2, v_toPure_1405_);
lean_inc_ref(v_instanceNames_1406_);
v___x_1410_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1407_, v___x_1408_, v_instanceNames_1406_, v_declName_1402_);
if (v___x_1410_ == 0)
{
lean_object* v___f_1411_; lean_object* v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec_ref(v_d_1401_);
v___f_1411_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1411_, 0, v___f_1409_);
v___x_1412_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_1413_ = l_Lean_MessageData_ofConstName(v_declName_1402_, v___x_1410_);
v___x_1414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1414_, 0, v___x_1412_);
lean_ctor_set(v___x_1414_, 1, v___x_1413_);
v___x_1415_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_1416_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1414_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = l_Lean_throwError___redArg(v_inst_1399_, v_inst_1400_, v___x_1416_);
v___x_1418_ = lean_apply_4(v_toBind_1404_, lean_box(0), lean_box(0), v___x_1417_, v___f_1411_);
return v___x_1418_;
}
else
{
lean_object* v___x_1419_; lean_object* v___x_1420_; 
lean_inc(v_toPure_1405_);
lean_dec_ref(v___f_1409_);
lean_dec(v_toBind_1404_);
lean_dec_ref(v_inst_1400_);
lean_dec_ref(v_inst_1399_);
v___x_1419_ = lean_box(0);
v___x_1420_ = l_Lean_Meta_Instances_erase___redArg___lam__0(v_d_1401_, v_declName_1402_, v_toPure_1405_, v___x_1419_);
return v___x_1420_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase(lean_object* v_m_1421_, lean_object* v_inst_1422_, lean_object* v_inst_1423_, lean_object* v_d_1424_, lean_object* v_declName_1425_){
_start:
{
lean_object* v___x_1426_; 
v___x_1426_ = l_Lean_Meta_Instances_erase___redArg(v_inst_1422_, v_inst_1423_, v_d_1424_, v_declName_1425_);
return v___x_1426_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_(lean_object* v_x_1427_, lean_object* v_e_1428_){
_start:
{
lean_object* v_globalName_x3f_1433_; 
v_globalName_x3f_1433_ = lean_ctor_get(v_e_1428_, 3);
lean_inc(v_globalName_x3f_1433_);
if (lean_obj_tag(v_globalName_x3f_1433_) == 0)
{
goto v___jp_1429_;
}
else
{
lean_object* v_val_1434_; lean_object* v___x_1436_; uint8_t v_isShared_1437_; uint8_t v_isSharedCheck_1443_; 
v_val_1434_ = lean_ctor_get(v_globalName_x3f_1433_, 0);
v_isSharedCheck_1443_ = !lean_is_exclusive(v_globalName_x3f_1433_);
if (v_isSharedCheck_1443_ == 0)
{
v___x_1436_ = v_globalName_x3f_1433_;
v_isShared_1437_ = v_isSharedCheck_1443_;
goto v_resetjp_1435_;
}
else
{
lean_inc(v_val_1434_);
lean_dec(v_globalName_x3f_1433_);
v___x_1436_ = lean_box(0);
v_isShared_1437_ = v_isSharedCheck_1443_;
goto v_resetjp_1435_;
}
v_resetjp_1435_:
{
uint8_t v___x_1438_; 
v___x_1438_ = l_Lean_isPrivateName(v_val_1434_);
lean_dec(v_val_1434_);
if (v___x_1438_ == 0)
{
lean_object* v___x_1440_; 
if (v_isShared_1437_ == 0)
{
lean_ctor_set(v___x_1436_, 0, v_e_1428_);
v___x_1440_ = v___x_1436_;
goto v_reusejp_1439_;
}
else
{
lean_object* v_reuseFailAlloc_1442_; 
v_reuseFailAlloc_1442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1442_, 0, v_e_1428_);
v___x_1440_ = v_reuseFailAlloc_1442_;
goto v_reusejp_1439_;
}
v_reusejp_1439_:
{
lean_object* v___x_1441_; 
lean_inc_ref_n(v___x_1440_, 2);
v___x_1441_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1441_, 0, v___x_1440_);
lean_ctor_set(v___x_1441_, 1, v___x_1440_);
lean_ctor_set(v___x_1441_, 2, v___x_1440_);
return v___x_1441_;
}
}
else
{
lean_del_object(v___x_1436_);
goto v___jp_1429_;
}
}
}
v___jp_1429_:
{
lean_object* v___x_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; 
v___x_1430_ = lean_box(0);
v___x_1431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1431_, 0, v_e_1428_);
v___x_1432_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1432_, 0, v___x_1430_);
lean_ctor_set(v___x_1432_, 1, v___x_1430_);
lean_ctor_set(v___x_1432_, 2, v___x_1431_);
return v___x_1432_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2____boxed(lean_object* v_x_1444_, lean_object* v_e_1445_){
_start:
{
lean_object* v_res_1446_; 
v_res_1446_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_(v_x_1444_, v_e_1445_);
lean_dec_ref(v_x_1444_);
return v_res_1446_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_(lean_object* v___y_1447_){
_start:
{
lean_inc_ref(v___y_1447_);
return v___y_1447_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2____boxed(lean_object* v___y_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_(v___y_1448_);
lean_dec_ref(v___y_1448_);
return v_res_1449_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_1459_; uint8_t v___x_1460_; uint8_t v___x_1461_; lean_object* v___f_1462_; lean_object* v___f_1463_; lean_object* v___x_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1468_; 
v___x_1459_ = lean_box(0);
v___x_1460_ = 0;
v___x_1461_ = 1;
v___f_1462_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_));
v___f_1463_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_));
v___x_1464_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__2, &l_Lean_Meta_instInhabitedInstances_default___closed__2_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__2);
v___x_1465_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_));
v___x_1466_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_));
v___x_1467_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_));
v___x_1468_ = lean_alloc_ctor(0, 7, 2);
lean_ctor_set(v___x_1468_, 0, v___x_1467_);
lean_ctor_set(v___x_1468_, 1, v___x_1466_);
lean_ctor_set(v___x_1468_, 2, v___x_1465_);
lean_ctor_set(v___x_1468_, 3, v___x_1464_);
lean_ctor_set(v___x_1468_, 4, v___f_1463_);
lean_ctor_set(v___x_1468_, 5, v___f_1462_);
lean_ctor_set(v___x_1468_, 6, v___x_1459_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*7, v___x_1461_);
lean_ctor_set_uint8(v___x_1468_, sizeof(void*)*7 + 1, v___x_1460_);
return v___x_1468_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1470_; lean_object* v___x_1471_; 
v___x_1470_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_);
v___x_1471_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1470_);
return v___x_1471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2____boxed(lean_object* v_a_1472_){
_start:
{
lean_object* v_res_1473_; 
v_res_1473_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_();
return v_res_1473_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object* v_k_1474_, uint8_t v_allowLevelAssignments_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_, lean_object* v___y_1478_, lean_object* v___y_1479_){
_start:
{
lean_object* v___x_1481_; 
v___x_1481_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1475_, v_k_1474_, v___y_1476_, v___y_1477_, v___y_1478_, v___y_1479_);
if (lean_obj_tag(v___x_1481_) == 0)
{
lean_object* v_a_1482_; lean_object* v___x_1484_; uint8_t v_isShared_1485_; uint8_t v_isSharedCheck_1489_; 
v_a_1482_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1489_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1489_ == 0)
{
v___x_1484_ = v___x_1481_;
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
else
{
lean_inc(v_a_1482_);
lean_dec(v___x_1481_);
v___x_1484_ = lean_box(0);
v_isShared_1485_ = v_isSharedCheck_1489_;
goto v_resetjp_1483_;
}
v_resetjp_1483_:
{
lean_object* v___x_1487_; 
if (v_isShared_1485_ == 0)
{
v___x_1487_ = v___x_1484_;
goto v_reusejp_1486_;
}
else
{
lean_object* v_reuseFailAlloc_1488_; 
v_reuseFailAlloc_1488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1488_, 0, v_a_1482_);
v___x_1487_ = v_reuseFailAlloc_1488_;
goto v_reusejp_1486_;
}
v_reusejp_1486_:
{
return v___x_1487_;
}
}
}
else
{
lean_object* v_a_1490_; lean_object* v___x_1492_; uint8_t v_isShared_1493_; uint8_t v_isSharedCheck_1497_; 
v_a_1490_ = lean_ctor_get(v___x_1481_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1481_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1492_ = v___x_1481_;
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
else
{
lean_inc(v_a_1490_);
lean_dec(v___x_1481_);
v___x_1492_ = lean_box(0);
v_isShared_1493_ = v_isSharedCheck_1497_;
goto v_resetjp_1491_;
}
v_resetjp_1491_:
{
lean_object* v___x_1495_; 
if (v_isShared_1493_ == 0)
{
v___x_1495_ = v___x_1492_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_a_1490_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object* v_k_1498_, lean_object* v_allowLevelAssignments_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_, lean_object* v___y_1504_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1505_; lean_object* v_res_1506_; 
v_allowLevelAssignments_boxed_1505_ = lean_unbox(v_allowLevelAssignments_1499_);
v_res_1506_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1498_, v_allowLevelAssignments_boxed_1505_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
lean_dec(v___y_1503_);
lean_dec_ref(v___y_1502_);
lean_dec(v___y_1501_);
lean_dec_ref(v___y_1500_);
return v_res_1506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object* v_00_u03b1_1507_, lean_object* v_k_1508_, uint8_t v_allowLevelAssignments_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_){
_start:
{
lean_object* v___x_1515_; 
v___x_1515_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1508_, v_allowLevelAssignments_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
return v___x_1515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object* v_00_u03b1_1516_, lean_object* v_k_1517_, lean_object* v_allowLevelAssignments_1518_, lean_object* v___y_1519_, lean_object* v___y_1520_, lean_object* v___y_1521_, lean_object* v___y_1522_, lean_object* v___y_1523_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1524_; lean_object* v_res_1525_; 
v_allowLevelAssignments_boxed_1524_ = lean_unbox(v_allowLevelAssignments_1518_);
v_res_1525_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(v_00_u03b1_1516_, v_k_1517_, v_allowLevelAssignments_boxed_1524_, v___y_1519_, v___y_1520_, v___y_1521_, v___y_1522_);
lean_dec(v___y_1522_);
lean_dec_ref(v___y_1521_);
lean_dec(v___y_1520_);
lean_dec_ref(v___y_1519_);
return v_res_1525_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1526_, lean_object* v___x_1527_, uint8_t v___x_1528_, lean_object* v___y_1529_, lean_object* v___y_1530_, lean_object* v___y_1531_, lean_object* v___y_1532_){
_start:
{
lean_object* v___x_1534_; 
v___x_1534_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1526_, v___x_1527_, v___x_1528_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
if (lean_obj_tag(v___x_1534_) == 0)
{
lean_object* v_a_1535_; lean_object* v_snd_1536_; lean_object* v_snd_1537_; uint8_t v___x_1538_; lean_object* v___x_1539_; 
v_a_1535_ = lean_ctor_get(v___x_1534_, 0);
lean_inc(v_a_1535_);
lean_dec_ref_known(v___x_1534_, 1);
v_snd_1536_ = lean_ctor_get(v_a_1535_, 1);
lean_inc(v_snd_1536_);
lean_dec(v_a_1535_);
v_snd_1537_ = lean_ctor_get(v_snd_1536_, 1);
lean_inc(v_snd_1537_);
lean_dec(v_snd_1536_);
v___x_1538_ = 0;
v___x_1539_ = l_Lean_Meta_DiscrTree_mkPath(v_snd_1537_, v___x_1538_, v___y_1529_, v___y_1530_, v___y_1531_, v___y_1532_);
return v___x_1539_;
}
else
{
lean_object* v_a_1540_; lean_object* v___x_1542_; uint8_t v_isShared_1543_; uint8_t v_isSharedCheck_1547_; 
v_a_1540_ = lean_ctor_get(v___x_1534_, 0);
v_isSharedCheck_1547_ = !lean_is_exclusive(v___x_1534_);
if (v_isSharedCheck_1547_ == 0)
{
v___x_1542_ = v___x_1534_;
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
else
{
lean_inc(v_a_1540_);
lean_dec(v___x_1534_);
v___x_1542_ = lean_box(0);
v_isShared_1543_ = v_isSharedCheck_1547_;
goto v_resetjp_1541_;
}
v_resetjp_1541_:
{
lean_object* v___x_1545_; 
if (v_isShared_1543_ == 0)
{
v___x_1545_ = v___x_1542_;
goto v_reusejp_1544_;
}
else
{
lean_object* v_reuseFailAlloc_1546_; 
v_reuseFailAlloc_1546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1546_, 0, v_a_1540_);
v___x_1545_ = v_reuseFailAlloc_1546_;
goto v_reusejp_1544_;
}
v_reusejp_1544_:
{
return v___x_1545_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object* v_a_1548_, lean_object* v___x_1549_, lean_object* v___x_1550_, lean_object* v___y_1551_, lean_object* v___y_1552_, lean_object* v___y_1553_, lean_object* v___y_1554_, lean_object* v___y_1555_){
_start:
{
uint8_t v___x_497__boxed_1556_; lean_object* v_res_1557_; 
v___x_497__boxed_1556_ = lean_unbox(v___x_1550_);
v_res_1557_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1548_, v___x_1549_, v___x_497__boxed_1556_, v___y_1551_, v___y_1552_, v___y_1553_, v___y_1554_);
lean_dec(v___y_1554_);
lean_dec_ref(v___y_1553_);
lean_dec(v___y_1552_);
lean_dec_ref(v___y_1551_);
return v_res_1557_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object* v_e_1558_, lean_object* v_a_1559_, lean_object* v_a_1560_, lean_object* v_a_1561_, lean_object* v_a_1562_){
_start:
{
lean_object* v___x_1564_; 
lean_inc(v_a_1562_);
lean_inc_ref(v_a_1561_);
lean_inc(v_a_1560_);
lean_inc_ref(v_a_1559_);
v___x_1564_ = lean_infer_type(v_e_1558_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
if (lean_obj_tag(v___x_1564_) == 0)
{
lean_object* v_a_1565_; lean_object* v___x_1566_; uint8_t v___x_1567_; lean_object* v___x_1568_; lean_object* v___f_1569_; uint8_t v___x_1570_; lean_object* v___x_1571_; 
v_a_1565_ = lean_ctor_get(v___x_1564_, 0);
lean_inc(v_a_1565_);
lean_dec_ref_known(v___x_1564_, 1);
v___x_1566_ = lean_box(0);
v___x_1567_ = 0;
v___x_1568_ = lean_box(v___x_1567_);
v___f_1569_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1569_, 0, v_a_1565_);
lean_closure_set(v___f_1569_, 1, v___x_1566_);
lean_closure_set(v___f_1569_, 2, v___x_1568_);
v___x_1570_ = 0;
v___x_1571_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v___f_1569_, v___x_1570_, v_a_1559_, v_a_1560_, v_a_1561_, v_a_1562_);
return v___x_1571_;
}
else
{
lean_object* v_a_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1579_; 
v_a_1572_ = lean_ctor_get(v___x_1564_, 0);
v_isSharedCheck_1579_ = !lean_is_exclusive(v___x_1564_);
if (v_isSharedCheck_1579_ == 0)
{
v___x_1574_ = v___x_1564_;
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
else
{
lean_inc(v_a_1572_);
lean_dec(v___x_1564_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1579_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1577_; 
if (v_isShared_1575_ == 0)
{
v___x_1577_ = v___x_1574_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v_a_1572_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object* v_e_1580_, lean_object* v_a_1581_, lean_object* v_a_1582_, lean_object* v_a_1583_, lean_object* v_a_1584_, lean_object* v_a_1585_){
_start:
{
lean_object* v_res_1586_; 
v_res_1586_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_e_1580_, v_a_1581_, v_a_1582_, v_a_1583_, v_a_1584_);
lean_dec(v_a_1584_);
lean_dec_ref(v_a_1583_);
lean_dec(v_a_1582_);
lean_dec_ref(v_a_1581_);
return v_res_1586_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1587_, lean_object* v_b_1588_, lean_object* v_c_1589_, lean_object* v___y_1590_, lean_object* v___y_1591_, lean_object* v___y_1592_, lean_object* v___y_1593_){
_start:
{
lean_object* v___x_1595_; 
lean_inc(v___y_1593_);
lean_inc_ref(v___y_1592_);
lean_inc(v___y_1591_);
lean_inc_ref(v___y_1590_);
v___x_1595_ = lean_apply_7(v_k_1587_, v_b_1588_, v_c_1589_, v___y_1590_, v___y_1591_, v___y_1592_, v___y_1593_, lean_box(0));
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1596_, lean_object* v_b_1597_, lean_object* v_c_1598_, lean_object* v___y_1599_, lean_object* v___y_1600_, lean_object* v___y_1601_, lean_object* v___y_1602_, lean_object* v___y_1603_){
_start:
{
lean_object* v_res_1604_; 
v_res_1604_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1596_, v_b_1597_, v_c_1598_, v___y_1599_, v___y_1600_, v___y_1601_, v___y_1602_);
lean_dec(v___y_1602_);
lean_dec_ref(v___y_1601_);
lean_dec(v___y_1600_);
lean_dec_ref(v___y_1599_);
return v_res_1604_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object* v_type_1605_, lean_object* v_k_1606_, uint8_t v_cleanupAnnotations_1607_, uint8_t v_whnfType_1608_, lean_object* v___y_1609_, lean_object* v___y_1610_, lean_object* v___y_1611_, lean_object* v___y_1612_){
_start:
{
lean_object* v___f_1614_; lean_object* v___x_1615_; 
v___f_1614_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1614_, 0, v_k_1606_);
v___x_1615_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1605_, v___f_1614_, v_cleanupAnnotations_1607_, v_whnfType_1608_, v___y_1609_, v___y_1610_, v___y_1611_, v___y_1612_);
if (lean_obj_tag(v___x_1615_) == 0)
{
lean_object* v_a_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1623_; 
v_a_1616_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1623_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1623_ == 0)
{
v___x_1618_ = v___x_1615_;
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_a_1616_);
lean_dec(v___x_1615_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1623_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
lean_object* v___x_1621_; 
if (v_isShared_1619_ == 0)
{
v___x_1621_ = v___x_1618_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_a_1616_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
else
{
lean_object* v_a_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1631_; 
v_a_1624_ = lean_ctor_get(v___x_1615_, 0);
v_isSharedCheck_1631_ = !lean_is_exclusive(v___x_1615_);
if (v_isSharedCheck_1631_ == 0)
{
v___x_1626_ = v___x_1615_;
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
else
{
lean_inc(v_a_1624_);
lean_dec(v___x_1615_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1631_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1629_; 
if (v_isShared_1627_ == 0)
{
v___x_1629_ = v___x_1626_;
goto v_reusejp_1628_;
}
else
{
lean_object* v_reuseFailAlloc_1630_; 
v_reuseFailAlloc_1630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1630_, 0, v_a_1624_);
v___x_1629_ = v_reuseFailAlloc_1630_;
goto v_reusejp_1628_;
}
v_reusejp_1628_:
{
return v___x_1629_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object* v_type_1632_, lean_object* v_k_1633_, lean_object* v_cleanupAnnotations_1634_, lean_object* v_whnfType_1635_, lean_object* v___y_1636_, lean_object* v___y_1637_, lean_object* v___y_1638_, lean_object* v___y_1639_, lean_object* v___y_1640_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1641_; uint8_t v_whnfType_boxed_1642_; lean_object* v_res_1643_; 
v_cleanupAnnotations_boxed_1641_ = lean_unbox(v_cleanupAnnotations_1634_);
v_whnfType_boxed_1642_ = lean_unbox(v_whnfType_1635_);
v_res_1643_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1632_, v_k_1633_, v_cleanupAnnotations_boxed_1641_, v_whnfType_boxed_1642_, v___y_1636_, v___y_1637_, v___y_1638_, v___y_1639_);
lean_dec(v___y_1639_);
lean_dec_ref(v___y_1638_);
lean_dec(v___y_1637_);
lean_dec_ref(v___y_1636_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object* v_00_u03b1_1644_, lean_object* v_type_1645_, lean_object* v_k_1646_, uint8_t v_cleanupAnnotations_1647_, uint8_t v_whnfType_1648_, lean_object* v___y_1649_, lean_object* v___y_1650_, lean_object* v___y_1651_, lean_object* v___y_1652_){
_start:
{
lean_object* v___x_1654_; 
v___x_1654_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1645_, v_k_1646_, v_cleanupAnnotations_1647_, v_whnfType_1648_, v___y_1649_, v___y_1650_, v___y_1651_, v___y_1652_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object* v_00_u03b1_1655_, lean_object* v_type_1656_, lean_object* v_k_1657_, lean_object* v_cleanupAnnotations_1658_, lean_object* v_whnfType_1659_, lean_object* v___y_1660_, lean_object* v___y_1661_, lean_object* v___y_1662_, lean_object* v___y_1663_, lean_object* v___y_1664_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1665_; uint8_t v_whnfType_boxed_1666_; lean_object* v_res_1667_; 
v_cleanupAnnotations_boxed_1665_ = lean_unbox(v_cleanupAnnotations_1658_);
v_whnfType_boxed_1666_ = lean_unbox(v_whnfType_1659_);
v_res_1667_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(v_00_u03b1_1655_, v_type_1656_, v_k_1657_, v_cleanupAnnotations_boxed_1665_, v_whnfType_boxed_1666_, v___y_1660_, v___y_1661_, v___y_1662_, v___y_1663_);
lean_dec(v___y_1663_);
lean_dec_ref(v___y_1662_);
lean_dec(v___y_1661_);
lean_dec_ref(v___y_1660_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object* v_as_1671_, size_t v_sz_1672_, size_t v_i_1673_, lean_object* v_b_1674_, lean_object* v___y_1675_, lean_object* v___y_1676_, lean_object* v___y_1677_, lean_object* v___y_1678_){
_start:
{
lean_object* v_a_1681_; uint8_t v___x_1685_; 
v___x_1685_ = lean_usize_dec_lt(v_i_1673_, v_sz_1672_);
if (v___x_1685_ == 0)
{
lean_object* v___x_1686_; 
v___x_1686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1686_, 0, v_b_1674_);
return v___x_1686_;
}
else
{
lean_object* v_fst_1687_; lean_object* v_snd_1688_; lean_object* v___x_1690_; uint8_t v_isShared_1691_; uint8_t v_isSharedCheck_1735_; 
v_fst_1687_ = lean_ctor_get(v_b_1674_, 0);
v_snd_1688_ = lean_ctor_get(v_b_1674_, 1);
v_isSharedCheck_1735_ = !lean_is_exclusive(v_b_1674_);
if (v_isSharedCheck_1735_ == 0)
{
v___x_1690_ = v_b_1674_;
v_isShared_1691_ = v_isSharedCheck_1735_;
goto v_resetjp_1689_;
}
else
{
lean_inc(v_snd_1688_);
lean_inc(v_fst_1687_);
lean_dec(v_b_1674_);
v___x_1690_ = lean_box(0);
v_isShared_1691_ = v_isSharedCheck_1735_;
goto v_resetjp_1689_;
}
v_resetjp_1689_:
{
lean_object* v_next_1697_; 
v_next_1697_ = lean_ctor_get(v_snd_1688_, 0);
lean_inc(v_next_1697_);
if (lean_obj_tag(v_next_1697_) == 0)
{
goto v___jp_1692_;
}
else
{
lean_object* v_upperBound_1698_; lean_object* v_val_1699_; lean_object* v___x_1701_; uint8_t v_isShared_1702_; uint8_t v_isSharedCheck_1734_; 
v_upperBound_1698_ = lean_ctor_get(v_snd_1688_, 1);
v_val_1699_ = lean_ctor_get(v_next_1697_, 0);
v_isSharedCheck_1734_ = !lean_is_exclusive(v_next_1697_);
if (v_isSharedCheck_1734_ == 0)
{
v___x_1701_ = v_next_1697_;
v_isShared_1702_ = v_isSharedCheck_1734_;
goto v_resetjp_1700_;
}
else
{
lean_inc(v_val_1699_);
lean_dec(v_next_1697_);
v___x_1701_ = lean_box(0);
v_isShared_1702_ = v_isSharedCheck_1734_;
goto v_resetjp_1700_;
}
v_resetjp_1700_:
{
uint8_t v___x_1703_; 
v___x_1703_ = lean_nat_dec_lt(v_val_1699_, v_upperBound_1698_);
if (v___x_1703_ == 0)
{
lean_del_object(v___x_1701_);
lean_dec(v_val_1699_);
goto v___jp_1692_;
}
else
{
lean_object* v___x_1705_; uint8_t v_isShared_1706_; uint8_t v_isSharedCheck_1731_; 
lean_inc(v_upperBound_1698_);
lean_del_object(v___x_1690_);
v_isSharedCheck_1731_ = !lean_is_exclusive(v_snd_1688_);
if (v_isSharedCheck_1731_ == 0)
{
lean_object* v_unused_1732_; lean_object* v_unused_1733_; 
v_unused_1732_ = lean_ctor_get(v_snd_1688_, 1);
lean_dec(v_unused_1732_);
v_unused_1733_ = lean_ctor_get(v_snd_1688_, 0);
lean_dec(v_unused_1733_);
v___x_1705_ = v_snd_1688_;
v_isShared_1706_ = v_isSharedCheck_1731_;
goto v_resetjp_1704_;
}
else
{
lean_dec(v_snd_1688_);
v___x_1705_ = lean_box(0);
v_isShared_1706_ = v_isSharedCheck_1731_;
goto v_resetjp_1704_;
}
v_resetjp_1704_:
{
lean_object* v_a_1707_; lean_object* v___x_1708_; lean_object* v___x_1709_; lean_object* v___x_1711_; 
v_a_1707_ = lean_array_uget_borrowed(v_as_1671_, v_i_1673_);
v___x_1708_ = lean_unsigned_to_nat(1u);
v___x_1709_ = lean_nat_add(v_val_1699_, v___x_1708_);
if (v_isShared_1702_ == 0)
{
lean_ctor_set(v___x_1701_, 0, v___x_1709_);
v___x_1711_ = v___x_1701_;
goto v_reusejp_1710_;
}
else
{
lean_object* v_reuseFailAlloc_1730_; 
v_reuseFailAlloc_1730_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1730_, 0, v___x_1709_);
v___x_1711_ = v_reuseFailAlloc_1730_;
goto v_reusejp_1710_;
}
v_reusejp_1710_:
{
lean_object* v___x_1713_; 
if (v_isShared_1706_ == 0)
{
lean_ctor_set(v___x_1705_, 0, v___x_1711_);
v___x_1713_ = v___x_1705_;
goto v_reusejp_1712_;
}
else
{
lean_object* v_reuseFailAlloc_1729_; 
v_reuseFailAlloc_1729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1729_, 0, v___x_1711_);
lean_ctor_set(v_reuseFailAlloc_1729_, 1, v_upperBound_1698_);
v___x_1713_ = v_reuseFailAlloc_1729_;
goto v_reusejp_1712_;
}
v_reusejp_1712_:
{
lean_object* v___x_1714_; 
lean_inc(v___y_1678_);
lean_inc_ref(v___y_1677_);
lean_inc(v___y_1676_);
lean_inc_ref(v___y_1675_);
lean_inc(v_a_1707_);
v___x_1714_ = lean_infer_type(v_a_1707_, v___y_1675_, v___y_1676_, v___y_1677_, v___y_1678_);
if (lean_obj_tag(v___x_1714_) == 0)
{
lean_object* v_a_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_a_1715_ = lean_ctor_get(v___x_1714_, 0);
lean_inc(v_a_1715_);
lean_dec_ref_known(v___x_1714_, 1);
v___x_1716_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1));
v___x_1717_ = l_Lean_Expr_isAppOf(v_a_1715_, v___x_1716_);
lean_dec(v_a_1715_);
if (v___x_1717_ == 0)
{
lean_object* v___x_1718_; 
lean_dec(v_val_1699_);
v___x_1718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1718_, 0, v_fst_1687_);
lean_ctor_set(v___x_1718_, 1, v___x_1713_);
v_a_1681_ = v___x_1718_;
goto v___jp_1680_;
}
else
{
lean_object* v___x_1719_; lean_object* v___x_1720_; 
v___x_1719_ = lean_array_push(v_fst_1687_, v_val_1699_);
v___x_1720_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1720_, 0, v___x_1719_);
lean_ctor_set(v___x_1720_, 1, v___x_1713_);
v_a_1681_ = v___x_1720_;
goto v___jp_1680_;
}
}
else
{
lean_object* v_a_1721_; lean_object* v___x_1723_; uint8_t v_isShared_1724_; uint8_t v_isSharedCheck_1728_; 
lean_dec_ref(v___x_1713_);
lean_dec(v_val_1699_);
lean_dec(v_fst_1687_);
v_a_1721_ = lean_ctor_get(v___x_1714_, 0);
v_isSharedCheck_1728_ = !lean_is_exclusive(v___x_1714_);
if (v_isSharedCheck_1728_ == 0)
{
v___x_1723_ = v___x_1714_;
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
else
{
lean_inc(v_a_1721_);
lean_dec(v___x_1714_);
v___x_1723_ = lean_box(0);
v_isShared_1724_ = v_isSharedCheck_1728_;
goto v_resetjp_1722_;
}
v_resetjp_1722_:
{
lean_object* v___x_1726_; 
if (v_isShared_1724_ == 0)
{
v___x_1726_ = v___x_1723_;
goto v_reusejp_1725_;
}
else
{
lean_object* v_reuseFailAlloc_1727_; 
v_reuseFailAlloc_1727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1727_, 0, v_a_1721_);
v___x_1726_ = v_reuseFailAlloc_1727_;
goto v_reusejp_1725_;
}
v_reusejp_1725_:
{
return v___x_1726_;
}
}
}
}
}
}
}
}
}
v___jp_1692_:
{
lean_object* v___x_1694_; 
if (v_isShared_1691_ == 0)
{
v___x_1694_ = v___x_1690_;
goto v_reusejp_1693_;
}
else
{
lean_object* v_reuseFailAlloc_1696_; 
v_reuseFailAlloc_1696_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1696_, 0, v_fst_1687_);
lean_ctor_set(v_reuseFailAlloc_1696_, 1, v_snd_1688_);
v___x_1694_ = v_reuseFailAlloc_1696_;
goto v_reusejp_1693_;
}
v_reusejp_1693_:
{
lean_object* v___x_1695_; 
v___x_1695_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1695_, 0, v___x_1694_);
return v___x_1695_;
}
}
}
}
v___jp_1680_:
{
size_t v___x_1682_; size_t v___x_1683_; 
v___x_1682_ = ((size_t)1ULL);
v___x_1683_ = lean_usize_add(v_i_1673_, v___x_1682_);
v_i_1673_ = v___x_1683_;
v_b_1674_ = v_a_1681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object* v_as_1736_, lean_object* v_sz_1737_, lean_object* v_i_1738_, lean_object* v_b_1739_, lean_object* v___y_1740_, lean_object* v___y_1741_, lean_object* v___y_1742_, lean_object* v___y_1743_, lean_object* v___y_1744_){
_start:
{
size_t v_sz_boxed_1745_; size_t v_i_boxed_1746_; lean_object* v_res_1747_; 
v_sz_boxed_1745_ = lean_unbox_usize(v_sz_1737_);
lean_dec(v_sz_1737_);
v_i_boxed_1746_ = lean_unbox_usize(v_i_1738_);
lean_dec(v_i_1738_);
v_res_1747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_as_1736_, v_sz_boxed_1745_, v_i_boxed_1746_, v_b_1739_, v___y_1740_, v___y_1741_, v___y_1742_, v___y_1743_);
lean_dec(v___y_1743_);
lean_dec_ref(v___y_1742_);
lean_dec(v___y_1741_);
lean_dec_ref(v___y_1740_);
lean_dec_ref(v_as_1736_);
return v_res_1747_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object* v_declName_1752_, lean_object* v_args_1753_, lean_object* v_x_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
lean_object* v___x_1760_; lean_object* v___y_1762_; lean_object* v_env_1787_; lean_object* v___x_1788_; 
v___x_1760_ = lean_st_ref_get(v___y_1758_);
v_env_1787_ = lean_ctor_get(v___x_1760_, 0);
lean_inc_ref(v_env_1787_);
lean_dec(v___x_1760_);
v___x_1788_ = l_Lean_getOutParamPositions_x3f(v_env_1787_, v_declName_1752_);
if (lean_obj_tag(v___x_1788_) == 0)
{
lean_object* v___x_1789_; 
v___x_1789_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___y_1762_ = v___x_1789_;
goto v___jp_1761_;
}
else
{
lean_object* v_val_1790_; 
v_val_1790_ = lean_ctor_get(v___x_1788_, 0);
lean_inc(v_val_1790_);
lean_dec_ref_known(v___x_1788_, 1);
v___y_1762_ = v_val_1790_;
goto v___jp_1761_;
}
v___jp_1761_:
{
lean_object* v___x_1763_; lean_object* v___x_1764_; lean_object* v___x_1765_; lean_object* v___x_1766_; size_t v_sz_1767_; size_t v___x_1768_; lean_object* v___x_1769_; 
v___x_1763_ = lean_array_get_size(v_args_1753_);
v___x_1764_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_1765_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1765_, 0, v___x_1764_);
lean_ctor_set(v___x_1765_, 1, v___x_1763_);
v___x_1766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1766_, 0, v___y_1762_);
lean_ctor_set(v___x_1766_, 1, v___x_1765_);
v_sz_1767_ = lean_array_size(v_args_1753_);
v___x_1768_ = ((size_t)0ULL);
v___x_1769_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_args_1753_, v_sz_1767_, v___x_1768_, v___x_1766_, v___y_1755_, v___y_1756_, v___y_1757_, v___y_1758_);
if (lean_obj_tag(v___x_1769_) == 0)
{
lean_object* v_a_1770_; lean_object* v___x_1772_; uint8_t v_isShared_1773_; uint8_t v_isSharedCheck_1778_; 
v_a_1770_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1778_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1778_ == 0)
{
v___x_1772_ = v___x_1769_;
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
else
{
lean_inc(v_a_1770_);
lean_dec(v___x_1769_);
v___x_1772_ = lean_box(0);
v_isShared_1773_ = v_isSharedCheck_1778_;
goto v_resetjp_1771_;
}
v_resetjp_1771_:
{
lean_object* v_fst_1774_; lean_object* v___x_1776_; 
v_fst_1774_ = lean_ctor_get(v_a_1770_, 0);
lean_inc(v_fst_1774_);
lean_dec(v_a_1770_);
if (v_isShared_1773_ == 0)
{
lean_ctor_set(v___x_1772_, 0, v_fst_1774_);
v___x_1776_ = v___x_1772_;
goto v_reusejp_1775_;
}
else
{
lean_object* v_reuseFailAlloc_1777_; 
v_reuseFailAlloc_1777_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1777_, 0, v_fst_1774_);
v___x_1776_ = v_reuseFailAlloc_1777_;
goto v_reusejp_1775_;
}
v_reusejp_1775_:
{
return v___x_1776_;
}
}
}
else
{
lean_object* v_a_1779_; lean_object* v___x_1781_; uint8_t v_isShared_1782_; uint8_t v_isSharedCheck_1786_; 
v_a_1779_ = lean_ctor_get(v___x_1769_, 0);
v_isSharedCheck_1786_ = !lean_is_exclusive(v___x_1769_);
if (v_isSharedCheck_1786_ == 0)
{
v___x_1781_ = v___x_1769_;
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
else
{
lean_inc(v_a_1779_);
lean_dec(v___x_1769_);
v___x_1781_ = lean_box(0);
v_isShared_1782_ = v_isSharedCheck_1786_;
goto v_resetjp_1780_;
}
v_resetjp_1780_:
{
lean_object* v___x_1784_; 
if (v_isShared_1782_ == 0)
{
v___x_1784_ = v___x_1781_;
goto v_reusejp_1783_;
}
else
{
lean_object* v_reuseFailAlloc_1785_; 
v_reuseFailAlloc_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1785_, 0, v_a_1779_);
v___x_1784_ = v_reuseFailAlloc_1785_;
goto v_reusejp_1783_;
}
v_reusejp_1783_:
{
return v___x_1784_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object* v_declName_1791_, lean_object* v_args_1792_, lean_object* v_x_1793_, lean_object* v___y_1794_, lean_object* v___y_1795_, lean_object* v___y_1796_, lean_object* v___y_1797_, lean_object* v___y_1798_){
_start:
{
lean_object* v_res_1799_; 
v_res_1799_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(v_declName_1791_, v_args_1792_, v_x_1793_, v___y_1794_, v___y_1795_, v___y_1796_, v___y_1797_);
lean_dec(v___y_1797_);
lean_dec_ref(v___y_1796_);
lean_dec(v___y_1795_);
lean_dec_ref(v___y_1794_);
lean_dec_ref(v_x_1793_);
lean_dec_ref(v_args_1792_);
lean_dec(v_declName_1791_);
return v_res_1799_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object* v_classTy_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_){
_start:
{
lean_object* v___x_1806_; 
v___x_1806_ = l_Lean_Expr_getAppFn(v_classTy_1800_);
if (lean_obj_tag(v___x_1806_) == 4)
{
lean_object* v_declName_1807_; lean_object* v___f_1808_; lean_object* v___x_1809_; 
v_declName_1807_ = lean_ctor_get(v___x_1806_, 0);
lean_inc(v_declName_1807_);
v___f_1808_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1808_, 0, v_declName_1807_);
lean_inc(v_a_1804_);
lean_inc_ref(v_a_1803_);
lean_inc(v_a_1802_);
lean_inc_ref(v_a_1801_);
v___x_1809_ = lean_infer_type(v___x_1806_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v_a_1810_; uint8_t v___x_1811_; lean_object* v___x_1812_; 
v_a_1810_ = lean_ctor_get(v___x_1809_, 0);
lean_inc(v_a_1810_);
lean_dec_ref_known(v___x_1809_, 1);
v___x_1811_ = 0;
v___x_1812_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_1810_, v___f_1808_, v___x_1811_, v___x_1811_, v_a_1801_, v_a_1802_, v_a_1803_, v_a_1804_);
return v___x_1812_;
}
else
{
lean_object* v_a_1813_; lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
lean_dec_ref(v___f_1808_);
v_a_1813_ = lean_ctor_get(v___x_1809_, 0);
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1820_ == 0)
{
v___x_1815_ = v___x_1809_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_inc(v_a_1813_);
lean_dec(v___x_1809_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v_a_1813_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
}
else
{
lean_object* v___x_1821_; lean_object* v___x_1822_; 
lean_dec_ref(v___x_1806_);
v___x_1821_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_1822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1822_, 0, v___x_1821_);
return v___x_1822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object* v_classTy_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_, lean_object* v_a_1828_){
_start:
{
lean_object* v_res_1829_; 
v_res_1829_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_classTy_1823_, v_a_1824_, v_a_1825_, v_a_1826_, v_a_1827_);
lean_dec(v_a_1827_);
lean_dec_ref(v_a_1826_);
lean_dec(v_a_1825_);
lean_dec_ref(v_a_1824_);
lean_dec_ref(v_classTy_1823_);
return v_res_1829_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_a_1830_, lean_object* v_as_1831_, lean_object* v_j_1832_){
_start:
{
lean_object* v___x_1833_; uint8_t v___x_1834_; 
v___x_1833_ = lean_array_get_size(v_as_1831_);
v___x_1834_ = lean_nat_dec_lt(v_j_1832_, v___x_1833_);
if (v___x_1834_ == 0)
{
lean_object* v___x_1835_; 
lean_dec(v_j_1832_);
v___x_1835_ = lean_box(0);
return v___x_1835_;
}
else
{
lean_object* v___x_1836_; lean_object* v___x_1837_; uint8_t v___x_1838_; 
v___x_1836_ = lean_array_fget_borrowed(v_as_1831_, v_j_1832_);
v___x_1837_ = l_Lean_Expr_mvarId_x21(v___x_1836_);
v___x_1838_ = l_Lean_instBEqMVarId_beq(v___x_1837_, v_a_1830_);
lean_dec(v___x_1837_);
if (v___x_1838_ == 0)
{
lean_object* v___x_1839_; lean_object* v___x_1840_; 
v___x_1839_ = lean_unsigned_to_nat(1u);
v___x_1840_ = lean_nat_add(v_j_1832_, v___x_1839_);
lean_dec(v_j_1832_);
v_j_1832_ = v___x_1840_;
goto _start;
}
else
{
lean_object* v___x_1842_; 
v___x_1842_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1842_, 0, v_j_1832_);
return v___x_1842_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_a_1843_, lean_object* v_as_1844_, lean_object* v_j_1845_){
_start:
{
lean_object* v_res_1846_; 
v_res_1846_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1843_, v_as_1844_, v_j_1845_);
lean_dec_ref(v_as_1844_);
lean_dec(v_a_1843_);
return v_res_1846_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1847_, lean_object* v_x_1848_, lean_object* v_x_1849_, lean_object* v_x_1850_){
_start:
{
lean_object* v_ks_1851_; lean_object* v_vs_1852_; lean_object* v___x_1854_; uint8_t v_isShared_1855_; uint8_t v_isSharedCheck_1876_; 
v_ks_1851_ = lean_ctor_get(v_x_1847_, 0);
v_vs_1852_ = lean_ctor_get(v_x_1847_, 1);
v_isSharedCheck_1876_ = !lean_is_exclusive(v_x_1847_);
if (v_isSharedCheck_1876_ == 0)
{
v___x_1854_ = v_x_1847_;
v_isShared_1855_ = v_isSharedCheck_1876_;
goto v_resetjp_1853_;
}
else
{
lean_inc(v_vs_1852_);
lean_inc(v_ks_1851_);
lean_dec(v_x_1847_);
v___x_1854_ = lean_box(0);
v_isShared_1855_ = v_isSharedCheck_1876_;
goto v_resetjp_1853_;
}
v_resetjp_1853_:
{
lean_object* v___x_1856_; uint8_t v___x_1857_; 
v___x_1856_ = lean_array_get_size(v_ks_1851_);
v___x_1857_ = lean_nat_dec_lt(v_x_1848_, v___x_1856_);
if (v___x_1857_ == 0)
{
lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1861_; 
lean_dec(v_x_1848_);
v___x_1858_ = lean_array_push(v_ks_1851_, v_x_1849_);
v___x_1859_ = lean_array_push(v_vs_1852_, v_x_1850_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 1, v___x_1859_);
lean_ctor_set(v___x_1854_, 0, v___x_1858_);
v___x_1861_ = v___x_1854_;
goto v_reusejp_1860_;
}
else
{
lean_object* v_reuseFailAlloc_1862_; 
v_reuseFailAlloc_1862_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1862_, 0, v___x_1858_);
lean_ctor_set(v_reuseFailAlloc_1862_, 1, v___x_1859_);
v___x_1861_ = v_reuseFailAlloc_1862_;
goto v_reusejp_1860_;
}
v_reusejp_1860_:
{
return v___x_1861_;
}
}
else
{
lean_object* v_k_x27_1863_; uint8_t v___x_1864_; 
v_k_x27_1863_ = lean_array_fget_borrowed(v_ks_1851_, v_x_1848_);
v___x_1864_ = l_Lean_instBEqMVarId_beq(v_x_1849_, v_k_x27_1863_);
if (v___x_1864_ == 0)
{
lean_object* v___x_1866_; 
if (v_isShared_1855_ == 0)
{
v___x_1866_ = v___x_1854_;
goto v_reusejp_1865_;
}
else
{
lean_object* v_reuseFailAlloc_1870_; 
v_reuseFailAlloc_1870_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1870_, 0, v_ks_1851_);
lean_ctor_set(v_reuseFailAlloc_1870_, 1, v_vs_1852_);
v___x_1866_ = v_reuseFailAlloc_1870_;
goto v_reusejp_1865_;
}
v_reusejp_1865_:
{
lean_object* v___x_1867_; lean_object* v___x_1868_; 
v___x_1867_ = lean_unsigned_to_nat(1u);
v___x_1868_ = lean_nat_add(v_x_1848_, v___x_1867_);
lean_dec(v_x_1848_);
v_x_1847_ = v___x_1866_;
v_x_1848_ = v___x_1868_;
goto _start;
}
}
else
{
lean_object* v___x_1871_; lean_object* v___x_1872_; lean_object* v___x_1874_; 
v___x_1871_ = lean_array_fset(v_ks_1851_, v_x_1848_, v_x_1849_);
v___x_1872_ = lean_array_fset(v_vs_1852_, v_x_1848_, v_x_1850_);
lean_dec(v_x_1848_);
if (v_isShared_1855_ == 0)
{
lean_ctor_set(v___x_1854_, 1, v___x_1872_);
lean_ctor_set(v___x_1854_, 0, v___x_1871_);
v___x_1874_ = v___x_1854_;
goto v_reusejp_1873_;
}
else
{
lean_object* v_reuseFailAlloc_1875_; 
v_reuseFailAlloc_1875_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1875_, 0, v___x_1871_);
lean_ctor_set(v_reuseFailAlloc_1875_, 1, v___x_1872_);
v___x_1874_ = v_reuseFailAlloc_1875_;
goto v_reusejp_1873_;
}
v_reusejp_1873_:
{
return v___x_1874_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1877_, lean_object* v_k_1878_, lean_object* v_v_1879_){
_start:
{
lean_object* v___x_1880_; lean_object* v___x_1881_; 
v___x_1880_ = lean_unsigned_to_nat(0u);
v___x_1881_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1877_, v___x_1880_, v_k_1878_, v_v_1879_);
return v___x_1881_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1882_, size_t v_x_1883_, size_t v_x_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_){
_start:
{
if (lean_obj_tag(v_x_1882_) == 0)
{
lean_object* v_es_1887_; size_t v___x_1888_; size_t v___x_1889_; lean_object* v_j_1890_; lean_object* v___x_1891_; uint8_t v___x_1892_; 
v_es_1887_ = lean_ctor_get(v_x_1882_, 0);
v___x_1888_ = ((size_t)31ULL);
v___x_1889_ = lean_usize_land(v_x_1883_, v___x_1888_);
v_j_1890_ = lean_usize_to_nat(v___x_1889_);
v___x_1891_ = lean_array_get_size(v_es_1887_);
v___x_1892_ = lean_nat_dec_lt(v_j_1890_, v___x_1891_);
if (v___x_1892_ == 0)
{
lean_dec(v_j_1890_);
lean_dec(v_x_1886_);
lean_dec(v_x_1885_);
return v_x_1882_;
}
else
{
lean_object* v___x_1894_; uint8_t v_isShared_1895_; uint8_t v_isSharedCheck_1931_; 
lean_inc_ref(v_es_1887_);
v_isSharedCheck_1931_ = !lean_is_exclusive(v_x_1882_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v_x_1882_, 0);
lean_dec(v_unused_1932_);
v___x_1894_ = v_x_1882_;
v_isShared_1895_ = v_isSharedCheck_1931_;
goto v_resetjp_1893_;
}
else
{
lean_dec(v_x_1882_);
v___x_1894_ = lean_box(0);
v_isShared_1895_ = v_isSharedCheck_1931_;
goto v_resetjp_1893_;
}
v_resetjp_1893_:
{
lean_object* v_v_1896_; lean_object* v___x_1897_; lean_object* v_xs_x27_1898_; lean_object* v___y_1900_; 
v_v_1896_ = lean_array_fget(v_es_1887_, v_j_1890_);
v___x_1897_ = lean_box(0);
v_xs_x27_1898_ = lean_array_fset(v_es_1887_, v_j_1890_, v___x_1897_);
switch(lean_obj_tag(v_v_1896_))
{
case 0:
{
lean_object* v_key_1905_; lean_object* v_val_1906_; lean_object* v___x_1908_; uint8_t v_isShared_1909_; uint8_t v_isSharedCheck_1916_; 
v_key_1905_ = lean_ctor_get(v_v_1896_, 0);
v_val_1906_ = lean_ctor_get(v_v_1896_, 1);
v_isSharedCheck_1916_ = !lean_is_exclusive(v_v_1896_);
if (v_isSharedCheck_1916_ == 0)
{
v___x_1908_ = v_v_1896_;
v_isShared_1909_ = v_isSharedCheck_1916_;
goto v_resetjp_1907_;
}
else
{
lean_inc(v_val_1906_);
lean_inc(v_key_1905_);
lean_dec(v_v_1896_);
v___x_1908_ = lean_box(0);
v_isShared_1909_ = v_isSharedCheck_1916_;
goto v_resetjp_1907_;
}
v_resetjp_1907_:
{
uint8_t v___x_1910_; 
v___x_1910_ = l_Lean_instBEqMVarId_beq(v_x_1885_, v_key_1905_);
if (v___x_1910_ == 0)
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_del_object(v___x_1908_);
v___x_1911_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1905_, v_val_1906_, v_x_1885_, v_x_1886_);
v___x_1912_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1912_, 0, v___x_1911_);
v___y_1900_ = v___x_1912_;
goto v___jp_1899_;
}
else
{
lean_object* v___x_1914_; 
lean_dec(v_val_1906_);
lean_dec(v_key_1905_);
if (v_isShared_1909_ == 0)
{
lean_ctor_set(v___x_1908_, 1, v_x_1886_);
lean_ctor_set(v___x_1908_, 0, v_x_1885_);
v___x_1914_ = v___x_1908_;
goto v_reusejp_1913_;
}
else
{
lean_object* v_reuseFailAlloc_1915_; 
v_reuseFailAlloc_1915_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1915_, 0, v_x_1885_);
lean_ctor_set(v_reuseFailAlloc_1915_, 1, v_x_1886_);
v___x_1914_ = v_reuseFailAlloc_1915_;
goto v_reusejp_1913_;
}
v_reusejp_1913_:
{
v___y_1900_ = v___x_1914_;
goto v___jp_1899_;
}
}
}
}
case 1:
{
lean_object* v_node_1917_; lean_object* v___x_1919_; uint8_t v_isShared_1920_; uint8_t v_isSharedCheck_1929_; 
v_node_1917_ = lean_ctor_get(v_v_1896_, 0);
v_isSharedCheck_1929_ = !lean_is_exclusive(v_v_1896_);
if (v_isSharedCheck_1929_ == 0)
{
v___x_1919_ = v_v_1896_;
v_isShared_1920_ = v_isSharedCheck_1929_;
goto v_resetjp_1918_;
}
else
{
lean_inc(v_node_1917_);
lean_dec(v_v_1896_);
v___x_1919_ = lean_box(0);
v_isShared_1920_ = v_isSharedCheck_1929_;
goto v_resetjp_1918_;
}
v_resetjp_1918_:
{
size_t v___x_1921_; size_t v___x_1922_; size_t v___x_1923_; size_t v___x_1924_; lean_object* v___x_1925_; lean_object* v___x_1927_; 
v___x_1921_ = ((size_t)5ULL);
v___x_1922_ = lean_usize_shift_right(v_x_1883_, v___x_1921_);
v___x_1923_ = ((size_t)1ULL);
v___x_1924_ = lean_usize_add(v_x_1884_, v___x_1923_);
v___x_1925_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_node_1917_, v___x_1922_, v___x_1924_, v_x_1885_, v_x_1886_);
if (v_isShared_1920_ == 0)
{
lean_ctor_set(v___x_1919_, 0, v___x_1925_);
v___x_1927_ = v___x_1919_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1928_; 
v_reuseFailAlloc_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1928_, 0, v___x_1925_);
v___x_1927_ = v_reuseFailAlloc_1928_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
v___y_1900_ = v___x_1927_;
goto v___jp_1899_;
}
}
}
default: 
{
lean_object* v___x_1930_; 
v___x_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1930_, 0, v_x_1885_);
lean_ctor_set(v___x_1930_, 1, v_x_1886_);
v___y_1900_ = v___x_1930_;
goto v___jp_1899_;
}
}
v___jp_1899_:
{
lean_object* v___x_1901_; lean_object* v___x_1903_; 
v___x_1901_ = lean_array_fset(v_xs_x27_1898_, v_j_1890_, v___y_1900_);
lean_dec(v_j_1890_);
if (v_isShared_1895_ == 0)
{
lean_ctor_set(v___x_1894_, 0, v___x_1901_);
v___x_1903_ = v___x_1894_;
goto v_reusejp_1902_;
}
else
{
lean_object* v_reuseFailAlloc_1904_; 
v_reuseFailAlloc_1904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1904_, 0, v___x_1901_);
v___x_1903_ = v_reuseFailAlloc_1904_;
goto v_reusejp_1902_;
}
v_reusejp_1902_:
{
return v___x_1903_;
}
}
}
}
}
else
{
lean_object* v_ks_1933_; lean_object* v_vs_1934_; lean_object* v___x_1936_; uint8_t v_isShared_1937_; uint8_t v_isSharedCheck_1952_; 
v_ks_1933_ = lean_ctor_get(v_x_1882_, 0);
v_vs_1934_ = lean_ctor_get(v_x_1882_, 1);
v_isSharedCheck_1952_ = !lean_is_exclusive(v_x_1882_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1936_ = v_x_1882_;
v_isShared_1937_ = v_isSharedCheck_1952_;
goto v_resetjp_1935_;
}
else
{
lean_inc(v_vs_1934_);
lean_inc(v_ks_1933_);
lean_dec(v_x_1882_);
v___x_1936_ = lean_box(0);
v_isShared_1937_ = v_isSharedCheck_1952_;
goto v_resetjp_1935_;
}
v_resetjp_1935_:
{
lean_object* v___x_1939_; 
if (v_isShared_1937_ == 0)
{
v___x_1939_ = v___x_1936_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_ks_1933_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_vs_1934_);
v___x_1939_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v_newNode_1940_; size_t v___x_1941_; uint8_t v___x_1942_; 
v_newNode_1940_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v___x_1939_, v_x_1885_, v_x_1886_);
v___x_1941_ = ((size_t)7ULL);
v___x_1942_ = lean_usize_dec_le(v___x_1941_, v_x_1884_);
if (v___x_1942_ == 0)
{
lean_object* v___x_1943_; lean_object* v___x_1944_; uint8_t v___x_1945_; 
v___x_1943_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1940_);
v___x_1944_ = lean_unsigned_to_nat(4u);
v___x_1945_ = lean_nat_dec_lt(v___x_1943_, v___x_1944_);
lean_dec(v___x_1943_);
if (v___x_1945_ == 0)
{
lean_object* v_ks_1946_; lean_object* v_vs_1947_; lean_object* v___x_1948_; lean_object* v___x_1949_; lean_object* v___x_1950_; 
v_ks_1946_ = lean_ctor_get(v_newNode_1940_, 0);
lean_inc_ref(v_ks_1946_);
v_vs_1947_ = lean_ctor_get(v_newNode_1940_, 1);
lean_inc_ref(v_vs_1947_);
lean_dec_ref(v_newNode_1940_);
v___x_1948_ = lean_unsigned_to_nat(0u);
v___x_1949_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00__private_Lean_Meta_Instances_0__Lean_Meta_Instances_logChange_spec__0_spec__0___redArg___closed__0);
v___x_1950_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_x_1884_, v_ks_1946_, v_vs_1947_, v___x_1948_, v___x_1949_);
lean_dec_ref(v_vs_1947_);
lean_dec_ref(v_ks_1946_);
return v___x_1950_;
}
else
{
return v_newNode_1940_;
}
}
else
{
return v_newNode_1940_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(size_t v_depth_1953_, lean_object* v_keys_1954_, lean_object* v_vals_1955_, lean_object* v_i_1956_, lean_object* v_entries_1957_){
_start:
{
lean_object* v___x_1958_; uint8_t v___x_1959_; 
v___x_1958_ = lean_array_get_size(v_keys_1954_);
v___x_1959_ = lean_nat_dec_lt(v_i_1956_, v___x_1958_);
if (v___x_1959_ == 0)
{
lean_dec(v_i_1956_);
return v_entries_1957_;
}
else
{
lean_object* v_k_1960_; lean_object* v_v_1961_; uint64_t v___x_1962_; size_t v_h_1963_; size_t v___x_1964_; lean_object* v___x_1965_; size_t v___x_1966_; size_t v___x_1967_; size_t v___x_1968_; size_t v_h_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v_k_1960_ = lean_array_fget_borrowed(v_keys_1954_, v_i_1956_);
v_v_1961_ = lean_array_fget_borrowed(v_vals_1955_, v_i_1956_);
v___x_1962_ = l_Lean_instHashableMVarId_hash(v_k_1960_);
v_h_1963_ = lean_uint64_to_usize(v___x_1962_);
v___x_1964_ = ((size_t)5ULL);
v___x_1965_ = lean_unsigned_to_nat(1u);
v___x_1966_ = ((size_t)1ULL);
v___x_1967_ = lean_usize_sub(v_depth_1953_, v___x_1966_);
v___x_1968_ = lean_usize_mul(v___x_1964_, v___x_1967_);
v_h_1969_ = lean_usize_shift_right(v_h_1963_, v___x_1968_);
v___x_1970_ = lean_nat_add(v_i_1956_, v___x_1965_);
lean_dec(v_i_1956_);
lean_inc(v_v_1961_);
lean_inc(v_k_1960_);
v___x_1971_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_entries_1957_, v_h_1969_, v_depth_1953_, v_k_1960_, v_v_1961_);
v_i_1956_ = v___x_1970_;
v_entries_1957_ = v___x_1971_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1973_, lean_object* v_keys_1974_, lean_object* v_vals_1975_, lean_object* v_i_1976_, lean_object* v_entries_1977_){
_start:
{
size_t v_depth_boxed_1978_; lean_object* v_res_1979_; 
v_depth_boxed_1978_ = lean_unbox_usize(v_depth_1973_);
lean_dec(v_depth_1973_);
v_res_1979_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1978_, v_keys_1974_, v_vals_1975_, v_i_1976_, v_entries_1977_);
lean_dec_ref(v_vals_1975_);
lean_dec_ref(v_keys_1974_);
return v_res_1979_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1980_, lean_object* v_x_1981_, lean_object* v_x_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_){
_start:
{
size_t v_x_1607__boxed_1985_; size_t v_x_1608__boxed_1986_; lean_object* v_res_1987_; 
v_x_1607__boxed_1985_ = lean_unbox_usize(v_x_1981_);
lean_dec(v_x_1981_);
v_x_1608__boxed_1986_ = lean_unbox_usize(v_x_1982_);
lean_dec(v_x_1982_);
v_res_1987_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1980_, v_x_1607__boxed_1985_, v_x_1608__boxed_1986_, v_x_1983_, v_x_1984_);
return v_res_1987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_){
_start:
{
uint64_t v___x_1991_; size_t v___x_1992_; size_t v___x_1993_; lean_object* v___x_1994_; 
v___x_1991_ = l_Lean_instHashableMVarId_hash(v_x_1989_);
v___x_1992_ = lean_uint64_to_usize(v___x_1991_);
v___x_1993_ = ((size_t)1ULL);
v___x_1994_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1988_, v___x_1992_, v___x_1993_, v_x_1989_, v_x_1990_);
return v___x_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(lean_object* v_mvarId_1995_, lean_object* v_val_1996_, lean_object* v___y_1997_){
_start:
{
lean_object* v___x_1999_; lean_object* v_mctx_2000_; lean_object* v_cache_2001_; lean_object* v_zetaDeltaFVarIds_2002_; lean_object* v_postponed_2003_; lean_object* v_diag_2004_; lean_object* v___x_2006_; uint8_t v_isShared_2007_; uint8_t v_isSharedCheck_2033_; 
v___x_1999_ = lean_st_ref_take(v___y_1997_);
v_mctx_2000_ = lean_ctor_get(v___x_1999_, 0);
v_cache_2001_ = lean_ctor_get(v___x_1999_, 1);
v_zetaDeltaFVarIds_2002_ = lean_ctor_get(v___x_1999_, 2);
v_postponed_2003_ = lean_ctor_get(v___x_1999_, 3);
v_diag_2004_ = lean_ctor_get(v___x_1999_, 4);
v_isSharedCheck_2033_ = !lean_is_exclusive(v___x_1999_);
if (v_isSharedCheck_2033_ == 0)
{
v___x_2006_ = v___x_1999_;
v_isShared_2007_ = v_isSharedCheck_2033_;
goto v_resetjp_2005_;
}
else
{
lean_inc(v_diag_2004_);
lean_inc(v_postponed_2003_);
lean_inc(v_zetaDeltaFVarIds_2002_);
lean_inc(v_cache_2001_);
lean_inc(v_mctx_2000_);
lean_dec(v___x_1999_);
v___x_2006_ = lean_box(0);
v_isShared_2007_ = v_isSharedCheck_2033_;
goto v_resetjp_2005_;
}
v_resetjp_2005_:
{
lean_object* v_depth_2008_; lean_object* v_levelAssignDepth_2009_; lean_object* v_lmvarCounter_2010_; lean_object* v_mvarCounter_2011_; lean_object* v_lDecls_2012_; lean_object* v_decls_2013_; lean_object* v_userNames_2014_; lean_object* v_lAssignment_2015_; lean_object* v_eAssignment_2016_; lean_object* v_dAssignment_2017_; lean_object* v_instanceTypedMVars_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2032_; 
v_depth_2008_ = lean_ctor_get(v_mctx_2000_, 0);
v_levelAssignDepth_2009_ = lean_ctor_get(v_mctx_2000_, 1);
v_lmvarCounter_2010_ = lean_ctor_get(v_mctx_2000_, 2);
v_mvarCounter_2011_ = lean_ctor_get(v_mctx_2000_, 3);
v_lDecls_2012_ = lean_ctor_get(v_mctx_2000_, 4);
v_decls_2013_ = lean_ctor_get(v_mctx_2000_, 5);
v_userNames_2014_ = lean_ctor_get(v_mctx_2000_, 6);
v_lAssignment_2015_ = lean_ctor_get(v_mctx_2000_, 7);
v_eAssignment_2016_ = lean_ctor_get(v_mctx_2000_, 8);
v_dAssignment_2017_ = lean_ctor_get(v_mctx_2000_, 9);
v_instanceTypedMVars_2018_ = lean_ctor_get(v_mctx_2000_, 10);
v_isSharedCheck_2032_ = !lean_is_exclusive(v_mctx_2000_);
if (v_isSharedCheck_2032_ == 0)
{
v___x_2020_ = v_mctx_2000_;
v_isShared_2021_ = v_isSharedCheck_2032_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_instanceTypedMVars_2018_);
lean_inc(v_dAssignment_2017_);
lean_inc(v_eAssignment_2016_);
lean_inc(v_lAssignment_2015_);
lean_inc(v_userNames_2014_);
lean_inc(v_decls_2013_);
lean_inc(v_lDecls_2012_);
lean_inc(v_mvarCounter_2011_);
lean_inc(v_lmvarCounter_2010_);
lean_inc(v_levelAssignDepth_2009_);
lean_inc(v_depth_2008_);
lean_dec(v_mctx_2000_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2032_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2022_; lean_object* v___x_2023_; lean_object* v___x_2025_; 
v___x_2022_ = lean_box(0);
v___x_2023_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_eAssignment_2016_, v_mvarId_1995_, v_val_1996_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 8, v___x_2023_);
v___x_2025_ = v___x_2020_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2031_; 
v_reuseFailAlloc_2031_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_2031_, 0, v_depth_2008_);
lean_ctor_set(v_reuseFailAlloc_2031_, 1, v_levelAssignDepth_2009_);
lean_ctor_set(v_reuseFailAlloc_2031_, 2, v_lmvarCounter_2010_);
lean_ctor_set(v_reuseFailAlloc_2031_, 3, v_mvarCounter_2011_);
lean_ctor_set(v_reuseFailAlloc_2031_, 4, v_lDecls_2012_);
lean_ctor_set(v_reuseFailAlloc_2031_, 5, v_decls_2013_);
lean_ctor_set(v_reuseFailAlloc_2031_, 6, v_userNames_2014_);
lean_ctor_set(v_reuseFailAlloc_2031_, 7, v_lAssignment_2015_);
lean_ctor_set(v_reuseFailAlloc_2031_, 8, v___x_2023_);
lean_ctor_set(v_reuseFailAlloc_2031_, 9, v_dAssignment_2017_);
lean_ctor_set(v_reuseFailAlloc_2031_, 10, v_instanceTypedMVars_2018_);
v___x_2025_ = v_reuseFailAlloc_2031_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2027_; 
if (v_isShared_2007_ == 0)
{
lean_ctor_set(v___x_2006_, 0, v___x_2025_);
v___x_2027_ = v___x_2006_;
goto v_reusejp_2026_;
}
else
{
lean_object* v_reuseFailAlloc_2030_; 
v_reuseFailAlloc_2030_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2030_, 0, v___x_2025_);
lean_ctor_set(v_reuseFailAlloc_2030_, 1, v_cache_2001_);
lean_ctor_set(v_reuseFailAlloc_2030_, 2, v_zetaDeltaFVarIds_2002_);
lean_ctor_set(v_reuseFailAlloc_2030_, 3, v_postponed_2003_);
lean_ctor_set(v_reuseFailAlloc_2030_, 4, v_diag_2004_);
v___x_2027_ = v_reuseFailAlloc_2030_;
goto v_reusejp_2026_;
}
v_reusejp_2026_:
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
v___x_2028_ = lean_st_ref_put(v___y_1997_, v___x_2027_);
v___x_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2029_, 0, v___x_2022_);
return v___x_2029_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg___boxed(lean_object* v_mvarId_2034_, lean_object* v_val_2035_, lean_object* v___y_2036_, lean_object* v___y_2037_){
_start:
{
lean_object* v_res_2038_; 
v_res_2038_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_2034_, v_val_2035_, v___y_2036_);
lean_dec(v___y_2036_);
return v_res_2038_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(lean_object* v_argMVars_2039_, lean_object* v_argVars_2040_, lean_object* v_as_2041_, size_t v_sz_2042_, size_t v_i_2043_, lean_object* v_b_2044_, lean_object* v___y_2045_, lean_object* v___y_2046_, lean_object* v___y_2047_, lean_object* v___y_2048_){
_start:
{
uint8_t v___x_2050_; 
v___x_2050_ = lean_usize_dec_lt(v_i_2043_, v_sz_2042_);
if (v___x_2050_ == 0)
{
lean_object* v___x_2051_; 
v___x_2051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2051_, 0, v_b_2044_);
return v___x_2051_;
}
else
{
lean_object* v___x_2052_; lean_object* v_a_2053_; lean_object* v___y_2055_; lean_object* v___y_2056_; lean_object* v___y_2057_; lean_object* v___y_2058_; lean_object* v___x_2074_; lean_object* v___x_2075_; 
v___x_2052_ = lean_box(0);
v_a_2053_ = lean_array_uget_borrowed(v_as_2041_, v_i_2043_);
v___x_2074_ = lean_unsigned_to_nat(0u);
v___x_2075_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_2053_, v_argMVars_2039_, v___x_2074_);
if (lean_obj_tag(v___x_2075_) == 1)
{
lean_object* v_val_2076_; lean_object* v___x_2077_; lean_object* v___x_2078_; lean_object* v___x_2079_; 
v_val_2076_ = lean_ctor_get(v___x_2075_, 0);
lean_inc(v_val_2076_);
lean_dec_ref_known(v___x_2075_, 1);
v___x_2077_ = l_Lean_instInhabitedExpr;
v___x_2078_ = lean_array_get_borrowed(v___x_2077_, v_argVars_2040_, v_val_2076_);
lean_dec(v_val_2076_);
lean_inc(v___x_2078_);
lean_inc(v_a_2053_);
v___x_2079_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_a_2053_, v___x_2078_, v___y_2046_);
if (lean_obj_tag(v___x_2079_) == 0)
{
lean_dec_ref_known(v___x_2079_, 1);
v___y_2055_ = v___y_2045_;
v___y_2056_ = v___y_2046_;
v___y_2057_ = v___y_2047_;
v___y_2058_ = v___y_2048_;
goto v___jp_2054_;
}
else
{
return v___x_2079_;
}
}
else
{
lean_dec(v___x_2075_);
v___y_2055_ = v___y_2045_;
v___y_2056_ = v___y_2046_;
v___y_2057_ = v___y_2047_;
v___y_2058_ = v___y_2048_;
goto v___jp_2054_;
}
v___jp_2054_:
{
lean_object* v___x_2059_; lean_object* v___x_2060_; 
lean_inc(v_a_2053_);
v___x_2059_ = l_Lean_Expr_mvar___override(v_a_2053_);
lean_inc(v___y_2058_);
lean_inc_ref(v___y_2057_);
lean_inc(v___y_2056_);
lean_inc_ref(v___y_2055_);
v___x_2060_ = lean_infer_type(v___x_2059_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2060_) == 0)
{
lean_object* v_a_2061_; lean_object* v___x_2062_; 
v_a_2061_ = lean_ctor_get(v___x_2060_, 0);
lean_inc(v_a_2061_);
lean_dec_ref_known(v___x_2060_, 1);
v___x_2062_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_2039_, v_argVars_2040_, v_a_2061_, v___y_2055_, v___y_2056_, v___y_2057_, v___y_2058_);
if (lean_obj_tag(v___x_2062_) == 0)
{
size_t v___x_2063_; size_t v___x_2064_; 
lean_dec_ref_known(v___x_2062_, 1);
v___x_2063_ = ((size_t)1ULL);
v___x_2064_ = lean_usize_add(v_i_2043_, v___x_2063_);
v_i_2043_ = v___x_2064_;
v_b_2044_ = v___x_2052_;
goto _start;
}
else
{
return v___x_2062_;
}
}
else
{
lean_object* v_a_2066_; lean_object* v___x_2068_; uint8_t v_isShared_2069_; uint8_t v_isSharedCheck_2073_; 
v_a_2066_ = lean_ctor_get(v___x_2060_, 0);
v_isSharedCheck_2073_ = !lean_is_exclusive(v___x_2060_);
if (v_isSharedCheck_2073_ == 0)
{
v___x_2068_ = v___x_2060_;
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
else
{
lean_inc(v_a_2066_);
lean_dec(v___x_2060_);
v___x_2068_ = lean_box(0);
v_isShared_2069_ = v_isSharedCheck_2073_;
goto v_resetjp_2067_;
}
v_resetjp_2067_:
{
lean_object* v___x_2071_; 
if (v_isShared_2069_ == 0)
{
v___x_2071_ = v___x_2068_;
goto v_reusejp_2070_;
}
else
{
lean_object* v_reuseFailAlloc_2072_; 
v_reuseFailAlloc_2072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2072_, 0, v_a_2066_);
v___x_2071_ = v_reuseFailAlloc_2072_;
goto v_reusejp_2070_;
}
v_reusejp_2070_:
{
return v___x_2071_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_2080_, lean_object* v_argVars_2081_, lean_object* v_e_2082_, lean_object* v_a_2083_, lean_object* v_a_2084_, lean_object* v_a_2085_, lean_object* v_a_2086_){
_start:
{
lean_object* v___x_2088_; 
v___x_2088_ = l_Lean_Meta_getMVars(v_e_2082_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
if (lean_obj_tag(v___x_2088_) == 0)
{
lean_object* v_a_2089_; lean_object* v___x_2090_; size_t v_sz_2091_; size_t v___x_2092_; lean_object* v___x_2093_; 
v_a_2089_ = lean_ctor_get(v___x_2088_, 0);
lean_inc(v_a_2089_);
lean_dec_ref_known(v___x_2088_, 1);
v___x_2090_ = lean_box(0);
v_sz_2091_ = lean_array_size(v_a_2089_);
v___x_2092_ = ((size_t)0ULL);
v___x_2093_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_2080_, v_argVars_2081_, v_a_2089_, v_sz_2091_, v___x_2092_, v___x_2090_, v_a_2083_, v_a_2084_, v_a_2085_, v_a_2086_);
lean_dec(v_a_2089_);
if (lean_obj_tag(v___x_2093_) == 0)
{
lean_object* v___x_2095_; uint8_t v_isShared_2096_; uint8_t v_isSharedCheck_2100_; 
v_isSharedCheck_2100_ = !lean_is_exclusive(v___x_2093_);
if (v_isSharedCheck_2100_ == 0)
{
lean_object* v_unused_2101_; 
v_unused_2101_ = lean_ctor_get(v___x_2093_, 0);
lean_dec(v_unused_2101_);
v___x_2095_ = v___x_2093_;
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
else
{
lean_dec(v___x_2093_);
v___x_2095_ = lean_box(0);
v_isShared_2096_ = v_isSharedCheck_2100_;
goto v_resetjp_2094_;
}
v_resetjp_2094_:
{
lean_object* v___x_2098_; 
if (v_isShared_2096_ == 0)
{
lean_ctor_set(v___x_2095_, 0, v___x_2090_);
v___x_2098_ = v___x_2095_;
goto v_reusejp_2097_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v___x_2090_);
v___x_2098_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2097_;
}
v_reusejp_2097_:
{
return v___x_2098_;
}
}
}
else
{
return v___x_2093_;
}
}
else
{
lean_object* v_a_2102_; lean_object* v___x_2104_; uint8_t v_isShared_2105_; uint8_t v_isSharedCheck_2109_; 
v_a_2102_ = lean_ctor_get(v___x_2088_, 0);
v_isSharedCheck_2109_ = !lean_is_exclusive(v___x_2088_);
if (v_isSharedCheck_2109_ == 0)
{
v___x_2104_ = v___x_2088_;
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
else
{
lean_inc(v_a_2102_);
lean_dec(v___x_2088_);
v___x_2104_ = lean_box(0);
v_isShared_2105_ = v_isSharedCheck_2109_;
goto v_resetjp_2103_;
}
v_resetjp_2103_:
{
lean_object* v___x_2107_; 
if (v_isShared_2105_ == 0)
{
v___x_2107_ = v___x_2104_;
goto v_reusejp_2106_;
}
else
{
lean_object* v_reuseFailAlloc_2108_; 
v_reuseFailAlloc_2108_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2108_, 0, v_a_2102_);
v___x_2107_ = v_reuseFailAlloc_2108_;
goto v_reusejp_2106_;
}
v_reusejp_2106_:
{
return v___x_2107_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_2110_, lean_object* v_argVars_2111_, lean_object* v_e_2112_, lean_object* v_a_2113_, lean_object* v_a_2114_, lean_object* v_a_2115_, lean_object* v_a_2116_, lean_object* v_a_2117_){
_start:
{
lean_object* v_res_2118_; 
v_res_2118_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_2110_, v_argVars_2111_, v_e_2112_, v_a_2113_, v_a_2114_, v_a_2115_, v_a_2116_);
lean_dec(v_a_2116_);
lean_dec_ref(v_a_2115_);
lean_dec(v_a_2114_);
lean_dec_ref(v_a_2113_);
lean_dec_ref(v_argVars_2111_);
lean_dec_ref(v_argMVars_2110_);
return v_res_2118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2___boxed(lean_object* v_argMVars_2119_, lean_object* v_argVars_2120_, lean_object* v_as_2121_, lean_object* v_sz_2122_, lean_object* v_i_2123_, lean_object* v_b_2124_, lean_object* v___y_2125_, lean_object* v___y_2126_, lean_object* v___y_2127_, lean_object* v___y_2128_, lean_object* v___y_2129_){
_start:
{
size_t v_sz_boxed_2130_; size_t v_i_boxed_2131_; lean_object* v_res_2132_; 
v_sz_boxed_2130_ = lean_unbox_usize(v_sz_2122_);
lean_dec(v_sz_2122_);
v_i_boxed_2131_ = lean_unbox_usize(v_i_2123_);
lean_dec(v_i_2123_);
v_res_2132_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_2119_, v_argVars_2120_, v_as_2121_, v_sz_boxed_2130_, v_i_boxed_2131_, v_b_2124_, v___y_2125_, v___y_2126_, v___y_2127_, v___y_2128_);
lean_dec(v___y_2128_);
lean_dec_ref(v___y_2127_);
lean_dec(v___y_2126_);
lean_dec_ref(v___y_2125_);
lean_dec_ref(v_as_2121_);
lean_dec_ref(v_argVars_2120_);
lean_dec_ref(v_argMVars_2119_);
return v_res_2132_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_mvarId_2133_, lean_object* v_val_2134_, lean_object* v___y_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_){
_start:
{
lean_object* v___x_2140_; 
v___x_2140_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_2133_, v_val_2134_, v___y_2136_);
return v___x_2140_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_mvarId_2141_, lean_object* v_val_2142_, lean_object* v___y_2143_, lean_object* v___y_2144_, lean_object* v___y_2145_, lean_object* v___y_2146_, lean_object* v___y_2147_){
_start:
{
lean_object* v_res_2148_; 
v_res_2148_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_mvarId_2141_, v_val_2142_, v___y_2143_, v___y_2144_, v___y_2145_, v___y_2146_);
lean_dec(v___y_2146_);
lean_dec_ref(v___y_2145_);
lean_dec(v___y_2144_);
lean_dec_ref(v___y_2143_);
return v_res_2148_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1(lean_object* v_00_u03b2_2149_, lean_object* v_x_2150_, lean_object* v_x_2151_, lean_object* v_x_2152_){
_start:
{
lean_object* v___x_2153_; 
v___x_2153_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_x_2150_, v_x_2151_, v_x_2152_);
return v___x_2153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_2154_, lean_object* v_x_2155_, size_t v_x_2156_, size_t v_x_2157_, lean_object* v_x_2158_, lean_object* v_x_2159_){
_start:
{
lean_object* v___x_2160_; 
v___x_2160_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_2155_, v_x_2156_, v_x_2157_, v_x_2158_, v_x_2159_);
return v___x_2160_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_2161_, lean_object* v_x_2162_, lean_object* v_x_2163_, lean_object* v_x_2164_, lean_object* v_x_2165_, lean_object* v_x_2166_){
_start:
{
size_t v_x_1965__boxed_2167_; size_t v_x_1966__boxed_2168_; lean_object* v_res_2169_; 
v_x_1965__boxed_2167_ = lean_unbox_usize(v_x_2163_);
lean_dec(v_x_2163_);
v_x_1966__boxed_2168_ = lean_unbox_usize(v_x_2164_);
lean_dec(v_x_2164_);
v_res_2169_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(v_00_u03b2_2161_, v_x_2162_, v_x_1965__boxed_2167_, v_x_1966__boxed_2168_, v_x_2165_, v_x_2166_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_2170_, lean_object* v_n_2171_, lean_object* v_k_2172_, lean_object* v_v_2173_){
_start:
{
lean_object* v___x_2174_; 
v___x_2174_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v_n_2171_, v_k_2172_, v_v_2173_);
return v___x_2174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2175_, size_t v_depth_2176_, lean_object* v_keys_2177_, lean_object* v_vals_2178_, lean_object* v_heq_2179_, lean_object* v_i_2180_, lean_object* v_entries_2181_){
_start:
{
lean_object* v___x_2182_; 
v___x_2182_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_2176_, v_keys_2177_, v_vals_2178_, v_i_2180_, v_entries_2181_);
return v___x_2182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2183_, lean_object* v_depth_2184_, lean_object* v_keys_2185_, lean_object* v_vals_2186_, lean_object* v_heq_2187_, lean_object* v_i_2188_, lean_object* v_entries_2189_){
_start:
{
size_t v_depth_boxed_2190_; lean_object* v_res_2191_; 
v_depth_boxed_2190_ = lean_unbox_usize(v_depth_2184_);
lean_dec(v_depth_2184_);
v_res_2191_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_2183_, v_depth_boxed_2190_, v_keys_2185_, v_vals_2186_, v_heq_2187_, v_i_2188_, v_entries_2189_);
lean_dec_ref(v_vals_2186_);
lean_dec_ref(v_keys_2185_);
return v_res_2191_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2192_, lean_object* v_x_2193_, lean_object* v_x_2194_, lean_object* v_x_2195_, lean_object* v_x_2196_){
_start:
{
lean_object* v___x_2197_; 
v___x_2197_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2193_, v_x_2194_, v_x_2195_, v_x_2196_);
return v___x_2197_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_2198_, lean_object* v___y_2199_){
_start:
{
uint8_t v___x_2201_; 
v___x_2201_ = l_Lean_Expr_hasMVar(v_e_2198_);
if (v___x_2201_ == 0)
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2202_, 0, v_e_2198_);
return v___x_2202_;
}
else
{
lean_object* v___x_2203_; lean_object* v_mctx_2204_; lean_object* v___x_2205_; lean_object* v_fst_2206_; lean_object* v_snd_2207_; lean_object* v___x_2208_; lean_object* v_cache_2209_; lean_object* v_zetaDeltaFVarIds_2210_; lean_object* v_postponed_2211_; lean_object* v_diag_2212_; lean_object* v___x_2214_; uint8_t v_isShared_2215_; uint8_t v_isSharedCheck_2221_; 
v___x_2203_ = lean_st_ref_get(v___y_2199_);
v_mctx_2204_ = lean_ctor_get(v___x_2203_, 0);
lean_inc_ref(v_mctx_2204_);
lean_dec(v___x_2203_);
v___x_2205_ = l_Lean_instantiateMVarsCore(v_mctx_2204_, v_e_2198_);
v_fst_2206_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_fst_2206_);
v_snd_2207_ = lean_ctor_get(v___x_2205_, 1);
lean_inc(v_snd_2207_);
lean_dec_ref(v___x_2205_);
v___x_2208_ = lean_st_ref_take(v___y_2199_);
v_cache_2209_ = lean_ctor_get(v___x_2208_, 1);
v_zetaDeltaFVarIds_2210_ = lean_ctor_get(v___x_2208_, 2);
v_postponed_2211_ = lean_ctor_get(v___x_2208_, 3);
v_diag_2212_ = lean_ctor_get(v___x_2208_, 4);
v_isSharedCheck_2221_ = !lean_is_exclusive(v___x_2208_);
if (v_isSharedCheck_2221_ == 0)
{
lean_object* v_unused_2222_; 
v_unused_2222_ = lean_ctor_get(v___x_2208_, 0);
lean_dec(v_unused_2222_);
v___x_2214_ = v___x_2208_;
v_isShared_2215_ = v_isSharedCheck_2221_;
goto v_resetjp_2213_;
}
else
{
lean_inc(v_diag_2212_);
lean_inc(v_postponed_2211_);
lean_inc(v_zetaDeltaFVarIds_2210_);
lean_inc(v_cache_2209_);
lean_dec(v___x_2208_);
v___x_2214_ = lean_box(0);
v_isShared_2215_ = v_isSharedCheck_2221_;
goto v_resetjp_2213_;
}
v_resetjp_2213_:
{
lean_object* v___x_2217_; 
if (v_isShared_2215_ == 0)
{
lean_ctor_set(v___x_2214_, 0, v_snd_2207_);
v___x_2217_ = v___x_2214_;
goto v_reusejp_2216_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_snd_2207_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v_cache_2209_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_zetaDeltaFVarIds_2210_);
lean_ctor_set(v_reuseFailAlloc_2220_, 3, v_postponed_2211_);
lean_ctor_set(v_reuseFailAlloc_2220_, 4, v_diag_2212_);
v___x_2217_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2216_;
}
v_reusejp_2216_:
{
lean_object* v___x_2218_; lean_object* v___x_2219_; 
v___x_2218_ = lean_st_ref_put(v___y_2199_, v___x_2217_);
v___x_2219_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2219_, 0, v_fst_2206_);
return v___x_2219_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_2223_, lean_object* v___y_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_2223_, v___y_2224_);
lean_dec(v___y_2224_);
return v_res_2226_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v___x_2233_; 
v___x_2233_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_2227_, v___y_2229_);
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_, lean_object* v___y_2238_, lean_object* v___y_2239_){
_start:
{
lean_object* v_res_2240_; 
v_res_2240_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_2234_, v___y_2235_, v___y_2236_, v___y_2237_, v___y_2238_);
lean_dec(v___y_2238_);
lean_dec_ref(v___y_2237_);
lean_dec(v___y_2236_);
lean_dec_ref(v___y_2235_);
return v_res_2240_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_2241_, lean_object* v_opt_2242_){
_start:
{
lean_object* v_name_2243_; lean_object* v_defValue_2244_; lean_object* v_map_2245_; lean_object* v___x_2246_; 
v_name_2243_ = lean_ctor_get(v_opt_2242_, 0);
v_defValue_2244_ = lean_ctor_get(v_opt_2242_, 1);
v_map_2245_ = lean_ctor_get(v_opts_2241_, 0);
v___x_2246_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2245_, v_name_2243_);
if (lean_obj_tag(v___x_2246_) == 0)
{
uint8_t v___x_2247_; 
v___x_2247_ = lean_unbox(v_defValue_2244_);
return v___x_2247_;
}
else
{
lean_object* v_val_2248_; 
v_val_2248_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_val_2248_);
lean_dec_ref_known(v___x_2246_, 1);
if (lean_obj_tag(v_val_2248_) == 1)
{
uint8_t v_v_2249_; 
v_v_2249_ = lean_ctor_get_uint8(v_val_2248_, 0);
lean_dec_ref_known(v_val_2248_, 0);
return v_v_2249_;
}
else
{
uint8_t v___x_2250_; 
lean_dec(v_val_2248_);
v___x_2250_ = lean_unbox(v_defValue_2244_);
return v___x_2250_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_2251_, lean_object* v_opt_2252_){
_start:
{
uint8_t v_res_2253_; lean_object* v_r_2254_; 
v_res_2253_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_2251_, v_opt_2252_);
lean_dec_ref(v_opt_2252_);
lean_dec_ref(v_opts_2251_);
v_r_2254_ = lean_box(v_res_2253_);
return v_r_2254_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_2255_, lean_object* v_as_2256_, size_t v_i_2257_, size_t v_stop_2258_){
_start:
{
uint8_t v___x_2259_; 
v___x_2259_ = lean_usize_dec_eq(v_i_2257_, v_stop_2258_);
if (v___x_2259_ == 0)
{
lean_object* v___x_2260_; uint8_t v___x_2261_; 
v___x_2260_ = lean_array_uget_borrowed(v_as_2256_, v_i_2257_);
v___x_2261_ = lean_nat_dec_eq(v_a_2255_, v___x_2260_);
if (v___x_2261_ == 0)
{
size_t v___x_2262_; size_t v___x_2263_; 
v___x_2262_ = ((size_t)1ULL);
v___x_2263_ = lean_usize_add(v_i_2257_, v___x_2262_);
v_i_2257_ = v___x_2263_;
goto _start;
}
else
{
return v___x_2261_;
}
}
else
{
uint8_t v___x_2265_; 
v___x_2265_ = 0;
return v___x_2265_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_2266_, lean_object* v_as_2267_, lean_object* v_i_2268_, lean_object* v_stop_2269_){
_start:
{
size_t v_i_boxed_2270_; size_t v_stop_boxed_2271_; uint8_t v_res_2272_; lean_object* v_r_2273_; 
v_i_boxed_2270_ = lean_unbox_usize(v_i_2268_);
lean_dec(v_i_2268_);
v_stop_boxed_2271_ = lean_unbox_usize(v_stop_2269_);
lean_dec(v_stop_2269_);
v_res_2272_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_2266_, v_as_2267_, v_i_boxed_2270_, v_stop_boxed_2271_);
lean_dec_ref(v_as_2267_);
lean_dec(v_a_2266_);
v_r_2273_ = lean_box(v_res_2272_);
return v_r_2273_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_2274_, lean_object* v_a_2275_){
_start:
{
lean_object* v___x_2276_; lean_object* v___x_2277_; uint8_t v___x_2278_; 
v___x_2276_ = lean_unsigned_to_nat(0u);
v___x_2277_ = lean_array_get_size(v_as_2274_);
v___x_2278_ = lean_nat_dec_lt(v___x_2276_, v___x_2277_);
if (v___x_2278_ == 0)
{
return v___x_2278_;
}
else
{
size_t v___x_2279_; size_t v___x_2280_; uint8_t v___x_2281_; 
v___x_2279_ = ((size_t)0ULL);
v___x_2280_ = lean_usize_of_nat(v___x_2277_);
v___x_2281_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_2275_, v_as_2274_, v___x_2279_, v___x_2280_);
return v___x_2281_;
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_2282_, lean_object* v_a_2283_){
_start:
{
uint8_t v_res_2284_; lean_object* v_r_2285_; 
v_res_2284_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_2282_, v_a_2283_);
lean_dec(v_a_2283_);
lean_dec_ref(v_as_2282_);
v_r_2285_ = lean_box(v_res_2284_);
return v_r_2285_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_2286_, lean_object* v_fst_2287_, lean_object* v_argVars_2288_, lean_object* v_as_2289_, size_t v_sz_2290_, size_t v_i_2291_, lean_object* v_b_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_){
_start:
{
lean_object* v_a_2299_; uint8_t v___x_2303_; 
v___x_2303_ = lean_usize_dec_lt(v_i_2291_, v_sz_2290_);
if (v___x_2303_ == 0)
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2304_, 0, v_b_2292_);
return v___x_2304_;
}
else
{
lean_object* v_next_2305_; 
v_next_2305_ = lean_ctor_get(v_b_2292_, 0);
lean_inc(v_next_2305_);
if (lean_obj_tag(v_next_2305_) == 0)
{
lean_object* v___x_2306_; 
v___x_2306_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2306_, 0, v_b_2292_);
return v___x_2306_;
}
else
{
lean_object* v_upperBound_2307_; lean_object* v_val_2308_; lean_object* v___x_2310_; uint8_t v_isShared_2311_; uint8_t v_isSharedCheck_2339_; 
v_upperBound_2307_ = lean_ctor_get(v_b_2292_, 1);
v_val_2308_ = lean_ctor_get(v_next_2305_, 0);
v_isSharedCheck_2339_ = !lean_is_exclusive(v_next_2305_);
if (v_isSharedCheck_2339_ == 0)
{
v___x_2310_ = v_next_2305_;
v_isShared_2311_ = v_isSharedCheck_2339_;
goto v_resetjp_2309_;
}
else
{
lean_inc(v_val_2308_);
lean_dec(v_next_2305_);
v___x_2310_ = lean_box(0);
v_isShared_2311_ = v_isSharedCheck_2339_;
goto v_resetjp_2309_;
}
v_resetjp_2309_:
{
uint8_t v___x_2312_; 
v___x_2312_ = lean_nat_dec_lt(v_val_2308_, v_upperBound_2307_);
if (v___x_2312_ == 0)
{
lean_object* v___x_2313_; 
lean_del_object(v___x_2310_);
lean_dec(v_val_2308_);
v___x_2313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2313_, 0, v_b_2292_);
return v___x_2313_;
}
else
{
lean_object* v___x_2315_; uint8_t v_isShared_2316_; uint8_t v_isSharedCheck_2336_; 
lean_inc(v_upperBound_2307_);
v_isSharedCheck_2336_ = !lean_is_exclusive(v_b_2292_);
if (v_isSharedCheck_2336_ == 0)
{
lean_object* v_unused_2337_; lean_object* v_unused_2338_; 
v_unused_2337_ = lean_ctor_get(v_b_2292_, 1);
lean_dec(v_unused_2337_);
v_unused_2338_ = lean_ctor_get(v_b_2292_, 0);
lean_dec(v_unused_2338_);
v___x_2315_ = v_b_2292_;
v_isShared_2316_ = v_isSharedCheck_2336_;
goto v_resetjp_2314_;
}
else
{
lean_dec(v_b_2292_);
v___x_2315_ = lean_box(0);
v_isShared_2316_ = v_isSharedCheck_2336_;
goto v_resetjp_2314_;
}
v_resetjp_2314_:
{
lean_object* v___x_2317_; lean_object* v___x_2318_; lean_object* v___x_2320_; 
v___x_2317_ = lean_unsigned_to_nat(1u);
v___x_2318_ = lean_nat_add(v_val_2308_, v___x_2317_);
if (v_isShared_2311_ == 0)
{
lean_ctor_set(v___x_2310_, 0, v___x_2318_);
v___x_2320_ = v___x_2310_;
goto v_reusejp_2319_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v___x_2318_);
v___x_2320_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2319_;
}
v_reusejp_2319_:
{
lean_object* v___x_2322_; 
if (v_isShared_2316_ == 0)
{
lean_ctor_set(v___x_2315_, 0, v___x_2320_);
v___x_2322_ = v___x_2315_;
goto v_reusejp_2321_;
}
else
{
lean_object* v_reuseFailAlloc_2334_; 
v_reuseFailAlloc_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2334_, 0, v___x_2320_);
lean_ctor_set(v_reuseFailAlloc_2334_, 1, v_upperBound_2307_);
v___x_2322_ = v_reuseFailAlloc_2334_;
goto v_reusejp_2321_;
}
v_reusejp_2321_:
{
uint8_t v___x_2323_; 
v___x_2323_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2286_, v_val_2308_);
lean_dec(v_val_2308_);
if (v___x_2323_ == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; 
v_a_2324_ = lean_array_uget_borrowed(v_as_2289_, v_i_2291_);
lean_inc(v_a_2324_);
v___x_2325_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2287_, v_argVars_2288_, v_a_2324_, v___y_2293_, v___y_2294_, v___y_2295_, v___y_2296_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_dec_ref_known(v___x_2325_, 1);
v_a_2299_ = v___x_2322_;
goto v___jp_2298_;
}
else
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2333_; 
lean_dec_ref(v___x_2322_);
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2333_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2333_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2333_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2331_; 
if (v_isShared_2329_ == 0)
{
v___x_2331_ = v___x_2328_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v_a_2326_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
}
}
else
{
v_a_2299_ = v___x_2322_;
goto v___jp_2298_;
}
}
}
}
}
}
}
}
v___jp_2298_:
{
size_t v___x_2300_; size_t v___x_2301_; 
v___x_2300_ = ((size_t)1ULL);
v___x_2301_ = lean_usize_add(v_i_2291_, v___x_2300_);
v_i_2291_ = v___x_2301_;
v_b_2292_ = v_a_2299_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2340_, lean_object* v_fst_2341_, lean_object* v_argVars_2342_, lean_object* v_as_2343_, lean_object* v_sz_2344_, lean_object* v_i_2345_, lean_object* v_b_2346_, lean_object* v___y_2347_, lean_object* v___y_2348_, lean_object* v___y_2349_, lean_object* v___y_2350_, lean_object* v___y_2351_){
_start:
{
size_t v_sz_boxed_2352_; size_t v_i_boxed_2353_; lean_object* v_res_2354_; 
v_sz_boxed_2352_ = lean_unbox_usize(v_sz_2344_);
lean_dec(v_sz_2344_);
v_i_boxed_2353_ = lean_unbox_usize(v_i_2345_);
lean_dec(v_i_2345_);
v_res_2354_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2340_, v_fst_2341_, v_argVars_2342_, v_as_2343_, v_sz_boxed_2352_, v_i_boxed_2353_, v_b_2346_, v___y_2347_, v___y_2348_, v___y_2349_, v___y_2350_);
lean_dec(v___y_2350_);
lean_dec_ref(v___y_2349_);
lean_dec(v___y_2348_);
lean_dec_ref(v___y_2347_);
lean_dec_ref(v_as_2343_);
lean_dec_ref(v_argVars_2342_);
lean_dec_ref(v_fst_2341_);
lean_dec_ref(v_a_2340_);
return v_res_2354_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2355_, lean_object* v_a_2356_, lean_object* v___x_2357_, lean_object* v_a_2358_, lean_object* v_b_2359_){
_start:
{
uint8_t v___x_2361_; 
v___x_2361_ = lean_nat_dec_lt(v_a_2358_, v_upperBound_2355_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; 
lean_dec(v_a_2358_);
v___x_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2362_, 0, v_b_2359_);
return v___x_2362_;
}
else
{
lean_object* v_snd_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2403_; 
v_snd_2363_ = lean_ctor_get(v_b_2359_, 1);
v_isSharedCheck_2403_ = !lean_is_exclusive(v_b_2359_);
if (v_isSharedCheck_2403_ == 0)
{
lean_object* v_unused_2404_; 
v_unused_2404_ = lean_ctor_get(v_b_2359_, 0);
lean_dec(v_unused_2404_);
v___x_2365_ = v_b_2359_;
v_isShared_2366_ = v_isSharedCheck_2403_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_snd_2363_);
lean_dec(v_b_2359_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2403_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v_array_2367_; lean_object* v_start_2368_; lean_object* v_stop_2369_; lean_object* v___x_2370_; uint8_t v___x_2371_; 
v_array_2367_ = lean_ctor_get(v_snd_2363_, 0);
v_start_2368_ = lean_ctor_get(v_snd_2363_, 1);
v_stop_2369_ = lean_ctor_get(v_snd_2363_, 2);
v___x_2370_ = lean_box(0);
v___x_2371_ = lean_nat_dec_lt(v_start_2368_, v_stop_2369_);
if (v___x_2371_ == 0)
{
lean_object* v___x_2373_; 
lean_dec(v_a_2358_);
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 0, v___x_2370_);
v___x_2373_ = v___x_2365_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2375_; 
v_reuseFailAlloc_2375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2375_, 0, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2375_, 1, v_snd_2363_);
v___x_2373_ = v_reuseFailAlloc_2375_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2374_; 
v___x_2374_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2374_, 0, v___x_2373_);
return v___x_2374_;
}
}
else
{
lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2399_; 
lean_inc(v_stop_2369_);
lean_inc(v_start_2368_);
lean_inc_ref(v_array_2367_);
v_isSharedCheck_2399_ = !lean_is_exclusive(v_snd_2363_);
if (v_isSharedCheck_2399_ == 0)
{
lean_object* v_unused_2400_; lean_object* v_unused_2401_; lean_object* v_unused_2402_; 
v_unused_2400_ = lean_ctor_get(v_snd_2363_, 2);
lean_dec(v_unused_2400_);
v_unused_2401_ = lean_ctor_get(v_snd_2363_, 1);
lean_dec(v_unused_2401_);
v_unused_2402_ = lean_ctor_get(v_snd_2363_, 0);
lean_dec(v_unused_2402_);
v___x_2377_ = v_snd_2363_;
v_isShared_2378_ = v_isSharedCheck_2399_;
goto v_resetjp_2376_;
}
else
{
lean_dec(v_snd_2363_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2399_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2379_; lean_object* v___x_2380_; lean_object* v___x_2381_; lean_object* v___x_2383_; 
v___x_2379_ = lean_array_fget(v_array_2367_, v_start_2368_);
v___x_2380_ = lean_unsigned_to_nat(1u);
v___x_2381_ = lean_nat_add(v_start_2368_, v___x_2380_);
lean_dec(v_start_2368_);
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 1, v___x_2381_);
v___x_2383_ = v___x_2377_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v_array_2367_);
lean_ctor_set(v_reuseFailAlloc_2398_, 1, v___x_2381_);
lean_ctor_set(v_reuseFailAlloc_2398_, 2, v_stop_2369_);
v___x_2383_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
uint8_t v___x_2390_; 
v___x_2390_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2356_, v_a_2358_);
if (v___x_2390_ == 0)
{
uint8_t v___x_2391_; 
v___x_2391_ = l_Lean_Expr_hasExprMVar(v___x_2379_);
lean_dec(v___x_2379_);
if (v___x_2391_ == 0)
{
goto v___jp_2384_;
}
else
{
lean_object* v___x_2392_; uint8_t v___x_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; lean_object* v___x_2396_; lean_object* v___x_2397_; 
lean_del_object(v___x_2365_);
lean_dec(v_a_2358_);
v___x_2392_ = lean_unsigned_to_nat(0u);
v___x_2393_ = lean_nat_dec_eq(v___x_2357_, v___x_2392_);
v___x_2394_ = lean_box(v___x_2393_);
v___x_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2395_, 0, v___x_2394_);
v___x_2396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2396_, 0, v___x_2395_);
lean_ctor_set(v___x_2396_, 1, v___x_2383_);
v___x_2397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2397_, 0, v___x_2396_);
return v___x_2397_;
}
}
else
{
lean_dec(v___x_2379_);
goto v___jp_2384_;
}
v___jp_2384_:
{
lean_object* v___x_2386_; 
if (v_isShared_2366_ == 0)
{
lean_ctor_set(v___x_2365_, 1, v___x_2383_);
lean_ctor_set(v___x_2365_, 0, v___x_2370_);
v___x_2386_ = v___x_2365_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v___x_2370_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v___x_2383_);
v___x_2386_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
lean_object* v___x_2387_; 
v___x_2387_ = lean_nat_add(v_a_2358_, v___x_2380_);
lean_dec(v_a_2358_);
v_a_2358_ = v___x_2387_;
v_b_2359_ = v___x_2386_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2405_, lean_object* v_a_2406_, lean_object* v___x_2407_, lean_object* v_a_2408_, lean_object* v_b_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2405_, v_a_2406_, v___x_2407_, v_a_2408_, v_b_2409_);
lean_dec(v___x_2407_);
lean_dec_ref(v_a_2406_);
lean_dec(v_upperBound_2405_);
return v_res_2411_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2412_; lean_object* v_dummy_2413_; 
v___x_2412_ = lean_box(0);
v_dummy_2413_ = l_Lean_Expr_sort___override(v___x_2412_);
return v_dummy_2413_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2414_, lean_object* v___x_2415_, uint8_t v___x_2416_, lean_object* v_x_2417_, lean_object* v_argTy_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_){
_start:
{
lean_object* v___x_2424_; 
lean_inc(v___y_2422_);
lean_inc_ref(v___y_2421_);
lean_inc(v___y_2420_);
lean_inc_ref(v___y_2419_);
v___x_2424_ = lean_whnf(v_argTy_2418_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2424_) == 0)
{
lean_object* v_a_2425_; lean_object* v___x_2426_; 
v_a_2425_ = lean_ctor_get(v___x_2424_, 0);
lean_inc(v_a_2425_);
lean_dec_ref_known(v___x_2424_, 1);
v___x_2426_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2425_, v___y_2419_, v___y_2420_, v___y_2421_, v___y_2422_);
if (lean_obj_tag(v___x_2426_) == 0)
{
lean_object* v_a_2427_; lean_object* v_dummy_2428_; lean_object* v_nargs_2429_; lean_object* v___x_2430_; lean_object* v___x_2431_; lean_object* v___x_2432_; lean_object* v___x_2433_; lean_object* v___x_2434_; lean_object* v___x_2435_; lean_object* v___x_2436_; lean_object* v___x_2437_; lean_object* v___x_2438_; 
v_a_2427_ = lean_ctor_get(v___x_2426_, 0);
lean_inc(v_a_2427_);
lean_dec_ref_known(v___x_2426_, 1);
v_dummy_2428_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2429_ = l_Lean_Expr_getAppNumArgs(v_a_2425_);
lean_inc(v_nargs_2429_);
v___x_2430_ = lean_mk_array(v_nargs_2429_, v_dummy_2428_);
v___x_2431_ = lean_unsigned_to_nat(1u);
v___x_2432_ = lean_nat_sub(v_nargs_2429_, v___x_2431_);
lean_dec(v_nargs_2429_);
v___x_2433_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2425_, v___x_2430_, v___x_2432_);
v___x_2434_ = lean_array_get_size(v___x_2433_);
lean_inc(v___x_2414_);
v___x_2435_ = l_Array_toSubarray___redArg(v___x_2433_, v___x_2414_, v___x_2434_);
v___x_2436_ = lean_box(0);
v___x_2437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2437_, 0, v___x_2436_);
lean_ctor_set(v___x_2437_, 1, v___x_2435_);
v___x_2438_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2434_, v_a_2427_, v___x_2415_, v___x_2414_, v___x_2437_);
lean_dec(v_a_2427_);
if (lean_obj_tag(v___x_2438_) == 0)
{
lean_object* v_a_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2452_; 
v_a_2439_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2452_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2452_ == 0)
{
v___x_2441_ = v___x_2438_;
v_isShared_2442_ = v_isSharedCheck_2452_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_a_2439_);
lean_dec(v___x_2438_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2452_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v_fst_2443_; 
v_fst_2443_ = lean_ctor_get(v_a_2439_, 0);
lean_inc(v_fst_2443_);
lean_dec(v_a_2439_);
if (lean_obj_tag(v_fst_2443_) == 0)
{
lean_object* v___x_2444_; lean_object* v___x_2446_; 
v___x_2444_ = lean_box(v___x_2416_);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v___x_2444_);
v___x_2446_ = v___x_2441_;
goto v_reusejp_2445_;
}
else
{
lean_object* v_reuseFailAlloc_2447_; 
v_reuseFailAlloc_2447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2447_, 0, v___x_2444_);
v___x_2446_ = v_reuseFailAlloc_2447_;
goto v_reusejp_2445_;
}
v_reusejp_2445_:
{
return v___x_2446_;
}
}
else
{
lean_object* v_val_2448_; lean_object* v___x_2450_; 
v_val_2448_ = lean_ctor_get(v_fst_2443_, 0);
lean_inc(v_val_2448_);
lean_dec_ref_known(v_fst_2443_, 1);
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v_val_2448_);
v___x_2450_ = v___x_2441_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2451_; 
v_reuseFailAlloc_2451_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2451_, 0, v_val_2448_);
v___x_2450_ = v_reuseFailAlloc_2451_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
return v___x_2450_;
}
}
}
}
else
{
lean_object* v_a_2453_; lean_object* v___x_2455_; uint8_t v_isShared_2456_; uint8_t v_isSharedCheck_2460_; 
v_a_2453_ = lean_ctor_get(v___x_2438_, 0);
v_isSharedCheck_2460_ = !lean_is_exclusive(v___x_2438_);
if (v_isSharedCheck_2460_ == 0)
{
v___x_2455_ = v___x_2438_;
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
else
{
lean_inc(v_a_2453_);
lean_dec(v___x_2438_);
v___x_2455_ = lean_box(0);
v_isShared_2456_ = v_isSharedCheck_2460_;
goto v_resetjp_2454_;
}
v_resetjp_2454_:
{
lean_object* v___x_2458_; 
if (v_isShared_2456_ == 0)
{
v___x_2458_ = v___x_2455_;
goto v_reusejp_2457_;
}
else
{
lean_object* v_reuseFailAlloc_2459_; 
v_reuseFailAlloc_2459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2459_, 0, v_a_2453_);
v___x_2458_ = v_reuseFailAlloc_2459_;
goto v_reusejp_2457_;
}
v_reusejp_2457_:
{
return v___x_2458_;
}
}
}
}
else
{
lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2468_; 
lean_dec(v_a_2425_);
lean_dec(v___x_2414_);
v_a_2461_ = lean_ctor_get(v___x_2426_, 0);
v_isSharedCheck_2468_ = !lean_is_exclusive(v___x_2426_);
if (v_isSharedCheck_2468_ == 0)
{
v___x_2463_ = v___x_2426_;
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2426_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2468_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2466_; 
if (v_isShared_2464_ == 0)
{
v___x_2466_ = v___x_2463_;
goto v_reusejp_2465_;
}
else
{
lean_object* v_reuseFailAlloc_2467_; 
v_reuseFailAlloc_2467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2467_, 0, v_a_2461_);
v___x_2466_ = v_reuseFailAlloc_2467_;
goto v_reusejp_2465_;
}
v_reusejp_2465_:
{
return v___x_2466_;
}
}
}
}
else
{
lean_object* v_a_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2476_; 
lean_dec(v___x_2414_);
v_a_2469_ = lean_ctor_get(v___x_2424_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2424_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2471_ = v___x_2424_;
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_a_2469_);
lean_dec(v___x_2424_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2476_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2474_; 
if (v_isShared_2472_ == 0)
{
v___x_2474_ = v___x_2471_;
goto v_reusejp_2473_;
}
else
{
lean_object* v_reuseFailAlloc_2475_; 
v_reuseFailAlloc_2475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2475_, 0, v_a_2469_);
v___x_2474_ = v_reuseFailAlloc_2475_;
goto v_reusejp_2473_;
}
v_reusejp_2473_:
{
return v___x_2474_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2477_, lean_object* v___x_2478_, lean_object* v___x_2479_, lean_object* v_x_2480_, lean_object* v_argTy_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_, lean_object* v___y_2486_){
_start:
{
uint8_t v___x_22665__boxed_2487_; lean_object* v_res_2488_; 
v___x_22665__boxed_2487_ = lean_unbox(v___x_2479_);
v_res_2488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2477_, v___x_2478_, v___x_22665__boxed_2487_, v_x_2480_, v_argTy_2481_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
lean_dec(v___y_2485_);
lean_dec_ref(v___y_2484_);
lean_dec(v___y_2483_);
lean_dec_ref(v___y_2482_);
lean_dec_ref(v_x_2480_);
lean_dec(v___x_2478_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2492_, lean_object* v_projInfo_x3f_2493_, lean_object* v___x_2494_, lean_object* v_argVars_2495_, lean_object* v_as_2496_, size_t v_sz_2497_, size_t v_i_2498_, lean_object* v_b_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
uint8_t v___x_2505_; 
v___x_2505_ = lean_usize_dec_lt(v_i_2498_, v_sz_2497_);
if (v___x_2505_ == 0)
{
lean_object* v___x_2506_; 
lean_dec(v___x_2494_);
v___x_2506_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2506_, 0, v_b_2499_);
return v___x_2506_;
}
else
{
lean_object* v___x_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; lean_object* v___f_2512_; uint8_t v___x_2513_; lean_object* v_a_2514_; lean_object* v___y_2521_; lean_object* v___x_2535_; lean_object* v___x_2536_; 
lean_dec_ref(v_b_2499_);
v___x_2507_ = lean_box(0);
v___x_2508_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2509_ = l_Lean_instInhabitedExpr;
v___x_2510_ = lean_unsigned_to_nat(0u);
v___x_2511_ = lean_box(v___x_2505_);
lean_inc(v___x_2494_);
v___f_2512_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2512_, 0, v___x_2510_);
lean_closure_set(v___f_2512_, 1, v___x_2494_);
lean_closure_set(v___f_2512_, 2, v___x_2511_);
v___x_2513_ = lean_nat_dec_eq(v___x_2494_, v___x_2510_);
v_a_2514_ = lean_array_uget_borrowed(v_as_2496_, v_i_2498_);
v___x_2535_ = lean_array_get_borrowed(v___x_2509_, v_fst_2492_, v_a_2514_);
lean_inc(v___y_2503_);
lean_inc_ref(v___y_2502_);
lean_inc(v___y_2501_);
lean_inc_ref(v___y_2500_);
lean_inc(v___x_2535_);
v___x_2536_ = lean_infer_type(v___x_2535_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2536_) == 0)
{
lean_object* v_a_2537_; lean_object* v___x_2538_; 
v_a_2537_ = lean_ctor_get(v___x_2536_, 0);
lean_inc(v_a_2537_);
lean_dec_ref_known(v___x_2536_, 1);
v___x_2538_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2537_, v___y_2501_);
if (lean_obj_tag(v___x_2538_) == 0)
{
if (lean_obj_tag(v_projInfo_x3f_2493_) == 1)
{
lean_object* v_val_2539_; lean_object* v_a_2540_; lean_object* v_numParams_2541_; uint8_t v___x_2542_; 
v_val_2539_ = lean_ctor_get(v_projInfo_x3f_2493_, 0);
v_a_2540_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2540_);
lean_dec_ref_known(v___x_2538_, 1);
v_numParams_2541_ = lean_ctor_get(v_val_2539_, 1);
v___x_2542_ = lean_nat_dec_eq(v_numParams_2541_, v_a_2514_);
if (v___x_2542_ == 0)
{
lean_object* v___x_2543_; 
v___x_2543_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2540_, v___f_2512_, v___x_2513_, v___x_2513_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
v___y_2521_ = v___x_2543_;
goto v___jp_2520_;
}
else
{
lean_object* v___x_2544_; 
lean_dec_ref(v___f_2512_);
lean_dec(v___x_2494_);
v___x_2544_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2492_, v_argVars_2495_, v_a_2540_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
if (lean_obj_tag(v___x_2544_) == 0)
{
lean_dec_ref_known(v___x_2544_, 1);
goto v___jp_2515_;
}
else
{
lean_object* v_a_2545_; lean_object* v___x_2547_; uint8_t v_isShared_2548_; uint8_t v_isSharedCheck_2552_; 
v_a_2545_ = lean_ctor_get(v___x_2544_, 0);
v_isSharedCheck_2552_ = !lean_is_exclusive(v___x_2544_);
if (v_isSharedCheck_2552_ == 0)
{
v___x_2547_ = v___x_2544_;
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
else
{
lean_inc(v_a_2545_);
lean_dec(v___x_2544_);
v___x_2547_ = lean_box(0);
v_isShared_2548_ = v_isSharedCheck_2552_;
goto v_resetjp_2546_;
}
v_resetjp_2546_:
{
lean_object* v___x_2550_; 
if (v_isShared_2548_ == 0)
{
v___x_2550_ = v___x_2547_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_a_2545_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
}
else
{
lean_object* v_a_2553_; lean_object* v___x_2554_; 
v_a_2553_ = lean_ctor_get(v___x_2538_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v___x_2538_, 1);
v___x_2554_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2553_, v___f_2512_, v___x_2513_, v___x_2513_, v___y_2500_, v___y_2501_, v___y_2502_, v___y_2503_);
v___y_2521_ = v___x_2554_;
goto v___jp_2520_;
}
}
else
{
lean_object* v_a_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2562_; 
lean_dec_ref(v___f_2512_);
lean_dec(v___x_2494_);
v_a_2555_ = lean_ctor_get(v___x_2538_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___x_2538_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2557_ = v___x_2538_;
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_a_2555_);
lean_dec(v___x_2538_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2562_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2560_; 
if (v_isShared_2558_ == 0)
{
v___x_2560_ = v___x_2557_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2555_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v___f_2512_);
lean_dec(v___x_2494_);
v_a_2563_ = lean_ctor_get(v___x_2536_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___x_2536_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___x_2536_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___x_2536_);
v___x_2565_ = lean_box(0);
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
v_resetjp_2564_:
{
lean_object* v___x_2568_; 
if (v_isShared_2566_ == 0)
{
v___x_2568_ = v___x_2565_;
goto v_reusejp_2567_;
}
else
{
lean_object* v_reuseFailAlloc_2569_; 
v_reuseFailAlloc_2569_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2569_, 0, v_a_2563_);
v___x_2568_ = v_reuseFailAlloc_2569_;
goto v_reusejp_2567_;
}
v_reusejp_2567_:
{
return v___x_2568_;
}
}
}
v___jp_2515_:
{
lean_object* v___x_2516_; lean_object* v___x_2517_; lean_object* v___x_2518_; lean_object* v___x_2519_; 
lean_inc(v_a_2514_);
v___x_2516_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2516_, 0, v_a_2514_);
v___x_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2517_, 0, v___x_2516_);
v___x_2518_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2518_, 0, v___x_2517_);
lean_ctor_set(v___x_2518_, 1, v___x_2507_);
v___x_2519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2519_, 0, v___x_2518_);
return v___x_2519_;
}
v___jp_2520_:
{
if (lean_obj_tag(v___y_2521_) == 0)
{
lean_object* v_a_2522_; uint8_t v___x_2523_; 
v_a_2522_ = lean_ctor_get(v___y_2521_, 0);
lean_inc(v_a_2522_);
lean_dec_ref_known(v___y_2521_, 1);
v___x_2523_ = lean_unbox(v_a_2522_);
lean_dec(v_a_2522_);
if (v___x_2523_ == 0)
{
size_t v___x_2524_; size_t v___x_2525_; 
v___x_2524_ = ((size_t)1ULL);
v___x_2525_ = lean_usize_add(v_i_2498_, v___x_2524_);
v_i_2498_ = v___x_2525_;
v_b_2499_ = v___x_2508_;
goto _start;
}
else
{
lean_dec(v___x_2494_);
goto v___jp_2515_;
}
}
else
{
lean_object* v_a_2527_; lean_object* v___x_2529_; uint8_t v_isShared_2530_; uint8_t v_isSharedCheck_2534_; 
lean_dec(v___x_2494_);
v_a_2527_ = lean_ctor_get(v___y_2521_, 0);
v_isSharedCheck_2534_ = !lean_is_exclusive(v___y_2521_);
if (v_isSharedCheck_2534_ == 0)
{
v___x_2529_ = v___y_2521_;
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
else
{
lean_inc(v_a_2527_);
lean_dec(v___y_2521_);
v___x_2529_ = lean_box(0);
v_isShared_2530_ = v_isSharedCheck_2534_;
goto v_resetjp_2528_;
}
v_resetjp_2528_:
{
lean_object* v___x_2532_; 
if (v_isShared_2530_ == 0)
{
v___x_2532_ = v___x_2529_;
goto v_reusejp_2531_;
}
else
{
lean_object* v_reuseFailAlloc_2533_; 
v_reuseFailAlloc_2533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2533_, 0, v_a_2527_);
v___x_2532_ = v_reuseFailAlloc_2533_;
goto v_reusejp_2531_;
}
v_reusejp_2531_:
{
return v___x_2532_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2571_, lean_object* v_projInfo_x3f_2572_, lean_object* v___x_2573_, lean_object* v_argVars_2574_, lean_object* v_as_2575_, lean_object* v_sz_2576_, lean_object* v_i_2577_, lean_object* v_b_2578_, lean_object* v___y_2579_, lean_object* v___y_2580_, lean_object* v___y_2581_, lean_object* v___y_2582_, lean_object* v___y_2583_){
_start:
{
size_t v_sz_boxed_2584_; size_t v_i_boxed_2585_; lean_object* v_res_2586_; 
v_sz_boxed_2584_ = lean_unbox_usize(v_sz_2576_);
lean_dec(v_sz_2576_);
v_i_boxed_2585_ = lean_unbox_usize(v_i_2577_);
lean_dec(v_i_2577_);
v_res_2586_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2571_, v_projInfo_x3f_2572_, v___x_2573_, v_argVars_2574_, v_as_2575_, v_sz_boxed_2584_, v_i_boxed_2585_, v_b_2578_, v___y_2579_, v___y_2580_, v___y_2581_, v___y_2582_);
lean_dec(v___y_2582_);
lean_dec_ref(v___y_2581_);
lean_dec(v___y_2580_);
lean_dec_ref(v___y_2579_);
lean_dec_ref(v_as_2575_);
lean_dec_ref(v_argVars_2574_);
lean_dec(v_projInfo_x3f_2572_);
lean_dec_ref(v_fst_2571_);
return v_res_2586_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2587_, lean_object* v_as_2588_, size_t v_i_2589_, size_t v_stop_2590_, lean_object* v_b_2591_){
_start:
{
lean_object* v___y_2593_; uint8_t v___x_2597_; 
v___x_2597_ = lean_usize_dec_eq(v_i_2589_, v_stop_2590_);
if (v___x_2597_ == 0)
{
lean_object* v___x_2598_; uint8_t v___x_2599_; 
v___x_2598_ = lean_array_uget_borrowed(v_as_2588_, v_i_2589_);
v___x_2599_ = lean_nat_dec_eq(v___x_2598_, v_next_2587_);
if (v___x_2599_ == 0)
{
lean_object* v___x_2600_; 
lean_inc(v___x_2598_);
v___x_2600_ = lean_array_push(v_b_2591_, v___x_2598_);
v___y_2593_ = v___x_2600_;
goto v___jp_2592_;
}
else
{
v___y_2593_ = v_b_2591_;
goto v___jp_2592_;
}
}
else
{
return v_b_2591_;
}
v___jp_2592_:
{
size_t v___x_2594_; size_t v___x_2595_; 
v___x_2594_ = ((size_t)1ULL);
v___x_2595_ = lean_usize_add(v_i_2589_, v___x_2594_);
v_i_2589_ = v___x_2595_;
v_b_2591_ = v___y_2593_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2601_, lean_object* v_as_2602_, lean_object* v_i_2603_, lean_object* v_stop_2604_, lean_object* v_b_2605_){
_start:
{
size_t v_i_boxed_2606_; size_t v_stop_boxed_2607_; lean_object* v_res_2608_; 
v_i_boxed_2606_ = lean_unbox_usize(v_i_2603_);
lean_dec(v_i_2603_);
v_stop_boxed_2607_ = lean_unbox_usize(v_stop_2604_);
lean_dec(v_stop_2604_);
v_res_2608_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2601_, v_as_2602_, v_i_boxed_2606_, v_stop_boxed_2607_, v_b_2605_);
lean_dec_ref(v_as_2602_);
lean_dec(v_next_2601_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object* v_fst_2609_, lean_object* v___x_2610_, lean_object* v_fst_2611_, lean_object* v_argVars_2612_, lean_object* v_snd_2613_, lean_object* v_next_2614_, lean_object* v___y_2615_, lean_object* v___y_2616_, lean_object* v___y_2617_, lean_object* v___y_2618_){
_start:
{
lean_object* v___x_2620_; lean_object* v___y_2622_; lean_object* v___x_2662_; lean_object* v___x_2663_; lean_object* v___x_2664_; uint8_t v___x_2665_; 
lean_inc(v_next_2614_);
v___x_2620_ = lean_array_push(v_fst_2609_, v_next_2614_);
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = lean_array_get_size(v_snd_2613_);
v___x_2664_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2665_ = lean_nat_dec_lt(v___x_2662_, v___x_2663_);
if (v___x_2665_ == 0)
{
v___y_2622_ = v___x_2664_;
goto v___jp_2621_;
}
else
{
size_t v___x_2666_; size_t v___x_2667_; lean_object* v___x_2668_; 
v___x_2666_ = ((size_t)0ULL);
v___x_2667_ = lean_usize_of_nat(v___x_2663_);
v___x_2668_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2614_, v_snd_2613_, v___x_2666_, v___x_2667_, v___x_2664_);
v___y_2622_ = v___x_2668_;
goto v___jp_2621_;
}
v___jp_2621_:
{
lean_object* v___x_2623_; lean_object* v___x_2624_; 
v___x_2623_ = lean_array_get_borrowed(v___x_2610_, v_fst_2611_, v_next_2614_);
lean_dec(v_next_2614_);
lean_inc(v___y_2618_);
lean_inc_ref(v___y_2617_);
lean_inc(v___y_2616_);
lean_inc_ref(v___y_2615_);
lean_inc(v___x_2623_);
v___x_2624_ = lean_infer_type(v___x_2623_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2624_) == 0)
{
lean_object* v_a_2625_; lean_object* v___x_2626_; 
v_a_2625_ = lean_ctor_get(v___x_2624_, 0);
lean_inc(v_a_2625_);
lean_dec_ref_known(v___x_2624_, 1);
v___x_2626_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2611_, v_argVars_2612_, v_a_2625_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2626_) == 0)
{
lean_object* v___x_2627_; 
lean_dec_ref_known(v___x_2626_, 1);
lean_inc(v___x_2623_);
v___x_2627_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2611_, v_argVars_2612_, v___x_2623_, v___y_2615_, v___y_2616_, v___y_2617_, v___y_2618_);
if (lean_obj_tag(v___x_2627_) == 0)
{
lean_object* v___x_2629_; uint8_t v_isShared_2630_; uint8_t v_isSharedCheck_2636_; 
v_isSharedCheck_2636_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; 
v_unused_2637_ = lean_ctor_get(v___x_2627_, 0);
lean_dec(v_unused_2637_);
v___x_2629_ = v___x_2627_;
v_isShared_2630_ = v_isSharedCheck_2636_;
goto v_resetjp_2628_;
}
else
{
lean_dec(v___x_2627_);
v___x_2629_ = lean_box(0);
v_isShared_2630_ = v_isSharedCheck_2636_;
goto v_resetjp_2628_;
}
v_resetjp_2628_:
{
lean_object* v___x_2631_; lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2631_, 0, v___x_2620_);
lean_ctor_set(v___x_2631_, 1, v___y_2622_);
v___x_2632_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2632_, 0, v___x_2631_);
if (v_isShared_2630_ == 0)
{
lean_ctor_set(v___x_2629_, 0, v___x_2632_);
v___x_2634_ = v___x_2629_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___x_2620_);
v_a_2638_ = lean_ctor_get(v___x_2627_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2627_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2627_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2627_);
v___x_2640_ = lean_box(0);
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
v_resetjp_2639_:
{
lean_object* v___x_2643_; 
if (v_isShared_2641_ == 0)
{
v___x_2643_ = v___x_2640_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2644_; 
v_reuseFailAlloc_2644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2644_, 0, v_a_2638_);
v___x_2643_ = v_reuseFailAlloc_2644_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
return v___x_2643_;
}
}
}
}
else
{
lean_object* v_a_2646_; lean_object* v___x_2648_; uint8_t v_isShared_2649_; uint8_t v_isSharedCheck_2653_; 
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___x_2620_);
v_a_2646_ = lean_ctor_get(v___x_2626_, 0);
v_isSharedCheck_2653_ = !lean_is_exclusive(v___x_2626_);
if (v_isSharedCheck_2653_ == 0)
{
v___x_2648_ = v___x_2626_;
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
else
{
lean_inc(v_a_2646_);
lean_dec(v___x_2626_);
v___x_2648_ = lean_box(0);
v_isShared_2649_ = v_isSharedCheck_2653_;
goto v_resetjp_2647_;
}
v_resetjp_2647_:
{
lean_object* v___x_2651_; 
if (v_isShared_2649_ == 0)
{
v___x_2651_ = v___x_2648_;
goto v_reusejp_2650_;
}
else
{
lean_object* v_reuseFailAlloc_2652_; 
v_reuseFailAlloc_2652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2652_, 0, v_a_2646_);
v___x_2651_ = v_reuseFailAlloc_2652_;
goto v_reusejp_2650_;
}
v_reusejp_2650_:
{
return v___x_2651_;
}
}
}
}
else
{
lean_object* v_a_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2661_; 
lean_dec_ref(v___y_2622_);
lean_dec_ref(v___x_2620_);
v_a_2654_ = lean_ctor_get(v___x_2624_, 0);
v_isSharedCheck_2661_ = !lean_is_exclusive(v___x_2624_);
if (v_isSharedCheck_2661_ == 0)
{
v___x_2656_ = v___x_2624_;
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
else
{
lean_inc(v_a_2654_);
lean_dec(v___x_2624_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2661_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2659_; 
if (v_isShared_2657_ == 0)
{
v___x_2659_ = v___x_2656_;
goto v_reusejp_2658_;
}
else
{
lean_object* v_reuseFailAlloc_2660_; 
v_reuseFailAlloc_2660_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2660_, 0, v_a_2654_);
v___x_2659_ = v_reuseFailAlloc_2660_;
goto v_reusejp_2658_;
}
v_reusejp_2658_:
{
return v___x_2659_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object* v_fst_2669_, lean_object* v___x_2670_, lean_object* v_fst_2671_, lean_object* v_argVars_2672_, lean_object* v_snd_2673_, lean_object* v_next_2674_, lean_object* v___y_2675_, lean_object* v___y_2676_, lean_object* v___y_2677_, lean_object* v___y_2678_, lean_object* v___y_2679_){
_start:
{
lean_object* v_res_2680_; 
v_res_2680_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2669_, v___x_2670_, v_fst_2671_, v_argVars_2672_, v_snd_2673_, v_next_2674_, v___y_2675_, v___y_2676_, v___y_2677_, v___y_2678_);
lean_dec(v___y_2678_);
lean_dec_ref(v___y_2677_);
lean_dec(v___y_2676_);
lean_dec_ref(v___y_2675_);
lean_dec(v_snd_2673_);
lean_dec_ref(v_argVars_2672_);
lean_dec_ref(v_fst_2671_);
lean_dec_ref(v___x_2670_);
return v_res_2680_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2681_, lean_object* v___y_2682_, lean_object* v___y_2683_, lean_object* v___y_2684_, lean_object* v___y_2685_){
_start:
{
lean_object* v___x_2687_; lean_object* v_env_2688_; uint8_t v___x_2689_; lean_object* v_env_2690_; lean_object* v___x_2691_; lean_object* v_toCold_2692_; lean_object* v_mctx_2693_; lean_object* v_lctx_2694_; lean_object* v_options_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2687_ = lean_st_ref_get(v___y_2685_);
v_env_2688_ = lean_ctor_get(v___x_2687_, 0);
lean_inc_ref(v_env_2688_);
lean_dec(v___x_2687_);
v___x_2689_ = 0;
v_env_2690_ = l_Lean_Environment_setRecordingDeps(v_env_2688_, v___x_2689_);
v___x_2691_ = lean_st_ref_get(v___y_2683_);
v_toCold_2692_ = lean_ctor_get(v___y_2684_, 0);
v_mctx_2693_ = lean_ctor_get(v___x_2691_, 0);
lean_inc_ref(v_mctx_2693_);
lean_dec(v___x_2691_);
v_lctx_2694_ = lean_ctor_get(v___y_2682_, 2);
v_options_2695_ = lean_ctor_get(v_toCold_2692_, 2);
lean_inc_ref(v_options_2695_);
lean_inc_ref(v_lctx_2694_);
v___x_2696_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2696_, 0, v_env_2690_);
lean_ctor_set(v___x_2696_, 1, v_mctx_2693_);
lean_ctor_set(v___x_2696_, 2, v_lctx_2694_);
lean_ctor_set(v___x_2696_, 3, v_options_2695_);
v___x_2697_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2697_, 0, v___x_2696_);
lean_ctor_set(v___x_2697_, 1, v_msgData_2681_);
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v___x_2697_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2699_, lean_object* v___y_2700_, lean_object* v___y_2701_, lean_object* v___y_2702_, lean_object* v___y_2703_, lean_object* v___y_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2699_, v___y_2700_, v___y_2701_, v___y_2702_, v___y_2703_);
lean_dec(v___y_2703_);
lean_dec_ref(v___y_2702_);
lean_dec(v___y_2701_);
lean_dec_ref(v___y_2700_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2706_, lean_object* v___y_2707_, lean_object* v___y_2708_, lean_object* v___y_2709_, lean_object* v___y_2710_){
_start:
{
lean_object* v_ref_2712_; lean_object* v___x_2713_; lean_object* v_a_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2722_; 
v_ref_2712_ = lean_ctor_get(v___y_2709_, 2);
v___x_2713_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2706_, v___y_2707_, v___y_2708_, v___y_2709_, v___y_2710_);
v_a_2714_ = lean_ctor_get(v___x_2713_, 0);
v_isSharedCheck_2722_ = !lean_is_exclusive(v___x_2713_);
if (v_isSharedCheck_2722_ == 0)
{
v___x_2716_ = v___x_2713_;
v_isShared_2717_ = v_isSharedCheck_2722_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_a_2714_);
lean_dec(v___x_2713_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2722_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; lean_object* v___x_2720_; 
lean_inc(v_ref_2712_);
v___x_2718_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2718_, 0, v_ref_2712_);
lean_ctor_set(v___x_2718_, 1, v_a_2714_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set_tag(v___x_2716_, 1);
lean_ctor_set(v___x_2716_, 0, v___x_2718_);
v___x_2720_ = v___x_2716_;
goto v_reusejp_2719_;
}
else
{
lean_object* v_reuseFailAlloc_2721_; 
v_reuseFailAlloc_2721_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2721_, 0, v___x_2718_);
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
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_, lean_object* v___y_2728_){
_start:
{
lean_object* v_res_2729_; 
v_res_2729_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2723_, v___y_2724_, v___y_2725_, v___y_2726_, v___y_2727_);
lean_dec(v___y_2727_);
lean_dec_ref(v___y_2726_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2730_, size_t v_sz_2731_, size_t v_i_2732_, lean_object* v_bs_2733_, lean_object* v___y_2734_, lean_object* v___y_2735_, lean_object* v___y_2736_, lean_object* v___y_2737_){
_start:
{
uint8_t v___x_2739_; 
v___x_2739_ = lean_usize_dec_lt(v_i_2732_, v_sz_2731_);
if (v___x_2739_ == 0)
{
lean_object* v___x_2740_; 
v___x_2740_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2740_, 0, v_bs_2733_);
return v___x_2740_;
}
else
{
lean_object* v___x_2741_; lean_object* v_v_2742_; lean_object* v___x_2743_; lean_object* v_bs_x27_2744_; lean_object* v___x_2745_; lean_object* v___x_2746_; 
v___x_2741_ = l_Lean_instInhabitedExpr;
v_v_2742_ = lean_array_uget(v_bs_2733_, v_i_2732_);
v___x_2743_ = lean_unsigned_to_nat(0u);
v_bs_x27_2744_ = lean_array_uset(v_bs_2733_, v_i_2732_, v___x_2743_);
v___x_2745_ = lean_array_get_borrowed(v___x_2741_, v_fst_2730_, v_v_2742_);
lean_dec(v_v_2742_);
lean_inc(v___y_2737_);
lean_inc_ref(v___y_2736_);
lean_inc(v___y_2735_);
lean_inc_ref(v___y_2734_);
lean_inc(v___x_2745_);
v___x_2746_ = lean_infer_type(v___x_2745_, v___y_2734_, v___y_2735_, v___y_2736_, v___y_2737_);
if (lean_obj_tag(v___x_2746_) == 0)
{
lean_object* v_a_2747_; lean_object* v___x_2748_; 
v_a_2747_ = lean_ctor_get(v___x_2746_, 0);
lean_inc(v_a_2747_);
lean_dec_ref_known(v___x_2746_, 1);
v___x_2748_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2747_, v___y_2735_);
if (lean_obj_tag(v___x_2748_) == 0)
{
lean_object* v_a_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; size_t v___x_2752_; size_t v___x_2753_; lean_object* v___x_2754_; 
v_a_2749_ = lean_ctor_get(v___x_2748_, 0);
lean_inc(v_a_2749_);
lean_dec_ref_known(v___x_2748_, 1);
v___x_2750_ = l_Lean_Expr_setPPExplicit(v_a_2749_, v___x_2739_);
v___x_2751_ = l_Lean_indentExpr(v___x_2750_);
v___x_2752_ = ((size_t)1ULL);
v___x_2753_ = lean_usize_add(v_i_2732_, v___x_2752_);
v___x_2754_ = lean_array_uset(v_bs_x27_2744_, v_i_2732_, v___x_2751_);
v_i_2732_ = v___x_2753_;
v_bs_2733_ = v___x_2754_;
goto _start;
}
else
{
lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2763_; 
lean_dec_ref(v_bs_x27_2744_);
v_a_2756_ = lean_ctor_get(v___x_2748_, 0);
v_isSharedCheck_2763_ = !lean_is_exclusive(v___x_2748_);
if (v_isSharedCheck_2763_ == 0)
{
v___x_2758_ = v___x_2748_;
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2748_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2763_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2761_; 
if (v_isShared_2759_ == 0)
{
v___x_2761_ = v___x_2758_;
goto v_reusejp_2760_;
}
else
{
lean_object* v_reuseFailAlloc_2762_; 
v_reuseFailAlloc_2762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2762_, 0, v_a_2756_);
v___x_2761_ = v_reuseFailAlloc_2762_;
goto v_reusejp_2760_;
}
v_reusejp_2760_:
{
return v___x_2761_;
}
}
}
}
else
{
lean_object* v_a_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2771_; 
lean_dec_ref(v_bs_x27_2744_);
v_a_2764_ = lean_ctor_get(v___x_2746_, 0);
v_isSharedCheck_2771_ = !lean_is_exclusive(v___x_2746_);
if (v_isSharedCheck_2771_ == 0)
{
v___x_2766_ = v___x_2746_;
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_a_2764_);
lean_dec(v___x_2746_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2771_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2769_; 
if (v_isShared_2767_ == 0)
{
v___x_2769_ = v___x_2766_;
goto v_reusejp_2768_;
}
else
{
lean_object* v_reuseFailAlloc_2770_; 
v_reuseFailAlloc_2770_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2770_, 0, v_a_2764_);
v___x_2769_ = v_reuseFailAlloc_2770_;
goto v_reusejp_2768_;
}
v_reusejp_2768_:
{
return v___x_2769_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2772_, lean_object* v_sz_2773_, lean_object* v_i_2774_, lean_object* v_bs_2775_, lean_object* v___y_2776_, lean_object* v___y_2777_, lean_object* v___y_2778_, lean_object* v___y_2779_, lean_object* v___y_2780_){
_start:
{
size_t v_sz_boxed_2781_; size_t v_i_boxed_2782_; lean_object* v_res_2783_; 
v_sz_boxed_2781_ = lean_unbox_usize(v_sz_2773_);
lean_dec(v_sz_2773_);
v_i_boxed_2782_ = lean_unbox_usize(v_i_2774_);
lean_dec(v_i_2774_);
v_res_2783_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2772_, v_sz_boxed_2781_, v_i_boxed_2782_, v_bs_2775_, v___y_2776_, v___y_2777_, v___y_2778_, v___y_2779_);
lean_dec(v___y_2779_);
lean_dec_ref(v___y_2778_);
lean_dec(v___y_2777_);
lean_dec_ref(v___y_2776_);
lean_dec_ref(v_fst_2772_);
return v_res_2783_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object* v___x_2784_, lean_object* v_snd_2785_, lean_object* v___f_2786_, lean_object* v_____r_2787_, lean_object* v___y_2788_, lean_object* v___y_2789_, lean_object* v___y_2790_, lean_object* v___y_2791_){
_start:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; 
v___x_2793_ = lean_unsigned_to_nat(0u);
v___x_2794_ = lean_array_get_borrowed(v___x_2784_, v_snd_2785_, v___x_2793_);
lean_inc(v___y_2791_);
lean_inc_ref(v___y_2790_);
lean_inc(v___y_2789_);
lean_inc_ref(v___y_2788_);
lean_inc(v___x_2794_);
v___x_2795_ = lean_apply_6(v___f_2786_, v___x_2794_, v___y_2788_, v___y_2789_, v___y_2790_, v___y_2791_, lean_box(0));
return v___x_2795_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object* v___x_2796_, lean_object* v_snd_2797_, lean_object* v___f_2798_, lean_object* v_____r_2799_, lean_object* v___y_2800_, lean_object* v___y_2801_, lean_object* v___y_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_){
_start:
{
lean_object* v_res_2805_; 
v_res_2805_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2796_, v_snd_2797_, v___f_2798_, v_____r_2799_, v___y_2800_, v___y_2801_, v___y_2802_, v___y_2803_);
lean_dec(v___y_2803_);
lean_dec_ref(v___y_2802_);
lean_dec(v___y_2801_);
lean_dec_ref(v___y_2800_);
lean_dec(v_snd_2797_);
lean_dec(v___x_2796_);
return v_res_2805_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2809_; lean_object* v___x_2810_; 
v___x_2809_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1));
v___x_2810_ = l_Lean_MessageData_ofFormat(v___x_2809_);
return v___x_2810_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2812_; lean_object* v___x_2813_; 
v___x_2812_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3));
v___x_2813_ = l_Lean_stringToMessageData(v___x_2812_);
return v___x_2813_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2815_; lean_object* v___x_2816_; 
v___x_2815_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5));
v___x_2816_ = l_Lean_stringToMessageData(v___x_2815_);
return v___x_2816_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; 
v___x_2818_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7));
v___x_2819_ = l_Lean_stringToMessageData(v___x_2818_);
return v___x_2819_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(lean_object* v_fst_2820_, lean_object* v_argVars_2821_, lean_object* v_inst_2822_, lean_object* v_a_2823_, lean_object* v_projInfo_x3f_2824_, lean_object* v_a_2825_, lean_object* v___y_2826_, lean_object* v___y_2827_, lean_object* v___y_2828_, lean_object* v___y_2829_){
_start:
{
lean_object* v___y_2832_; lean_object* v_fst_2852_; lean_object* v_snd_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2925_; 
v_fst_2852_ = lean_ctor_get(v_a_2825_, 0);
v_snd_2853_ = lean_ctor_get(v_a_2825_, 1);
v_isSharedCheck_2925_ = !lean_is_exclusive(v_a_2825_);
if (v_isSharedCheck_2925_ == 0)
{
v___x_2855_ = v_a_2825_;
v_isShared_2856_ = v_isSharedCheck_2925_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_snd_2853_);
lean_inc(v_fst_2852_);
lean_dec(v_a_2825_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2925_;
goto v_resetjp_2854_;
}
v___jp_2831_:
{
if (lean_obj_tag(v___y_2832_) == 0)
{
lean_object* v_a_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2843_; 
v_a_2833_ = lean_ctor_get(v___y_2832_, 0);
v_isSharedCheck_2843_ = !lean_is_exclusive(v___y_2832_);
if (v_isSharedCheck_2843_ == 0)
{
v___x_2835_ = v___y_2832_;
v_isShared_2836_ = v_isSharedCheck_2843_;
goto v_resetjp_2834_;
}
else
{
lean_inc(v_a_2833_);
lean_dec(v___y_2832_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2843_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
if (lean_obj_tag(v_a_2833_) == 0)
{
lean_object* v_a_2837_; lean_object* v___x_2839_; 
lean_dec_ref(v_a_2823_);
lean_dec_ref(v_inst_2822_);
lean_dec_ref(v_argVars_2821_);
lean_dec_ref(v_fst_2820_);
v_a_2837_ = lean_ctor_get(v_a_2833_, 0);
lean_inc(v_a_2837_);
lean_dec_ref_known(v_a_2833_, 1);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 0, v_a_2837_);
v___x_2839_ = v___x_2835_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_a_2837_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
else
{
lean_object* v_a_2841_; 
lean_del_object(v___x_2835_);
v_a_2841_ = lean_ctor_get(v_a_2833_, 0);
lean_inc(v_a_2841_);
lean_dec_ref_known(v_a_2833_, 1);
v_a_2825_ = v_a_2841_;
goto _start;
}
}
}
else
{
lean_object* v_a_2844_; lean_object* v___x_2846_; uint8_t v_isShared_2847_; uint8_t v_isSharedCheck_2851_; 
lean_dec_ref(v_a_2823_);
lean_dec_ref(v_inst_2822_);
lean_dec_ref(v_argVars_2821_);
lean_dec_ref(v_fst_2820_);
v_a_2844_ = lean_ctor_get(v___y_2832_, 0);
v_isSharedCheck_2851_ = !lean_is_exclusive(v___y_2832_);
if (v_isSharedCheck_2851_ == 0)
{
v___x_2846_ = v___y_2832_;
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
else
{
lean_inc(v_a_2844_);
lean_dec(v___y_2832_);
v___x_2846_ = lean_box(0);
v_isShared_2847_ = v_isSharedCheck_2851_;
goto v_resetjp_2845_;
}
v_resetjp_2845_:
{
lean_object* v___x_2849_; 
if (v_isShared_2847_ == 0)
{
v___x_2849_ = v___x_2846_;
goto v_reusejp_2848_;
}
else
{
lean_object* v_reuseFailAlloc_2850_; 
v_reuseFailAlloc_2850_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2850_, 0, v_a_2844_);
v___x_2849_ = v_reuseFailAlloc_2850_;
goto v_reusejp_2848_;
}
v_reusejp_2848_:
{
return v___x_2849_;
}
}
}
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2857_ = lean_array_get_size(v_snd_2853_);
v___x_2858_ = lean_unsigned_to_nat(0u);
v___x_2859_ = lean_nat_dec_eq(v___x_2857_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___f_2861_; lean_object* v___x_2904_; size_t v_sz_2905_; size_t v___x_2906_; lean_object* v___x_2907_; 
lean_del_object(v___x_2855_);
v___x_2860_ = l_Lean_instInhabitedExpr;
lean_inc(v_snd_2853_);
lean_inc_ref(v_argVars_2821_);
lean_inc_ref(v_fst_2820_);
lean_inc(v_fst_2852_);
v___f_2861_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2861_, 0, v_fst_2852_);
lean_closure_set(v___f_2861_, 1, v___x_2860_);
lean_closure_set(v___f_2861_, 2, v_fst_2820_);
lean_closure_set(v___f_2861_, 3, v_argVars_2821_);
lean_closure_set(v___f_2861_, 4, v_snd_2853_);
v___x_2904_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2905_ = lean_array_size(v_snd_2853_);
v___x_2906_ = ((size_t)0ULL);
v___x_2907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2820_, v_projInfo_x3f_2824_, v___x_2857_, v_argVars_2821_, v_snd_2853_, v_sz_2905_, v___x_2906_, v___x_2904_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2907_) == 0)
{
lean_object* v_a_2908_; lean_object* v_fst_2909_; 
v_a_2908_ = lean_ctor_get(v___x_2907_, 0);
lean_inc(v_a_2908_);
lean_dec_ref_known(v___x_2907_, 1);
v_fst_2909_ = lean_ctor_get(v_a_2908_, 0);
lean_inc(v_fst_2909_);
lean_dec(v_a_2908_);
if (lean_obj_tag(v_fst_2909_) == 0)
{
lean_dec(v_fst_2852_);
goto v___jp_2862_;
}
else
{
lean_object* v_val_2910_; 
v_val_2910_ = lean_ctor_get(v_fst_2909_, 0);
lean_inc(v_val_2910_);
lean_dec_ref_known(v_fst_2909_, 1);
if (lean_obj_tag(v_val_2910_) == 0)
{
lean_dec(v_fst_2852_);
goto v___jp_2862_;
}
else
{
lean_object* v_val_2911_; lean_object* v___x_2912_; 
lean_dec_ref(v___f_2861_);
v_val_2911_ = lean_ctor_get(v_val_2910_, 0);
lean_inc(v_val_2911_);
lean_dec_ref_known(v_val_2910_, 1);
v___x_2912_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2852_, v___x_2860_, v_fst_2820_, v_argVars_2821_, v_snd_2853_, v_val_2911_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v_snd_2853_);
v___y_2832_ = v___x_2912_;
goto v___jp_2831_;
}
}
}
else
{
lean_object* v_a_2913_; lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
lean_dec_ref(v___f_2861_);
lean_dec(v_snd_2853_);
lean_dec(v_fst_2852_);
lean_dec_ref(v_a_2823_);
lean_dec_ref(v_inst_2822_);
lean_dec_ref(v_argVars_2821_);
lean_dec_ref(v_fst_2820_);
v_a_2913_ = lean_ctor_get(v___x_2907_, 0);
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2907_);
if (v_isSharedCheck_2920_ == 0)
{
v___x_2915_ = v___x_2907_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_inc(v_a_2913_);
lean_dec(v___x_2907_);
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
v___jp_2862_:
{
lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v___x_2863_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_2828_);
v___x_2864_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2865_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_2863_, v___x_2864_);
lean_dec_ref(v___x_2863_);
if (v___x_2865_ == 0)
{
lean_object* v___x_2866_; lean_object* v___x_2867_; 
v___x_2866_ = lean_box(0);
v___x_2867_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2858_, v_snd_2853_, v___f_2861_, v___x_2866_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v_snd_2853_);
v___y_2832_ = v___x_2867_;
goto v___jp_2831_;
}
else
{
size_t v_sz_2868_; size_t v___x_2869_; lean_object* v___x_2870_; 
v_sz_2868_ = lean_array_size(v_snd_2853_);
v___x_2869_ = ((size_t)0ULL);
lean_inc(v_snd_2853_);
v___x_2870_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2820_, v_sz_2868_, v___x_2869_, v_snd_2853_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2870_) == 0)
{
lean_object* v_a_2871_; lean_object* v___x_2872_; lean_object* v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; lean_object* v___x_2877_; lean_object* v___x_2878_; lean_object* v___x_2879_; lean_object* v___x_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; 
v_a_2871_ = lean_ctor_get(v___x_2870_, 0);
lean_inc(v_a_2871_);
lean_dec_ref_known(v___x_2870_, 1);
v___x_2872_ = lean_array_to_list(v_a_2871_);
v___x_2873_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2874_ = l_Lean_MessageData_joinSep(v___x_2872_, v___x_2873_);
v___x_2875_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4);
lean_inc_ref(v_inst_2822_);
v___x_2876_ = l_Lean_MessageData_ofExpr(v_inst_2822_);
v___x_2877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2877_, 0, v___x_2875_);
lean_ctor_set(v___x_2877_, 1, v___x_2876_);
v___x_2878_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6);
v___x_2879_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2879_, 0, v___x_2877_);
lean_ctor_set(v___x_2879_, 1, v___x_2878_);
lean_inc_ref(v_a_2823_);
v___x_2880_ = l_Lean_indentExpr(v_a_2823_);
v___x_2881_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2881_, 0, v___x_2879_);
lean_ctor_set(v___x_2881_, 1, v___x_2880_);
v___x_2882_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8);
v___x_2883_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2883_, 0, v___x_2881_);
lean_ctor_set(v___x_2883_, 1, v___x_2882_);
v___x_2884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2884_, 0, v___x_2883_);
lean_ctor_set(v___x_2884_, 1, v___x_2874_);
v___x_2885_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2884_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
if (lean_obj_tag(v___x_2885_) == 0)
{
lean_object* v_a_2886_; lean_object* v___x_2887_; 
v_a_2886_ = lean_ctor_get(v___x_2885_, 0);
lean_inc(v_a_2886_);
lean_dec_ref_known(v___x_2885_, 1);
v___x_2887_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2858_, v_snd_2853_, v___f_2861_, v_a_2886_, v___y_2826_, v___y_2827_, v___y_2828_, v___y_2829_);
lean_dec(v_snd_2853_);
v___y_2832_ = v___x_2887_;
goto v___jp_2831_;
}
else
{
lean_object* v_a_2888_; lean_object* v___x_2890_; uint8_t v_isShared_2891_; uint8_t v_isSharedCheck_2895_; 
lean_dec_ref(v___f_2861_);
lean_dec(v_snd_2853_);
lean_dec_ref(v_a_2823_);
lean_dec_ref(v_inst_2822_);
lean_dec_ref(v_argVars_2821_);
lean_dec_ref(v_fst_2820_);
v_a_2888_ = lean_ctor_get(v___x_2885_, 0);
v_isSharedCheck_2895_ = !lean_is_exclusive(v___x_2885_);
if (v_isSharedCheck_2895_ == 0)
{
v___x_2890_ = v___x_2885_;
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
else
{
lean_inc(v_a_2888_);
lean_dec(v___x_2885_);
v___x_2890_ = lean_box(0);
v_isShared_2891_ = v_isSharedCheck_2895_;
goto v_resetjp_2889_;
}
v_resetjp_2889_:
{
lean_object* v___x_2893_; 
if (v_isShared_2891_ == 0)
{
v___x_2893_ = v___x_2890_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_a_2888_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
}
}
else
{
lean_object* v_a_2896_; lean_object* v___x_2898_; uint8_t v_isShared_2899_; uint8_t v_isSharedCheck_2903_; 
lean_dec_ref(v___f_2861_);
lean_dec(v_snd_2853_);
lean_dec_ref(v_a_2823_);
lean_dec_ref(v_inst_2822_);
lean_dec_ref(v_argVars_2821_);
lean_dec_ref(v_fst_2820_);
v_a_2896_ = lean_ctor_get(v___x_2870_, 0);
v_isSharedCheck_2903_ = !lean_is_exclusive(v___x_2870_);
if (v_isSharedCheck_2903_ == 0)
{
v___x_2898_ = v___x_2870_;
v_isShared_2899_ = v_isSharedCheck_2903_;
goto v_resetjp_2897_;
}
else
{
lean_inc(v_a_2896_);
lean_dec(v___x_2870_);
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
}
else
{
lean_object* v___x_2922_; 
lean_dec_ref(v_a_2823_);
lean_dec_ref(v_inst_2822_);
lean_dec_ref(v_argVars_2821_);
lean_dec_ref(v_fst_2820_);
if (v_isShared_2856_ == 0)
{
v___x_2922_ = v___x_2855_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2924_; 
v_reuseFailAlloc_2924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2924_, 0, v_fst_2852_);
lean_ctor_set(v_reuseFailAlloc_2924_, 1, v_snd_2853_);
v___x_2922_ = v_reuseFailAlloc_2924_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
lean_object* v___x_2923_; 
v___x_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2923_, 0, v___x_2922_);
return v___x_2923_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___boxed(lean_object* v_fst_2926_, lean_object* v_argVars_2927_, lean_object* v_inst_2928_, lean_object* v_a_2929_, lean_object* v_projInfo_x3f_2930_, lean_object* v_a_2931_, lean_object* v___y_2932_, lean_object* v___y_2933_, lean_object* v___y_2934_, lean_object* v___y_2935_, lean_object* v___y_2936_){
_start:
{
lean_object* v_res_2937_; 
v_res_2937_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2926_, v_argVars_2927_, v_inst_2928_, v_a_2929_, v_projInfo_x3f_2930_, v_a_2931_, v___y_2932_, v___y_2933_, v___y_2934_, v___y_2935_);
lean_dec(v___y_2935_);
lean_dec_ref(v___y_2934_);
lean_dec(v___y_2933_);
lean_dec_ref(v___y_2932_);
lean_dec(v_projInfo_x3f_2930_);
return v_res_2937_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2938_, lean_object* v_a_2939_, lean_object* v_a_2940_){
_start:
{
if (lean_obj_tag(v_a_2939_) == 0)
{
lean_object* v___x_2941_; 
v___x_2941_ = l_List_reverse___redArg(v_a_2940_);
return v___x_2941_;
}
else
{
lean_object* v_head_2942_; lean_object* v_tail_2943_; lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2958_; 
v_head_2942_ = lean_ctor_get(v_a_2939_, 0);
v_tail_2943_ = lean_ctor_get(v_a_2939_, 1);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_a_2939_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2945_ = v_a_2939_;
v_isShared_2946_ = v_isSharedCheck_2958_;
goto v_resetjp_2944_;
}
else
{
lean_inc(v_tail_2943_);
lean_inc(v_head_2942_);
lean_dec(v_a_2939_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2958_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
uint8_t v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; uint8_t v___x_2950_; uint8_t v___x_2951_; uint8_t v___x_2952_; 
v___x_2947_ = 0;
v___x_2948_ = lean_box(v___x_2947_);
v___x_2949_ = lean_array_get(v___x_2948_, v_fst_2938_, v_head_2942_);
lean_dec(v___x_2948_);
v___x_2950_ = 3;
v___x_2951_ = lean_unbox(v___x_2949_);
lean_dec(v___x_2949_);
v___x_2952_ = l_Lean_instBEqBinderInfo_beq(v___x_2951_, v___x_2950_);
if (v___x_2952_ == 0)
{
lean_del_object(v___x_2945_);
lean_dec(v_head_2942_);
v_a_2939_ = v_tail_2943_;
goto _start;
}
else
{
lean_object* v___x_2955_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 1, v_a_2940_);
v___x_2955_ = v___x_2945_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_head_2942_);
lean_ctor_set(v_reuseFailAlloc_2957_, 1, v_a_2940_);
v___x_2955_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
v_a_2939_ = v_tail_2943_;
v_a_2940_ = v___x_2955_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2959_, lean_object* v_a_2960_, lean_object* v_a_2961_){
_start:
{
lean_object* v_res_2962_; 
v_res_2962_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2959_, v_a_2960_, v_a_2961_);
lean_dec_ref(v_fst_2959_);
return v_res_2962_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2963_, size_t v_sz_2964_, size_t v_i_2965_, lean_object* v_bs_2966_, lean_object* v___y_2967_, lean_object* v___y_2968_, lean_object* v___y_2969_, lean_object* v___y_2970_){
_start:
{
uint8_t v___x_2972_; 
v___x_2972_ = lean_usize_dec_lt(v_i_2965_, v_sz_2964_);
if (v___x_2972_ == 0)
{
lean_object* v___x_2973_; 
v___x_2973_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2973_, 0, v_bs_2966_);
return v___x_2973_;
}
else
{
lean_object* v___x_2974_; lean_object* v_v_2975_; lean_object* v___x_2976_; lean_object* v_bs_x27_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; 
v___x_2974_ = l_Lean_instInhabitedExpr;
v_v_2975_ = lean_array_uget(v_bs_2966_, v_i_2965_);
v___x_2976_ = lean_unsigned_to_nat(0u);
v_bs_x27_2977_ = lean_array_uset(v_bs_2966_, v_i_2965_, v___x_2976_);
v___x_2978_ = lean_array_get_borrowed(v___x_2974_, v_argVars_2963_, v_v_2975_);
lean_dec(v_v_2975_);
lean_inc(v___y_2970_);
lean_inc_ref(v___y_2969_);
lean_inc(v___y_2968_);
lean_inc_ref(v___y_2967_);
lean_inc(v___x_2978_);
v___x_2979_ = lean_infer_type(v___x_2978_, v___y_2967_, v___y_2968_, v___y_2969_, v___y_2970_);
if (lean_obj_tag(v___x_2979_) == 0)
{
lean_object* v_a_2980_; lean_object* v___x_2981_; size_t v___x_2982_; size_t v___x_2983_; lean_object* v___x_2984_; 
v_a_2980_ = lean_ctor_get(v___x_2979_, 0);
lean_inc(v_a_2980_);
lean_dec_ref_known(v___x_2979_, 1);
v___x_2981_ = l_Lean_indentExpr(v_a_2980_);
v___x_2982_ = ((size_t)1ULL);
v___x_2983_ = lean_usize_add(v_i_2965_, v___x_2982_);
v___x_2984_ = lean_array_uset(v_bs_x27_2977_, v_i_2965_, v___x_2981_);
v_i_2965_ = v___x_2983_;
v_bs_2966_ = v___x_2984_;
goto _start;
}
else
{
lean_object* v_a_2986_; lean_object* v___x_2988_; uint8_t v_isShared_2989_; uint8_t v_isSharedCheck_2993_; 
lean_dec_ref(v_bs_x27_2977_);
v_a_2986_ = lean_ctor_get(v___x_2979_, 0);
v_isSharedCheck_2993_ = !lean_is_exclusive(v___x_2979_);
if (v_isSharedCheck_2993_ == 0)
{
v___x_2988_ = v___x_2979_;
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
else
{
lean_inc(v_a_2986_);
lean_dec(v___x_2979_);
v___x_2988_ = lean_box(0);
v_isShared_2989_ = v_isSharedCheck_2993_;
goto v_resetjp_2987_;
}
v_resetjp_2987_:
{
lean_object* v___x_2991_; 
if (v_isShared_2989_ == 0)
{
v___x_2991_ = v___x_2988_;
goto v_reusejp_2990_;
}
else
{
lean_object* v_reuseFailAlloc_2992_; 
v_reuseFailAlloc_2992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2992_, 0, v_a_2986_);
v___x_2991_ = v_reuseFailAlloc_2992_;
goto v_reusejp_2990_;
}
v_reusejp_2990_:
{
return v___x_2991_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2994_, lean_object* v_sz_2995_, lean_object* v_i_2996_, lean_object* v_bs_2997_, lean_object* v___y_2998_, lean_object* v___y_2999_, lean_object* v___y_3000_, lean_object* v___y_3001_, lean_object* v___y_3002_){
_start:
{
size_t v_sz_boxed_3003_; size_t v_i_boxed_3004_; lean_object* v_res_3005_; 
v_sz_boxed_3003_ = lean_unbox_usize(v_sz_2995_);
lean_dec(v_sz_2995_);
v_i_boxed_3004_ = lean_unbox_usize(v_i_2996_);
lean_dec(v_i_2996_);
v_res_3005_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2994_, v_sz_boxed_3003_, v_i_boxed_3004_, v_bs_2997_, v___y_2998_, v___y_2999_, v___y_3000_, v___y_3001_);
lean_dec(v___y_3001_);
lean_dec_ref(v___y_3000_);
lean_dec(v___y_2999_);
lean_dec_ref(v___y_2998_);
lean_dec_ref(v_argVars_2994_);
return v_res_3005_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_3006_, lean_object* v_a_3007_){
_start:
{
if (lean_obj_tag(v_a_3006_) == 0)
{
lean_object* v___x_3008_; 
v___x_3008_ = l_List_reverse___redArg(v_a_3007_);
return v___x_3008_;
}
else
{
lean_object* v_head_3009_; lean_object* v_tail_3010_; lean_object* v___x_3012_; uint8_t v_isShared_3013_; uint8_t v_isSharedCheck_3021_; 
v_head_3009_ = lean_ctor_get(v_a_3006_, 0);
v_tail_3010_ = lean_ctor_get(v_a_3006_, 1);
v_isSharedCheck_3021_ = !lean_is_exclusive(v_a_3006_);
if (v_isSharedCheck_3021_ == 0)
{
v___x_3012_ = v_a_3006_;
v_isShared_3013_ = v_isSharedCheck_3021_;
goto v_resetjp_3011_;
}
else
{
lean_inc(v_tail_3010_);
lean_inc(v_head_3009_);
lean_dec(v_a_3006_);
v___x_3012_ = lean_box(0);
v_isShared_3013_ = v_isSharedCheck_3021_;
goto v_resetjp_3011_;
}
v_resetjp_3011_:
{
lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3018_; 
v___x_3014_ = l_Nat_reprFast(v_head_3009_);
v___x_3015_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3014_);
v___x_3016_ = l_Lean_MessageData_ofFormat(v___x_3015_);
if (v_isShared_3013_ == 0)
{
lean_ctor_set(v___x_3012_, 1, v_a_3007_);
lean_ctor_set(v___x_3012_, 0, v___x_3016_);
v___x_3018_ = v___x_3012_;
goto v_reusejp_3017_;
}
else
{
lean_object* v_reuseFailAlloc_3020_; 
v_reuseFailAlloc_3020_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3020_, 0, v___x_3016_);
lean_ctor_set(v_reuseFailAlloc_3020_, 1, v_a_3007_);
v___x_3018_ = v_reuseFailAlloc_3020_;
goto v_reusejp_3017_;
}
v_reusejp_3017_:
{
v_a_3006_ = v_tail_3010_;
v_a_3007_ = v___x_3018_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_3022_; double v___x_3023_; 
v___x_3022_ = lean_unsigned_to_nat(0u);
v___x_3023_ = lean_float_of_nat(v___x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_3026_, lean_object* v_msg_3027_, lean_object* v___y_3028_, lean_object* v___y_3029_, lean_object* v___y_3030_, lean_object* v___y_3031_){
_start:
{
lean_object* v_ref_3033_; lean_object* v___x_3034_; lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3080_; 
v_ref_3033_ = lean_ctor_get(v___y_3030_, 2);
v___x_3034_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_3027_, v___y_3028_, v___y_3029_, v___y_3030_, v___y_3031_);
v_a_3035_ = lean_ctor_get(v___x_3034_, 0);
v_isSharedCheck_3080_ = !lean_is_exclusive(v___x_3034_);
if (v_isSharedCheck_3080_ == 0)
{
v___x_3037_ = v___x_3034_;
v_isShared_3038_ = v_isSharedCheck_3080_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3034_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3080_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3039_; lean_object* v_traceState_3040_; lean_object* v_env_3041_; lean_object* v_nextMacroScope_3042_; lean_object* v_ngen_3043_; lean_object* v_auxDeclNGen_3044_; lean_object* v_cache_3045_; lean_object* v_recordedDeps_3046_; lean_object* v_messages_3047_; lean_object* v_infoState_3048_; lean_object* v_snapshotTasks_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3079_; 
v___x_3039_ = lean_st_ref_take(v___y_3031_);
v_traceState_3040_ = lean_ctor_get(v___x_3039_, 4);
v_env_3041_ = lean_ctor_get(v___x_3039_, 0);
v_nextMacroScope_3042_ = lean_ctor_get(v___x_3039_, 1);
v_ngen_3043_ = lean_ctor_get(v___x_3039_, 2);
v_auxDeclNGen_3044_ = lean_ctor_get(v___x_3039_, 3);
v_cache_3045_ = lean_ctor_get(v___x_3039_, 5);
v_recordedDeps_3046_ = lean_ctor_get(v___x_3039_, 6);
v_messages_3047_ = lean_ctor_get(v___x_3039_, 7);
v_infoState_3048_ = lean_ctor_get(v___x_3039_, 8);
v_snapshotTasks_3049_ = lean_ctor_get(v___x_3039_, 9);
v_isSharedCheck_3079_ = !lean_is_exclusive(v___x_3039_);
if (v_isSharedCheck_3079_ == 0)
{
v___x_3051_ = v___x_3039_;
v_isShared_3052_ = v_isSharedCheck_3079_;
goto v_resetjp_3050_;
}
else
{
lean_inc(v_snapshotTasks_3049_);
lean_inc(v_infoState_3048_);
lean_inc(v_messages_3047_);
lean_inc(v_recordedDeps_3046_);
lean_inc(v_cache_3045_);
lean_inc(v_traceState_3040_);
lean_inc(v_auxDeclNGen_3044_);
lean_inc(v_ngen_3043_);
lean_inc(v_nextMacroScope_3042_);
lean_inc(v_env_3041_);
lean_dec(v___x_3039_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3079_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
uint64_t v_tid_3053_; lean_object* v_traces_3054_; lean_object* v___x_3056_; uint8_t v_isShared_3057_; uint8_t v_isSharedCheck_3078_; 
v_tid_3053_ = lean_ctor_get_uint64(v_traceState_3040_, sizeof(void*)*1);
v_traces_3054_ = lean_ctor_get(v_traceState_3040_, 0);
v_isSharedCheck_3078_ = !lean_is_exclusive(v_traceState_3040_);
if (v_isSharedCheck_3078_ == 0)
{
v___x_3056_ = v_traceState_3040_;
v_isShared_3057_ = v_isSharedCheck_3078_;
goto v_resetjp_3055_;
}
else
{
lean_inc(v_traces_3054_);
lean_dec(v_traceState_3040_);
v___x_3056_ = lean_box(0);
v_isShared_3057_ = v_isSharedCheck_3078_;
goto v_resetjp_3055_;
}
v_resetjp_3055_:
{
lean_object* v___x_3058_; lean_object* v___x_3059_; double v___x_3060_; uint8_t v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3069_; 
v___x_3058_ = lean_box(0);
v___x_3059_ = lean_box(0);
v___x_3060_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_3061_ = 0;
v___x_3062_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___x_3063_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_3063_, 0, v_cls_3026_);
lean_ctor_set(v___x_3063_, 1, v___x_3059_);
lean_ctor_set(v___x_3063_, 2, v___x_3062_);
lean_ctor_set_float(v___x_3063_, sizeof(void*)*3, v___x_3060_);
lean_ctor_set_float(v___x_3063_, sizeof(void*)*3 + 8, v___x_3060_);
lean_ctor_set_uint8(v___x_3063_, sizeof(void*)*3 + 16, v___x_3061_);
v___x_3064_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_3065_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_3065_, 0, v___x_3063_);
lean_ctor_set(v___x_3065_, 1, v_a_3035_);
lean_ctor_set(v___x_3065_, 2, v___x_3064_);
lean_inc(v_ref_3033_);
v___x_3066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3066_, 0, v_ref_3033_);
lean_ctor_set(v___x_3066_, 1, v___x_3065_);
v___x_3067_ = l_Lean_PersistentArray_push___redArg(v_traces_3054_, v___x_3066_);
if (v_isShared_3057_ == 0)
{
lean_ctor_set(v___x_3056_, 0, v___x_3067_);
v___x_3069_ = v___x_3056_;
goto v_reusejp_3068_;
}
else
{
lean_object* v_reuseFailAlloc_3077_; 
v_reuseFailAlloc_3077_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_3077_, 0, v___x_3067_);
lean_ctor_set_uint64(v_reuseFailAlloc_3077_, sizeof(void*)*1, v_tid_3053_);
v___x_3069_ = v_reuseFailAlloc_3077_;
goto v_reusejp_3068_;
}
v_reusejp_3068_:
{
lean_object* v___x_3071_; 
if (v_isShared_3052_ == 0)
{
lean_ctor_set(v___x_3051_, 4, v___x_3069_);
v___x_3071_ = v___x_3051_;
goto v_reusejp_3070_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v_env_3041_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v_nextMacroScope_3042_);
lean_ctor_set(v_reuseFailAlloc_3076_, 2, v_ngen_3043_);
lean_ctor_set(v_reuseFailAlloc_3076_, 3, v_auxDeclNGen_3044_);
lean_ctor_set(v_reuseFailAlloc_3076_, 4, v___x_3069_);
lean_ctor_set(v_reuseFailAlloc_3076_, 5, v_cache_3045_);
lean_ctor_set(v_reuseFailAlloc_3076_, 6, v_recordedDeps_3046_);
lean_ctor_set(v_reuseFailAlloc_3076_, 7, v_messages_3047_);
lean_ctor_set(v_reuseFailAlloc_3076_, 8, v_infoState_3048_);
lean_ctor_set(v_reuseFailAlloc_3076_, 9, v_snapshotTasks_3049_);
v___x_3071_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3070_;
}
v_reusejp_3070_:
{
lean_object* v___x_3072_; lean_object* v___x_3074_; 
v___x_3072_ = lean_st_ref_put(v___y_3031_, v___x_3071_);
if (v_isShared_3038_ == 0)
{
lean_ctor_set(v___x_3037_, 0, v___x_3058_);
v___x_3074_ = v___x_3037_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3058_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_3081_, lean_object* v_msg_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_3081_, v_msg_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
return v_res_3088_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3096_; lean_object* v___x_3097_; lean_object* v___x_3098_; 
v___x_3096_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_3097_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_3098_ = l_Lean_Name_append(v___x_3097_, v___x_3096_);
return v___x_3098_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; 
v___x_3100_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_3101_ = l_Lean_stringToMessageData(v___x_3100_);
return v___x_3101_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; 
v___x_3103_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_3104_ = l_Lean_stringToMessageData(v___x_3103_);
return v___x_3104_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3106_; lean_object* v___x_3107_; 
v___x_3106_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_3107_ = l_Lean_stringToMessageData(v___x_3106_);
return v___x_3107_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_3109_; lean_object* v___x_3110_; 
v___x_3109_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_3110_ = l_Lean_stringToMessageData(v___x_3109_);
return v___x_3110_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_3111_, lean_object* v_fst_3112_, lean_object* v_fst_3113_, lean_object* v_inst_3114_, lean_object* v_a_3115_, lean_object* v_projInfo_x3f_3116_, lean_object* v_argVars_3117_, lean_object* v_x_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_3111_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
if (lean_obj_tag(v___x_3124_) == 0)
{
lean_object* v_a_3125_; lean_object* v_dummy_3126_; lean_object* v_nargs_3127_; lean_object* v___x_3128_; lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; size_t v_sz_3135_; size_t v___x_3136_; lean_object* v___x_3137_; 
v_a_3125_ = lean_ctor_get(v___x_3124_, 0);
lean_inc(v_a_3125_);
lean_dec_ref_known(v___x_3124_, 1);
v_dummy_3126_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_3127_ = l_Lean_Expr_getAppNumArgs(v_a_3111_);
lean_inc(v_nargs_3127_);
v___x_3128_ = lean_mk_array(v_nargs_3127_, v_dummy_3126_);
v___x_3129_ = lean_unsigned_to_nat(1u);
v___x_3130_ = lean_nat_sub(v_nargs_3127_, v___x_3129_);
lean_dec(v_nargs_3127_);
lean_inc_ref(v_a_3111_);
v___x_3131_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_3111_, v___x_3128_, v___x_3130_);
v___x_3132_ = lean_array_get_size(v___x_3131_);
v___x_3133_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_3134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3134_, 0, v___x_3133_);
lean_ctor_set(v___x_3134_, 1, v___x_3132_);
v_sz_3135_ = lean_array_size(v___x_3131_);
v___x_3136_ = ((size_t)0ULL);
v___x_3137_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_3125_, v_fst_3112_, v_argVars_3117_, v___x_3131_, v_sz_3135_, v___x_3136_, v___x_3134_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
lean_dec_ref(v___x_3131_);
lean_dec(v_a_3125_);
if (lean_obj_tag(v___x_3137_) == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; 
lean_dec_ref_known(v___x_3137_, 1);
v___x_3138_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_3139_ = lean_array_get_size(v_fst_3112_);
v___x_3140_ = l_List_range(v___x_3139_);
v___x_3141_ = lean_box(0);
v___x_3142_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_3113_, v___x_3140_, v___x_3141_);
v___x_3143_ = lean_array_mk(v___x_3142_);
v___x_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3138_);
lean_ctor_set(v___x_3144_, 1, v___x_3143_);
lean_inc_ref(v_inst_3114_);
lean_inc_ref(v_argVars_3117_);
v___x_3145_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_3112_, v_argVars_3117_, v_inst_3114_, v_a_3115_, v_projInfo_x3f_3116_, v___x_3144_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
if (lean_obj_tag(v___x_3145_) == 0)
{
lean_object* v_a_3146_; lean_object* v___x_3148_; uint8_t v_isShared_3149_; uint8_t v_isSharedCheck_3238_; 
v_a_3146_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3238_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3238_ == 0)
{
v___x_3148_ = v___x_3145_;
v_isShared_3149_ = v_isSharedCheck_3238_;
goto v_resetjp_3147_;
}
else
{
lean_inc(v_a_3146_);
lean_dec(v___x_3145_);
v___x_3148_ = lean_box(0);
v_isShared_3149_ = v_isSharedCheck_3238_;
goto v_resetjp_3147_;
}
v_resetjp_3147_:
{
lean_object* v_fst_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3236_; 
v_fst_3150_ = lean_ctor_get(v_a_3146_, 0);
v_isSharedCheck_3236_ = !lean_is_exclusive(v_a_3146_);
if (v_isSharedCheck_3236_ == 0)
{
lean_object* v_unused_3237_; 
v_unused_3237_ = lean_ctor_get(v_a_3146_, 1);
lean_dec(v_unused_3237_);
v___x_3152_ = v_a_3146_;
v_isShared_3153_ = v_isSharedCheck_3236_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_fst_3150_);
lean_dec(v_a_3146_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3236_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___y_3155_; lean_object* v___y_3156_; lean_object* v___y_3157_; lean_object* v___y_3158_; lean_object* v___x_3217_; lean_object* v___x_3218_; uint8_t v___x_3219_; 
v___x_3217_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3121_);
v___x_3218_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_3219_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_3217_, v___x_3218_);
lean_dec_ref(v___x_3217_);
if (v___x_3219_ == 0)
{
lean_dec_ref(v_a_3111_);
v___y_3155_ = v___y_3119_;
v___y_3156_ = v___y_3120_;
v___y_3157_ = v___y_3121_;
v___y_3158_ = v___y_3122_;
goto v___jp_3154_;
}
else
{
lean_object* v___x_3220_; lean_object* v_a_3221_; uint8_t v___x_3222_; 
v___x_3220_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_3111_, v___y_3120_);
v_a_3221_ = lean_ctor_get(v___x_3220_, 0);
lean_inc(v_a_3221_);
lean_dec_ref(v___x_3220_);
v___x_3222_ = l_Lean_Expr_hasExprMVar(v_a_3221_);
if (v___x_3222_ == 0)
{
lean_dec(v_a_3221_);
v___y_3155_ = v___y_3119_;
v___y_3156_ = v___y_3120_;
v___y_3157_ = v___y_3121_;
v___y_3158_ = v___y_3122_;
goto v___jp_3154_;
}
else
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v_a_3228_; lean_object* v___x_3230_; uint8_t v_isShared_3231_; uint8_t v_isSharedCheck_3235_; 
lean_del_object(v___x_3152_);
lean_dec(v_fst_3150_);
lean_del_object(v___x_3148_);
lean_dec_ref(v_argVars_3117_);
lean_dec_ref(v_inst_3114_);
v___x_3223_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_3224_ = l_Lean_Expr_setPPExplicit(v_a_3221_, v___x_3219_);
v___x_3225_ = l_Lean_indentExpr(v___x_3224_);
v___x_3226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3226_, 0, v___x_3223_);
lean_ctor_set(v___x_3226_, 1, v___x_3225_);
v___x_3227_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3226_, v___y_3119_, v___y_3120_, v___y_3121_, v___y_3122_);
v_a_3228_ = lean_ctor_get(v___x_3227_, 0);
v_isSharedCheck_3235_ = !lean_is_exclusive(v___x_3227_);
if (v_isSharedCheck_3235_ == 0)
{
v___x_3230_ = v___x_3227_;
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
else
{
lean_inc(v_a_3228_);
lean_dec(v___x_3227_);
v___x_3230_ = lean_box(0);
v_isShared_3231_ = v_isSharedCheck_3235_;
goto v_resetjp_3229_;
}
v_resetjp_3229_:
{
lean_object* v___x_3233_; 
if (v_isShared_3231_ == 0)
{
v___x_3233_ = v___x_3230_;
goto v_reusejp_3232_;
}
else
{
lean_object* v_reuseFailAlloc_3234_; 
v_reuseFailAlloc_3234_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3234_, 0, v_a_3228_);
v___x_3233_ = v_reuseFailAlloc_3234_;
goto v_reusejp_3232_;
}
v_reusejp_3232_:
{
return v___x_3233_;
}
}
}
}
v___jp_3154_:
{
lean_object* v_toCold_3159_; lean_object* v_options_3160_; uint8_t v_hasTrace_3161_; 
v_toCold_3159_ = lean_ctor_get(v___y_3157_, 0);
v_options_3160_ = lean_ctor_get(v_toCold_3159_, 2);
v_hasTrace_3161_ = lean_ctor_get_uint8(v_options_3160_, sizeof(void*)*1);
if (v_hasTrace_3161_ == 0)
{
lean_object* v___x_3163_; 
lean_del_object(v___x_3152_);
lean_dec_ref(v_argVars_3117_);
lean_dec_ref(v_inst_3114_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 0, v_fst_3150_);
v___x_3163_ = v___x_3148_;
goto v_reusejp_3162_;
}
else
{
lean_object* v_reuseFailAlloc_3164_; 
v_reuseFailAlloc_3164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3164_, 0, v_fst_3150_);
v___x_3163_ = v_reuseFailAlloc_3164_;
goto v_reusejp_3162_;
}
v_reusejp_3162_:
{
return v___x_3163_;
}
}
else
{
lean_object* v_inheritedTraceOptions_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; uint8_t v___x_3168_; 
v_inheritedTraceOptions_3165_ = lean_ctor_get(v_toCold_3159_, 11);
v___x_3166_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_3167_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_3168_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_3165_, v_options_3160_, v___x_3167_);
if (v___x_3168_ == 0)
{
lean_object* v___x_3170_; 
lean_del_object(v___x_3152_);
lean_dec_ref(v_argVars_3117_);
lean_dec_ref(v_inst_3114_);
if (v_isShared_3149_ == 0)
{
lean_ctor_set(v___x_3148_, 0, v_fst_3150_);
v___x_3170_ = v___x_3148_;
goto v_reusejp_3169_;
}
else
{
lean_object* v_reuseFailAlloc_3171_; 
v_reuseFailAlloc_3171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3171_, 0, v_fst_3150_);
v___x_3170_ = v_reuseFailAlloc_3171_;
goto v_reusejp_3169_;
}
v_reusejp_3169_:
{
return v___x_3170_;
}
}
else
{
size_t v_sz_3172_; lean_object* v___x_3173_; 
lean_del_object(v___x_3148_);
v_sz_3172_ = lean_array_size(v_fst_3150_);
lean_inc(v_fst_3150_);
v___x_3173_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_3117_, v_sz_3172_, v___x_3136_, v_fst_3150_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
lean_dec_ref(v_argVars_3117_);
if (lean_obj_tag(v___x_3173_) == 0)
{
lean_object* v_a_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3178_; 
v_a_3174_ = lean_ctor_get(v___x_3173_, 0);
lean_inc(v_a_3174_);
lean_dec_ref_known(v___x_3173_, 1);
v___x_3175_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_3176_ = l_Lean_MessageData_ofExpr(v_inst_3114_);
if (v_isShared_3153_ == 0)
{
lean_ctor_set_tag(v___x_3152_, 7);
lean_ctor_set(v___x_3152_, 1, v___x_3176_);
lean_ctor_set(v___x_3152_, 0, v___x_3175_);
v___x_3178_ = v___x_3152_;
goto v_reusejp_3177_;
}
else
{
lean_object* v_reuseFailAlloc_3208_; 
v_reuseFailAlloc_3208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3208_, 0, v___x_3175_);
lean_ctor_set(v_reuseFailAlloc_3208_, 1, v___x_3176_);
v___x_3178_ = v_reuseFailAlloc_3208_;
goto v_reusejp_3177_;
}
v_reusejp_3177_:
{
lean_object* v___x_3179_; lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3179_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_3180_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3180_, 0, v___x_3178_);
lean_ctor_set(v___x_3180_, 1, v___x_3179_);
lean_inc(v_fst_3150_);
v___x_3181_ = lean_array_to_list(v_fst_3150_);
v___x_3182_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_3181_, v___x_3141_);
v___x_3183_ = l_Lean_MessageData_ofList(v___x_3182_);
v___x_3184_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3184_, 0, v___x_3180_);
lean_ctor_set(v___x_3184_, 1, v___x_3183_);
v___x_3185_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_3186_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3186_, 0, v___x_3184_);
lean_ctor_set(v___x_3186_, 1, v___x_3185_);
v___x_3187_ = lean_array_to_list(v_a_3174_);
v___x_3188_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_3189_ = l_Lean_MessageData_joinSep(v___x_3187_, v___x_3188_);
v___x_3190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3190_, 0, v___x_3186_);
lean_ctor_set(v___x_3190_, 1, v___x_3189_);
v___x_3191_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_3166_, v___x_3190_, v___y_3155_, v___y_3156_, v___y_3157_, v___y_3158_);
if (lean_obj_tag(v___x_3191_) == 0)
{
lean_object* v___x_3193_; uint8_t v_isShared_3194_; uint8_t v_isSharedCheck_3198_; 
v_isSharedCheck_3198_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3198_ == 0)
{
lean_object* v_unused_3199_; 
v_unused_3199_ = lean_ctor_get(v___x_3191_, 0);
lean_dec(v_unused_3199_);
v___x_3193_ = v___x_3191_;
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
else
{
lean_dec(v___x_3191_);
v___x_3193_ = lean_box(0);
v_isShared_3194_ = v_isSharedCheck_3198_;
goto v_resetjp_3192_;
}
v_resetjp_3192_:
{
lean_object* v___x_3196_; 
if (v_isShared_3194_ == 0)
{
lean_ctor_set(v___x_3193_, 0, v_fst_3150_);
v___x_3196_ = v___x_3193_;
goto v_reusejp_3195_;
}
else
{
lean_object* v_reuseFailAlloc_3197_; 
v_reuseFailAlloc_3197_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3197_, 0, v_fst_3150_);
v___x_3196_ = v_reuseFailAlloc_3197_;
goto v_reusejp_3195_;
}
v_reusejp_3195_:
{
return v___x_3196_;
}
}
}
else
{
lean_object* v_a_3200_; lean_object* v___x_3202_; uint8_t v_isShared_3203_; uint8_t v_isSharedCheck_3207_; 
lean_dec(v_fst_3150_);
v_a_3200_ = lean_ctor_get(v___x_3191_, 0);
v_isSharedCheck_3207_ = !lean_is_exclusive(v___x_3191_);
if (v_isSharedCheck_3207_ == 0)
{
v___x_3202_ = v___x_3191_;
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
else
{
lean_inc(v_a_3200_);
lean_dec(v___x_3191_);
v___x_3202_ = lean_box(0);
v_isShared_3203_ = v_isSharedCheck_3207_;
goto v_resetjp_3201_;
}
v_resetjp_3201_:
{
lean_object* v___x_3205_; 
if (v_isShared_3203_ == 0)
{
v___x_3205_ = v___x_3202_;
goto v_reusejp_3204_;
}
else
{
lean_object* v_reuseFailAlloc_3206_; 
v_reuseFailAlloc_3206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3206_, 0, v_a_3200_);
v___x_3205_ = v_reuseFailAlloc_3206_;
goto v_reusejp_3204_;
}
v_reusejp_3204_:
{
return v___x_3205_;
}
}
}
}
}
else
{
lean_object* v_a_3209_; lean_object* v___x_3211_; uint8_t v_isShared_3212_; uint8_t v_isSharedCheck_3216_; 
lean_del_object(v___x_3152_);
lean_dec(v_fst_3150_);
lean_dec_ref(v_inst_3114_);
v_a_3209_ = lean_ctor_get(v___x_3173_, 0);
v_isSharedCheck_3216_ = !lean_is_exclusive(v___x_3173_);
if (v_isSharedCheck_3216_ == 0)
{
v___x_3211_ = v___x_3173_;
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
else
{
lean_inc(v_a_3209_);
lean_dec(v___x_3173_);
v___x_3211_ = lean_box(0);
v_isShared_3212_ = v_isSharedCheck_3216_;
goto v_resetjp_3210_;
}
v_resetjp_3210_:
{
lean_object* v___x_3214_; 
if (v_isShared_3212_ == 0)
{
v___x_3214_ = v___x_3211_;
goto v_reusejp_3213_;
}
else
{
lean_object* v_reuseFailAlloc_3215_; 
v_reuseFailAlloc_3215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3215_, 0, v_a_3209_);
v___x_3214_ = v_reuseFailAlloc_3215_;
goto v_reusejp_3213_;
}
v_reusejp_3213_:
{
return v___x_3214_;
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
lean_object* v_a_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3246_; 
lean_dec_ref(v_argVars_3117_);
lean_dec_ref(v_inst_3114_);
lean_dec_ref(v_a_3111_);
v_a_3239_ = lean_ctor_get(v___x_3145_, 0);
v_isSharedCheck_3246_ = !lean_is_exclusive(v___x_3145_);
if (v_isSharedCheck_3246_ == 0)
{
v___x_3241_ = v___x_3145_;
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
else
{
lean_inc(v_a_3239_);
lean_dec(v___x_3145_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3246_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3244_; 
if (v_isShared_3242_ == 0)
{
v___x_3244_ = v___x_3241_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3245_; 
v_reuseFailAlloc_3245_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3245_, 0, v_a_3239_);
v___x_3244_ = v_reuseFailAlloc_3245_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
return v___x_3244_;
}
}
}
}
else
{
lean_object* v_a_3247_; lean_object* v___x_3249_; uint8_t v_isShared_3250_; uint8_t v_isSharedCheck_3254_; 
lean_dec_ref(v_argVars_3117_);
lean_dec_ref(v_a_3115_);
lean_dec_ref(v_inst_3114_);
lean_dec_ref(v_fst_3112_);
lean_dec_ref(v_a_3111_);
v_a_3247_ = lean_ctor_get(v___x_3137_, 0);
v_isSharedCheck_3254_ = !lean_is_exclusive(v___x_3137_);
if (v_isSharedCheck_3254_ == 0)
{
v___x_3249_ = v___x_3137_;
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
else
{
lean_inc(v_a_3247_);
lean_dec(v___x_3137_);
v___x_3249_ = lean_box(0);
v_isShared_3250_ = v_isSharedCheck_3254_;
goto v_resetjp_3248_;
}
v_resetjp_3248_:
{
lean_object* v___x_3252_; 
if (v_isShared_3250_ == 0)
{
v___x_3252_ = v___x_3249_;
goto v_reusejp_3251_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_a_3247_);
v___x_3252_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3251_;
}
v_reusejp_3251_:
{
return v___x_3252_;
}
}
}
}
else
{
lean_dec_ref(v_argVars_3117_);
lean_dec_ref(v_a_3115_);
lean_dec_ref(v_inst_3114_);
lean_dec_ref(v_fst_3112_);
lean_dec_ref(v_a_3111_);
return v___x_3124_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_3255_, lean_object* v_fst_3256_, lean_object* v_fst_3257_, lean_object* v_inst_3258_, lean_object* v_a_3259_, lean_object* v_projInfo_x3f_3260_, lean_object* v_argVars_3261_, lean_object* v_x_3262_, lean_object* v___y_3263_, lean_object* v___y_3264_, lean_object* v___y_3265_, lean_object* v___y_3266_, lean_object* v___y_3267_){
_start:
{
lean_object* v_res_3268_; 
v_res_3268_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_3255_, v_fst_3256_, v_fst_3257_, v_inst_3258_, v_a_3259_, v_projInfo_x3f_3260_, v_argVars_3261_, v_x_3262_, v___y_3263_, v___y_3264_, v___y_3265_, v___y_3266_);
lean_dec(v___y_3266_);
lean_dec_ref(v___y_3265_);
lean_dec(v___y_3264_);
lean_dec_ref(v___y_3263_);
lean_dec_ref(v_x_3262_);
lean_dec(v_projInfo_x3f_3260_);
lean_dec_ref(v_fst_3257_);
return v_res_3268_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(lean_object* v_inst_3269_, lean_object* v_projInfo_x3f_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
lean_object* v___x_3276_; 
lean_inc(v___y_3274_);
lean_inc_ref(v___y_3273_);
lean_inc(v___y_3272_);
lean_inc_ref(v___y_3271_);
lean_inc_ref(v_inst_3269_);
v___x_3276_ = lean_infer_type(v_inst_3269_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3276_) == 0)
{
lean_object* v_a_3277_; lean_object* v___x_3278_; uint8_t v___x_3279_; lean_object* v___x_3280_; 
v_a_3277_ = lean_ctor_get(v___x_3276_, 0);
lean_inc_n(v_a_3277_, 2);
lean_dec_ref_known(v___x_3276_, 1);
v___x_3278_ = lean_box(0);
v___x_3279_ = 0;
v___x_3280_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3277_, v___x_3278_, v___x_3279_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3280_) == 0)
{
lean_object* v_a_3281_; lean_object* v_snd_3282_; lean_object* v_fst_3283_; lean_object* v_fst_3284_; lean_object* v_snd_3285_; lean_object* v___x_3286_; 
v_a_3281_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_a_3281_);
lean_dec_ref_known(v___x_3280_, 1);
v_snd_3282_ = lean_ctor_get(v_a_3281_, 1);
lean_inc(v_snd_3282_);
v_fst_3283_ = lean_ctor_get(v_a_3281_, 0);
lean_inc(v_fst_3283_);
lean_dec(v_a_3281_);
v_fst_3284_ = lean_ctor_get(v_snd_3282_, 0);
lean_inc(v_fst_3284_);
v_snd_3285_ = lean_ctor_get(v_snd_3282_, 1);
lean_inc(v_snd_3285_);
lean_dec(v_snd_3282_);
lean_inc(v___y_3274_);
lean_inc_ref(v___y_3273_);
lean_inc(v___y_3272_);
lean_inc_ref(v___y_3271_);
v___x_3286_ = lean_whnf(v_snd_3285_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
if (lean_obj_tag(v___x_3286_) == 0)
{
lean_object* v_a_3287_; lean_object* v___f_3288_; uint8_t v___x_3289_; lean_object* v___x_3290_; 
v_a_3287_ = lean_ctor_get(v___x_3286_, 0);
lean_inc(v_a_3287_);
lean_dec_ref_known(v___x_3286_, 1);
lean_inc(v_a_3277_);
v___f_3288_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3288_, 0, v_a_3287_);
lean_closure_set(v___f_3288_, 1, v_fst_3283_);
lean_closure_set(v___f_3288_, 2, v_fst_3284_);
lean_closure_set(v___f_3288_, 3, v_inst_3269_);
lean_closure_set(v___f_3288_, 4, v_a_3277_);
lean_closure_set(v___f_3288_, 5, v_projInfo_x3f_3270_);
v___x_3289_ = 0;
v___x_3290_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3277_, v___f_3288_, v___x_3289_, v___x_3289_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
return v___x_3290_;
}
else
{
lean_object* v_a_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3298_; 
lean_dec(v_fst_3284_);
lean_dec(v_fst_3283_);
lean_dec(v_a_3277_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v_projInfo_x3f_3270_);
lean_dec_ref(v_inst_3269_);
v_a_3291_ = lean_ctor_get(v___x_3286_, 0);
v_isSharedCheck_3298_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3298_ == 0)
{
v___x_3293_ = v___x_3286_;
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_a_3291_);
lean_dec(v___x_3286_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3298_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3296_; 
if (v_isShared_3294_ == 0)
{
v___x_3296_ = v___x_3293_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3297_; 
v_reuseFailAlloc_3297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3297_, 0, v_a_3291_);
v___x_3296_ = v_reuseFailAlloc_3297_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
return v___x_3296_;
}
}
}
}
else
{
lean_object* v_a_3299_; lean_object* v___x_3301_; uint8_t v_isShared_3302_; uint8_t v_isSharedCheck_3306_; 
lean_dec(v_a_3277_);
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v_projInfo_x3f_3270_);
lean_dec_ref(v_inst_3269_);
v_a_3299_ = lean_ctor_get(v___x_3280_, 0);
v_isSharedCheck_3306_ = !lean_is_exclusive(v___x_3280_);
if (v_isSharedCheck_3306_ == 0)
{
v___x_3301_ = v___x_3280_;
v_isShared_3302_ = v_isSharedCheck_3306_;
goto v_resetjp_3300_;
}
else
{
lean_inc(v_a_3299_);
lean_dec(v___x_3280_);
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
v_reuseFailAlloc_3305_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3314_; 
lean_dec(v___y_3274_);
lean_dec_ref(v___y_3273_);
lean_dec(v___y_3272_);
lean_dec_ref(v___y_3271_);
lean_dec(v_projInfo_x3f_3270_);
lean_dec_ref(v_inst_3269_);
v_a_3307_ = lean_ctor_get(v___x_3276_, 0);
v_isSharedCheck_3314_ = !lean_is_exclusive(v___x_3276_);
if (v_isSharedCheck_3314_ == 0)
{
v___x_3309_ = v___x_3276_;
v_isShared_3310_ = v_isSharedCheck_3314_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_a_3307_);
lean_dec(v___x_3276_);
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
v_reuseFailAlloc_3313_ = lean_alloc_ctor(1, 1, 0);
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
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1___boxed(lean_object* v_inst_3315_, lean_object* v_projInfo_x3f_3316_, lean_object* v___y_3317_, lean_object* v___y_3318_, lean_object* v___y_3319_, lean_object* v___y_3320_, lean_object* v___y_3321_){
_start:
{
lean_object* v_res_3322_; 
v_res_3322_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3315_, v_projInfo_x3f_3316_, v___y_3317_, v___y_3318_, v___y_3319_, v___y_3320_);
return v_res_3322_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_3323_, lean_object* v_projInfo_x3f_3324_, lean_object* v_a_3325_, lean_object* v_a_3326_, lean_object* v_a_3327_, lean_object* v_a_3328_){
_start:
{
lean_object* v___y_3331_; lean_object* v___x_3348_; uint8_t v_transparency_3349_; uint8_t v___x_3350_; uint8_t v___x_3351_; 
v___x_3348_ = l_Lean_Meta_Context_config(v_a_3325_);
v_transparency_3349_ = lean_ctor_get_uint8(v___x_3348_, 9);
lean_dec_ref(v___x_3348_);
v___x_3350_ = 2;
v___x_3351_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3349_, v___x_3350_);
if (v___x_3351_ == 0)
{
lean_object* v_keyedConfig_3352_; uint8_t v_trackZetaDelta_3353_; lean_object* v_zetaDeltaSet_3354_; lean_object* v_lctx_3355_; lean_object* v_localInstances_3356_; lean_object* v_defEqCtx_x3f_3357_; lean_object* v_synthPendingDepth_3358_; lean_object* v_customCanUnfoldPredicate_x3f_3359_; uint8_t v_univApprox_3360_; uint8_t v_inTypeClassResolution_3361_; uint8_t v_cacheInferType_3362_; lean_object* v___x_3363_; lean_object* v___x_3364_; lean_object* v___x_3365_; 
v_keyedConfig_3352_ = lean_ctor_get(v_a_3325_, 0);
v_trackZetaDelta_3353_ = lean_ctor_get_uint8(v_a_3325_, sizeof(void*)*7);
v_zetaDeltaSet_3354_ = lean_ctor_get(v_a_3325_, 1);
v_lctx_3355_ = lean_ctor_get(v_a_3325_, 2);
v_localInstances_3356_ = lean_ctor_get(v_a_3325_, 3);
v_defEqCtx_x3f_3357_ = lean_ctor_get(v_a_3325_, 4);
v_synthPendingDepth_3358_ = lean_ctor_get(v_a_3325_, 5);
v_customCanUnfoldPredicate_x3f_3359_ = lean_ctor_get(v_a_3325_, 6);
v_univApprox_3360_ = lean_ctor_get_uint8(v_a_3325_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3361_ = lean_ctor_get_uint8(v_a_3325_, sizeof(void*)*7 + 2);
v_cacheInferType_3362_ = lean_ctor_get_uint8(v_a_3325_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3352_);
v___x_3363_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3350_, v_keyedConfig_3352_);
lean_inc(v_customCanUnfoldPredicate_x3f_3359_);
lean_inc(v_synthPendingDepth_3358_);
lean_inc(v_defEqCtx_x3f_3357_);
lean_inc_ref(v_localInstances_3356_);
lean_inc_ref(v_lctx_3355_);
lean_inc(v_zetaDeltaSet_3354_);
v___x_3364_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3364_, 0, v___x_3363_);
lean_ctor_set(v___x_3364_, 1, v_zetaDeltaSet_3354_);
lean_ctor_set(v___x_3364_, 2, v_lctx_3355_);
lean_ctor_set(v___x_3364_, 3, v_localInstances_3356_);
lean_ctor_set(v___x_3364_, 4, v_defEqCtx_x3f_3357_);
lean_ctor_set(v___x_3364_, 5, v_synthPendingDepth_3358_);
lean_ctor_set(v___x_3364_, 6, v_customCanUnfoldPredicate_x3f_3359_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*7, v_trackZetaDelta_3353_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*7 + 1, v_univApprox_3360_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3361_);
lean_ctor_set_uint8(v___x_3364_, sizeof(void*)*7 + 3, v_cacheInferType_3362_);
lean_inc(v_a_3328_);
lean_inc_ref(v_a_3327_);
lean_inc(v_a_3326_);
v___x_3365_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3323_, v_projInfo_x3f_3324_, v___x_3364_, v_a_3326_, v_a_3327_, v_a_3328_);
v___y_3331_ = v___x_3365_;
goto v___jp_3330_;
}
else
{
lean_object* v___x_3366_; 
lean_inc(v_a_3328_);
lean_inc_ref(v_a_3327_);
lean_inc(v_a_3326_);
lean_inc_ref(v_a_3325_);
v___x_3366_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3323_, v_projInfo_x3f_3324_, v_a_3325_, v_a_3326_, v_a_3327_, v_a_3328_);
v___y_3331_ = v___x_3366_;
goto v___jp_3330_;
}
v___jp_3330_:
{
if (lean_obj_tag(v___y_3331_) == 0)
{
lean_object* v_a_3332_; lean_object* v___x_3334_; uint8_t v_isShared_3335_; uint8_t v_isSharedCheck_3339_; 
v_a_3332_ = lean_ctor_get(v___y_3331_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v___y_3331_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3334_ = v___y_3331_;
v_isShared_3335_ = v_isSharedCheck_3339_;
goto v_resetjp_3333_;
}
else
{
lean_inc(v_a_3332_);
lean_dec(v___y_3331_);
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
lean_object* v_a_3340_; lean_object* v___x_3342_; uint8_t v_isShared_3343_; uint8_t v_isSharedCheck_3347_; 
v_a_3340_ = lean_ctor_get(v___y_3331_, 0);
v_isSharedCheck_3347_ = !lean_is_exclusive(v___y_3331_);
if (v_isSharedCheck_3347_ == 0)
{
v___x_3342_ = v___y_3331_;
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
else
{
lean_inc(v_a_3340_);
lean_dec(v___y_3331_);
v___x_3342_ = lean_box(0);
v_isShared_3343_ = v_isSharedCheck_3347_;
goto v_resetjp_3341_;
}
v_resetjp_3341_:
{
lean_object* v___x_3345_; 
if (v_isShared_3343_ == 0)
{
v___x_3345_ = v___x_3342_;
goto v_reusejp_3344_;
}
else
{
lean_object* v_reuseFailAlloc_3346_; 
v_reuseFailAlloc_3346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3346_, 0, v_a_3340_);
v___x_3345_ = v_reuseFailAlloc_3346_;
goto v_reusejp_3344_;
}
v_reusejp_3344_:
{
return v___x_3345_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_3367_, lean_object* v_projInfo_x3f_3368_, lean_object* v_a_3369_, lean_object* v_a_3370_, lean_object* v_a_3371_, lean_object* v_a_3372_, lean_object* v_a_3373_){
_start:
{
lean_object* v_res_3374_; 
v_res_3374_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_3367_, v_projInfo_x3f_3368_, v_a_3369_, v_a_3370_, v_a_3371_, v_a_3372_);
lean_dec(v_a_3372_);
lean_dec_ref(v_a_3371_);
lean_dec(v_a_3370_);
lean_dec_ref(v_a_3369_);
return v_res_3374_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_3375_, lean_object* v_a_3376_, lean_object* v___x_3377_, lean_object* v_inst_3378_, lean_object* v_R_3379_, lean_object* v_a_3380_, lean_object* v_b_3381_, lean_object* v_c_3382_, lean_object* v___y_3383_, lean_object* v___y_3384_, lean_object* v___y_3385_, lean_object* v___y_3386_){
_start:
{
lean_object* v___x_3388_; 
v___x_3388_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_3375_, v_a_3376_, v___x_3377_, v_a_3380_, v_b_3381_);
return v___x_3388_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_3389_, lean_object* v_a_3390_, lean_object* v___x_3391_, lean_object* v_inst_3392_, lean_object* v_R_3393_, lean_object* v_a_3394_, lean_object* v_b_3395_, lean_object* v_c_3396_, lean_object* v___y_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v_res_3402_; 
v_res_3402_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_3389_, v_a_3390_, v___x_3391_, v_inst_3392_, v_R_3393_, v_a_3394_, v_b_3395_, v_c_3396_, v___y_3397_, v___y_3398_, v___y_3399_, v___y_3400_);
lean_dec(v___y_3400_);
lean_dec_ref(v___y_3399_);
lean_dec(v___y_3398_);
lean_dec_ref(v___y_3397_);
lean_dec(v___x_3391_);
lean_dec_ref(v_a_3390_);
lean_dec(v_upperBound_3389_);
return v_res_3402_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3403_, lean_object* v_msg_3404_, lean_object* v___y_3405_, lean_object* v___y_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_){
_start:
{
lean_object* v___x_3410_; 
v___x_3410_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3404_, v___y_3405_, v___y_3406_, v___y_3407_, v___y_3408_);
return v___x_3410_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3411_, lean_object* v_msg_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_, lean_object* v___y_3416_, lean_object* v___y_3417_){
_start:
{
lean_object* v_res_3418_; 
v_res_3418_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3411_, v_msg_3412_, v___y_3413_, v___y_3414_, v___y_3415_, v___y_3416_);
lean_dec(v___y_3416_);
lean_dec_ref(v___y_3415_);
lean_dec(v___y_3414_);
lean_dec_ref(v___y_3413_);
return v_res_3418_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_3419_, lean_object* v_argVars_3420_, lean_object* v_inst_3421_, lean_object* v_a_3422_, lean_object* v_projInfo_x3f_3423_, lean_object* v_inst_3424_, lean_object* v_a_3425_, lean_object* v___y_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_){
_start:
{
lean_object* v___x_3431_; 
v___x_3431_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_3419_, v_argVars_3420_, v_inst_3421_, v_a_3422_, v_projInfo_x3f_3423_, v_a_3425_, v___y_3426_, v___y_3427_, v___y_3428_, v___y_3429_);
return v___x_3431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_3432_, lean_object* v_argVars_3433_, lean_object* v_inst_3434_, lean_object* v_a_3435_, lean_object* v_projInfo_x3f_3436_, lean_object* v_inst_3437_, lean_object* v_a_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_){
_start:
{
lean_object* v_res_3444_; 
v_res_3444_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_3432_, v_argVars_3433_, v_inst_3434_, v_a_3435_, v_projInfo_x3f_3436_, v_inst_3437_, v_a_3438_, v___y_3439_, v___y_3440_, v___y_3441_, v___y_3442_);
lean_dec(v___y_3442_);
lean_dec_ref(v___y_3441_);
lean_dec(v___y_3440_);
lean_dec_ref(v___y_3439_);
lean_dec(v_projInfo_x3f_3436_);
return v_res_3444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(lean_object* v_type_3445_, lean_object* v_k_3446_, uint8_t v_cleanupAnnotations_3447_, lean_object* v___y_3448_, lean_object* v___y_3449_, lean_object* v___y_3450_, lean_object* v___y_3451_){
_start:
{
lean_object* v___f_3453_; uint8_t v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; 
v___f_3453_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3453_, 0, v_k_3446_);
v___x_3454_ = 0;
v___x_3455_ = lean_box(0);
v___x_3456_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3454_, v___x_3455_, v_type_3445_, v___f_3453_, v_cleanupAnnotations_3447_, v___x_3454_, v___y_3448_, v___y_3449_, v___y_3450_, v___y_3451_);
if (lean_obj_tag(v___x_3456_) == 0)
{
lean_object* v_a_3457_; lean_object* v___x_3459_; uint8_t v_isShared_3460_; uint8_t v_isSharedCheck_3464_; 
v_a_3457_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3459_ = v___x_3456_;
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
else
{
lean_inc(v_a_3457_);
lean_dec(v___x_3456_);
v___x_3459_ = lean_box(0);
v_isShared_3460_ = v_isSharedCheck_3464_;
goto v_resetjp_3458_;
}
v_resetjp_3458_:
{
lean_object* v___x_3462_; 
if (v_isShared_3460_ == 0)
{
v___x_3462_ = v___x_3459_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v_a_3457_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
}
else
{
lean_object* v_a_3465_; lean_object* v___x_3467_; uint8_t v_isShared_3468_; uint8_t v_isSharedCheck_3472_; 
v_a_3465_ = lean_ctor_get(v___x_3456_, 0);
v_isSharedCheck_3472_ = !lean_is_exclusive(v___x_3456_);
if (v_isSharedCheck_3472_ == 0)
{
v___x_3467_ = v___x_3456_;
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
else
{
lean_inc(v_a_3465_);
lean_dec(v___x_3456_);
v___x_3467_ = lean_box(0);
v_isShared_3468_ = v_isSharedCheck_3472_;
goto v_resetjp_3466_;
}
v_resetjp_3466_:
{
lean_object* v___x_3470_; 
if (v_isShared_3468_ == 0)
{
v___x_3470_ = v___x_3467_;
goto v_reusejp_3469_;
}
else
{
lean_object* v_reuseFailAlloc_3471_; 
v_reuseFailAlloc_3471_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3471_, 0, v_a_3465_);
v___x_3470_ = v_reuseFailAlloc_3471_;
goto v_reusejp_3469_;
}
v_reusejp_3469_:
{
return v___x_3470_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg___boxed(lean_object* v_type_3473_, lean_object* v_k_3474_, lean_object* v_cleanupAnnotations_3475_, lean_object* v___y_3476_, lean_object* v___y_3477_, lean_object* v___y_3478_, lean_object* v___y_3479_, lean_object* v___y_3480_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3481_; lean_object* v_res_3482_; 
v_cleanupAnnotations_boxed_3481_ = lean_unbox(v_cleanupAnnotations_3475_);
v_res_3482_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3473_, v_k_3474_, v_cleanupAnnotations_boxed_3481_, v___y_3476_, v___y_3477_, v___y_3478_, v___y_3479_);
lean_dec(v___y_3479_);
lean_dec_ref(v___y_3478_);
lean_dec(v___y_3477_);
lean_dec_ref(v___y_3476_);
return v_res_3482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(lean_object* v_00_u03b1_3483_, lean_object* v_type_3484_, lean_object* v_k_3485_, uint8_t v_cleanupAnnotations_3486_, lean_object* v___y_3487_, lean_object* v___y_3488_, lean_object* v___y_3489_, lean_object* v___y_3490_){
_start:
{
lean_object* v___x_3492_; 
v___x_3492_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3484_, v_k_3485_, v_cleanupAnnotations_3486_, v___y_3487_, v___y_3488_, v___y_3489_, v___y_3490_);
return v___x_3492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___boxed(lean_object* v_00_u03b1_3493_, lean_object* v_type_3494_, lean_object* v_k_3495_, lean_object* v_cleanupAnnotations_3496_, lean_object* v___y_3497_, lean_object* v___y_3498_, lean_object* v___y_3499_, lean_object* v___y_3500_, lean_object* v___y_3501_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3502_; lean_object* v_res_3503_; 
v_cleanupAnnotations_boxed_3502_ = lean_unbox(v_cleanupAnnotations_3496_);
v_res_3503_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(v_00_u03b1_3493_, v_type_3494_, v_k_3495_, v_cleanupAnnotations_boxed_3502_, v___y_3497_, v___y_3498_, v___y_3499_, v___y_3500_);
lean_dec(v___y_3500_);
lean_dec_ref(v___y_3499_);
lean_dec(v___y_3498_);
lean_dec_ref(v___y_3497_);
return v_res_3503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(lean_object* v_as_3504_, size_t v_sz_3505_, size_t v_i_3506_, lean_object* v_b_3507_, lean_object* v___y_3508_, lean_object* v___y_3509_, lean_object* v___y_3510_, lean_object* v___y_3511_){
_start:
{
lean_object* v_a_3514_; uint8_t v___x_3518_; 
v___x_3518_ = lean_usize_dec_lt(v_i_3506_, v_sz_3505_);
if (v___x_3518_ == 0)
{
lean_object* v___x_3519_; 
v___x_3519_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3519_, 0, v_b_3507_);
return v___x_3519_;
}
else
{
lean_object* v___x_3520_; lean_object* v_a_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; 
v___x_3520_ = lean_box(0);
v_a_3521_ = lean_array_uget_borrowed(v_as_3504_, v_i_3506_);
v___x_3522_ = l_Lean_Expr_fvarId_x21(v_a_3521_);
lean_inc(v___x_3522_);
v___x_3523_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_3522_, v___y_3509_, v___y_3510_, v___y_3511_);
if (lean_obj_tag(v___x_3523_) == 0)
{
lean_object* v_a_3524_; uint8_t v___x_3525_; uint8_t v___x_3526_; 
v_a_3524_ = lean_ctor_get(v___x_3523_, 0);
lean_inc(v_a_3524_);
lean_dec_ref_known(v___x_3523_, 1);
v___x_3525_ = lean_unbox(v_a_3524_);
lean_dec(v_a_3524_);
v___x_3526_ = l_Lean_BinderInfo_isInstImplicit(v___x_3525_);
if (v___x_3526_ == 0)
{
lean_dec(v___x_3522_);
v_a_3514_ = v___x_3520_;
goto v___jp_3513_;
}
else
{
lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3529_; 
v___x_3527_ = lean_st_ref_take(v___y_3508_);
v___x_3528_ = l_Lean_CollectFVars_State_add(v___x_3527_, v___x_3522_);
v___x_3529_ = lean_st_ref_put(v___y_3508_, v___x_3528_);
v_a_3514_ = v___x_3520_;
goto v___jp_3513_;
}
}
else
{
lean_object* v_a_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3537_; 
lean_dec(v___x_3522_);
v_a_3530_ = lean_ctor_get(v___x_3523_, 0);
v_isSharedCheck_3537_ = !lean_is_exclusive(v___x_3523_);
if (v_isSharedCheck_3537_ == 0)
{
v___x_3532_ = v___x_3523_;
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_a_3530_);
lean_dec(v___x_3523_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3537_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v___x_3535_; 
if (v_isShared_3533_ == 0)
{
v___x_3535_ = v___x_3532_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_a_3530_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
return v___x_3535_;
}
}
}
}
v___jp_3513_:
{
size_t v___x_3515_; size_t v___x_3516_; 
v___x_3515_ = ((size_t)1ULL);
v___x_3516_ = lean_usize_add(v_i_3506_, v___x_3515_);
v_i_3506_ = v___x_3516_;
v_b_3507_ = v_a_3514_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg___boxed(lean_object* v_as_3538_, lean_object* v_sz_3539_, lean_object* v_i_3540_, lean_object* v_b_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_, lean_object* v___y_3546_){
_start:
{
size_t v_sz_boxed_3547_; size_t v_i_boxed_3548_; lean_object* v_res_3549_; 
v_sz_boxed_3547_ = lean_unbox_usize(v_sz_3539_);
lean_dec(v_sz_3539_);
v_i_boxed_3548_ = lean_unbox_usize(v_i_3540_);
lean_dec(v_i_3540_);
v_res_3549_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_as_3538_, v_sz_boxed_3547_, v_i_boxed_3548_, v_b_3541_, v___y_3542_, v___y_3543_, v___y_3544_, v___y_3545_);
lean_dec(v___y_3545_);
lean_dec_ref(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v_as_3538_);
return v_res_3549_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(uint8_t v_suppressElabErrors_3557_, lean_object* v_x_3558_){
_start:
{
if (lean_obj_tag(v_x_3558_) == 1)
{
lean_object* v_pre_3559_; 
v_pre_3559_ = lean_ctor_get(v_x_3558_, 0);
switch(lean_obj_tag(v_pre_3559_))
{
case 1:
{
lean_object* v_pre_3560_; 
v_pre_3560_ = lean_ctor_get(v_pre_3559_, 0);
switch(lean_obj_tag(v_pre_3560_))
{
case 0:
{
lean_object* v_str_3561_; lean_object* v_str_3562_; lean_object* v___x_3563_; uint8_t v___x_3564_; 
v_str_3561_ = lean_ctor_get(v_x_3558_, 1);
v_str_3562_ = lean_ctor_get(v_pre_3559_, 1);
v___x_3563_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__0));
v___x_3564_ = lean_string_dec_eq(v_str_3562_, v___x_3563_);
if (v___x_3564_ == 0)
{
lean_object* v___x_3565_; uint8_t v___x_3566_; 
v___x_3565_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__1));
v___x_3566_ = lean_string_dec_eq(v_str_3562_, v___x_3565_);
if (v___x_3566_ == 0)
{
return v___x_3566_;
}
else
{
lean_object* v___x_3567_; uint8_t v___x_3568_; 
v___x_3567_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__2));
v___x_3568_ = lean_string_dec_eq(v_str_3561_, v___x_3567_);
if (v___x_3568_ == 0)
{
return v___x_3568_;
}
else
{
return v_suppressElabErrors_3557_;
}
}
}
else
{
lean_object* v___x_3569_; uint8_t v___x_3570_; 
v___x_3569_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__3));
v___x_3570_ = lean_string_dec_eq(v_str_3561_, v___x_3569_);
if (v___x_3570_ == 0)
{
return v___x_3570_;
}
else
{
return v_suppressElabErrors_3557_;
}
}
}
case 1:
{
lean_object* v_pre_3571_; 
v_pre_3571_ = lean_ctor_get(v_pre_3560_, 0);
if (lean_obj_tag(v_pre_3571_) == 0)
{
lean_object* v_str_3572_; lean_object* v_str_3573_; lean_object* v_str_3574_; lean_object* v___x_3575_; uint8_t v___x_3576_; 
v_str_3572_ = lean_ctor_get(v_x_3558_, 1);
v_str_3573_ = lean_ctor_get(v_pre_3559_, 1);
v_str_3574_ = lean_ctor_get(v_pre_3560_, 1);
v___x_3575_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__4));
v___x_3576_ = lean_string_dec_eq(v_str_3574_, v___x_3575_);
if (v___x_3576_ == 0)
{
return v___x_3576_;
}
else
{
lean_object* v___x_3577_; uint8_t v___x_3578_; 
v___x_3577_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__5));
v___x_3578_ = lean_string_dec_eq(v_str_3573_, v___x_3577_);
if (v___x_3578_ == 0)
{
return v___x_3578_;
}
else
{
lean_object* v___x_3579_; uint8_t v___x_3580_; 
v___x_3579_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__6));
v___x_3580_ = lean_string_dec_eq(v_str_3572_, v___x_3579_);
if (v___x_3580_ == 0)
{
return v___x_3580_;
}
else
{
return v_suppressElabErrors_3557_;
}
}
}
}
else
{
uint8_t v___x_3581_; 
v___x_3581_ = 0;
return v___x_3581_;
}
}
default: 
{
uint8_t v___x_3582_; 
v___x_3582_ = 0;
return v___x_3582_;
}
}
}
case 0:
{
lean_object* v_str_3583_; lean_object* v___x_3584_; uint8_t v___x_3585_; 
v_str_3583_ = lean_ctor_get(v_x_3558_, 1);
v___x_3584_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3585_ = lean_string_dec_eq(v_str_3583_, v___x_3584_);
if (v___x_3585_ == 0)
{
return v___x_3585_;
}
else
{
return v_suppressElabErrors_3557_;
}
}
default: 
{
uint8_t v___x_3586_; 
v___x_3586_ = 0;
return v___x_3586_;
}
}
}
else
{
uint8_t v___x_3587_; 
v___x_3587_ = 0;
return v___x_3587_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed(lean_object* v_suppressElabErrors_3588_, lean_object* v_x_3589_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3590_; uint8_t v_res_3591_; lean_object* v_r_3592_; 
v_suppressElabErrors_boxed_3590_ = lean_unbox(v_suppressElabErrors_3588_);
v_res_3591_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(v_suppressElabErrors_boxed_3590_, v_x_3589_);
lean_dec(v_x_3589_);
v_r_3592_ = lean_box(v_res_3591_);
return v_r_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(lean_object* v_ref_3593_, lean_object* v_msgData_3594_, uint8_t v_severity_3595_, uint8_t v_isSilent_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; uint8_t v___y_3608_; uint8_t v___y_3609_; lean_object* v_toCold_3610_; lean_object* v___y_3611_; lean_object* v___y_3640_; lean_object* v___y_3641_; lean_object* v___y_3642_; uint8_t v___y_3643_; lean_object* v___y_3644_; uint8_t v___y_3645_; uint8_t v___y_3646_; lean_object* v___y_3647_; lean_object* v___y_3667_; lean_object* v___y_3668_; uint8_t v___y_3669_; lean_object* v___y_3670_; uint8_t v___y_3671_; uint8_t v___y_3672_; lean_object* v___y_3673_; uint8_t v___y_3677_; uint8_t v___y_3678_; uint8_t v___x_3688_; uint8_t v___y_3690_; uint8_t v___x_3696_; 
v___x_3688_ = 2;
v___x_3696_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3595_, v___x_3688_);
if (v___x_3696_ == 0)
{
v___y_3690_ = v___x_3696_;
goto v___jp_3689_;
}
else
{
uint8_t v___x_3697_; 
lean_inc_ref(v_msgData_3594_);
v___x_3697_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3594_);
if (v___x_3697_ == 0)
{
v___y_3690_ = v___x_3697_;
goto v___jp_3689_;
}
else
{
lean_object* v___x_3698_; lean_object* v___x_3699_; 
lean_dec_ref(v_msgData_3594_);
v___x_3698_ = lean_box(0);
v___x_3699_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3699_, 0, v___x_3698_);
return v___x_3699_;
}
}
v___jp_3602_:
{
lean_object* v_currNamespace_3612_; lean_object* v_openDecls_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; lean_object* v_env_3618_; lean_object* v_nextMacroScope_3619_; lean_object* v_ngen_3620_; lean_object* v_auxDeclNGen_3621_; lean_object* v_traceState_3622_; lean_object* v_cache_3623_; lean_object* v_recordedDeps_3624_; lean_object* v_messages_3625_; lean_object* v_infoState_3626_; lean_object* v_snapshotTasks_3627_; lean_object* v___x_3629_; uint8_t v_isShared_3630_; uint8_t v_isSharedCheck_3638_; 
v_currNamespace_3612_ = lean_ctor_get(v_toCold_3610_, 4);
v_openDecls_3613_ = lean_ctor_get(v_toCold_3610_, 5);
lean_inc(v_openDecls_3613_);
lean_inc(v_currNamespace_3612_);
v___x_3614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3614_, 0, v_currNamespace_3612_);
lean_ctor_set(v___x_3614_, 1, v_openDecls_3613_);
v___x_3615_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3614_);
lean_ctor_set(v___x_3615_, 1, v___y_3604_);
lean_inc_ref(v___y_3605_);
lean_inc_ref(v___y_3606_);
v___x_3616_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3616_, 0, v___y_3606_);
lean_ctor_set(v___x_3616_, 1, v___y_3603_);
lean_ctor_set(v___x_3616_, 2, v___y_3607_);
lean_ctor_set(v___x_3616_, 3, v___y_3605_);
lean_ctor_set(v___x_3616_, 4, v___x_3615_);
lean_ctor_set_uint8(v___x_3616_, sizeof(void*)*5, v___y_3609_);
lean_ctor_set_uint8(v___x_3616_, sizeof(void*)*5 + 1, v___y_3608_);
lean_ctor_set_uint8(v___x_3616_, sizeof(void*)*5 + 2, v_isSilent_3596_);
v___x_3617_ = lean_st_ref_take(v___y_3611_);
v_env_3618_ = lean_ctor_get(v___x_3617_, 0);
v_nextMacroScope_3619_ = lean_ctor_get(v___x_3617_, 1);
v_ngen_3620_ = lean_ctor_get(v___x_3617_, 2);
v_auxDeclNGen_3621_ = lean_ctor_get(v___x_3617_, 3);
v_traceState_3622_ = lean_ctor_get(v___x_3617_, 4);
v_cache_3623_ = lean_ctor_get(v___x_3617_, 5);
v_recordedDeps_3624_ = lean_ctor_get(v___x_3617_, 6);
v_messages_3625_ = lean_ctor_get(v___x_3617_, 7);
v_infoState_3626_ = lean_ctor_get(v___x_3617_, 8);
v_snapshotTasks_3627_ = lean_ctor_get(v___x_3617_, 9);
v_isSharedCheck_3638_ = !lean_is_exclusive(v___x_3617_);
if (v_isSharedCheck_3638_ == 0)
{
v___x_3629_ = v___x_3617_;
v_isShared_3630_ = v_isSharedCheck_3638_;
goto v_resetjp_3628_;
}
else
{
lean_inc(v_snapshotTasks_3627_);
lean_inc(v_infoState_3626_);
lean_inc(v_messages_3625_);
lean_inc(v_recordedDeps_3624_);
lean_inc(v_cache_3623_);
lean_inc(v_traceState_3622_);
lean_inc(v_auxDeclNGen_3621_);
lean_inc(v_ngen_3620_);
lean_inc(v_nextMacroScope_3619_);
lean_inc(v_env_3618_);
lean_dec(v___x_3617_);
v___x_3629_ = lean_box(0);
v_isShared_3630_ = v_isSharedCheck_3638_;
goto v_resetjp_3628_;
}
v_resetjp_3628_:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3634_; 
v___x_3631_ = lean_box(0);
v___x_3632_ = l_Lean_MessageLog_add(v___x_3616_, v_messages_3625_);
if (v_isShared_3630_ == 0)
{
lean_ctor_set(v___x_3629_, 7, v___x_3632_);
v___x_3634_ = v___x_3629_;
goto v_reusejp_3633_;
}
else
{
lean_object* v_reuseFailAlloc_3637_; 
v_reuseFailAlloc_3637_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3637_, 0, v_env_3618_);
lean_ctor_set(v_reuseFailAlloc_3637_, 1, v_nextMacroScope_3619_);
lean_ctor_set(v_reuseFailAlloc_3637_, 2, v_ngen_3620_);
lean_ctor_set(v_reuseFailAlloc_3637_, 3, v_auxDeclNGen_3621_);
lean_ctor_set(v_reuseFailAlloc_3637_, 4, v_traceState_3622_);
lean_ctor_set(v_reuseFailAlloc_3637_, 5, v_cache_3623_);
lean_ctor_set(v_reuseFailAlloc_3637_, 6, v_recordedDeps_3624_);
lean_ctor_set(v_reuseFailAlloc_3637_, 7, v___x_3632_);
lean_ctor_set(v_reuseFailAlloc_3637_, 8, v_infoState_3626_);
lean_ctor_set(v_reuseFailAlloc_3637_, 9, v_snapshotTasks_3627_);
v___x_3634_ = v_reuseFailAlloc_3637_;
goto v_reusejp_3633_;
}
v_reusejp_3633_:
{
lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3635_ = lean_st_ref_put(v___y_3611_, v___x_3634_);
v___x_3636_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3631_);
return v___x_3636_;
}
}
}
v___jp_3639_:
{
lean_object* v_fileName_3648_; lean_object* v_fileMap_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v_a_3652_; lean_object* v___x_3654_; uint8_t v_isShared_3655_; uint8_t v_isSharedCheck_3665_; 
v_fileName_3648_ = lean_ctor_get(v___y_3642_, 0);
v_fileMap_3649_ = lean_ctor_get(v___y_3642_, 1);
v___x_3650_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3594_);
v___x_3651_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3650_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
v_a_3652_ = lean_ctor_get(v___x_3651_, 0);
v_isSharedCheck_3665_ = !lean_is_exclusive(v___x_3651_);
if (v_isSharedCheck_3665_ == 0)
{
v___x_3654_ = v___x_3651_;
v_isShared_3655_ = v_isSharedCheck_3665_;
goto v_resetjp_3653_;
}
else
{
lean_inc(v_a_3652_);
lean_dec(v___x_3651_);
v___x_3654_ = lean_box(0);
v_isShared_3655_ = v_isSharedCheck_3665_;
goto v_resetjp_3653_;
}
v_resetjp_3653_:
{
lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; 
lean_inc_ref_n(v_fileMap_3649_, 2);
v___x_3656_ = l_Lean_FileMap_toPosition(v_fileMap_3649_, v___y_3644_);
lean_dec(v___y_3644_);
v___x_3657_ = l_Lean_FileMap_toPosition(v_fileMap_3649_, v___y_3647_);
lean_dec(v___y_3647_);
v___x_3658_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3657_);
v___x_3659_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3643_ == 0)
{
lean_del_object(v___x_3654_);
lean_dec_ref(v___y_3640_);
v___y_3603_ = v___x_3656_;
v___y_3604_ = v_a_3652_;
v___y_3605_ = v___x_3659_;
v___y_3606_ = v_fileName_3648_;
v___y_3607_ = v___x_3658_;
v___y_3608_ = v___y_3646_;
v___y_3609_ = v___y_3645_;
v_toCold_3610_ = v___y_3641_;
v___y_3611_ = v___y_3600_;
goto v___jp_3602_;
}
else
{
uint8_t v___x_3660_; 
lean_inc(v_a_3652_);
v___x_3660_ = l_Lean_MessageData_hasTag(v___y_3640_, v_a_3652_);
if (v___x_3660_ == 0)
{
lean_object* v___x_3661_; lean_object* v___x_3663_; 
lean_dec_ref_known(v___x_3658_, 1);
lean_dec_ref(v___x_3656_);
lean_dec(v_a_3652_);
v___x_3661_ = lean_box(0);
if (v_isShared_3655_ == 0)
{
lean_ctor_set(v___x_3654_, 0, v___x_3661_);
v___x_3663_ = v___x_3654_;
goto v_reusejp_3662_;
}
else
{
lean_object* v_reuseFailAlloc_3664_; 
v_reuseFailAlloc_3664_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3664_, 0, v___x_3661_);
v___x_3663_ = v_reuseFailAlloc_3664_;
goto v_reusejp_3662_;
}
v_reusejp_3662_:
{
return v___x_3663_;
}
}
else
{
lean_del_object(v___x_3654_);
v___y_3603_ = v___x_3656_;
v___y_3604_ = v_a_3652_;
v___y_3605_ = v___x_3659_;
v___y_3606_ = v_fileName_3648_;
v___y_3607_ = v___x_3658_;
v___y_3608_ = v___y_3646_;
v___y_3609_ = v___y_3645_;
v_toCold_3610_ = v___y_3641_;
v___y_3611_ = v___y_3600_;
goto v___jp_3602_;
}
}
}
}
v___jp_3666_:
{
lean_object* v___x_3674_; 
v___x_3674_ = l_Lean_Syntax_getTailPos_x3f(v___y_3670_, v___y_3672_);
lean_dec(v___y_3670_);
if (lean_obj_tag(v___x_3674_) == 0)
{
lean_inc(v___y_3673_);
v___y_3640_ = v___y_3667_;
v___y_3641_ = v___y_3668_;
v___y_3642_ = v___y_3668_;
v___y_3643_ = v___y_3669_;
v___y_3644_ = v___y_3673_;
v___y_3645_ = v___y_3672_;
v___y_3646_ = v___y_3671_;
v___y_3647_ = v___y_3673_;
goto v___jp_3639_;
}
else
{
lean_object* v_val_3675_; 
v_val_3675_ = lean_ctor_get(v___x_3674_, 0);
lean_inc(v_val_3675_);
lean_dec_ref_known(v___x_3674_, 1);
v___y_3640_ = v___y_3667_;
v___y_3641_ = v___y_3668_;
v___y_3642_ = v___y_3668_;
v___y_3643_ = v___y_3669_;
v___y_3644_ = v___y_3673_;
v___y_3645_ = v___y_3672_;
v___y_3646_ = v___y_3671_;
v___y_3647_ = v_val_3675_;
goto v___jp_3639_;
}
}
v___jp_3676_:
{
lean_object* v_toCold_3679_; lean_object* v_ref_3680_; uint8_t v_suppressElabErrors_3681_; lean_object* v___x_3682_; lean_object* v___f_3683_; lean_object* v_ref_3684_; lean_object* v___x_3685_; 
v_toCold_3679_ = lean_ctor_get(v___y_3599_, 0);
v_ref_3680_ = lean_ctor_get(v___y_3599_, 2);
v_suppressElabErrors_3681_ = lean_ctor_get_uint8(v___y_3599_, sizeof(void*)*3 + 2);
v___x_3682_ = lean_box(v_suppressElabErrors_3681_);
v___f_3683_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed), 2, 1);
lean_closure_set(v___f_3683_, 0, v___x_3682_);
v_ref_3684_ = l_Lean_replaceRef(v_ref_3593_, v_ref_3680_);
v___x_3685_ = l_Lean_Syntax_getPos_x3f(v_ref_3684_, v___y_3677_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v___x_3686_; 
v___x_3686_ = lean_unsigned_to_nat(0u);
v___y_3667_ = v___f_3683_;
v___y_3668_ = v_toCold_3679_;
v___y_3669_ = v_suppressElabErrors_3681_;
v___y_3670_ = v_ref_3684_;
v___y_3671_ = v___y_3678_;
v___y_3672_ = v___y_3677_;
v___y_3673_ = v___x_3686_;
goto v___jp_3666_;
}
else
{
lean_object* v_val_3687_; 
v_val_3687_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_val_3687_);
lean_dec_ref_known(v___x_3685_, 1);
v___y_3667_ = v___f_3683_;
v___y_3668_ = v_toCold_3679_;
v___y_3669_ = v_suppressElabErrors_3681_;
v___y_3670_ = v_ref_3684_;
v___y_3671_ = v___y_3678_;
v___y_3672_ = v___y_3677_;
v___y_3673_ = v_val_3687_;
goto v___jp_3666_;
}
}
v___jp_3689_:
{
uint8_t v___x_3691_; uint8_t v___x_3692_; 
v___x_3691_ = 1;
v___x_3692_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3595_, v___x_3691_);
if (v___x_3692_ == 0)
{
v___y_3677_ = v___y_3690_;
v___y_3678_ = v_severity_3595_;
goto v___jp_3676_;
}
else
{
lean_object* v___x_3693_; lean_object* v___x_3694_; uint8_t v___x_3695_; 
v___x_3693_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3599_);
v___x_3694_ = l_Lean_warningAsError;
v___x_3695_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_3693_, v___x_3694_);
lean_dec_ref(v___x_3693_);
if (v___x_3695_ == 0)
{
v___y_3677_ = v___y_3690_;
v___y_3678_ = v_severity_3595_;
goto v___jp_3676_;
}
else
{
v___y_3677_ = v___y_3690_;
v___y_3678_ = v___x_3688_;
goto v___jp_3676_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___boxed(lean_object* v_ref_3700_, lean_object* v_msgData_3701_, lean_object* v_severity_3702_, lean_object* v_isSilent_3703_, lean_object* v___y_3704_, lean_object* v___y_3705_, lean_object* v___y_3706_, lean_object* v___y_3707_, lean_object* v___y_3708_){
_start:
{
uint8_t v_severity_boxed_3709_; uint8_t v_isSilent_boxed_3710_; lean_object* v_res_3711_; 
v_severity_boxed_3709_ = lean_unbox(v_severity_3702_);
v_isSilent_boxed_3710_ = lean_unbox(v_isSilent_3703_);
v_res_3711_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3700_, v_msgData_3701_, v_severity_boxed_3709_, v_isSilent_boxed_3710_, v___y_3704_, v___y_3705_, v___y_3706_, v___y_3707_);
lean_dec(v___y_3707_);
lean_dec_ref(v___y_3706_);
lean_dec(v___y_3705_);
lean_dec_ref(v___y_3704_);
lean_dec(v_ref_3700_);
return v_res_3711_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(lean_object* v_msgData_3712_, uint8_t v_severity_3713_, uint8_t v_isSilent_3714_, lean_object* v___y_3715_, lean_object* v___y_3716_, lean_object* v___y_3717_, lean_object* v___y_3718_){
_start:
{
lean_object* v_ref_3720_; lean_object* v___x_3721_; 
v_ref_3720_ = lean_ctor_get(v___y_3717_, 2);
v___x_3721_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3720_, v_msgData_3712_, v_severity_3713_, v_isSilent_3714_, v___y_3715_, v___y_3716_, v___y_3717_, v___y_3718_);
return v___x_3721_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3___boxed(lean_object* v_msgData_3722_, lean_object* v_severity_3723_, lean_object* v_isSilent_3724_, lean_object* v___y_3725_, lean_object* v___y_3726_, lean_object* v___y_3727_, lean_object* v___y_3728_, lean_object* v___y_3729_){
_start:
{
uint8_t v_severity_boxed_3730_; uint8_t v_isSilent_boxed_3731_; lean_object* v_res_3732_; 
v_severity_boxed_3730_ = lean_unbox(v_severity_3723_);
v_isSilent_boxed_3731_ = lean_unbox(v_isSilent_3724_);
v_res_3732_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3722_, v_severity_boxed_3730_, v_isSilent_boxed_3731_, v___y_3725_, v___y_3726_, v___y_3727_, v___y_3728_);
lean_dec(v___y_3728_);
lean_dec_ref(v___y_3727_);
lean_dec(v___y_3726_);
lean_dec_ref(v___y_3725_);
return v_res_3732_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object* v_msgData_3733_, lean_object* v___y_3734_, lean_object* v___y_3735_, lean_object* v___y_3736_, lean_object* v___y_3737_){
_start:
{
uint8_t v___x_3739_; uint8_t v___x_3740_; lean_object* v___x_3741_; 
v___x_3739_ = 1;
v___x_3740_ = 0;
v___x_3741_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3733_, v___x_3739_, v___x_3740_, v___y_3734_, v___y_3735_, v___y_3736_, v___y_3737_);
return v___x_3741_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object* v_msgData_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v_res_3748_; 
v_res_3748_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v_msgData_3742_, v___y_3743_, v___y_3744_, v___y_3745_, v___y_3746_);
lean_dec(v___y_3746_);
lean_dec_ref(v___y_3745_);
lean_dec(v___y_3744_);
lean_dec_ref(v___y_3743_);
return v_res_3748_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object* v_k_3749_, lean_object* v_t_3750_){
_start:
{
if (lean_obj_tag(v_t_3750_) == 0)
{
lean_object* v_k_3751_; lean_object* v_l_3752_; lean_object* v_r_3753_; uint8_t v___x_3754_; 
v_k_3751_ = lean_ctor_get(v_t_3750_, 1);
v_l_3752_ = lean_ctor_get(v_t_3750_, 3);
v_r_3753_ = lean_ctor_get(v_t_3750_, 4);
v___x_3754_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3749_, v_k_3751_);
switch(v___x_3754_)
{
case 0:
{
v_t_3750_ = v_l_3752_;
goto _start;
}
case 1:
{
uint8_t v___x_3756_; 
v___x_3756_ = 1;
return v___x_3756_;
}
default: 
{
v_t_3750_ = v_r_3753_;
goto _start;
}
}
}
else
{
uint8_t v___x_3758_; 
v___x_3758_ = 0;
return v___x_3758_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object* v_k_3759_, lean_object* v_t_3760_){
_start:
{
uint8_t v_res_3761_; lean_object* v_r_3762_; 
v_res_3761_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3759_, v_t_3760_);
lean_dec(v_t_3760_);
lean_dec(v_k_3759_);
v_r_3762_ = lean_box(v_res_3761_);
return v_r_3762_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3764_; lean_object* v___x_3765_; 
v___x_3764_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__0));
v___x_3765_ = l_Lean_stringToMessageData(v___x_3764_);
return v___x_3765_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3767_; lean_object* v___x_3768_; 
v___x_3767_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__2));
v___x_3768_ = l_Lean_stringToMessageData(v___x_3767_);
return v___x_3768_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(lean_object* v_a_3769_, lean_object* v_as_3770_, size_t v_sz_3771_, size_t v_i_3772_, lean_object* v_b_3773_, lean_object* v___y_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_){
_start:
{
lean_object* v_a_3779_; uint8_t v___x_3783_; 
v___x_3783_ = lean_usize_dec_lt(v_i_3772_, v_sz_3771_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; 
v___x_3784_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3784_, 0, v_b_3773_);
return v___x_3784_;
}
else
{
lean_object* v_snd_3785_; 
v_snd_3785_ = lean_ctor_get(v_b_3773_, 1);
lean_inc(v_snd_3785_);
if (lean_obj_tag(v_snd_3785_) == 0)
{
lean_object* v_fst_3786_; lean_object* v___x_3788_; uint8_t v_isShared_3789_; uint8_t v_isSharedCheck_3794_; 
v_fst_3786_ = lean_ctor_get(v_b_3773_, 0);
v_isSharedCheck_3794_ = !lean_is_exclusive(v_b_3773_);
if (v_isSharedCheck_3794_ == 0)
{
lean_object* v_unused_3795_; 
v_unused_3795_ = lean_ctor_get(v_b_3773_, 1);
lean_dec(v_unused_3795_);
v___x_3788_ = v_b_3773_;
v_isShared_3789_ = v_isSharedCheck_3794_;
goto v_resetjp_3787_;
}
else
{
lean_inc(v_fst_3786_);
lean_dec(v_b_3773_);
v___x_3788_ = lean_box(0);
v_isShared_3789_ = v_isSharedCheck_3794_;
goto v_resetjp_3787_;
}
v_resetjp_3787_:
{
lean_object* v___x_3791_; 
if (v_isShared_3789_ == 0)
{
v___x_3791_ = v___x_3788_;
goto v_reusejp_3790_;
}
else
{
lean_object* v_reuseFailAlloc_3793_; 
v_reuseFailAlloc_3793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3793_, 0, v_fst_3786_);
lean_ctor_set(v_reuseFailAlloc_3793_, 1, v_snd_3785_);
v___x_3791_ = v_reuseFailAlloc_3793_;
goto v_reusejp_3790_;
}
v_reusejp_3790_:
{
lean_object* v___x_3792_; 
v___x_3792_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3792_, 0, v___x_3791_);
return v___x_3792_;
}
}
}
else
{
lean_object* v_fst_3796_; lean_object* v___x_3798_; uint8_t v_isShared_3799_; uint8_t v_isSharedCheck_3853_; 
v_fst_3796_ = lean_ctor_get(v_b_3773_, 0);
v_isSharedCheck_3853_ = !lean_is_exclusive(v_b_3773_);
if (v_isSharedCheck_3853_ == 0)
{
lean_object* v_unused_3854_; 
v_unused_3854_ = lean_ctor_get(v_b_3773_, 1);
lean_dec(v_unused_3854_);
v___x_3798_ = v_b_3773_;
v_isShared_3799_ = v_isSharedCheck_3853_;
goto v_resetjp_3797_;
}
else
{
lean_inc(v_fst_3796_);
lean_dec(v_b_3773_);
v___x_3798_ = lean_box(0);
v_isShared_3799_ = v_isSharedCheck_3853_;
goto v_resetjp_3797_;
}
v_resetjp_3797_:
{
lean_object* v_val_3800_; lean_object* v___x_3802_; uint8_t v_isShared_3803_; uint8_t v_isSharedCheck_3852_; 
v_val_3800_ = lean_ctor_get(v_snd_3785_, 0);
v_isSharedCheck_3852_ = !lean_is_exclusive(v_snd_3785_);
if (v_isSharedCheck_3852_ == 0)
{
v___x_3802_ = v_snd_3785_;
v_isShared_3803_ = v_isSharedCheck_3852_;
goto v_resetjp_3801_;
}
else
{
lean_inc(v_val_3800_);
lean_dec(v_snd_3785_);
v___x_3802_ = lean_box(0);
v_isShared_3803_ = v_isSharedCheck_3852_;
goto v_resetjp_3801_;
}
v_resetjp_3801_:
{
lean_object* v_fvarSet_3804_; lean_object* v_a_3805_; lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3809_; 
v_fvarSet_3804_ = lean_ctor_get(v_a_3769_, 1);
v_a_3805_ = lean_array_uget_borrowed(v_as_3770_, v_i_3772_);
v___x_3806_ = lean_unsigned_to_nat(1u);
v___x_3807_ = lean_nat_add(v_val_3800_, v___x_3806_);
if (v_isShared_3803_ == 0)
{
lean_ctor_set(v___x_3802_, 0, v___x_3807_);
v___x_3809_ = v___x_3802_;
goto v_reusejp_3808_;
}
else
{
lean_object* v_reuseFailAlloc_3851_; 
v_reuseFailAlloc_3851_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3851_, 0, v___x_3807_);
v___x_3809_ = v_reuseFailAlloc_3851_;
goto v_reusejp_3808_;
}
v_reusejp_3808_:
{
lean_object* v___x_3810_; uint8_t v___x_3811_; 
v___x_3810_ = l_Lean_Expr_fvarId_x21(v_a_3805_);
v___x_3811_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v___x_3810_, v_fvarSet_3804_);
if (v___x_3811_ == 0)
{
lean_object* v___x_3812_; 
v___x_3812_ = l_Lean_FVarId_getDecl___redArg(v___x_3810_, v___y_3774_, v___y_3775_, v___y_3776_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v_a_3813_; lean_object* v___x_3814_; 
v_a_3813_ = lean_ctor_get(v___x_3812_, 0);
lean_inc(v_a_3813_);
lean_dec_ref_known(v___x_3812_, 1);
v___x_3814_ = l_Lean_LocalDecl_ppAsBinder(v_a_3813_);
if (lean_obj_tag(v___x_3814_) == 1)
{
lean_object* v_val_3815_; lean_object* v___x_3817_; uint8_t v_isShared_3818_; uint8_t v_isSharedCheck_3836_; 
v_val_3815_ = lean_ctor_get(v___x_3814_, 0);
v_isSharedCheck_3836_ = !lean_is_exclusive(v___x_3814_);
if (v_isSharedCheck_3836_ == 0)
{
v___x_3817_ = v___x_3814_;
v_isShared_3818_ = v_isSharedCheck_3836_;
goto v_resetjp_3816_;
}
else
{
lean_inc(v_val_3815_);
lean_dec(v___x_3814_);
v___x_3817_ = lean_box(0);
v_isShared_3818_ = v_isSharedCheck_3836_;
goto v_resetjp_3816_;
}
v_resetjp_3816_:
{
lean_object* v___x_3819_; lean_object* v___x_3820_; lean_object* v___x_3822_; 
v___x_3819_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1);
v___x_3820_ = l_Nat_reprFast(v_val_3800_);
if (v_isShared_3818_ == 0)
{
lean_ctor_set_tag(v___x_3817_, 3);
lean_ctor_set(v___x_3817_, 0, v___x_3820_);
v___x_3822_ = v___x_3817_;
goto v_reusejp_3821_;
}
else
{
lean_object* v_reuseFailAlloc_3835_; 
v_reuseFailAlloc_3835_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3835_, 0, v___x_3820_);
v___x_3822_ = v_reuseFailAlloc_3835_;
goto v_reusejp_3821_;
}
v_reusejp_3821_:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; lean_object* v___x_3825_; lean_object* v___x_3826_; lean_object* v___x_3827_; lean_object* v___x_3828_; lean_object* v___x_3829_; lean_object* v___x_3830_; lean_object* v___x_3831_; lean_object* v___x_3833_; 
v___x_3823_ = l_Lean_MessageData_ofFormat(v___x_3822_);
v___x_3824_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3824_, 0, v___x_3819_);
lean_ctor_set(v___x_3824_, 1, v___x_3823_);
v___x_3825_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3);
v___x_3826_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3826_, 0, v___x_3824_);
lean_ctor_set(v___x_3826_, 1, v___x_3825_);
v___x_3827_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3827_, 0, v___x_3826_);
lean_ctor_set(v___x_3827_, 1, v_val_3815_);
v___x_3828_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3829_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3829_, 0, v___x_3827_);
lean_ctor_set(v___x_3829_, 1, v___x_3828_);
v___x_3830_ = l_Lean_indentD(v___x_3829_);
v___x_3831_ = lean_array_push(v_fst_3796_, v___x_3830_);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 1, v___x_3809_);
lean_ctor_set(v___x_3798_, 0, v___x_3831_);
v___x_3833_ = v___x_3798_;
goto v_reusejp_3832_;
}
else
{
lean_object* v_reuseFailAlloc_3834_; 
v_reuseFailAlloc_3834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3834_, 0, v___x_3831_);
lean_ctor_set(v_reuseFailAlloc_3834_, 1, v___x_3809_);
v___x_3833_ = v_reuseFailAlloc_3834_;
goto v_reusejp_3832_;
}
v_reusejp_3832_:
{
v_a_3779_ = v___x_3833_;
goto v___jp_3778_;
}
}
}
}
else
{
lean_object* v___x_3838_; 
lean_dec(v___x_3814_);
lean_dec(v_val_3800_);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 1, v___x_3809_);
v___x_3838_ = v___x_3798_;
goto v_reusejp_3837_;
}
else
{
lean_object* v_reuseFailAlloc_3839_; 
v_reuseFailAlloc_3839_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3839_, 0, v_fst_3796_);
lean_ctor_set(v_reuseFailAlloc_3839_, 1, v___x_3809_);
v___x_3838_ = v_reuseFailAlloc_3839_;
goto v_reusejp_3837_;
}
v_reusejp_3837_:
{
v_a_3779_ = v___x_3838_;
goto v___jp_3778_;
}
}
}
else
{
lean_object* v_a_3840_; lean_object* v___x_3842_; uint8_t v_isShared_3843_; uint8_t v_isSharedCheck_3847_; 
lean_dec_ref(v___x_3809_);
lean_dec(v_val_3800_);
lean_del_object(v___x_3798_);
lean_dec(v_fst_3796_);
v_a_3840_ = lean_ctor_get(v___x_3812_, 0);
v_isSharedCheck_3847_ = !lean_is_exclusive(v___x_3812_);
if (v_isSharedCheck_3847_ == 0)
{
v___x_3842_ = v___x_3812_;
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
else
{
lean_inc(v_a_3840_);
lean_dec(v___x_3812_);
v___x_3842_ = lean_box(0);
v_isShared_3843_ = v_isSharedCheck_3847_;
goto v_resetjp_3841_;
}
v_resetjp_3841_:
{
lean_object* v___x_3845_; 
if (v_isShared_3843_ == 0)
{
v___x_3845_ = v___x_3842_;
goto v_reusejp_3844_;
}
else
{
lean_object* v_reuseFailAlloc_3846_; 
v_reuseFailAlloc_3846_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3846_, 0, v_a_3840_);
v___x_3845_ = v_reuseFailAlloc_3846_;
goto v_reusejp_3844_;
}
v_reusejp_3844_:
{
return v___x_3845_;
}
}
}
}
else
{
lean_object* v___x_3849_; 
lean_dec(v___x_3810_);
lean_dec(v_val_3800_);
if (v_isShared_3799_ == 0)
{
lean_ctor_set(v___x_3798_, 1, v___x_3809_);
v___x_3849_ = v___x_3798_;
goto v_reusejp_3848_;
}
else
{
lean_object* v_reuseFailAlloc_3850_; 
v_reuseFailAlloc_3850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3850_, 0, v_fst_3796_);
lean_ctor_set(v_reuseFailAlloc_3850_, 1, v___x_3809_);
v___x_3849_ = v_reuseFailAlloc_3850_;
goto v_reusejp_3848_;
}
v_reusejp_3848_:
{
v_a_3779_ = v___x_3849_;
goto v___jp_3778_;
}
}
}
}
}
}
}
v___jp_3778_:
{
size_t v___x_3780_; size_t v___x_3781_; 
v___x_3780_ = ((size_t)1ULL);
v___x_3781_ = lean_usize_add(v_i_3772_, v___x_3780_);
v_i_3772_ = v___x_3781_;
v_b_3773_ = v_a_3779_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___boxed(lean_object* v_a_3855_, lean_object* v_as_3856_, lean_object* v_sz_3857_, lean_object* v_i_3858_, lean_object* v_b_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_, lean_object* v___y_3863_){
_start:
{
size_t v_sz_boxed_3864_; size_t v_i_boxed_3865_; lean_object* v_res_3866_; 
v_sz_boxed_3864_ = lean_unbox_usize(v_sz_3857_);
lean_dec(v_sz_3857_);
v_i_boxed_3865_ = lean_unbox_usize(v_i_3858_);
lean_dec(v_i_3858_);
v_res_3866_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3855_, v_as_3856_, v_sz_boxed_3864_, v_i_boxed_3865_, v_b_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
lean_dec(v___y_3862_);
lean_dec_ref(v___y_3861_);
lean_dec_ref(v___y_3860_);
lean_dec_ref(v_as_3856_);
lean_dec_ref(v_a_3855_);
return v_res_3866_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; 
v___x_3869_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0));
v___x_3870_ = lean_box(1);
v___x_3871_ = l_Lean_CollectFVars_State_ofFVarSet(v___x_3870_, v___x_3869_);
return v___x_3871_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3878_; lean_object* v___x_3879_; 
v___x_3878_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4));
v___x_3879_ = l_Lean_stringToMessageData(v___x_3878_);
return v___x_3879_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3881_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6));
v___x_3882_ = l_Lean_stringToMessageData(v___x_3881_);
return v___x_3882_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_3884_; lean_object* v___x_3885_; 
v___x_3884_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8));
v___x_3885_ = l_Lean_stringToMessageData(v___x_3884_);
return v___x_3885_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3887_; lean_object* v___x_3888_; 
v___x_3887_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10));
v___x_3888_ = l_Lean_stringToMessageData(v___x_3887_);
return v___x_3888_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v___x_3890_, lean_object* v_args_3891_, lean_object* v_ty_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_){
_start:
{
lean_object* v___x_3898_; lean_object* v___x_3899_; lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3898_ = lean_unsigned_to_nat(0u);
v___x_3899_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1);
v___x_3900_ = lean_st_mk_ref(v___x_3899_);
v___x_3901_ = l_Lean_Expr_collectFVars(v_ty_3892_, v___x_3900_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
if (lean_obj_tag(v___x_3901_) == 0)
{
lean_object* v___x_3902_; size_t v_sz_3903_; size_t v___x_3904_; lean_object* v___x_3905_; 
lean_dec_ref_known(v___x_3901_, 1);
v___x_3902_ = lean_box(0);
v_sz_3903_ = lean_array_size(v_args_3891_);
v___x_3904_ = ((size_t)0ULL);
v___x_3905_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_args_3891_, v_sz_3903_, v___x_3904_, v___x_3902_, v___x_3900_, v___y_3893_, v___y_3895_, v___y_3896_);
if (lean_obj_tag(v___x_3905_) == 0)
{
lean_object* v___x_3907_; uint8_t v_isShared_3908_; uint8_t v_isSharedCheck_3976_; 
v_isSharedCheck_3976_ = !lean_is_exclusive(v___x_3905_);
if (v_isSharedCheck_3976_ == 0)
{
lean_object* v_unused_3977_; 
v_unused_3977_ = lean_ctor_get(v___x_3905_, 0);
lean_dec(v_unused_3977_);
v___x_3907_ = v___x_3905_;
v_isShared_3908_ = v_isSharedCheck_3976_;
goto v_resetjp_3906_;
}
else
{
lean_dec(v___x_3905_);
v___x_3907_ = lean_box(0);
v_isShared_3908_ = v_isSharedCheck_3976_;
goto v_resetjp_3906_;
}
v_resetjp_3906_:
{
lean_object* v___x_3909_; lean_object* v___x_3910_; 
v___x_3909_ = lean_st_ref_get(v___x_3900_);
lean_dec(v___x_3900_);
v___x_3910_ = l_Lean_CollectFVars_State_addDependencies(v___x_3909_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
if (lean_obj_tag(v___x_3910_) == 0)
{
lean_object* v_a_3911_; lean_object* v___x_3912_; lean_object* v___x_3913_; lean_object* v___x_3914_; 
v_a_3911_ = lean_ctor_get(v___x_3910_, 0);
lean_inc(v_a_3911_);
lean_dec_ref_known(v___x_3910_, 1);
v___x_3912_ = lean_unsigned_to_nat(1u);
v___x_3913_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3));
v___x_3914_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3911_, v_args_3891_, v_sz_3903_, v___x_3904_, v___x_3913_, v___y_3893_, v___y_3895_, v___y_3896_);
lean_dec(v_a_3911_);
if (lean_obj_tag(v___x_3914_) == 0)
{
lean_object* v_a_3915_; lean_object* v___x_3917_; uint8_t v_isShared_3918_; uint8_t v_isSharedCheck_3959_; 
v_a_3915_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3959_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3959_ == 0)
{
v___x_3917_ = v___x_3914_;
v_isShared_3918_ = v_isSharedCheck_3959_;
goto v_resetjp_3916_;
}
else
{
lean_inc(v_a_3915_);
lean_dec(v___x_3914_);
v___x_3917_ = lean_box(0);
v_isShared_3918_ = v_isSharedCheck_3959_;
goto v_resetjp_3916_;
}
v_resetjp_3916_:
{
lean_object* v_fst_3919_; lean_object* v___x_3921_; uint8_t v_isShared_3922_; uint8_t v_isSharedCheck_3957_; 
v_fst_3919_ = lean_ctor_get(v_a_3915_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v_a_3915_);
if (v_isSharedCheck_3957_ == 0)
{
lean_object* v_unused_3958_; 
v_unused_3958_ = lean_ctor_get(v_a_3915_, 1);
lean_dec(v_unused_3958_);
v___x_3921_ = v_a_3915_;
v_isShared_3922_ = v_isSharedCheck_3957_;
goto v_resetjp_3920_;
}
else
{
lean_inc(v_fst_3919_);
lean_dec(v_a_3915_);
v___x_3921_ = lean_box(0);
v_isShared_3922_ = v_isSharedCheck_3957_;
goto v_resetjp_3920_;
}
v_resetjp_3920_:
{
lean_object* v___x_3923_; uint8_t v___x_3924_; 
v___x_3923_ = lean_array_get_size(v_fst_3919_);
v___x_3924_ = lean_nat_dec_eq(v___x_3923_, v___x_3898_);
if (v___x_3924_ == 0)
{
lean_object* v___x_3925_; lean_object* v___x_3926_; lean_object* v___x_3928_; 
lean_del_object(v___x_3917_);
v___x_3925_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5);
v___x_3926_ = l_Nat_reprFast(v___x_3923_);
if (v_isShared_3908_ == 0)
{
lean_ctor_set_tag(v___x_3907_, 3);
lean_ctor_set(v___x_3907_, 0, v___x_3926_);
v___x_3928_ = v___x_3907_;
goto v_reusejp_3927_;
}
else
{
lean_object* v_reuseFailAlloc_3953_; 
v_reuseFailAlloc_3953_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3953_, 0, v___x_3926_);
v___x_3928_ = v_reuseFailAlloc_3953_;
goto v_reusejp_3927_;
}
v_reusejp_3927_:
{
lean_object* v___x_3929_; lean_object* v___x_3931_; 
v___x_3929_ = l_Lean_MessageData_ofFormat(v___x_3928_);
if (v_isShared_3922_ == 0)
{
lean_ctor_set_tag(v___x_3921_, 7);
lean_ctor_set(v___x_3921_, 1, v___x_3929_);
lean_ctor_set(v___x_3921_, 0, v___x_3925_);
v___x_3931_ = v___x_3921_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3952_; 
v_reuseFailAlloc_3952_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3952_, 0, v___x_3925_);
lean_ctor_set(v_reuseFailAlloc_3952_, 1, v___x_3929_);
v___x_3931_ = v_reuseFailAlloc_3952_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v___y_3935_; uint8_t v___x_3949_; 
v___x_3932_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7);
v___x_3933_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3931_);
lean_ctor_set(v___x_3933_, 1, v___x_3932_);
v___x_3949_ = lean_nat_dec_eq(v___x_3923_, v___x_3912_);
if (v___x_3949_ == 0)
{
lean_object* v___x_3950_; 
v___x_3950_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12));
v___y_3935_ = v___x_3950_;
goto v___jp_3934_;
}
else
{
lean_object* v___x_3951_; 
v___x_3951_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___y_3935_ = v___x_3951_;
goto v___jp_3934_;
}
v___jp_3934_:
{
lean_object* v___x_3936_; lean_object* v___x_3937_; lean_object* v___x_3938_; lean_object* v___x_3939_; lean_object* v___x_3940_; lean_object* v___x_3941_; lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; uint8_t v___x_3946_; 
lean_inc_ref(v___y_3935_);
v___x_3936_ = l_Lean_stringToMessageData(v___y_3935_);
v___x_3937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3937_, 0, v___x_3933_);
lean_ctor_set(v___x_3937_, 1, v___x_3936_);
v___x_3938_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9);
v___x_3939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3939_, 0, v___x_3937_);
lean_ctor_set(v___x_3939_, 1, v___x_3938_);
v___x_3940_ = lean_array_to_list(v_fst_3919_);
v___x_3941_ = l_Lean_MessageData_nil;
v___x_3942_ = l_Lean_MessageData_joinSep(v___x_3940_, v___x_3941_);
v___x_3943_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3943_, 0, v___x_3939_);
lean_ctor_set(v___x_3943_, 1, v___x_3942_);
v___x_3944_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11);
v___x_3945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3943_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = l_Lean_Expr_hasSorry(v___x_3890_);
if (v___x_3946_ == 0)
{
lean_object* v___x_3947_; 
v___x_3947_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3945_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
return v___x_3947_;
}
else
{
lean_object* v___x_3948_; 
v___x_3948_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_3945_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
return v___x_3948_;
}
}
}
}
}
else
{
lean_object* v___x_3955_; 
lean_del_object(v___x_3921_);
lean_dec(v_fst_3919_);
lean_del_object(v___x_3907_);
if (v_isShared_3918_ == 0)
{
lean_ctor_set(v___x_3917_, 0, v___x_3902_);
v___x_3955_ = v___x_3917_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3902_);
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
else
{
lean_object* v_a_3960_; lean_object* v___x_3962_; uint8_t v_isShared_3963_; uint8_t v_isSharedCheck_3967_; 
lean_del_object(v___x_3907_);
v_a_3960_ = lean_ctor_get(v___x_3914_, 0);
v_isSharedCheck_3967_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3967_ == 0)
{
v___x_3962_ = v___x_3914_;
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
else
{
lean_inc(v_a_3960_);
lean_dec(v___x_3914_);
v___x_3962_ = lean_box(0);
v_isShared_3963_ = v_isSharedCheck_3967_;
goto v_resetjp_3961_;
}
v_resetjp_3961_:
{
lean_object* v___x_3965_; 
if (v_isShared_3963_ == 0)
{
v___x_3965_ = v___x_3962_;
goto v_reusejp_3964_;
}
else
{
lean_object* v_reuseFailAlloc_3966_; 
v_reuseFailAlloc_3966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3966_, 0, v_a_3960_);
v___x_3965_ = v_reuseFailAlloc_3966_;
goto v_reusejp_3964_;
}
v_reusejp_3964_:
{
return v___x_3965_;
}
}
}
}
else
{
lean_object* v_a_3968_; lean_object* v___x_3970_; uint8_t v_isShared_3971_; uint8_t v_isSharedCheck_3975_; 
lean_del_object(v___x_3907_);
v_a_3968_ = lean_ctor_get(v___x_3910_, 0);
v_isSharedCheck_3975_ = !lean_is_exclusive(v___x_3910_);
if (v_isSharedCheck_3975_ == 0)
{
v___x_3970_ = v___x_3910_;
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
else
{
lean_inc(v_a_3968_);
lean_dec(v___x_3910_);
v___x_3970_ = lean_box(0);
v_isShared_3971_ = v_isSharedCheck_3975_;
goto v_resetjp_3969_;
}
v_resetjp_3969_:
{
lean_object* v___x_3973_; 
if (v_isShared_3971_ == 0)
{
v___x_3973_ = v___x_3970_;
goto v_reusejp_3972_;
}
else
{
lean_object* v_reuseFailAlloc_3974_; 
v_reuseFailAlloc_3974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3974_, 0, v_a_3968_);
v___x_3973_ = v_reuseFailAlloc_3974_;
goto v_reusejp_3972_;
}
v_reusejp_3972_:
{
return v___x_3973_;
}
}
}
}
}
else
{
lean_dec(v___x_3900_);
return v___x_3905_;
}
}
else
{
lean_dec(v___x_3900_);
return v___x_3901_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v___x_3978_, lean_object* v_args_3979_, lean_object* v_ty_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
lean_object* v_res_3986_; 
v_res_3986_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v___x_3978_, v_args_3979_, v_ty_3980_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec_ref(v_args_3979_);
lean_dec_ref(v___x_3978_);
return v_res_3986_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object* v_e_3987_){
_start:
{
lean_object* v___x_3988_; 
v___x_3988_ = l_Lean_Expr_cleanupAnnotations(v_e_3987_);
lean_dec_ref(v_e_3987_);
switch(lean_obj_tag(v___x_3988_))
{
case 7:
{
lean_object* v_body_3989_; uint8_t v_binderInfo_3990_; uint8_t v___x_3991_; 
v_body_3989_ = lean_ctor_get(v___x_3988_, 2);
lean_inc_ref(v_body_3989_);
v_binderInfo_3990_ = lean_ctor_get_uint8(v___x_3988_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3988_, 3);
v___x_3991_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3990_);
if (v___x_3991_ == 0)
{
lean_object* v___x_3992_; uint8_t v___x_3993_; 
v___x_3992_ = lean_unsigned_to_nat(0u);
v___x_3993_ = lean_expr_has_loose_bvar(v_body_3989_, v___x_3992_);
if (v___x_3993_ == 0)
{
uint8_t v___x_3994_; 
lean_dec_ref(v_body_3989_);
v___x_3994_ = 1;
return v___x_3994_;
}
else
{
v_e_3987_ = v_body_3989_;
goto _start;
}
}
else
{
v_e_3987_ = v_body_3989_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3997_; 
v_body_3997_ = lean_ctor_get(v___x_3988_, 3);
lean_inc_ref(v_body_3997_);
lean_dec_ref_known(v___x_3988_, 4);
v_e_3987_ = v_body_3997_;
goto _start;
}
default: 
{
uint8_t v___x_3999_; 
lean_dec_ref(v___x_3988_);
v___x_3999_ = 0;
return v___x_3999_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object* v_e_4000_){
_start:
{
uint8_t v_res_4001_; lean_object* v_r_4002_; 
v_res_4001_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(v_e_4000_);
v_r_4002_ = lean_box(v_res_4001_);
return v_r_4002_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_cinfo_4003_, lean_object* v_a_4004_, lean_object* v_a_4005_, lean_object* v_a_4006_, lean_object* v_a_4007_){
_start:
{
lean_object* v___x_4009_; uint8_t v___x_4010_; 
v___x_4009_ = l_Lean_ConstantInfo_type(v_cinfo_4003_);
lean_inc_ref(v___x_4009_);
v___x_4010_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(v___x_4009_);
if (v___x_4010_ == 0)
{
lean_object* v___x_4011_; lean_object* v___x_4012_; 
lean_dec_ref(v___x_4009_);
v___x_4011_ = lean_box(0);
v___x_4012_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4012_, 0, v___x_4011_);
return v___x_4012_;
}
else
{
lean_object* v___f_4013_; uint8_t v___x_4014_; lean_object* v___x_4015_; 
lean_inc_ref(v___x_4009_);
v___f_4013_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4013_, 0, v___x_4009_);
v___x_4014_ = 0;
v___x_4015_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v___x_4009_, v___f_4013_, v___x_4014_, v_a_4004_, v_a_4005_, v_a_4006_, v_a_4007_);
return v___x_4015_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_cinfo_4016_, lean_object* v_a_4017_, lean_object* v_a_4018_, lean_object* v_a_4019_, lean_object* v_a_4020_, lean_object* v_a_4021_){
_start:
{
lean_object* v_res_4022_; 
v_res_4022_ = l_Lean_Meta_checkImpossibleInstance(v_cinfo_4016_, v_a_4017_, v_a_4018_, v_a_4019_, v_a_4020_);
lean_dec(v_a_4020_);
lean_dec_ref(v_a_4019_);
lean_dec(v_a_4018_);
lean_dec_ref(v_a_4017_);
lean_dec_ref(v_cinfo_4016_);
return v_res_4022_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object* v_as_4023_, size_t v_sz_4024_, size_t v_i_4025_, lean_object* v_b_4026_, lean_object* v___y_4027_, lean_object* v___y_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_){
_start:
{
lean_object* v___x_4033_; 
v___x_4033_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_as_4023_, v_sz_4024_, v_i_4025_, v_b_4026_, v___y_4027_, v___y_4028_, v___y_4030_, v___y_4031_);
return v___x_4033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_as_4034_, lean_object* v_sz_4035_, lean_object* v_i_4036_, lean_object* v_b_4037_, lean_object* v___y_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
size_t v_sz_boxed_4044_; size_t v_i_boxed_4045_; lean_object* v_res_4046_; 
v_sz_boxed_4044_ = lean_unbox_usize(v_sz_4035_);
lean_dec(v_sz_4035_);
v_i_boxed_4045_ = lean_unbox_usize(v_i_4036_);
lean_dec(v_i_4036_);
v_res_4046_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_as_4034_, v_sz_boxed_4044_, v_i_boxed_4045_, v_b_4037_, v___y_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v___y_4038_);
lean_dec_ref(v_as_4034_);
return v_res_4046_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v_00_u03b2_4047_, lean_object* v_k_4048_, lean_object* v_t_4049_){
_start:
{
uint8_t v___x_4050_; 
v___x_4050_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_4048_, v_t_4049_);
return v___x_4050_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v_00_u03b2_4051_, lean_object* v_k_4052_, lean_object* v_t_4053_){
_start:
{
uint8_t v_res_4054_; lean_object* v_r_4055_; 
v_res_4054_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(v_00_u03b2_4051_, v_k_4052_, v_t_4053_);
lean_dec(v_t_4053_);
lean_dec(v_k_4052_);
v_r_4055_ = lean_box(v_res_4054_);
return v_r_4055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_a_4056_, lean_object* v_as_4057_, size_t v_sz_4058_, size_t v_i_4059_, lean_object* v_b_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_, lean_object* v___y_4063_, lean_object* v___y_4064_){
_start:
{
lean_object* v___x_4066_; 
v___x_4066_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_4056_, v_as_4057_, v_sz_4058_, v_i_4059_, v_b_4060_, v___y_4061_, v___y_4063_, v___y_4064_);
return v___x_4066_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_a_4067_, lean_object* v_as_4068_, lean_object* v_sz_4069_, lean_object* v_i_4070_, lean_object* v_b_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_, lean_object* v___y_4075_, lean_object* v___y_4076_){
_start:
{
size_t v_sz_boxed_4077_; size_t v_i_boxed_4078_; lean_object* v_res_4079_; 
v_sz_boxed_4077_ = lean_unbox_usize(v_sz_4069_);
lean_dec(v_sz_4069_);
v_i_boxed_4078_ = lean_unbox_usize(v_i_4070_);
lean_dec(v_i_4070_);
v_res_4079_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_a_4067_, v_as_4068_, v_sz_boxed_4077_, v_i_boxed_4078_, v_b_4071_, v___y_4072_, v___y_4073_, v___y_4074_, v___y_4075_);
lean_dec(v___y_4075_);
lean_dec_ref(v___y_4074_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec_ref(v_as_4068_);
lean_dec_ref(v_a_4067_);
return v_res_4079_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_4082_ = l_Lean_stringToMessageData(v___x_4081_);
return v___x_4082_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_4085_ = l_Lean_stringToMessageData(v___x_4084_);
return v___x_4085_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_4087_; lean_object* v___x_4088_; 
v___x_4087_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_4088_ = l_Lean_stringToMessageData(v___x_4087_);
return v___x_4088_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_c_4089_, lean_object* v_x_4090_, lean_object* v_target_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
lean_object* v___x_4097_; 
lean_inc_ref(v_target_4091_);
v___x_4097_ = l_Lean_Meta_isClass_x3f(v_target_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
if (lean_obj_tag(v___x_4097_) == 0)
{
lean_object* v_a_4098_; lean_object* v___x_4100_; uint8_t v_isShared_4101_; uint8_t v_isSharedCheck_4116_; 
v_a_4098_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4116_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4116_ == 0)
{
v___x_4100_ = v___x_4097_;
v_isShared_4101_ = v_isSharedCheck_4116_;
goto v_resetjp_4099_;
}
else
{
lean_inc(v_a_4098_);
lean_dec(v___x_4097_);
v___x_4100_ = lean_box(0);
v_isShared_4101_ = v_isSharedCheck_4116_;
goto v_resetjp_4099_;
}
v_resetjp_4099_:
{
if (lean_obj_tag(v_a_4098_) == 0)
{
lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_del_object(v___x_4100_);
v___x_4102_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_4103_ = l_Lean_MessageData_ofExpr(v_c_4089_);
v___x_4104_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4104_, 0, v___x_4102_);
lean_ctor_set(v___x_4104_, 1, v___x_4103_);
v___x_4105_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_4106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4104_);
lean_ctor_set(v___x_4106_, 1, v___x_4105_);
v___x_4107_ = l_Lean_MessageData_ofExpr(v_target_4091_);
v___x_4108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4106_);
lean_ctor_set(v___x_4108_, 1, v___x_4107_);
v___x_4109_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_4110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4108_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_4110_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
return v___x_4111_;
}
else
{
lean_object* v___x_4112_; lean_object* v___x_4114_; 
lean_dec_ref_known(v_a_4098_, 1);
lean_dec_ref(v_target_4091_);
lean_dec_ref(v_c_4089_);
v___x_4112_ = lean_box(0);
if (v_isShared_4101_ == 0)
{
lean_ctor_set(v___x_4100_, 0, v___x_4112_);
v___x_4114_ = v___x_4100_;
goto v_reusejp_4113_;
}
else
{
lean_object* v_reuseFailAlloc_4115_; 
v_reuseFailAlloc_4115_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4115_, 0, v___x_4112_);
v___x_4114_ = v_reuseFailAlloc_4115_;
goto v_reusejp_4113_;
}
v_reusejp_4113_:
{
return v___x_4114_;
}
}
}
}
else
{
lean_object* v_a_4117_; lean_object* v___x_4119_; uint8_t v_isShared_4120_; uint8_t v_isSharedCheck_4124_; 
lean_dec_ref(v_target_4091_);
lean_dec_ref(v_c_4089_);
v_a_4117_ = lean_ctor_get(v___x_4097_, 0);
v_isSharedCheck_4124_ = !lean_is_exclusive(v___x_4097_);
if (v_isSharedCheck_4124_ == 0)
{
v___x_4119_ = v___x_4097_;
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
else
{
lean_inc(v_a_4117_);
lean_dec(v___x_4097_);
v___x_4119_ = lean_box(0);
v_isShared_4120_ = v_isSharedCheck_4124_;
goto v_resetjp_4118_;
}
v_resetjp_4118_:
{
lean_object* v___x_4122_; 
if (v_isShared_4120_ == 0)
{
v___x_4122_ = v___x_4119_;
goto v_reusejp_4121_;
}
else
{
lean_object* v_reuseFailAlloc_4123_; 
v_reuseFailAlloc_4123_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4123_, 0, v_a_4117_);
v___x_4122_ = v_reuseFailAlloc_4123_;
goto v_reusejp_4121_;
}
v_reusejp_4121_:
{
return v___x_4122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_c_4125_, lean_object* v_x_4126_, lean_object* v_target_4127_, lean_object* v___y_4128_, lean_object* v___y_4129_, lean_object* v___y_4130_, lean_object* v___y_4131_, lean_object* v___y_4132_){
_start:
{
lean_object* v_res_4133_; 
v_res_4133_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_c_4125_, v_x_4126_, v_target_4127_, v___y_4128_, v___y_4129_, v___y_4130_, v___y_4131_);
lean_dec(v___y_4131_);
lean_dec_ref(v___y_4130_);
lean_dec(v___y_4129_);
lean_dec_ref(v___y_4128_);
lean_dec_ref(v_x_4126_);
return v_res_4133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_c_4134_, lean_object* v_a_4135_, lean_object* v_a_4136_, lean_object* v_a_4137_, lean_object* v_a_4138_){
_start:
{
lean_object* v___f_4140_; lean_object* v___x_4141_; 
lean_inc_ref(v_c_4134_);
v___f_4140_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_4140_, 0, v_c_4134_);
lean_inc(v_a_4138_);
lean_inc_ref(v_a_4137_);
lean_inc(v_a_4136_);
lean_inc_ref(v_a_4135_);
v___x_4141_ = lean_infer_type(v_c_4134_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
if (lean_obj_tag(v___x_4141_) == 0)
{
lean_object* v_a_4142_; uint8_t v___x_4143_; lean_object* v___x_4144_; 
v_a_4142_ = lean_ctor_get(v___x_4141_, 0);
lean_inc(v_a_4142_);
lean_dec_ref_known(v___x_4141_, 1);
v___x_4143_ = 0;
v___x_4144_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_4142_, v___f_4140_, v___x_4143_, v___x_4143_, v_a_4135_, v_a_4136_, v_a_4137_, v_a_4138_);
return v___x_4144_;
}
else
{
lean_object* v_a_4145_; lean_object* v___x_4147_; uint8_t v_isShared_4148_; uint8_t v_isSharedCheck_4152_; 
lean_dec_ref(v___f_4140_);
v_a_4145_ = lean_ctor_get(v___x_4141_, 0);
v_isSharedCheck_4152_ = !lean_is_exclusive(v___x_4141_);
if (v_isSharedCheck_4152_ == 0)
{
v___x_4147_ = v___x_4141_;
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
else
{
lean_inc(v_a_4145_);
lean_dec(v___x_4141_);
v___x_4147_ = lean_box(0);
v_isShared_4148_ = v_isSharedCheck_4152_;
goto v_resetjp_4146_;
}
v_resetjp_4146_:
{
lean_object* v___x_4150_; 
if (v_isShared_4148_ == 0)
{
v___x_4150_ = v___x_4147_;
goto v_reusejp_4149_;
}
else
{
lean_object* v_reuseFailAlloc_4151_; 
v_reuseFailAlloc_4151_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4151_, 0, v_a_4145_);
v___x_4150_ = v_reuseFailAlloc_4151_;
goto v_reusejp_4149_;
}
v_reusejp_4149_:
{
return v___x_4150_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_c_4153_, lean_object* v_a_4154_, lean_object* v_a_4155_, lean_object* v_a_4156_, lean_object* v_a_4157_, lean_object* v_a_4158_){
_start:
{
lean_object* v_res_4159_; 
v_res_4159_ = l_Lean_Meta_checkNonClassInstance(v_c_4153_, v_a_4154_, v_a_4155_, v_a_4156_, v_a_4157_);
lean_dec(v_a_4157_);
lean_dec_ref(v_a_4156_);
lean_dec(v_a_4155_);
lean_dec_ref(v_a_4154_);
return v_res_4159_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_declName_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v___x_4173_; lean_object* v_env_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; 
v___x_4173_ = lean_st_ref_get(v___y_4171_);
v_env_4174_ = lean_ctor_get(v___x_4173_, 0);
lean_inc_ref(v_env_4174_);
lean_dec(v___x_4173_);
v___x_4175_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_4174_, v_declName_4170_);
v___x_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4176_, 0, v___x_4175_);
return v___x_4176_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_declName_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__2___redArg(v_declName_4177_, v___y_4178_);
lean_dec(v___y_4178_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__2(lean_object* v_declName_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; 
v___x_4187_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__2___redArg(v_declName_4181_, v___y_4185_);
return v___x_4187_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_declName_4188_, lean_object* v___y_4189_, lean_object* v___y_4190_, lean_object* v___y_4191_, lean_object* v___y_4192_, lean_object* v___y_4193_){
_start:
{
lean_object* v_res_4194_; 
v_res_4194_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__2(v_declName_4188_, v___y_4189_, v___y_4190_, v___y_4191_, v___y_4192_);
lean_dec(v___y_4192_);
lean_dec_ref(v___y_4191_);
lean_dec(v___y_4190_);
lean_dec_ref(v___y_4189_);
return v_res_4194_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__4___redArg(lean_object* v_declName_4195_, lean_object* v___y_4196_){
_start:
{
lean_object* v___x_4198_; lean_object* v_env_4199_; uint8_t v___x_4200_; lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4198_ = lean_st_ref_get(v___y_4196_);
v_env_4199_ = lean_ctor_get(v___x_4198_, 0);
lean_inc_ref(v_env_4199_);
lean_dec(v___x_4198_);
v___x_4200_ = l_Lean_getReducibilityStatusCore(v_env_4199_, v_declName_4195_);
v___x_4201_ = lean_box(v___x_4200_);
v___x_4202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4202_, 0, v___x_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__4___redArg___boxed(lean_object* v_declName_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_){
_start:
{
lean_object* v_res_4206_; 
v_res_4206_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__4___redArg(v_declName_4203_, v___y_4204_);
lean_dec(v___y_4204_);
return v_res_4206_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__4(lean_object* v_declName_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_, lean_object* v___y_4211_){
_start:
{
lean_object* v___x_4213_; 
v___x_4213_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__4___redArg(v_declName_4207_, v___y_4211_);
return v___x_4213_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_declName_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_, lean_object* v___y_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_){
_start:
{
lean_object* v_res_4220_; 
v_res_4220_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__4(v_declName_4214_, v___y_4215_, v___y_4216_, v___y_4217_, v___y_4218_);
lean_dec(v___y_4218_);
lean_dec_ref(v___y_4217_);
lean_dec(v___y_4216_);
lean_dec_ref(v___y_4215_);
return v_res_4220_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__0(void){
_start:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; 
v___x_4221_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4221_);
return v___x_4222_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__1(void){
_start:
{
lean_object* v___x_4223_; lean_object* v___x_4224_; lean_object* v___x_4225_; 
v___x_4223_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__0);
v___x_4224_ = lean_unsigned_to_nat(0u);
v___x_4225_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4225_, 0, v___x_4224_);
lean_ctor_set(v___x_4225_, 1, v___x_4224_);
lean_ctor_set(v___x_4225_, 2, v___x_4224_);
lean_ctor_set(v___x_4225_, 3, v___x_4224_);
lean_ctor_set(v___x_4225_, 4, v___x_4223_);
lean_ctor_set(v___x_4225_, 5, v___x_4223_);
lean_ctor_set(v___x_4225_, 6, v___x_4223_);
lean_ctor_set(v___x_4225_, 7, v___x_4223_);
lean_ctor_set(v___x_4225_, 8, v___x_4223_);
lean_ctor_set(v___x_4225_, 9, v___x_4223_);
lean_ctor_set(v___x_4225_, 10, v___x_4223_);
return v___x_4225_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__2(void){
_start:
{
lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; 
v___x_4226_ = lean_unsigned_to_nat(32u);
v___x_4227_ = lean_mk_empty_array_with_capacity(v___x_4226_);
v___x_4228_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4227_);
return v___x_4228_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__3(void){
_start:
{
size_t v___x_4229_; lean_object* v___x_4230_; lean_object* v___x_4231_; lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; 
v___x_4229_ = ((size_t)5ULL);
v___x_4230_ = lean_unsigned_to_nat(0u);
v___x_4231_ = lean_unsigned_to_nat(32u);
v___x_4232_ = lean_mk_empty_array_with_capacity(v___x_4231_);
v___x_4233_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__2);
v___x_4234_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4234_, 0, v___x_4233_);
lean_ctor_set(v___x_4234_, 1, v___x_4232_);
lean_ctor_set(v___x_4234_, 2, v___x_4230_);
lean_ctor_set(v___x_4234_, 3, v___x_4230_);
lean_ctor_set_usize(v___x_4234_, 4, v___x_4229_);
return v___x_4234_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__4(void){
_start:
{
lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
v___x_4235_ = lean_box(1);
v___x_4236_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__3);
v___x_4237_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__0);
v___x_4238_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
lean_ctor_set(v___x_4238_, 1, v___x_4236_);
lean_ctor_set(v___x_4238_, 2, v___x_4235_);
return v___x_4238_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__6(void){
_start:
{
lean_object* v___x_4240_; lean_object* v___x_4241_; 
v___x_4240_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__5));
v___x_4241_ = l_Lean_stringToMessageData(v___x_4240_);
return v___x_4241_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__8(void){
_start:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; 
v___x_4243_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__7));
v___x_4244_ = l_Lean_stringToMessageData(v___x_4243_);
return v___x_4244_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__10(void){
_start:
{
lean_object* v___x_4246_; lean_object* v___x_4247_; 
v___x_4246_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__9));
v___x_4247_ = l_Lean_stringToMessageData(v___x_4246_);
return v___x_4247_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__12(void){
_start:
{
lean_object* v___x_4249_; lean_object* v___x_4250_; 
v___x_4249_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__11));
v___x_4250_ = l_Lean_stringToMessageData(v___x_4249_);
return v___x_4250_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__14(void){
_start:
{
lean_object* v___x_4252_; lean_object* v___x_4253_; 
v___x_4252_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__13));
v___x_4253_ = l_Lean_stringToMessageData(v___x_4252_);
return v___x_4253_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__16(void){
_start:
{
lean_object* v___x_4255_; lean_object* v___x_4256_; 
v___x_4255_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__15));
v___x_4256_ = l_Lean_stringToMessageData(v___x_4255_);
return v___x_4256_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__18(void){
_start:
{
lean_object* v___x_4258_; lean_object* v___x_4259_; 
v___x_4258_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__17));
v___x_4259_ = l_Lean_stringToMessageData(v___x_4258_);
return v___x_4259_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg(lean_object* v_msg_4260_, lean_object* v_declHint_4261_, lean_object* v___y_4262_){
_start:
{
lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v_env_4266_; uint8_t v___x_4267_; 
v___x_4264_ = lean_box(0);
v___x_4265_ = lean_st_ref_get(v___y_4262_);
v_env_4266_ = lean_ctor_get(v___x_4265_, 0);
lean_inc_ref(v_env_4266_);
lean_dec(v___x_4265_);
v___x_4267_ = l_Lean_Name_isAnonymous(v_declHint_4261_);
if (v___x_4267_ == 0)
{
uint8_t v_isExporting_4268_; 
v_isExporting_4268_ = lean_ctor_get_uint8(v_env_4266_, sizeof(void*)*13);
if (v_isExporting_4268_ == 0)
{
lean_object* v___x_4269_; 
lean_dec_ref(v_env_4266_);
lean_dec(v_declHint_4261_);
v___x_4269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4269_, 0, v_msg_4260_);
return v___x_4269_;
}
else
{
lean_object* v___x_4270_; uint8_t v___x_4271_; 
lean_inc_ref(v_env_4266_);
v___x_4270_ = l_Lean_Environment_setExporting(v_env_4266_, v___x_4267_);
lean_inc(v_declHint_4261_);
lean_inc_ref(v___x_4270_);
v___x_4271_ = l_Lean_Environment_contains(v___x_4270_, v_declHint_4261_, v_isExporting_4268_);
if (v___x_4271_ == 0)
{
lean_object* v___x_4272_; 
lean_dec_ref(v___x_4270_);
lean_dec_ref(v_env_4266_);
lean_dec(v_declHint_4261_);
v___x_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4272_, 0, v_msg_4260_);
return v___x_4272_;
}
else
{
lean_object* v___x_4273_; lean_object* v___x_4274_; lean_object* v___x_4275_; lean_object* v___x_4276_; lean_object* v___x_4277_; lean_object* v_c_4278_; lean_object* v___x_4279_; 
v___x_4273_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__1);
v___x_4274_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__4);
v___x_4275_ = l_Lean_Options_empty;
lean_inc_ref(v___x_4270_);
v___x_4276_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4276_, 0, v___x_4270_);
lean_ctor_set(v___x_4276_, 1, v___x_4273_);
lean_ctor_set(v___x_4276_, 2, v___x_4274_);
lean_ctor_set(v___x_4276_, 3, v___x_4275_);
lean_inc(v_declHint_4261_);
v___x_4277_ = l_Lean_MessageData_ofConstName(v_declHint_4261_, v___x_4267_);
v_c_4278_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4278_, 0, v___x_4276_);
lean_ctor_set(v_c_4278_, 1, v___x_4277_);
v___x_4279_ = l_Lean_Environment_getModuleIdxFor_x3f(v___x_4270_, v_declHint_4261_);
lean_dec_ref(v___x_4270_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v___x_4280_; lean_object* v___x_4281_; lean_object* v___x_4282_; lean_object* v___x_4283_; lean_object* v___x_4284_; lean_object* v___x_4285_; lean_object* v___x_4286_; 
lean_dec_ref(v_env_4266_);
lean_dec(v_declHint_4261_);
v___x_4280_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__6);
v___x_4281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4281_, 0, v___x_4280_);
lean_ctor_set(v___x_4281_, 1, v_c_4278_);
v___x_4282_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__8);
v___x_4283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4283_, 0, v___x_4281_);
lean_ctor_set(v___x_4283_, 1, v___x_4282_);
v___x_4284_ = l_Lean_MessageData_note(v___x_4283_);
v___x_4285_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4285_, 0, v_msg_4260_);
lean_ctor_set(v___x_4285_, 1, v___x_4284_);
v___x_4286_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4286_, 0, v___x_4285_);
return v___x_4286_;
}
else
{
lean_object* v_val_4287_; lean_object* v___x_4289_; uint8_t v_isShared_4290_; uint8_t v_isSharedCheck_4321_; 
v_val_4287_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4321_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4321_ == 0)
{
v___x_4289_ = v___x_4279_;
v_isShared_4290_ = v_isSharedCheck_4321_;
goto v_resetjp_4288_;
}
else
{
lean_inc(v_val_4287_);
lean_dec(v___x_4279_);
v___x_4289_ = lean_box(0);
v_isShared_4290_ = v_isSharedCheck_4321_;
goto v_resetjp_4288_;
}
v_resetjp_4288_:
{
lean_object* v___x_4291_; lean_object* v_moduleNames_4292_; lean_object* v_mod_4293_; uint8_t v___x_4294_; 
v___x_4291_ = l_Lean_Environment_header(v_env_4266_);
lean_dec_ref(v_env_4266_);
v_moduleNames_4292_ = lean_ctor_get(v___x_4291_, 4);
lean_inc_ref(v_moduleNames_4292_);
lean_dec_ref(v___x_4291_);
v_mod_4293_ = lean_array_get(v___x_4264_, v_moduleNames_4292_, v_val_4287_);
lean_dec(v_val_4287_);
lean_dec_ref(v_moduleNames_4292_);
v___x_4294_ = l_Lean_isPrivateName(v_declHint_4261_);
lean_dec(v_declHint_4261_);
if (v___x_4294_ == 0)
{
lean_object* v___x_4295_; lean_object* v___x_4296_; lean_object* v___x_4297_; lean_object* v___x_4298_; lean_object* v___x_4299_; lean_object* v___x_4300_; lean_object* v___x_4301_; lean_object* v___x_4302_; lean_object* v___x_4303_; lean_object* v___x_4304_; lean_object* v___x_4306_; 
v___x_4295_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__10);
v___x_4296_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4296_, 0, v___x_4295_);
lean_ctor_set(v___x_4296_, 1, v_c_4278_);
v___x_4297_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__12);
v___x_4298_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4298_, 0, v___x_4296_);
lean_ctor_set(v___x_4298_, 1, v___x_4297_);
v___x_4299_ = l_Lean_MessageData_ofName(v_mod_4293_);
v___x_4300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4300_, 0, v___x_4298_);
lean_ctor_set(v___x_4300_, 1, v___x_4299_);
v___x_4301_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__14);
v___x_4302_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4302_, 0, v___x_4300_);
lean_ctor_set(v___x_4302_, 1, v___x_4301_);
v___x_4303_ = l_Lean_MessageData_note(v___x_4302_);
v___x_4304_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4304_, 0, v_msg_4260_);
lean_ctor_set(v___x_4304_, 1, v___x_4303_);
if (v_isShared_4290_ == 0)
{
lean_ctor_set_tag(v___x_4289_, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4304_);
v___x_4306_ = v___x_4289_;
goto v_reusejp_4305_;
}
else
{
lean_object* v_reuseFailAlloc_4307_; 
v_reuseFailAlloc_4307_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4307_, 0, v___x_4304_);
v___x_4306_ = v_reuseFailAlloc_4307_;
goto v_reusejp_4305_;
}
v_reusejp_4305_:
{
return v___x_4306_;
}
}
else
{
lean_object* v___x_4308_; lean_object* v___x_4309_; lean_object* v___x_4310_; lean_object* v___x_4311_; lean_object* v___x_4312_; lean_object* v___x_4313_; lean_object* v___x_4314_; lean_object* v___x_4315_; lean_object* v___x_4316_; lean_object* v___x_4317_; lean_object* v___x_4319_; 
v___x_4308_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__6);
v___x_4309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4309_, 0, v___x_4308_);
lean_ctor_set(v___x_4309_, 1, v_c_4278_);
v___x_4310_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__16);
v___x_4311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4311_, 0, v___x_4309_);
lean_ctor_set(v___x_4311_, 1, v___x_4310_);
v___x_4312_ = l_Lean_MessageData_ofName(v_mod_4293_);
v___x_4313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4313_, 0, v___x_4311_);
lean_ctor_set(v___x_4313_, 1, v___x_4312_);
v___x_4314_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__18);
v___x_4315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4315_, 0, v___x_4313_);
lean_ctor_set(v___x_4315_, 1, v___x_4314_);
v___x_4316_ = l_Lean_MessageData_note(v___x_4315_);
v___x_4317_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4317_, 0, v_msg_4260_);
lean_ctor_set(v___x_4317_, 1, v___x_4316_);
if (v_isShared_4290_ == 0)
{
lean_ctor_set_tag(v___x_4289_, 0);
lean_ctor_set(v___x_4289_, 0, v___x_4317_);
v___x_4319_ = v___x_4289_;
goto v_reusejp_4318_;
}
else
{
lean_object* v_reuseFailAlloc_4320_; 
v_reuseFailAlloc_4320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4320_, 0, v___x_4317_);
v___x_4319_ = v_reuseFailAlloc_4320_;
goto v_reusejp_4318_;
}
v_reusejp_4318_:
{
return v___x_4319_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4322_; 
lean_dec_ref(v_env_4266_);
lean_dec(v_declHint_4261_);
v___x_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4322_, 0, v_msg_4260_);
return v___x_4322_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___boxed(lean_object* v_msg_4323_, lean_object* v_declHint_4324_, lean_object* v___y_4325_, lean_object* v___y_4326_){
_start:
{
lean_object* v_res_4327_; 
v_res_4327_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg(v_msg_4323_, v_declHint_4324_, v___y_4325_);
lean_dec(v___y_4325_);
return v_res_4327_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11(lean_object* v_msg_4328_, lean_object* v_declHint_4329_, lean_object* v___y_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_){
_start:
{
lean_object* v___x_4335_; lean_object* v_a_4336_; lean_object* v___x_4338_; uint8_t v_isShared_4339_; uint8_t v_isSharedCheck_4345_; 
v___x_4335_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg(v_msg_4328_, v_declHint_4329_, v___y_4333_);
v_a_4336_ = lean_ctor_get(v___x_4335_, 0);
v_isSharedCheck_4345_ = !lean_is_exclusive(v___x_4335_);
if (v_isSharedCheck_4345_ == 0)
{
v___x_4338_ = v___x_4335_;
v_isShared_4339_ = v_isSharedCheck_4345_;
goto v_resetjp_4337_;
}
else
{
lean_inc(v_a_4336_);
lean_dec(v___x_4335_);
v___x_4338_ = lean_box(0);
v_isShared_4339_ = v_isSharedCheck_4345_;
goto v_resetjp_4337_;
}
v_resetjp_4337_:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4343_; 
v___x_4340_ = l_Lean_unknownIdentifierMessageTag;
v___x_4341_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4340_);
lean_ctor_set(v___x_4341_, 1, v_a_4336_);
if (v_isShared_4339_ == 0)
{
lean_ctor_set(v___x_4338_, 0, v___x_4341_);
v___x_4343_ = v___x_4338_;
goto v_reusejp_4342_;
}
else
{
lean_object* v_reuseFailAlloc_4344_; 
v_reuseFailAlloc_4344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4344_, 0, v___x_4341_);
v___x_4343_ = v_reuseFailAlloc_4344_;
goto v_reusejp_4342_;
}
v_reusejp_4342_:
{
return v___x_4343_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11___boxed(lean_object* v_msg_4346_, lean_object* v_declHint_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_, lean_object* v___y_4350_, lean_object* v___y_4351_, lean_object* v___y_4352_){
_start:
{
lean_object* v_res_4353_; 
v_res_4353_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11(v_msg_4346_, v_declHint_4347_, v___y_4348_, v___y_4349_, v___y_4350_, v___y_4351_);
lean_dec(v___y_4351_);
lean_dec_ref(v___y_4350_);
lean_dec(v___y_4349_);
lean_dec_ref(v___y_4348_);
return v_res_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__12___redArg(lean_object* v_ref_4354_, lean_object* v_msg_4355_, lean_object* v___y_4356_, lean_object* v___y_4357_, lean_object* v___y_4358_, lean_object* v___y_4359_){
_start:
{
lean_object* v_toCold_4361_; lean_object* v_currRecDepth_4362_; lean_object* v_ref_4363_; uint16_t v_optionFlags_4364_; uint8_t v_suppressElabErrors_4365_; uint8_t v_checkDeprecated_4366_; uint8_t v_isRecordingDeps_4367_; lean_object* v_ref_4368_; lean_object* v___x_4369_; lean_object* v___x_4370_; 
v_toCold_4361_ = lean_ctor_get(v___y_4358_, 0);
v_currRecDepth_4362_ = lean_ctor_get(v___y_4358_, 1);
v_ref_4363_ = lean_ctor_get(v___y_4358_, 2);
v_optionFlags_4364_ = lean_ctor_get_uint16(v___y_4358_, sizeof(void*)*3);
v_suppressElabErrors_4365_ = lean_ctor_get_uint8(v___y_4358_, sizeof(void*)*3 + 2);
v_checkDeprecated_4366_ = lean_ctor_get_uint8(v___y_4358_, sizeof(void*)*3 + 3);
v_isRecordingDeps_4367_ = lean_ctor_get_uint8(v___y_4358_, sizeof(void*)*3 + 4);
v_ref_4368_ = l_Lean_replaceRef(v_ref_4354_, v_ref_4363_);
lean_inc(v_currRecDepth_4362_);
lean_inc_ref(v_toCold_4361_);
v___x_4369_ = lean_alloc_ctor(0, 3, 5);
lean_ctor_set(v___x_4369_, 0, v_toCold_4361_);
lean_ctor_set(v___x_4369_, 1, v_currRecDepth_4362_);
lean_ctor_set(v___x_4369_, 2, v_ref_4368_);
lean_ctor_set_uint16(v___x_4369_, sizeof(void*)*3, v_optionFlags_4364_);
lean_ctor_set_uint8(v___x_4369_, sizeof(void*)*3 + 2, v_suppressElabErrors_4365_);
lean_ctor_set_uint8(v___x_4369_, sizeof(void*)*3 + 3, v_checkDeprecated_4366_);
lean_ctor_set_uint8(v___x_4369_, sizeof(void*)*3 + 4, v_isRecordingDeps_4367_);
v___x_4370_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_4355_, v___y_4356_, v___y_4357_, v___x_4369_, v___y_4359_);
lean_dec_ref_known(v___x_4369_, 3);
return v___x_4370_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__12___redArg___boxed(lean_object* v_ref_4371_, lean_object* v_msg_4372_, lean_object* v___y_4373_, lean_object* v___y_4374_, lean_object* v___y_4375_, lean_object* v___y_4376_, lean_object* v___y_4377_){
_start:
{
lean_object* v_res_4378_; 
v_res_4378_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__12___redArg(v_ref_4371_, v_msg_4372_, v___y_4373_, v___y_4374_, v___y_4375_, v___y_4376_);
lean_dec(v___y_4376_);
lean_dec_ref(v___y_4375_);
lean_dec(v___y_4374_);
lean_dec_ref(v___y_4373_);
lean_dec(v_ref_4371_);
return v_res_4378_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8___redArg(lean_object* v_ref_4379_, lean_object* v_msg_4380_, lean_object* v_declHint_4381_, lean_object* v___y_4382_, lean_object* v___y_4383_, lean_object* v___y_4384_, lean_object* v___y_4385_){
_start:
{
lean_object* v___x_4387_; lean_object* v_a_4388_; lean_object* v___x_4389_; 
v___x_4387_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11(v_msg_4380_, v_declHint_4381_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
v_a_4388_ = lean_ctor_get(v___x_4387_, 0);
lean_inc(v_a_4388_);
lean_dec_ref(v___x_4387_);
v___x_4389_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__12___redArg(v_ref_4379_, v_a_4388_, v___y_4382_, v___y_4383_, v___y_4384_, v___y_4385_);
return v___x_4389_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8___redArg___boxed(lean_object* v_ref_4390_, lean_object* v_msg_4391_, lean_object* v_declHint_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_, lean_object* v___y_4397_){
_start:
{
lean_object* v_res_4398_; 
v_res_4398_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8___redArg(v_ref_4390_, v_msg_4391_, v_declHint_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
lean_dec(v___y_4396_);
lean_dec_ref(v___y_4395_);
lean_dec(v___y_4394_);
lean_dec_ref(v___y_4393_);
lean_dec(v_ref_4390_);
return v_res_4398_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__1(void){
_start:
{
lean_object* v___x_4400_; lean_object* v___x_4401_; 
v___x_4400_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__0));
v___x_4401_ = l_Lean_stringToMessageData(v___x_4400_);
return v___x_4401_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg(lean_object* v_ref_4402_, lean_object* v_constName_4403_, lean_object* v___y_4404_, lean_object* v___y_4405_, lean_object* v___y_4406_, lean_object* v___y_4407_){
_start:
{
lean_object* v___x_4409_; uint8_t v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4409_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__1);
v___x_4410_ = 0;
lean_inc(v_constName_4403_);
v___x_4411_ = l_Lean_MessageData_ofConstName(v_constName_4403_, v___x_4410_);
v___x_4412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4409_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
v___x_4413_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4412_);
lean_ctor_set(v___x_4414_, 1, v___x_4413_);
v___x_4415_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8___redArg(v_ref_4402_, v___x_4414_, v_constName_4403_, v___y_4404_, v___y_4405_, v___y_4406_, v___y_4407_);
return v___x_4415_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___boxed(lean_object* v_ref_4416_, lean_object* v_constName_4417_, lean_object* v___y_4418_, lean_object* v___y_4419_, lean_object* v___y_4420_, lean_object* v___y_4421_, lean_object* v___y_4422_){
_start:
{
lean_object* v_res_4423_; 
v_res_4423_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg(v_ref_4416_, v_constName_4417_, v___y_4418_, v___y_4419_, v___y_4420_, v___y_4421_);
lean_dec(v___y_4421_);
lean_dec_ref(v___y_4420_);
lean_dec(v___y_4419_);
lean_dec_ref(v___y_4418_);
lean_dec(v_ref_4416_);
return v_res_4423_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3___redArg(lean_object* v_constName_4424_, lean_object* v___y_4425_, lean_object* v___y_4426_, lean_object* v___y_4427_, lean_object* v___y_4428_){
_start:
{
lean_object* v_ref_4430_; lean_object* v___x_4431_; 
v_ref_4430_ = lean_ctor_get(v___y_4427_, 2);
v___x_4431_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg(v_ref_4430_, v_constName_4424_, v___y_4425_, v___y_4426_, v___y_4427_, v___y_4428_);
return v___x_4431_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3___redArg___boxed(lean_object* v_constName_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_, lean_object* v___y_4437_){
_start:
{
lean_object* v_res_4438_; 
v_res_4438_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3___redArg(v_constName_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
lean_dec(v___y_4436_);
lean_dec_ref(v___y_4435_);
lean_dec(v___y_4434_);
lean_dec_ref(v___y_4433_);
return v_res_4438_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4439_, lean_object* v___y_4440_, lean_object* v___y_4441_, lean_object* v___y_4442_, lean_object* v___y_4443_){
_start:
{
lean_object* v___x_4445_; lean_object* v_env_4446_; uint8_t v___x_4447_; lean_object* v___x_4448_; 
v___x_4445_ = lean_st_ref_get(v___y_4443_);
v_env_4446_ = lean_ctor_get(v___x_4445_, 0);
lean_inc_ref(v_env_4446_);
lean_dec(v___x_4445_);
v___x_4447_ = 0;
lean_inc(v_constName_4439_);
v___x_4448_ = l_Lean_Environment_findConstVal_x3f(v_env_4446_, v_constName_4439_, v___x_4447_);
if (lean_obj_tag(v___x_4448_) == 0)
{
lean_object* v___x_4449_; 
v___x_4449_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3___redArg(v_constName_4439_, v___y_4440_, v___y_4441_, v___y_4442_, v___y_4443_);
return v___x_4449_;
}
else
{
lean_object* v_val_4450_; lean_object* v___x_4452_; uint8_t v_isShared_4453_; uint8_t v_isSharedCheck_4457_; 
lean_dec(v_constName_4439_);
v_val_4450_ = lean_ctor_get(v___x_4448_, 0);
v_isSharedCheck_4457_ = !lean_is_exclusive(v___x_4448_);
if (v_isSharedCheck_4457_ == 0)
{
v___x_4452_ = v___x_4448_;
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
else
{
lean_inc(v_val_4450_);
lean_dec(v___x_4448_);
v___x_4452_ = lean_box(0);
v_isShared_4453_ = v_isSharedCheck_4457_;
goto v_resetjp_4451_;
}
v_resetjp_4451_:
{
lean_object* v___x_4455_; 
if (v_isShared_4453_ == 0)
{
lean_ctor_set_tag(v___x_4452_, 0);
v___x_4455_ = v___x_4452_;
goto v_reusejp_4454_;
}
else
{
lean_object* v_reuseFailAlloc_4456_; 
v_reuseFailAlloc_4456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4456_, 0, v_val_4450_);
v___x_4455_ = v_reuseFailAlloc_4456_;
goto v_reusejp_4454_;
}
v_reusejp_4454_:
{
return v___x_4455_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4458_, lean_object* v___y_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_){
_start:
{
lean_object* v_res_4464_; 
v_res_4464_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4458_, v___y_4459_, v___y_4460_, v___y_4461_, v___y_4462_);
lean_dec(v___y_4462_);
lean_dec_ref(v___y_4461_);
lean_dec(v___y_4460_);
lean_dec_ref(v___y_4459_);
return v_res_4464_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4465_, lean_object* v_a_4466_){
_start:
{
if (lean_obj_tag(v_a_4465_) == 0)
{
lean_object* v___x_4467_; 
v___x_4467_ = l_List_reverse___redArg(v_a_4466_);
return v___x_4467_;
}
else
{
lean_object* v_head_4468_; lean_object* v_tail_4469_; lean_object* v___x_4471_; uint8_t v_isShared_4472_; uint8_t v_isSharedCheck_4478_; 
v_head_4468_ = lean_ctor_get(v_a_4465_, 0);
v_tail_4469_ = lean_ctor_get(v_a_4465_, 1);
v_isSharedCheck_4478_ = !lean_is_exclusive(v_a_4465_);
if (v_isSharedCheck_4478_ == 0)
{
v___x_4471_ = v_a_4465_;
v_isShared_4472_ = v_isSharedCheck_4478_;
goto v_resetjp_4470_;
}
else
{
lean_inc(v_tail_4469_);
lean_inc(v_head_4468_);
lean_dec(v_a_4465_);
v___x_4471_ = lean_box(0);
v_isShared_4472_ = v_isSharedCheck_4478_;
goto v_resetjp_4470_;
}
v_resetjp_4470_:
{
lean_object* v___x_4473_; lean_object* v___x_4475_; 
v___x_4473_ = l_Lean_mkLevelParam(v_head_4468_);
if (v_isShared_4472_ == 0)
{
lean_ctor_set(v___x_4471_, 1, v_a_4466_);
lean_ctor_set(v___x_4471_, 0, v___x_4473_);
v___x_4475_ = v___x_4471_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4477_; 
v_reuseFailAlloc_4477_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4477_, 0, v___x_4473_);
lean_ctor_set(v_reuseFailAlloc_4477_, 1, v_a_4466_);
v___x_4475_ = v_reuseFailAlloc_4477_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
v_a_4465_ = v_tail_4469_;
v_a_4466_ = v___x_4475_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_){
_start:
{
lean_object* v___x_4485_; 
lean_inc(v_constName_4479_);
v___x_4485_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
if (lean_obj_tag(v___x_4485_) == 0)
{
lean_object* v_a_4486_; lean_object* v___x_4488_; uint8_t v_isShared_4489_; uint8_t v_isSharedCheck_4497_; 
v_a_4486_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4497_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4497_ == 0)
{
v___x_4488_ = v___x_4485_;
v_isShared_4489_ = v_isSharedCheck_4497_;
goto v_resetjp_4487_;
}
else
{
lean_inc(v_a_4486_);
lean_dec(v___x_4485_);
v___x_4488_ = lean_box(0);
v_isShared_4489_ = v_isSharedCheck_4497_;
goto v_resetjp_4487_;
}
v_resetjp_4487_:
{
lean_object* v_levelParams_4490_; lean_object* v___x_4491_; lean_object* v___x_4492_; lean_object* v___x_4493_; lean_object* v___x_4495_; 
v_levelParams_4490_ = lean_ctor_get(v_a_4486_, 1);
lean_inc(v_levelParams_4490_);
lean_dec(v_a_4486_);
v___x_4491_ = lean_box(0);
v___x_4492_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4490_, v___x_4491_);
v___x_4493_ = l_Lean_mkConst(v_constName_4479_, v___x_4492_);
if (v_isShared_4489_ == 0)
{
lean_ctor_set(v___x_4488_, 0, v___x_4493_);
v___x_4495_ = v___x_4488_;
goto v_reusejp_4494_;
}
else
{
lean_object* v_reuseFailAlloc_4496_; 
v_reuseFailAlloc_4496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4496_, 0, v___x_4493_);
v___x_4495_ = v_reuseFailAlloc_4496_;
goto v_reusejp_4494_;
}
v_reusejp_4494_:
{
return v___x_4495_;
}
}
}
else
{
lean_object* v_a_4498_; lean_object* v___x_4500_; uint8_t v_isShared_4501_; uint8_t v_isSharedCheck_4505_; 
lean_dec(v_constName_4479_);
v_a_4498_ = lean_ctor_get(v___x_4485_, 0);
v_isSharedCheck_4505_ = !lean_is_exclusive(v___x_4485_);
if (v_isSharedCheck_4505_ == 0)
{
v___x_4500_ = v___x_4485_;
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
else
{
lean_inc(v_a_4498_);
lean_dec(v___x_4485_);
v___x_4500_ = lean_box(0);
v_isShared_4501_ = v_isSharedCheck_4505_;
goto v_resetjp_4499_;
}
v_resetjp_4499_:
{
lean_object* v___x_4503_; 
if (v_isShared_4501_ == 0)
{
v___x_4503_ = v___x_4500_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4504_; 
v_reuseFailAlloc_4504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4504_, 0, v_a_4498_);
v___x_4503_ = v_reuseFailAlloc_4504_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
return v___x_4503_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4506_, lean_object* v___y_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v_res_4512_; 
v_res_4512_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4506_, v___y_4507_, v___y_4508_, v___y_4509_, v___y_4510_);
lean_dec(v___y_4510_);
lean_dec_ref(v___y_4509_);
lean_dec(v___y_4508_);
lean_dec_ref(v___y_4507_);
return v_res_4512_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9___redArg___closed__0(void){
_start:
{
lean_object* v___x_4513_; lean_object* v___x_4514_; 
v___x_4513_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4514_, 0, v___x_4513_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9___redArg(){
_start:
{
lean_object* v___x_4516_; 
v___x_4516_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9___redArg___closed__0);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9___redArg___boxed(lean_object* v___dummy_4517_){
_start:
{
lean_object* v_res_4518_; 
v_res_4518_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9___redArg();
return v_res_4518_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_4519_; lean_object* v___x_4520_; 
v___x_4519_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4520_, 0, v___x_4519_);
return v___x_4520_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1(void){
_start:
{
lean_object* v___x_4521_; lean_object* v___x_4522_; 
v___x_4521_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0);
v___x_4522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4522_, 0, v___x_4521_);
lean_ctor_set(v___x_4522_, 1, v___x_4521_);
return v___x_4522_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2(void){
_start:
{
lean_object* v___x_4523_; 
v___x_4523_ = l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9___redArg();
return v___x_4523_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__3(void){
_start:
{
lean_object* v___x_4524_; lean_object* v___x_4525_; 
v___x_4524_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0);
v___x_4525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4525_, 0, v___x_4524_);
lean_ctor_set(v___x_4525_, 1, v___x_4524_);
return v___x_4525_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__4(void){
_start:
{
lean_object* v___x_4526_; lean_object* v___x_4527_; lean_object* v___x_4528_; 
v___x_4526_ = lean_unsigned_to_nat(0u);
v___x_4527_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0);
v___x_4528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4528_, 0, v___x_4527_);
lean_ctor_set(v___x_4528_, 1, v___x_4527_);
lean_ctor_set(v___x_4528_, 2, v___x_4526_);
return v___x_4528_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__5(void){
_start:
{
lean_object* v___x_4529_; lean_object* v___x_4530_; lean_object* v___x_4531_; lean_object* v___x_4532_; lean_object* v___x_4533_; 
v___x_4529_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__4, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__4_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__4);
v___x_4530_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__3);
v___x_4531_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__0);
v___x_4532_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2);
v___x_4533_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_4533_, 0, v___x_4532_);
lean_ctor_set(v___x_4533_, 1, v___x_4531_);
lean_ctor_set(v___x_4533_, 2, v___x_4530_);
lean_ctor_set(v___x_4533_, 3, v___x_4531_);
lean_ctor_set(v___x_4533_, 4, v___x_4531_);
lean_ctor_set(v___x_4533_, 5, v___x_4531_);
lean_ctor_set(v___x_4533_, 6, v___x_4531_);
lean_ctor_set(v___x_4533_, 7, v___x_4529_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_ext_4534_, lean_object* v_b_4535_, uint8_t v_kind_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v_toCold_4541_; lean_object* v_currNamespace_4542_; lean_object* v___x_4543_; lean_object* v_env_4544_; lean_object* v_nextMacroScope_4545_; lean_object* v_ngen_4546_; lean_object* v_auxDeclNGen_4547_; lean_object* v_traceState_4548_; lean_object* v_recordedDeps_4549_; lean_object* v_messages_4550_; lean_object* v_infoState_4551_; lean_object* v_snapshotTasks_4552_; lean_object* v___x_4554_; uint8_t v_isShared_4555_; uint8_t v_isSharedCheck_4579_; 
v_toCold_4541_ = lean_ctor_get(v___y_4538_, 0);
v_currNamespace_4542_ = lean_ctor_get(v_toCold_4541_, 4);
v___x_4543_ = lean_st_ref_take(v___y_4539_);
v_env_4544_ = lean_ctor_get(v___x_4543_, 0);
v_nextMacroScope_4545_ = lean_ctor_get(v___x_4543_, 1);
v_ngen_4546_ = lean_ctor_get(v___x_4543_, 2);
v_auxDeclNGen_4547_ = lean_ctor_get(v___x_4543_, 3);
v_traceState_4548_ = lean_ctor_get(v___x_4543_, 4);
v_recordedDeps_4549_ = lean_ctor_get(v___x_4543_, 6);
v_messages_4550_ = lean_ctor_get(v___x_4543_, 7);
v_infoState_4551_ = lean_ctor_get(v___x_4543_, 8);
v_snapshotTasks_4552_ = lean_ctor_get(v___x_4543_, 9);
v_isSharedCheck_4579_ = !lean_is_exclusive(v___x_4543_);
if (v_isSharedCheck_4579_ == 0)
{
lean_object* v_unused_4580_; 
v_unused_4580_ = lean_ctor_get(v___x_4543_, 5);
lean_dec(v_unused_4580_);
v___x_4554_ = v___x_4543_;
v_isShared_4555_ = v_isSharedCheck_4579_;
goto v_resetjp_4553_;
}
else
{
lean_inc(v_snapshotTasks_4552_);
lean_inc(v_infoState_4551_);
lean_inc(v_messages_4550_);
lean_inc(v_recordedDeps_4549_);
lean_inc(v_traceState_4548_);
lean_inc(v_auxDeclNGen_4547_);
lean_inc(v_ngen_4546_);
lean_inc(v_nextMacroScope_4545_);
lean_inc(v_env_4544_);
lean_dec(v___x_4543_);
v___x_4554_ = lean_box(0);
v_isShared_4555_ = v_isSharedCheck_4579_;
goto v_resetjp_4553_;
}
v_resetjp_4553_:
{
lean_object* v___x_4556_; lean_object* v___x_4557_; lean_object* v___x_4559_; 
lean_inc(v_currNamespace_4542_);
v___x_4556_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_4544_, v_ext_4534_, v_b_4535_, v_kind_4536_, v_currNamespace_4542_);
v___x_4557_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1);
if (v_isShared_4555_ == 0)
{
lean_ctor_set(v___x_4554_, 5, v___x_4557_);
lean_ctor_set(v___x_4554_, 0, v___x_4556_);
v___x_4559_ = v___x_4554_;
goto v_reusejp_4558_;
}
else
{
lean_object* v_reuseFailAlloc_4578_; 
v_reuseFailAlloc_4578_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4578_, 0, v___x_4556_);
lean_ctor_set(v_reuseFailAlloc_4578_, 1, v_nextMacroScope_4545_);
lean_ctor_set(v_reuseFailAlloc_4578_, 2, v_ngen_4546_);
lean_ctor_set(v_reuseFailAlloc_4578_, 3, v_auxDeclNGen_4547_);
lean_ctor_set(v_reuseFailAlloc_4578_, 4, v_traceState_4548_);
lean_ctor_set(v_reuseFailAlloc_4578_, 5, v___x_4557_);
lean_ctor_set(v_reuseFailAlloc_4578_, 6, v_recordedDeps_4549_);
lean_ctor_set(v_reuseFailAlloc_4578_, 7, v_messages_4550_);
lean_ctor_set(v_reuseFailAlloc_4578_, 8, v_infoState_4551_);
lean_ctor_set(v_reuseFailAlloc_4578_, 9, v_snapshotTasks_4552_);
v___x_4559_ = v_reuseFailAlloc_4578_;
goto v_reusejp_4558_;
}
v_reusejp_4558_:
{
lean_object* v___x_4560_; lean_object* v___x_4561_; lean_object* v_mctx_4562_; lean_object* v_zetaDeltaFVarIds_4563_; lean_object* v_postponed_4564_; lean_object* v_diag_4565_; lean_object* v___x_4567_; uint8_t v_isShared_4568_; uint8_t v_isSharedCheck_4576_; 
v___x_4560_ = lean_st_ref_put(v___y_4539_, v___x_4559_);
v___x_4561_ = lean_st_ref_take(v___y_4537_);
v_mctx_4562_ = lean_ctor_get(v___x_4561_, 0);
v_zetaDeltaFVarIds_4563_ = lean_ctor_get(v___x_4561_, 2);
v_postponed_4564_ = lean_ctor_get(v___x_4561_, 3);
v_diag_4565_ = lean_ctor_get(v___x_4561_, 4);
v_isSharedCheck_4576_ = !lean_is_exclusive(v___x_4561_);
if (v_isSharedCheck_4576_ == 0)
{
lean_object* v_unused_4577_; 
v_unused_4577_ = lean_ctor_get(v___x_4561_, 1);
lean_dec(v_unused_4577_);
v___x_4567_ = v___x_4561_;
v_isShared_4568_ = v_isSharedCheck_4576_;
goto v_resetjp_4566_;
}
else
{
lean_inc(v_diag_4565_);
lean_inc(v_postponed_4564_);
lean_inc(v_zetaDeltaFVarIds_4563_);
lean_inc(v_mctx_4562_);
lean_dec(v___x_4561_);
v___x_4567_ = lean_box(0);
v_isShared_4568_ = v_isSharedCheck_4576_;
goto v_resetjp_4566_;
}
v_resetjp_4566_:
{
lean_object* v___x_4569_; lean_object* v___x_4570_; lean_object* v___x_4572_; 
v___x_4569_ = lean_box(0);
v___x_4570_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__5);
if (v_isShared_4568_ == 0)
{
lean_ctor_set(v___x_4567_, 1, v___x_4570_);
v___x_4572_ = v___x_4567_;
goto v_reusejp_4571_;
}
else
{
lean_object* v_reuseFailAlloc_4575_; 
v_reuseFailAlloc_4575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4575_, 0, v_mctx_4562_);
lean_ctor_set(v_reuseFailAlloc_4575_, 1, v___x_4570_);
lean_ctor_set(v_reuseFailAlloc_4575_, 2, v_zetaDeltaFVarIds_4563_);
lean_ctor_set(v_reuseFailAlloc_4575_, 3, v_postponed_4564_);
lean_ctor_set(v_reuseFailAlloc_4575_, 4, v_diag_4565_);
v___x_4572_ = v_reuseFailAlloc_4575_;
goto v_reusejp_4571_;
}
v_reusejp_4571_:
{
lean_object* v___x_4573_; lean_object* v___x_4574_; 
v___x_4573_ = lean_st_ref_put(v___y_4537_, v___x_4572_);
v___x_4574_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4574_, 0, v___x_4569_);
return v___x_4574_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_ext_4581_, lean_object* v_b_4582_, lean_object* v_kind_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
uint8_t v_kind_boxed_4588_; lean_object* v_res_4589_; 
v_kind_boxed_4588_ = lean_unbox(v_kind_4583_);
v_res_4589_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg(v_ext_4581_, v_b_4582_, v_kind_boxed_4588_, v___y_4584_, v___y_4585_, v___y_4586_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
return v_res_4589_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1(lean_object* v_constName_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v___x_4596_; lean_object* v_env_4597_; uint8_t v___x_4598_; lean_object* v___x_4599_; 
v___x_4596_ = lean_st_ref_get(v___y_4594_);
v_env_4597_ = lean_ctor_get(v___x_4596_, 0);
lean_inc_ref(v_env_4597_);
lean_dec(v___x_4596_);
v___x_4598_ = 0;
lean_inc(v_constName_4590_);
v___x_4599_ = l_Lean_Environment_find_x3f(v_env_4597_, v_constName_4590_, v___x_4598_);
if (lean_obj_tag(v___x_4599_) == 0)
{
lean_object* v___x_4600_; 
v___x_4600_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3___redArg(v_constName_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
return v___x_4600_;
}
else
{
lean_object* v_val_4601_; lean_object* v___x_4603_; uint8_t v_isShared_4604_; uint8_t v_isSharedCheck_4608_; 
lean_dec(v_constName_4590_);
v_val_4601_ = lean_ctor_get(v___x_4599_, 0);
v_isSharedCheck_4608_ = !lean_is_exclusive(v___x_4599_);
if (v_isSharedCheck_4608_ == 0)
{
v___x_4603_ = v___x_4599_;
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
else
{
lean_inc(v_val_4601_);
lean_dec(v___x_4599_);
v___x_4603_ = lean_box(0);
v_isShared_4604_ = v_isSharedCheck_4608_;
goto v_resetjp_4602_;
}
v_resetjp_4602_:
{
lean_object* v___x_4606_; 
if (v_isShared_4604_ == 0)
{
lean_ctor_set_tag(v___x_4603_, 0);
v___x_4606_ = v___x_4603_;
goto v_reusejp_4605_;
}
else
{
lean_object* v_reuseFailAlloc_4607_; 
v_reuseFailAlloc_4607_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4607_, 0, v_val_4601_);
v___x_4606_ = v_reuseFailAlloc_4607_;
goto v_reusejp_4605_;
}
v_reusejp_4605_:
{
return v___x_4606_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_constName_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v_res_4615_; 
v_res_4615_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1(v_constName_4609_, v___y_4610_, v___y_4611_, v___y_4612_, v___y_4613_);
lean_dec(v___y_4613_);
lean_dec_ref(v___y_4612_);
lean_dec(v___y_4611_);
lean_dec_ref(v___y_4610_);
return v_res_4615_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4617_; lean_object* v___x_4618_; 
v___x_4617_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4618_ = l_Lean_stringToMessageData(v___x_4617_);
return v___x_4618_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4620_; lean_object* v___x_4621_; 
v___x_4620_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4621_ = l_Lean_stringToMessageData(v___x_4620_);
return v___x_4621_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_4623_; lean_object* v___x_4624_; 
v___x_4623_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_4624_ = l_Lean_stringToMessageData(v___x_4623_);
return v___x_4624_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__7(void){
_start:
{
lean_object* v___x_4626_; lean_object* v___x_4627_; 
v___x_4626_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__6));
v___x_4627_ = l_Lean_stringToMessageData(v___x_4626_);
return v___x_4627_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__9(void){
_start:
{
lean_object* v___x_4629_; lean_object* v___x_4630_; 
v___x_4629_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__8));
v___x_4630_ = l_Lean_stringToMessageData(v___x_4629_);
return v___x_4630_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__11(void){
_start:
{
lean_object* v___x_4632_; lean_object* v___x_4633_; 
v___x_4632_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__10));
v___x_4633_ = l_Lean_stringToMessageData(v___x_4632_);
return v___x_4633_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4634_, uint8_t v_attrKind_4635_, lean_object* v_prio_4636_, lean_object* v_a_4637_, lean_object* v_a_4638_, lean_object* v_a_4639_, lean_object* v_a_4640_){
_start:
{
lean_object* v___x_4642_; 
lean_inc(v_declName_4634_);
v___x_4642_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4634_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
if (lean_obj_tag(v___x_4642_) == 0)
{
lean_object* v_a_4643_; lean_object* v___y_4645_; lean_object* v___y_4646_; lean_object* v___y_4647_; lean_object* v___y_4648_; lean_object* v___y_4649_; lean_object* v___y_4650_; lean_object* v___x_4655_; 
v_a_4643_ = lean_ctor_get(v___x_4642_, 0);
lean_inc(v_a_4643_);
lean_dec_ref_known(v___x_4642_, 1);
lean_inc(v_declName_4634_);
v___x_4655_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1(v_declName_4634_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
if (lean_obj_tag(v___x_4655_) == 0)
{
lean_object* v_a_4656_; lean_object* v___y_4658_; lean_object* v___y_4659_; lean_object* v___y_4660_; lean_object* v___y_4661_; lean_object* v___y_4662_; lean_object* v___y_4663_; lean_object* v___y_4674_; lean_object* v___y_4675_; lean_object* v___y_4676_; lean_object* v___y_4677_; lean_object* v___y_4678_; lean_object* v___y_4696_; lean_object* v___y_4697_; lean_object* v___y_4698_; lean_object* v___y_4699_; lean_object* v___x_4744_; uint8_t v___x_4745_; 
v_a_4656_ = lean_ctor_get(v___x_4655_, 0);
lean_inc(v_a_4656_);
lean_dec_ref_known(v___x_4655_, 1);
v___x_4744_ = l_Lean_ConstantInfo_type(v_a_4656_);
v___x_4745_ = l_Lean_Expr_hasSorry(v___x_4744_);
lean_dec_ref(v___x_4744_);
if (v___x_4745_ == 0)
{
lean_object* v___x_4746_; 
lean_inc(v_a_4643_);
v___x_4746_ = l_Lean_Meta_checkNonClassInstance(v_a_4643_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
if (lean_obj_tag(v___x_4746_) == 0)
{
lean_object* v___x_4747_; 
lean_dec_ref_known(v___x_4746_, 1);
v___x_4747_ = l_Lean_Meta_checkImpossibleInstance(v_a_4656_, v_a_4637_, v_a_4638_, v_a_4639_, v_a_4640_);
if (lean_obj_tag(v___x_4747_) == 0)
{
lean_dec_ref_known(v___x_4747_, 1);
v___y_4696_ = v_a_4637_;
v___y_4697_ = v_a_4638_;
v___y_4698_ = v_a_4639_;
v___y_4699_ = v_a_4640_;
goto v___jp_4695_;
}
else
{
lean_dec(v_a_4656_);
lean_dec(v_a_4643_);
lean_dec(v_prio_4636_);
lean_dec(v_declName_4634_);
return v___x_4747_;
}
}
else
{
lean_dec(v_a_4656_);
lean_dec(v_a_4643_);
lean_dec(v_prio_4636_);
lean_dec(v_declName_4634_);
return v___x_4746_;
}
}
else
{
v___y_4696_ = v_a_4637_;
v___y_4697_ = v_a_4638_;
v___y_4698_ = v_a_4639_;
v___y_4699_ = v_a_4640_;
goto v___jp_4695_;
}
v___jp_4657_:
{
lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; lean_object* v___x_4669_; lean_object* v___x_4670_; lean_object* v___x_4671_; lean_object* v___x_4672_; 
lean_dec_ref(v___y_4659_);
lean_dec_ref(v___y_4658_);
v___x_4664_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
v___x_4665_ = l_Lean_MessageData_ofName(v_declName_4634_);
v___x_4666_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4664_);
lean_ctor_set(v___x_4666_, 1, v___x_4665_);
v___x_4667_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4666_);
lean_ctor_set(v___x_4668_, 1, v___x_4667_);
v___x_4669_ = l_Lean_ConstantInfo_type(v_a_4656_);
lean_dec(v_a_4656_);
v___x_4670_ = l_Lean_indentExpr(v___x_4669_);
v___x_4671_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4671_, 0, v___x_4668_);
lean_ctor_set(v___x_4671_, 1, v___x_4670_);
v___x_4672_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_4671_, v___y_4663_, v___y_4661_, v___y_4660_, v___y_4662_);
return v___x_4672_;
}
v___jp_4673_:
{
lean_object* v___x_4679_; lean_object* v_a_4680_; lean_object* v___x_4681_; 
lean_inc(v_declName_4634_);
v___x_4679_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__2___redArg(v_declName_4634_, v___y_4678_);
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
lean_inc(v_a_4680_);
lean_dec_ref(v___x_4679_);
lean_inc(v_a_4643_);
v___x_4681_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4643_, v_a_4680_, v___y_4675_, v___y_4676_, v___y_4677_, v___y_4678_);
if (lean_obj_tag(v___x_4681_) == 0)
{
lean_object* v_a_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; uint8_t v___x_4685_; 
v_a_4682_ = lean_ctor_get(v___x_4681_, 0);
lean_inc(v_a_4682_);
lean_dec_ref_known(v___x_4681_, 1);
v___x_4683_ = lean_unsigned_to_nat(0u);
v___x_4684_ = lean_array_get_size(v___y_4674_);
v___x_4685_ = lean_nat_dec_lt(v___x_4683_, v___x_4684_);
if (v___x_4685_ == 0)
{
lean_dec(v_a_4643_);
lean_dec(v_prio_4636_);
v___y_4658_ = v___y_4674_;
v___y_4659_ = v_a_4682_;
v___y_4660_ = v___y_4677_;
v___y_4661_ = v___y_4676_;
v___y_4662_ = v___y_4678_;
v___y_4663_ = v___y_4675_;
goto v___jp_4657_;
}
else
{
lean_object* v___x_4686_; 
v___x_4686_ = lean_array_fget_borrowed(v___y_4674_, v___x_4683_);
if (lean_obj_tag(v___x_4686_) == 4)
{
lean_dec(v_a_4656_);
v___y_4645_ = v_a_4682_;
v___y_4646_ = v___y_4674_;
v___y_4647_ = v___y_4675_;
v___y_4648_ = v___y_4676_;
v___y_4649_ = v___y_4677_;
v___y_4650_ = v___y_4678_;
goto v___jp_4644_;
}
else
{
lean_dec(v_a_4643_);
lean_dec(v_prio_4636_);
v___y_4658_ = v___y_4674_;
v___y_4659_ = v_a_4682_;
v___y_4660_ = v___y_4677_;
v___y_4661_ = v___y_4676_;
v___y_4662_ = v___y_4678_;
v___y_4663_ = v___y_4675_;
goto v___jp_4657_;
}
}
}
else
{
lean_object* v_a_4687_; lean_object* v___x_4689_; uint8_t v_isShared_4690_; uint8_t v_isSharedCheck_4694_; 
lean_dec_ref(v___y_4674_);
lean_dec(v_a_4656_);
lean_dec(v_a_4643_);
lean_dec(v_prio_4636_);
lean_dec(v_declName_4634_);
v_a_4687_ = lean_ctor_get(v___x_4681_, 0);
v_isSharedCheck_4694_ = !lean_is_exclusive(v___x_4681_);
if (v_isSharedCheck_4694_ == 0)
{
v___x_4689_ = v___x_4681_;
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
else
{
lean_inc(v_a_4687_);
lean_dec(v___x_4681_);
v___x_4689_ = lean_box(0);
v_isShared_4690_ = v_isSharedCheck_4694_;
goto v_resetjp_4688_;
}
v_resetjp_4688_:
{
lean_object* v___x_4692_; 
if (v_isShared_4690_ == 0)
{
v___x_4692_ = v___x_4689_;
goto v_reusejp_4691_;
}
else
{
lean_object* v_reuseFailAlloc_4693_; 
v_reuseFailAlloc_4693_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4693_, 0, v_a_4687_);
v___x_4692_ = v_reuseFailAlloc_4693_;
goto v_reusejp_4691_;
}
v_reusejp_4691_:
{
return v___x_4692_;
}
}
}
}
v___jp_4695_:
{
lean_object* v___x_4700_; 
lean_inc(v_a_4643_);
v___x_4700_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4643_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
if (lean_obj_tag(v___x_4700_) == 0)
{
lean_object* v_a_4701_; lean_object* v___x_4702_; lean_object* v_a_4703_; uint8_t v___x_4704_; uint8_t v___x_4705_; uint8_t v___x_4706_; 
v_a_4701_ = lean_ctor_get(v___x_4700_, 0);
lean_inc(v_a_4701_);
lean_dec_ref_known(v___x_4700_, 1);
lean_inc(v_declName_4634_);
v___x_4702_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__4___redArg(v_declName_4634_, v___y_4699_);
v_a_4703_ = lean_ctor_get(v___x_4702_, 0);
lean_inc(v_a_4703_);
lean_dec_ref(v___x_4702_);
v___x_4704_ = 1;
v___x_4705_ = lean_unbox(v_a_4703_);
lean_dec(v_a_4703_);
v___x_4706_ = l_Lean_instBEqReducibilityStatus_beq(v___x_4705_, v___x_4704_);
if (v___x_4706_ == 0)
{
v___y_4674_ = v_a_4701_;
v___y_4675_ = v___y_4696_;
v___y_4676_ = v___y_4697_;
v___y_4677_ = v___y_4698_;
v___y_4678_ = v___y_4699_;
goto v___jp_4673_;
}
else
{
lean_object* v___x_4707_; 
lean_inc(v_declName_4634_);
v___x_4707_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1(v_declName_4634_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
if (lean_obj_tag(v___x_4707_) == 0)
{
lean_object* v_a_4708_; uint8_t v___x_4709_; 
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
lean_inc(v_a_4708_);
lean_dec_ref_known(v___x_4707_, 1);
v___x_4709_ = l_Lean_ConstantInfo_isDefinition(v_a_4708_);
lean_dec(v_a_4708_);
if (v___x_4709_ == 0)
{
lean_object* v___x_4710_; lean_object* v_env_4711_; uint8_t v___x_4712_; 
v___x_4710_ = lean_st_ref_get(v___y_4699_);
v_env_4711_ = lean_ctor_get(v___x_4710_, 0);
lean_inc_ref(v_env_4711_);
lean_dec(v___x_4710_);
lean_inc(v_declName_4634_);
v___x_4712_ = l_Lean_wasOriginallyDefn(v_env_4711_, v_declName_4634_);
if (v___x_4712_ == 0)
{
v___y_4674_ = v_a_4701_;
v___y_4675_ = v___y_4696_;
v___y_4676_ = v___y_4697_;
v___y_4677_ = v___y_4698_;
v___y_4678_ = v___y_4699_;
goto v___jp_4673_;
}
else
{
lean_object* v___x_4713_; lean_object* v___x_4714_; lean_object* v___x_4715_; lean_object* v___x_4716_; lean_object* v___x_4717_; lean_object* v___x_4718_; 
v___x_4713_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
lean_inc(v_declName_4634_);
v___x_4714_ = l_Lean_MessageData_ofName(v_declName_4634_);
v___x_4715_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4715_, 0, v___x_4713_);
lean_ctor_set(v___x_4715_, 1, v___x_4714_);
v___x_4716_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__7, &l_Lean_Meta_addInstance___closed__7_once, _init_l_Lean_Meta_addInstance___closed__7);
v___x_4717_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4717_, 0, v___x_4715_);
lean_ctor_set(v___x_4717_, 1, v___x_4716_);
v___x_4718_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4717_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
if (lean_obj_tag(v___x_4718_) == 0)
{
lean_dec_ref_known(v___x_4718_, 1);
v___y_4674_ = v_a_4701_;
v___y_4675_ = v___y_4696_;
v___y_4676_ = v___y_4697_;
v___y_4677_ = v___y_4698_;
v___y_4678_ = v___y_4699_;
goto v___jp_4673_;
}
else
{
lean_dec(v_a_4701_);
lean_dec(v_a_4656_);
lean_dec(v_a_4643_);
lean_dec(v_prio_4636_);
lean_dec(v_declName_4634_);
return v___x_4718_;
}
}
}
else
{
lean_object* v___x_4719_; lean_object* v___x_4720_; uint8_t v___x_4721_; 
v___x_4719_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4698_);
v___x_4720_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility));
v___x_4721_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_4719_, v___x_4720_);
lean_dec_ref(v___x_4719_);
if (v___x_4721_ == 0)
{
v___y_4674_ = v_a_4701_;
v___y_4675_ = v___y_4696_;
v___y_4676_ = v___y_4697_;
v___y_4677_ = v___y_4698_;
v___y_4678_ = v___y_4699_;
goto v___jp_4673_;
}
else
{
lean_object* v___x_4722_; lean_object* v___x_4723_; lean_object* v___x_4724_; lean_object* v___x_4725_; lean_object* v___x_4726_; lean_object* v___x_4727_; 
v___x_4722_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__9, &l_Lean_Meta_addInstance___closed__9_once, _init_l_Lean_Meta_addInstance___closed__9);
lean_inc(v_declName_4634_);
v___x_4723_ = l_Lean_MessageData_ofName(v_declName_4634_);
v___x_4724_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4724_, 0, v___x_4722_);
lean_ctor_set(v___x_4724_, 1, v___x_4723_);
v___x_4725_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__11, &l_Lean_Meta_addInstance___closed__11_once, _init_l_Lean_Meta_addInstance___closed__11);
v___x_4726_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4726_, 0, v___x_4724_);
lean_ctor_set(v___x_4726_, 1, v___x_4725_);
v___x_4727_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4726_, v___y_4696_, v___y_4697_, v___y_4698_, v___y_4699_);
if (lean_obj_tag(v___x_4727_) == 0)
{
lean_dec_ref_known(v___x_4727_, 1);
v___y_4674_ = v_a_4701_;
v___y_4675_ = v___y_4696_;
v___y_4676_ = v___y_4697_;
v___y_4677_ = v___y_4698_;
v___y_4678_ = v___y_4699_;
goto v___jp_4673_;
}
else
{
lean_dec(v_a_4701_);
lean_dec(v_a_4656_);
lean_dec(v_a_4643_);
lean_dec(v_prio_4636_);
lean_dec(v_declName_4634_);
return v___x_4727_;
}
}
}
}
else
{
lean_object* v_a_4728_; lean_object* v___x_4730_; uint8_t v_isShared_4731_; uint8_t v_isSharedCheck_4735_; 
lean_dec(v_a_4701_);
lean_dec(v_a_4656_);
lean_dec(v_a_4643_);
lean_dec(v_prio_4636_);
lean_dec(v_declName_4634_);
v_a_4728_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4735_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4735_ == 0)
{
v___x_4730_ = v___x_4707_;
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
else
{
lean_inc(v_a_4728_);
lean_dec(v___x_4707_);
v___x_4730_ = lean_box(0);
v_isShared_4731_ = v_isSharedCheck_4735_;
goto v_resetjp_4729_;
}
v_resetjp_4729_:
{
lean_object* v___x_4733_; 
if (v_isShared_4731_ == 0)
{
v___x_4733_ = v___x_4730_;
goto v_reusejp_4732_;
}
else
{
lean_object* v_reuseFailAlloc_4734_; 
v_reuseFailAlloc_4734_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4734_, 0, v_a_4728_);
v___x_4733_ = v_reuseFailAlloc_4734_;
goto v_reusejp_4732_;
}
v_reusejp_4732_:
{
return v___x_4733_;
}
}
}
}
}
else
{
lean_object* v_a_4736_; lean_object* v___x_4738_; uint8_t v_isShared_4739_; uint8_t v_isSharedCheck_4743_; 
lean_dec(v_a_4656_);
lean_dec(v_a_4643_);
lean_dec(v_prio_4636_);
lean_dec(v_declName_4634_);
v_a_4736_ = lean_ctor_get(v___x_4700_, 0);
v_isSharedCheck_4743_ = !lean_is_exclusive(v___x_4700_);
if (v_isSharedCheck_4743_ == 0)
{
v___x_4738_ = v___x_4700_;
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
else
{
lean_inc(v_a_4736_);
lean_dec(v___x_4700_);
v___x_4738_ = lean_box(0);
v_isShared_4739_ = v_isSharedCheck_4743_;
goto v_resetjp_4737_;
}
v_resetjp_4737_:
{
lean_object* v___x_4741_; 
if (v_isShared_4739_ == 0)
{
v___x_4741_ = v___x_4738_;
goto v_reusejp_4740_;
}
else
{
lean_object* v_reuseFailAlloc_4742_; 
v_reuseFailAlloc_4742_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4742_, 0, v_a_4736_);
v___x_4741_ = v_reuseFailAlloc_4742_;
goto v_reusejp_4740_;
}
v_reusejp_4740_:
{
return v___x_4741_;
}
}
}
}
}
else
{
lean_object* v_a_4748_; lean_object* v___x_4750_; uint8_t v_isShared_4751_; uint8_t v_isSharedCheck_4755_; 
lean_dec(v_a_4643_);
lean_dec(v_prio_4636_);
lean_dec(v_declName_4634_);
v_a_4748_ = lean_ctor_get(v___x_4655_, 0);
v_isSharedCheck_4755_ = !lean_is_exclusive(v___x_4655_);
if (v_isSharedCheck_4755_ == 0)
{
v___x_4750_ = v___x_4655_;
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
else
{
lean_inc(v_a_4748_);
lean_dec(v___x_4655_);
v___x_4750_ = lean_box(0);
v_isShared_4751_ = v_isSharedCheck_4755_;
goto v_resetjp_4749_;
}
v_resetjp_4749_:
{
lean_object* v___x_4753_; 
if (v_isShared_4751_ == 0)
{
v___x_4753_ = v___x_4750_;
goto v_reusejp_4752_;
}
else
{
lean_object* v_reuseFailAlloc_4754_; 
v_reuseFailAlloc_4754_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4754_, 0, v_a_4748_);
v___x_4753_ = v_reuseFailAlloc_4754_;
goto v_reusejp_4752_;
}
v_reusejp_4752_:
{
return v___x_4753_;
}
}
}
v___jp_4644_:
{
lean_object* v___x_4651_; lean_object* v___x_4652_; lean_object* v___x_4653_; lean_object* v___x_4654_; 
v___x_4651_ = l_Lean_Meta_instanceExtension;
v___x_4652_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_4652_, 0, v_declName_4634_);
v___x_4653_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4653_, 0, v___y_4646_);
lean_ctor_set(v___x_4653_, 1, v_a_4643_);
lean_ctor_set(v___x_4653_, 2, v_prio_4636_);
lean_ctor_set(v___x_4653_, 3, v___x_4652_);
lean_ctor_set(v___x_4653_, 4, v___y_4645_);
lean_ctor_set_uint8(v___x_4653_, sizeof(void*)*5, v_attrKind_4635_);
v___x_4654_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg(v___x_4651_, v___x_4653_, v_attrKind_4635_, v___y_4648_, v___y_4649_, v___y_4650_);
return v___x_4654_;
}
}
else
{
lean_object* v_a_4756_; lean_object* v___x_4758_; uint8_t v_isShared_4759_; uint8_t v_isSharedCheck_4763_; 
lean_dec(v_prio_4636_);
lean_dec(v_declName_4634_);
v_a_4756_ = lean_ctor_get(v___x_4642_, 0);
v_isSharedCheck_4763_ = !lean_is_exclusive(v___x_4642_);
if (v_isSharedCheck_4763_ == 0)
{
v___x_4758_ = v___x_4642_;
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
else
{
lean_inc(v_a_4756_);
lean_dec(v___x_4642_);
v___x_4758_ = lean_box(0);
v_isShared_4759_ = v_isSharedCheck_4763_;
goto v_resetjp_4757_;
}
v_resetjp_4757_:
{
lean_object* v___x_4761_; 
if (v_isShared_4759_ == 0)
{
v___x_4761_ = v___x_4758_;
goto v_reusejp_4760_;
}
else
{
lean_object* v_reuseFailAlloc_4762_; 
v_reuseFailAlloc_4762_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4762_, 0, v_a_4756_);
v___x_4761_ = v_reuseFailAlloc_4762_;
goto v_reusejp_4760_;
}
v_reusejp_4760_:
{
return v___x_4761_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4764_, lean_object* v_attrKind_4765_, lean_object* v_prio_4766_, lean_object* v_a_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_){
_start:
{
uint8_t v_attrKind_boxed_4772_; lean_object* v_res_4773_; 
v_attrKind_boxed_4772_ = lean_unbox(v_attrKind_4765_);
v_res_4773_ = l_Lean_Meta_addInstance(v_declName_4764_, v_attrKind_boxed_4772_, v_prio_4766_, v_a_4767_, v_a_4768_, v_a_4769_, v_a_4770_);
lean_dec(v_a_4770_);
lean_dec_ref(v_a_4769_);
lean_dec(v_a_4768_);
lean_dec_ref(v_a_4767_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3(lean_object* v_00_u03b1_4774_, lean_object* v_00_u03b2_4775_, lean_object* v_00_u03c3_4776_, lean_object* v_ext_4777_, lean_object* v_b_4778_, uint8_t v_kind_4779_, lean_object* v___y_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_, lean_object* v___y_4783_){
_start:
{
lean_object* v___x_4785_; 
v___x_4785_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg(v_ext_4777_, v_b_4778_, v_kind_4779_, v___y_4781_, v___y_4782_, v___y_4783_);
return v___x_4785_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_00_u03b1_4786_, lean_object* v_00_u03b2_4787_, lean_object* v_00_u03c3_4788_, lean_object* v_ext_4789_, lean_object* v_b_4790_, lean_object* v_kind_4791_, lean_object* v___y_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_, lean_object* v___y_4795_, lean_object* v___y_4796_){
_start:
{
uint8_t v_kind_boxed_4797_; lean_object* v_res_4798_; 
v_kind_boxed_4797_ = lean_unbox(v_kind_4791_);
v_res_4798_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3(v_00_u03b1_4786_, v_00_u03b2_4787_, v_00_u03c3_4788_, v_ext_4789_, v_b_4790_, v_kind_boxed_4797_, v___y_4792_, v___y_4793_, v___y_4794_, v___y_4795_);
lean_dec(v___y_4795_);
lean_dec_ref(v___y_4794_);
lean_dec(v___y_4793_);
lean_dec_ref(v___y_4792_);
return v_res_4798_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3(lean_object* v_00_u03b1_4799_, lean_object* v_constName_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_, lean_object* v___y_4803_, lean_object* v___y_4804_){
_start:
{
lean_object* v___x_4806_; 
v___x_4806_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3___redArg(v_constName_4800_, v___y_4801_, v___y_4802_, v___y_4803_, v___y_4804_);
return v___x_4806_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3___boxed(lean_object* v_00_u03b1_4807_, lean_object* v_constName_4808_, lean_object* v___y_4809_, lean_object* v___y_4810_, lean_object* v___y_4811_, lean_object* v___y_4812_, lean_object* v___y_4813_){
_start:
{
lean_object* v_res_4814_; 
v_res_4814_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3(v_00_u03b1_4807_, v_constName_4808_, v___y_4809_, v___y_4810_, v___y_4811_, v___y_4812_);
lean_dec(v___y_4812_);
lean_dec_ref(v___y_4811_);
lean_dec(v___y_4810_);
lean_dec_ref(v___y_4809_);
return v_res_4814_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6_spec__9(lean_object* v_00_u03b2_4815_){
_start:
{
lean_object* v___x_4816_; 
v___x_4816_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2);
return v___x_4816_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6___redArg(){
_start:
{
lean_object* v___x_4818_; 
v___x_4818_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2);
return v___x_4818_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6___redArg___boxed(lean_object* v___dummy_4819_){
_start:
{
lean_object* v_res_4820_; 
v_res_4820_ = l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6___redArg();
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l_Lean_instInhabitedBudgetedCache_default___at___00Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3_spec__6(lean_object* v_00_u03b2_4821_){
_start:
{
lean_object* v___x_4822_; 
v___x_4822_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2);
return v___x_4822_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6(lean_object* v_00_u03b1_4823_, lean_object* v_ref_4824_, lean_object* v_constName_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_){
_start:
{
lean_object* v___x_4831_; 
v___x_4831_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg(v_ref_4824_, v_constName_4825_, v___y_4826_, v___y_4827_, v___y_4828_, v___y_4829_);
return v___x_4831_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___boxed(lean_object* v_00_u03b1_4832_, lean_object* v_ref_4833_, lean_object* v_constName_4834_, lean_object* v___y_4835_, lean_object* v___y_4836_, lean_object* v___y_4837_, lean_object* v___y_4838_, lean_object* v___y_4839_){
_start:
{
lean_object* v_res_4840_; 
v_res_4840_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6(v_00_u03b1_4832_, v_ref_4833_, v_constName_4834_, v___y_4835_, v___y_4836_, v___y_4837_, v___y_4838_);
lean_dec(v___y_4838_);
lean_dec_ref(v___y_4837_);
lean_dec(v___y_4836_);
lean_dec_ref(v___y_4835_);
lean_dec(v_ref_4833_);
return v_res_4840_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8(lean_object* v_00_u03b1_4841_, lean_object* v_ref_4842_, lean_object* v_msg_4843_, lean_object* v_declHint_4844_, lean_object* v___y_4845_, lean_object* v___y_4846_, lean_object* v___y_4847_, lean_object* v___y_4848_){
_start:
{
lean_object* v___x_4850_; 
v___x_4850_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8___redArg(v_ref_4842_, v_msg_4843_, v_declHint_4844_, v___y_4845_, v___y_4846_, v___y_4847_, v___y_4848_);
return v___x_4850_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8___boxed(lean_object* v_00_u03b1_4851_, lean_object* v_ref_4852_, lean_object* v_msg_4853_, lean_object* v_declHint_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8(v_00_u03b1_4851_, v_ref_4852_, v_msg_4853_, v_declHint_4854_, v___y_4855_, v___y_4856_, v___y_4857_, v___y_4858_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
lean_dec(v___y_4856_);
lean_dec_ref(v___y_4855_);
lean_dec(v_ref_4852_);
return v_res_4860_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12(lean_object* v_msg_4861_, lean_object* v_declHint_4862_, lean_object* v___y_4863_, lean_object* v___y_4864_, lean_object* v___y_4865_, lean_object* v___y_4866_){
_start:
{
lean_object* v___x_4868_; 
v___x_4868_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg(v_msg_4861_, v_declHint_4862_, v___y_4866_);
return v___x_4868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___boxed(lean_object* v_msg_4869_, lean_object* v_declHint_4870_, lean_object* v___y_4871_, lean_object* v___y_4872_, lean_object* v___y_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_){
_start:
{
lean_object* v_res_4876_; 
v_res_4876_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12(v_msg_4869_, v_declHint_4870_, v___y_4871_, v___y_4872_, v___y_4873_, v___y_4874_);
lean_dec(v___y_4874_);
lean_dec_ref(v___y_4873_);
lean_dec(v___y_4872_);
lean_dec_ref(v___y_4871_);
return v_res_4876_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__12(lean_object* v_00_u03b1_4877_, lean_object* v_ref_4878_, lean_object* v_msg_4879_, lean_object* v___y_4880_, lean_object* v___y_4881_, lean_object* v___y_4882_, lean_object* v___y_4883_){
_start:
{
lean_object* v___x_4885_; 
v___x_4885_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__12___redArg(v_ref_4878_, v_msg_4879_, v___y_4880_, v___y_4881_, v___y_4882_, v___y_4883_);
return v___x_4885_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__12___boxed(lean_object* v_00_u03b1_4886_, lean_object* v_ref_4887_, lean_object* v_msg_4888_, lean_object* v___y_4889_, lean_object* v___y_4890_, lean_object* v___y_4891_, lean_object* v___y_4892_, lean_object* v___y_4893_){
_start:
{
lean_object* v_res_4894_; 
v_res_4894_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__12(v_00_u03b1_4886_, v_ref_4887_, v_msg_4888_, v___y_4889_, v___y_4890_, v___y_4891_, v___y_4892_);
lean_dec(v___y_4892_);
lean_dec_ref(v___y_4891_);
lean_dec(v___y_4890_);
lean_dec_ref(v___y_4889_);
lean_dec(v_ref_4887_);
return v_res_4894_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4895_, uint8_t v_s_4896_, lean_object* v___y_4897_, lean_object* v___y_4898_){
_start:
{
lean_object* v___x_4900_; lean_object* v_env_4901_; lean_object* v_nextMacroScope_4902_; lean_object* v_ngen_4903_; lean_object* v_auxDeclNGen_4904_; lean_object* v_traceState_4905_; lean_object* v_recordedDeps_4906_; lean_object* v_messages_4907_; lean_object* v_infoState_4908_; lean_object* v_snapshotTasks_4909_; lean_object* v___x_4911_; uint8_t v_isShared_4912_; uint8_t v_isSharedCheck_4938_; 
v___x_4900_ = lean_st_ref_take(v___y_4898_);
v_env_4901_ = lean_ctor_get(v___x_4900_, 0);
v_nextMacroScope_4902_ = lean_ctor_get(v___x_4900_, 1);
v_ngen_4903_ = lean_ctor_get(v___x_4900_, 2);
v_auxDeclNGen_4904_ = lean_ctor_get(v___x_4900_, 3);
v_traceState_4905_ = lean_ctor_get(v___x_4900_, 4);
v_recordedDeps_4906_ = lean_ctor_get(v___x_4900_, 6);
v_messages_4907_ = lean_ctor_get(v___x_4900_, 7);
v_infoState_4908_ = lean_ctor_get(v___x_4900_, 8);
v_snapshotTasks_4909_ = lean_ctor_get(v___x_4900_, 9);
v_isSharedCheck_4938_ = !lean_is_exclusive(v___x_4900_);
if (v_isSharedCheck_4938_ == 0)
{
lean_object* v_unused_4939_; 
v_unused_4939_ = lean_ctor_get(v___x_4900_, 5);
lean_dec(v_unused_4939_);
v___x_4911_ = v___x_4900_;
v_isShared_4912_ = v_isSharedCheck_4938_;
goto v_resetjp_4910_;
}
else
{
lean_inc(v_snapshotTasks_4909_);
lean_inc(v_infoState_4908_);
lean_inc(v_messages_4907_);
lean_inc(v_recordedDeps_4906_);
lean_inc(v_traceState_4905_);
lean_inc(v_auxDeclNGen_4904_);
lean_inc(v_ngen_4903_);
lean_inc(v_nextMacroScope_4902_);
lean_inc(v_env_4901_);
lean_dec(v___x_4900_);
v___x_4911_ = lean_box(0);
v_isShared_4912_ = v_isSharedCheck_4938_;
goto v_resetjp_4910_;
}
v_resetjp_4910_:
{
uint8_t v___x_4913_; lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4918_; 
v___x_4913_ = 0;
v___x_4914_ = lean_box(0);
v___x_4915_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4901_, v_declName_4895_, v_s_4896_, v___x_4913_, v___x_4914_);
v___x_4916_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1);
if (v_isShared_4912_ == 0)
{
lean_ctor_set(v___x_4911_, 5, v___x_4916_);
lean_ctor_set(v___x_4911_, 0, v___x_4915_);
v___x_4918_ = v___x_4911_;
goto v_reusejp_4917_;
}
else
{
lean_object* v_reuseFailAlloc_4937_; 
v_reuseFailAlloc_4937_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4937_, 0, v___x_4915_);
lean_ctor_set(v_reuseFailAlloc_4937_, 1, v_nextMacroScope_4902_);
lean_ctor_set(v_reuseFailAlloc_4937_, 2, v_ngen_4903_);
lean_ctor_set(v_reuseFailAlloc_4937_, 3, v_auxDeclNGen_4904_);
lean_ctor_set(v_reuseFailAlloc_4937_, 4, v_traceState_4905_);
lean_ctor_set(v_reuseFailAlloc_4937_, 5, v___x_4916_);
lean_ctor_set(v_reuseFailAlloc_4937_, 6, v_recordedDeps_4906_);
lean_ctor_set(v_reuseFailAlloc_4937_, 7, v_messages_4907_);
lean_ctor_set(v_reuseFailAlloc_4937_, 8, v_infoState_4908_);
lean_ctor_set(v_reuseFailAlloc_4937_, 9, v_snapshotTasks_4909_);
v___x_4918_ = v_reuseFailAlloc_4937_;
goto v_reusejp_4917_;
}
v_reusejp_4917_:
{
lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v_mctx_4921_; lean_object* v_zetaDeltaFVarIds_4922_; lean_object* v_postponed_4923_; lean_object* v_diag_4924_; lean_object* v___x_4926_; uint8_t v_isShared_4927_; uint8_t v_isSharedCheck_4935_; 
v___x_4919_ = lean_st_ref_put(v___y_4898_, v___x_4918_);
v___x_4920_ = lean_st_ref_take(v___y_4897_);
v_mctx_4921_ = lean_ctor_get(v___x_4920_, 0);
v_zetaDeltaFVarIds_4922_ = lean_ctor_get(v___x_4920_, 2);
v_postponed_4923_ = lean_ctor_get(v___x_4920_, 3);
v_diag_4924_ = lean_ctor_get(v___x_4920_, 4);
v_isSharedCheck_4935_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_4935_ == 0)
{
lean_object* v_unused_4936_; 
v_unused_4936_ = lean_ctor_get(v___x_4920_, 1);
lean_dec(v_unused_4936_);
v___x_4926_ = v___x_4920_;
v_isShared_4927_ = v_isSharedCheck_4935_;
goto v_resetjp_4925_;
}
else
{
lean_inc(v_diag_4924_);
lean_inc(v_postponed_4923_);
lean_inc(v_zetaDeltaFVarIds_4922_);
lean_inc(v_mctx_4921_);
lean_dec(v___x_4920_);
v___x_4926_ = lean_box(0);
v_isShared_4927_ = v_isSharedCheck_4935_;
goto v_resetjp_4925_;
}
v_resetjp_4925_:
{
lean_object* v___x_4928_; lean_object* v___x_4929_; lean_object* v___x_4931_; 
v___x_4928_ = lean_box(0);
v___x_4929_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__5);
if (v_isShared_4927_ == 0)
{
lean_ctor_set(v___x_4926_, 1, v___x_4929_);
v___x_4931_ = v___x_4926_;
goto v_reusejp_4930_;
}
else
{
lean_object* v_reuseFailAlloc_4934_; 
v_reuseFailAlloc_4934_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4934_, 0, v_mctx_4921_);
lean_ctor_set(v_reuseFailAlloc_4934_, 1, v___x_4929_);
lean_ctor_set(v_reuseFailAlloc_4934_, 2, v_zetaDeltaFVarIds_4922_);
lean_ctor_set(v_reuseFailAlloc_4934_, 3, v_postponed_4923_);
lean_ctor_set(v_reuseFailAlloc_4934_, 4, v_diag_4924_);
v___x_4931_ = v_reuseFailAlloc_4934_;
goto v_reusejp_4930_;
}
v_reusejp_4930_:
{
lean_object* v___x_4932_; lean_object* v___x_4933_; 
v___x_4932_ = lean_st_ref_put(v___y_4897_, v___x_4931_);
v___x_4933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4933_, 0, v___x_4928_);
return v___x_4933_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4940_, lean_object* v_s_4941_, lean_object* v___y_4942_, lean_object* v___y_4943_, lean_object* v___y_4944_){
_start:
{
uint8_t v_s_boxed_4945_; lean_object* v_res_4946_; 
v_s_boxed_4945_ = lean_unbox(v_s_4941_);
v_res_4946_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4940_, v_s_boxed_4945_, v___y_4942_, v___y_4943_);
lean_dec(v___y_4943_);
lean_dec(v___y_4942_);
return v_res_4946_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4947_, uint8_t v_attrKind_4948_, lean_object* v_prio_4949_, lean_object* v_a_4950_, lean_object* v_a_4951_, lean_object* v_a_4952_, lean_object* v_a_4953_){
_start:
{
uint8_t v___x_4955_; lean_object* v___x_4956_; lean_object* v___x_4957_; 
v___x_4955_ = 4;
lean_inc(v_declName_4947_);
v___x_4956_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4947_, v___x_4955_, v_a_4951_, v_a_4953_);
lean_dec_ref(v___x_4956_);
v___x_4957_ = l_Lean_Meta_addInstance(v_declName_4947_, v_attrKind_4948_, v_prio_4949_, v_a_4950_, v_a_4951_, v_a_4952_, v_a_4953_);
return v___x_4957_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4958_, lean_object* v_attrKind_4959_, lean_object* v_prio_4960_, lean_object* v_a_4961_, lean_object* v_a_4962_, lean_object* v_a_4963_, lean_object* v_a_4964_, lean_object* v_a_4965_){
_start:
{
uint8_t v_attrKind_boxed_4966_; lean_object* v_res_4967_; 
v_attrKind_boxed_4966_ = lean_unbox(v_attrKind_4959_);
v_res_4967_ = l_Lean_Meta_registerInstance(v_declName_4958_, v_attrKind_boxed_4966_, v_prio_4960_, v_a_4961_, v_a_4962_, v_a_4963_, v_a_4964_);
lean_dec(v_a_4964_);
lean_dec_ref(v_a_4963_);
lean_dec(v_a_4962_);
lean_dec_ref(v_a_4961_);
return v_res_4967_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4968_, uint8_t v_s_4969_, lean_object* v___y_4970_, lean_object* v___y_4971_, lean_object* v___y_4972_, lean_object* v___y_4973_){
_start:
{
lean_object* v___x_4975_; 
v___x_4975_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4968_, v_s_4969_, v___y_4971_, v___y_4973_);
return v___x_4975_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4976_, lean_object* v_s_4977_, lean_object* v___y_4978_, lean_object* v___y_4979_, lean_object* v___y_4980_, lean_object* v___y_4981_, lean_object* v___y_4982_){
_start:
{
uint8_t v_s_boxed_4983_; lean_object* v_res_4984_; 
v_s_boxed_4983_ = lean_unbox(v_s_4977_);
v_res_4984_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4976_, v_s_boxed_4983_, v___y_4978_, v___y_4979_, v___y_4980_, v___y_4981_);
lean_dec(v___y_4981_);
lean_dec_ref(v___y_4980_);
lean_dec(v___y_4979_);
lean_dec_ref(v___y_4978_);
return v_res_4984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4985_, lean_object* v_x_4986_){
_start:
{
lean_inc_ref(v_a_4985_);
return v_a_4985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4987_, lean_object* v_x_4988_){
_start:
{
lean_object* v_res_4989_; 
v_res_4989_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4987_, v_x_4988_);
lean_dec_ref(v_x_4988_);
lean_dec_ref(v_a_4987_);
return v_res_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4990_, lean_object* v___y_4991_, lean_object* v___y_4992_){
_start:
{
lean_object* v___x_4994_; lean_object* v_toCold_4995_; lean_object* v_env_4996_; lean_object* v_options_4997_; uint8_t v___x_4998_; lean_object* v_env_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; 
v___x_4994_ = lean_st_ref_get(v___y_4992_);
v_toCold_4995_ = lean_ctor_get(v___y_4991_, 0);
v_env_4996_ = lean_ctor_get(v___x_4994_, 0);
lean_inc_ref(v_env_4996_);
lean_dec(v___x_4994_);
v_options_4997_ = lean_ctor_get(v_toCold_4995_, 2);
v___x_4998_ = 0;
v_env_4999_ = l_Lean_Environment_setRecordingDeps(v_env_4996_, v___x_4998_);
v___x_5000_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__1);
v___x_5001_ = lean_unsigned_to_nat(32u);
v___x_5002_ = lean_mk_empty_array_with_capacity(v___x_5001_);
lean_dec_ref(v___x_5002_);
v___x_5003_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__4);
lean_inc_ref(v_options_4997_);
v___x_5004_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_5004_, 0, v_env_4999_);
lean_ctor_set(v___x_5004_, 1, v___x_5000_);
lean_ctor_set(v___x_5004_, 2, v___x_5003_);
lean_ctor_set(v___x_5004_, 3, v_options_4997_);
v___x_5005_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_5005_, 0, v___x_5004_);
lean_ctor_set(v___x_5005_, 1, v_msgData_4990_);
v___x_5006_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5005_);
return v___x_5006_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_5007_, lean_object* v___y_5008_, lean_object* v___y_5009_, lean_object* v___y_5010_){
_start:
{
lean_object* v_res_5011_; 
v_res_5011_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_5007_, v___y_5008_, v___y_5009_);
lean_dec(v___y_5009_);
lean_dec_ref(v___y_5008_);
return v_res_5011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_5012_, lean_object* v___y_5013_, lean_object* v___y_5014_){
_start:
{
lean_object* v_ref_5016_; lean_object* v___x_5017_; lean_object* v_a_5018_; lean_object* v___x_5020_; uint8_t v_isShared_5021_; uint8_t v_isSharedCheck_5026_; 
v_ref_5016_ = lean_ctor_get(v___y_5013_, 2);
v___x_5017_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_5012_, v___y_5013_, v___y_5014_);
v_a_5018_ = lean_ctor_get(v___x_5017_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_5017_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5020_ = v___x_5017_;
v_isShared_5021_ = v_isSharedCheck_5026_;
goto v_resetjp_5019_;
}
else
{
lean_inc(v_a_5018_);
lean_dec(v___x_5017_);
v___x_5020_ = lean_box(0);
v_isShared_5021_ = v_isSharedCheck_5026_;
goto v_resetjp_5019_;
}
v_resetjp_5019_:
{
lean_object* v___x_5022_; lean_object* v___x_5024_; 
lean_inc(v_ref_5016_);
v___x_5022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5022_, 0, v_ref_5016_);
lean_ctor_set(v___x_5022_, 1, v_a_5018_);
if (v_isShared_5021_ == 0)
{
lean_ctor_set_tag(v___x_5020_, 1);
lean_ctor_set(v___x_5020_, 0, v___x_5022_);
v___x_5024_ = v___x_5020_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v___x_5022_);
v___x_5024_ = v_reuseFailAlloc_5025_;
goto v_reusejp_5023_;
}
v_reusejp_5023_:
{
return v___x_5024_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_5027_, lean_object* v___y_5028_, lean_object* v___y_5029_, lean_object* v___y_5030_){
_start:
{
lean_object* v_res_5031_; 
v_res_5031_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_5027_, v___y_5028_, v___y_5029_);
lean_dec(v___y_5029_);
lean_dec_ref(v___y_5028_);
return v_res_5031_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_5032_, lean_object* v_i_5033_, lean_object* v_k_5034_){
_start:
{
lean_object* v___x_5035_; uint8_t v___x_5036_; 
v___x_5035_ = lean_array_get_size(v_keys_5032_);
v___x_5036_ = lean_nat_dec_lt(v_i_5033_, v___x_5035_);
if (v___x_5036_ == 0)
{
lean_dec(v_i_5033_);
return v___x_5036_;
}
else
{
lean_object* v_k_x27_5037_; uint8_t v___x_5038_; 
v_k_x27_5037_ = lean_array_fget_borrowed(v_keys_5032_, v_i_5033_);
v___x_5038_ = lean_name_eq(v_k_5034_, v_k_x27_5037_);
if (v___x_5038_ == 0)
{
lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5039_ = lean_unsigned_to_nat(1u);
v___x_5040_ = lean_nat_add(v_i_5033_, v___x_5039_);
lean_dec(v_i_5033_);
v_i_5033_ = v___x_5040_;
goto _start;
}
else
{
lean_dec(v_i_5033_);
return v___x_5036_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_5042_, lean_object* v_i_5043_, lean_object* v_k_5044_){
_start:
{
uint8_t v_res_5045_; lean_object* v_r_5046_; 
v_res_5045_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_5042_, v_i_5043_, v_k_5044_);
lean_dec(v_k_5044_);
lean_dec_ref(v_keys_5042_);
v_r_5046_ = lean_box(v_res_5045_);
return v_r_5046_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_5047_, size_t v_x_5048_, lean_object* v_x_5049_){
_start:
{
if (lean_obj_tag(v_x_5047_) == 0)
{
lean_object* v_es_5050_; lean_object* v___x_5051_; size_t v___x_5052_; size_t v___x_5053_; lean_object* v_j_5054_; lean_object* v___x_5055_; 
v_es_5050_ = lean_ctor_get(v_x_5047_, 0);
v___x_5051_ = lean_box(2);
v___x_5052_ = ((size_t)31ULL);
v___x_5053_ = lean_usize_land(v_x_5048_, v___x_5052_);
v_j_5054_ = lean_usize_to_nat(v___x_5053_);
v___x_5055_ = lean_array_get_borrowed(v___x_5051_, v_es_5050_, v_j_5054_);
lean_dec(v_j_5054_);
switch(lean_obj_tag(v___x_5055_))
{
case 0:
{
lean_object* v_key_5056_; uint8_t v___x_5057_; 
v_key_5056_ = lean_ctor_get(v___x_5055_, 0);
v___x_5057_ = lean_name_eq(v_x_5049_, v_key_5056_);
return v___x_5057_;
}
case 1:
{
lean_object* v_node_5058_; size_t v___x_5059_; size_t v___x_5060_; 
v_node_5058_ = lean_ctor_get(v___x_5055_, 0);
v___x_5059_ = ((size_t)5ULL);
v___x_5060_ = lean_usize_shift_right(v_x_5048_, v___x_5059_);
v_x_5047_ = v_node_5058_;
v_x_5048_ = v___x_5060_;
goto _start;
}
default: 
{
uint8_t v___x_5062_; 
v___x_5062_ = 0;
return v___x_5062_;
}
}
}
else
{
lean_object* v_ks_5063_; lean_object* v___x_5064_; uint8_t v___x_5065_; 
v_ks_5063_ = lean_ctor_get(v_x_5047_, 0);
v___x_5064_ = lean_unsigned_to_nat(0u);
v___x_5065_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_5063_, v___x_5064_, v_x_5049_);
return v___x_5065_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_5066_, lean_object* v_x_5067_, lean_object* v_x_5068_){
_start:
{
size_t v_x_2480__boxed_5069_; uint8_t v_res_5070_; lean_object* v_r_5071_; 
v_x_2480__boxed_5069_ = lean_unbox_usize(v_x_5067_);
lean_dec(v_x_5067_);
v_res_5070_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5066_, v_x_2480__boxed_5069_, v_x_5068_);
lean_dec(v_x_5068_);
lean_dec_ref(v_x_5066_);
v_r_5071_ = lean_box(v_res_5070_);
return v_r_5071_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_5072_, lean_object* v_x_5073_){
_start:
{
uint64_t v___y_5075_; 
if (lean_obj_tag(v_x_5073_) == 0)
{
uint64_t v___x_5078_; 
v___x_5078_ = 1723ULL;
v___y_5075_ = v___x_5078_;
goto v___jp_5074_;
}
else
{
uint64_t v_hash_5079_; 
v_hash_5079_ = lean_ctor_get_uint64(v_x_5073_, sizeof(void*)*2);
v___y_5075_ = v_hash_5079_;
goto v___jp_5074_;
}
v___jp_5074_:
{
size_t v___x_5076_; uint8_t v___x_5077_; 
v___x_5076_ = lean_uint64_to_usize(v___y_5075_);
v___x_5077_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5072_, v___x_5076_, v_x_5073_);
return v___x_5077_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_5080_, lean_object* v_x_5081_){
_start:
{
uint8_t v_res_5082_; lean_object* v_r_5083_; 
v_res_5082_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_5080_, v_x_5081_);
lean_dec(v_x_5081_);
lean_dec_ref(v_x_5080_);
v_r_5083_ = lean_box(v_res_5082_);
return v_r_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_5084_, lean_object* v_declName_5085_, lean_object* v___y_5086_, lean_object* v___y_5087_){
_start:
{
lean_object* v_instanceNames_5092_; uint8_t v___x_5093_; 
v_instanceNames_5092_ = lean_ctor_get(v_d_5084_, 1);
v___x_5093_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_5092_, v_declName_5085_);
if (v___x_5093_ == 0)
{
lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v___x_5098_; lean_object* v___x_5099_; lean_object* v_a_5100_; lean_object* v___x_5102_; uint8_t v_isShared_5103_; uint8_t v_isSharedCheck_5107_; 
lean_dec_ref(v_d_5084_);
v___x_5094_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5095_ = l_Lean_MessageData_ofConstName(v_declName_5085_, v___x_5093_);
v___x_5096_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5096_, 0, v___x_5094_);
lean_ctor_set(v___x_5096_, 1, v___x_5095_);
v___x_5097_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_5098_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5098_, 0, v___x_5096_);
lean_ctor_set(v___x_5098_, 1, v___x_5097_);
v___x_5099_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5098_, v___y_5086_, v___y_5087_);
v_a_5100_ = lean_ctor_get(v___x_5099_, 0);
v_isSharedCheck_5107_ = !lean_is_exclusive(v___x_5099_);
if (v_isSharedCheck_5107_ == 0)
{
v___x_5102_ = v___x_5099_;
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
else
{
lean_inc(v_a_5100_);
lean_dec(v___x_5099_);
v___x_5102_ = lean_box(0);
v_isShared_5103_ = v_isSharedCheck_5107_;
goto v_resetjp_5101_;
}
v_resetjp_5101_:
{
lean_object* v___x_5105_; 
if (v_isShared_5103_ == 0)
{
v___x_5105_ = v___x_5102_;
goto v_reusejp_5104_;
}
else
{
lean_object* v_reuseFailAlloc_5106_; 
v_reuseFailAlloc_5106_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5106_, 0, v_a_5100_);
v___x_5105_ = v_reuseFailAlloc_5106_;
goto v_reusejp_5104_;
}
v_reusejp_5104_:
{
return v___x_5105_;
}
}
}
else
{
goto v___jp_5089_;
}
v___jp_5089_:
{
lean_object* v___x_5090_; lean_object* v___x_5091_; 
v___x_5090_ = l_Lean_Meta_Instances_eraseCore(v_d_5084_, v_declName_5085_);
v___x_5091_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5091_, 0, v___x_5090_);
return v___x_5091_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_5108_, lean_object* v_declName_5109_, lean_object* v___y_5110_, lean_object* v___y_5111_, lean_object* v___y_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_5108_, v_declName_5109_, v___y_5110_, v___y_5111_);
lean_dec(v___y_5111_);
lean_dec_ref(v___y_5110_);
return v_res_5113_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_5114_, lean_object* v_declName_5115_, lean_object* v___y_5116_, lean_object* v___y_5117_){
_start:
{
lean_object* v___x_5119_; lean_object* v_env_5120_; lean_object* v___x_5121_; lean_object* v_ext_5122_; lean_object* v_toEnvExtension_5123_; lean_object* v_asyncMode_5124_; uint8_t v___x_5125_; lean_object* v___x_5126_; lean_object* v___x_5127_; 
v___x_5119_ = lean_st_ref_get(v___y_5117_);
v_env_5120_ = lean_ctor_get(v___x_5119_, 0);
lean_inc_ref(v_env_5120_);
lean_dec(v___x_5119_);
v___x_5121_ = l_Lean_Meta_instanceExtension;
v_ext_5122_ = lean_ctor_get(v___x_5121_, 1);
v_toEnvExtension_5123_ = lean_ctor_get(v_ext_5122_, 0);
v_asyncMode_5124_ = lean_ctor_get(v_toEnvExtension_5123_, 2);
v___x_5125_ = 0;
v___x_5126_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5114_, v___x_5121_, v_env_5120_, v_asyncMode_5124_, v___x_5125_);
v___x_5127_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_5126_, v_declName_5115_, v___y_5116_, v___y_5117_);
if (lean_obj_tag(v___x_5127_) == 0)
{
lean_object* v_a_5128_; lean_object* v___x_5130_; uint8_t v_isShared_5131_; uint8_t v_isSharedCheck_5158_; 
v_a_5128_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5158_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5158_ == 0)
{
v___x_5130_ = v___x_5127_;
v_isShared_5131_ = v_isSharedCheck_5158_;
goto v_resetjp_5129_;
}
else
{
lean_inc(v_a_5128_);
lean_dec(v___x_5127_);
v___x_5130_ = lean_box(0);
v_isShared_5131_ = v_isSharedCheck_5158_;
goto v_resetjp_5129_;
}
v_resetjp_5129_:
{
lean_object* v___f_5132_; lean_object* v___x_5133_; lean_object* v_env_5134_; lean_object* v_nextMacroScope_5135_; lean_object* v_ngen_5136_; lean_object* v_auxDeclNGen_5137_; lean_object* v_traceState_5138_; lean_object* v_recordedDeps_5139_; lean_object* v_messages_5140_; lean_object* v_infoState_5141_; lean_object* v_snapshotTasks_5142_; lean_object* v___x_5144_; uint8_t v_isShared_5145_; uint8_t v_isSharedCheck_5156_; 
v___f_5132_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_5132_, 0, v_a_5128_);
v___x_5133_ = lean_st_ref_take(v___y_5117_);
v_env_5134_ = lean_ctor_get(v___x_5133_, 0);
v_nextMacroScope_5135_ = lean_ctor_get(v___x_5133_, 1);
v_ngen_5136_ = lean_ctor_get(v___x_5133_, 2);
v_auxDeclNGen_5137_ = lean_ctor_get(v___x_5133_, 3);
v_traceState_5138_ = lean_ctor_get(v___x_5133_, 4);
v_recordedDeps_5139_ = lean_ctor_get(v___x_5133_, 6);
v_messages_5140_ = lean_ctor_get(v___x_5133_, 7);
v_infoState_5141_ = lean_ctor_get(v___x_5133_, 8);
v_snapshotTasks_5142_ = lean_ctor_get(v___x_5133_, 9);
v_isSharedCheck_5156_ = !lean_is_exclusive(v___x_5133_);
if (v_isSharedCheck_5156_ == 0)
{
lean_object* v_unused_5157_; 
v_unused_5157_ = lean_ctor_get(v___x_5133_, 5);
lean_dec(v_unused_5157_);
v___x_5144_ = v___x_5133_;
v_isShared_5145_ = v_isSharedCheck_5156_;
goto v_resetjp_5143_;
}
else
{
lean_inc(v_snapshotTasks_5142_);
lean_inc(v_infoState_5141_);
lean_inc(v_messages_5140_);
lean_inc(v_recordedDeps_5139_);
lean_inc(v_traceState_5138_);
lean_inc(v_auxDeclNGen_5137_);
lean_inc(v_ngen_5136_);
lean_inc(v_nextMacroScope_5135_);
lean_inc(v_env_5134_);
lean_dec(v___x_5133_);
v___x_5144_ = lean_box(0);
v_isShared_5145_ = v_isSharedCheck_5156_;
goto v_resetjp_5143_;
}
v_resetjp_5143_:
{
lean_object* v___x_5146_; lean_object* v___x_5147_; lean_object* v___x_5148_; lean_object* v___x_5150_; 
v___x_5146_ = lean_box(0);
v___x_5147_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_5121_, v_env_5134_, v___f_5132_);
v___x_5148_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1);
if (v_isShared_5145_ == 0)
{
lean_ctor_set(v___x_5144_, 5, v___x_5148_);
lean_ctor_set(v___x_5144_, 0, v___x_5147_);
v___x_5150_ = v___x_5144_;
goto v_reusejp_5149_;
}
else
{
lean_object* v_reuseFailAlloc_5155_; 
v_reuseFailAlloc_5155_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5155_, 0, v___x_5147_);
lean_ctor_set(v_reuseFailAlloc_5155_, 1, v_nextMacroScope_5135_);
lean_ctor_set(v_reuseFailAlloc_5155_, 2, v_ngen_5136_);
lean_ctor_set(v_reuseFailAlloc_5155_, 3, v_auxDeclNGen_5137_);
lean_ctor_set(v_reuseFailAlloc_5155_, 4, v_traceState_5138_);
lean_ctor_set(v_reuseFailAlloc_5155_, 5, v___x_5148_);
lean_ctor_set(v_reuseFailAlloc_5155_, 6, v_recordedDeps_5139_);
lean_ctor_set(v_reuseFailAlloc_5155_, 7, v_messages_5140_);
lean_ctor_set(v_reuseFailAlloc_5155_, 8, v_infoState_5141_);
lean_ctor_set(v_reuseFailAlloc_5155_, 9, v_snapshotTasks_5142_);
v___x_5150_ = v_reuseFailAlloc_5155_;
goto v_reusejp_5149_;
}
v_reusejp_5149_:
{
lean_object* v___x_5151_; lean_object* v___x_5153_; 
v___x_5151_ = lean_st_ref_put(v___y_5117_, v___x_5150_);
if (v_isShared_5131_ == 0)
{
lean_ctor_set(v___x_5130_, 0, v___x_5146_);
v___x_5153_ = v___x_5130_;
goto v_reusejp_5152_;
}
else
{
lean_object* v_reuseFailAlloc_5154_; 
v_reuseFailAlloc_5154_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5154_, 0, v___x_5146_);
v___x_5153_ = v_reuseFailAlloc_5154_;
goto v_reusejp_5152_;
}
v_reusejp_5152_:
{
return v___x_5153_;
}
}
}
}
}
else
{
lean_object* v_a_5159_; lean_object* v___x_5161_; uint8_t v_isShared_5162_; uint8_t v_isSharedCheck_5166_; 
v_a_5159_ = lean_ctor_get(v___x_5127_, 0);
v_isSharedCheck_5166_ = !lean_is_exclusive(v___x_5127_);
if (v_isSharedCheck_5166_ == 0)
{
v___x_5161_ = v___x_5127_;
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
else
{
lean_inc(v_a_5159_);
lean_dec(v___x_5127_);
v___x_5161_ = lean_box(0);
v_isShared_5162_ = v_isSharedCheck_5166_;
goto v_resetjp_5160_;
}
v_resetjp_5160_:
{
lean_object* v___x_5164_; 
if (v_isShared_5162_ == 0)
{
v___x_5164_ = v___x_5161_;
goto v_reusejp_5163_;
}
else
{
lean_object* v_reuseFailAlloc_5165_; 
v_reuseFailAlloc_5165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5165_, 0, v_a_5159_);
v___x_5164_ = v_reuseFailAlloc_5165_;
goto v_reusejp_5163_;
}
v_reusejp_5163_:
{
return v___x_5164_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_5167_, lean_object* v_declName_5168_, lean_object* v___y_5169_, lean_object* v___y_5170_, lean_object* v___y_5171_){
_start:
{
lean_object* v_res_5172_; 
v_res_5172_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_5167_, v_declName_5168_, v___y_5169_, v___y_5170_);
lean_dec(v___y_5170_);
lean_dec_ref(v___y_5169_);
lean_dec_ref(v___x_5167_);
return v_res_5172_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5179_; uint64_t v___x_5180_; 
v___x_5179_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5180_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_5179_);
return v___x_5180_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_5181_; lean_object* v___x_5182_; lean_object* v___x_5183_; 
v___x_5181_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5182_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5183_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_5183_, 0, v___x_5182_);
lean_ctor_set_uint64(v___x_5183_, sizeof(void*)*1, v___x_5181_);
return v___x_5183_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5184_; lean_object* v___x_5185_; 
v___x_5184_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_5185_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5185_, 0, v___x_5184_);
return v___x_5185_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5186_; lean_object* v___x_5187_; 
v___x_5186_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5187_, 0, v___x_5186_);
lean_ctor_set(v___x_5187_, 1, v___x_5186_);
return v___x_5187_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5188_; lean_object* v___x_5189_; 
v___x_5188_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5189_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5189_, 0, v___x_5188_);
lean_ctor_set(v___x_5189_, 1, v___x_5188_);
lean_ctor_set(v___x_5189_, 2, v___x_5188_);
lean_ctor_set(v___x_5189_, 3, v___x_5188_);
lean_ctor_set(v___x_5189_, 4, v___x_5188_);
return v___x_5189_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_5190_, lean_object* v___x_5191_, lean_object* v_declName_5192_, lean_object* v_stx_5193_, uint8_t v_attrKind_5194_, lean_object* v___y_5195_, lean_object* v___y_5196_){
_start:
{
lean_object* v___x_5198_; lean_object* v___x_5199_; lean_object* v___x_5200_; 
v___x_5198_ = lean_unsigned_to_nat(1u);
v___x_5199_ = l_Lean_Syntax_getArg(v_stx_5193_, v___x_5198_);
v___x_5200_ = l_Lean_getAttrParamOptPrio(v___x_5199_, v___y_5195_, v___y_5196_);
if (lean_obj_tag(v___x_5200_) == 0)
{
lean_object* v_a_5201_; uint8_t v___x_5202_; uint8_t v___x_5203_; lean_object* v___x_5204_; lean_object* v___x_5205_; lean_object* v___x_5206_; lean_object* v___x_5207_; lean_object* v___x_5208_; size_t v___x_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; lean_object* v___x_5212_; lean_object* v___x_5213_; lean_object* v___x_5214_; lean_object* v___x_5215_; lean_object* v___x_5216_; lean_object* v___x_5217_; lean_object* v___x_5218_; lean_object* v___x_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v___x_5223_; lean_object* v___x_5224_; lean_object* v___x_5225_; 
v_a_5201_ = lean_ctor_get(v___x_5200_, 0);
lean_inc(v_a_5201_);
lean_dec_ref_known(v___x_5200_, 1);
v___x_5202_ = 0;
v___x_5203_ = 1;
v___x_5204_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5205_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5206_ = lean_unsigned_to_nat(32u);
v___x_5207_ = lean_mk_empty_array_with_capacity(v___x_5206_);
v___x_5208_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__2);
v___x_5209_ = ((size_t)5ULL);
lean_inc_n(v___x_5190_, 7);
v___x_5210_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_5210_, 0, v___x_5208_);
lean_ctor_set(v___x_5210_, 1, v___x_5207_);
lean_ctor_set(v___x_5210_, 2, v___x_5190_);
lean_ctor_set(v___x_5210_, 3, v___x_5190_);
lean_ctor_set_usize(v___x_5210_, 4, v___x_5209_);
v___x_5211_ = lean_box(1);
lean_inc_ref(v___x_5210_);
v___x_5212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5212_, 0, v___x_5205_);
lean_ctor_set(v___x_5212_, 1, v___x_5210_);
lean_ctor_set(v___x_5212_, 2, v___x_5211_);
v___x_5213_ = lean_mk_empty_array_with_capacity(v___x_5190_);
v___x_5214_ = lean_box(0);
lean_inc(v___x_5191_);
v___x_5215_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5215_, 0, v___x_5204_);
lean_ctor_set(v___x_5215_, 1, v___x_5191_);
lean_ctor_set(v___x_5215_, 2, v___x_5212_);
lean_ctor_set(v___x_5215_, 3, v___x_5213_);
lean_ctor_set(v___x_5215_, 4, v___x_5214_);
lean_ctor_set(v___x_5215_, 5, v___x_5190_);
lean_ctor_set(v___x_5215_, 6, v___x_5214_);
lean_ctor_set_uint8(v___x_5215_, sizeof(void*)*7, v___x_5202_);
lean_ctor_set_uint8(v___x_5215_, sizeof(void*)*7 + 1, v___x_5202_);
lean_ctor_set_uint8(v___x_5215_, sizeof(void*)*7 + 2, v___x_5202_);
lean_ctor_set_uint8(v___x_5215_, sizeof(void*)*7 + 3, v___x_5203_);
v___x_5216_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5216_, 0, v___x_5190_);
lean_ctor_set(v___x_5216_, 1, v___x_5190_);
lean_ctor_set(v___x_5216_, 2, v___x_5190_);
lean_ctor_set(v___x_5216_, 3, v___x_5190_);
lean_ctor_set(v___x_5216_, 4, v___x_5205_);
lean_ctor_set(v___x_5216_, 5, v___x_5205_);
lean_ctor_set(v___x_5216_, 6, v___x_5205_);
lean_ctor_set(v___x_5216_, 7, v___x_5205_);
lean_ctor_set(v___x_5216_, 8, v___x_5205_);
lean_ctor_set(v___x_5216_, 9, v___x_5205_);
lean_ctor_set(v___x_5216_, 10, v___x_5205_);
v___x_5217_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2);
v___x_5218_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5219_, 0, v___x_5205_);
lean_ctor_set(v___x_5219_, 1, v___x_5205_);
lean_ctor_set(v___x_5219_, 2, v___x_5190_);
v___x_5220_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_5220_, 0, v___x_5217_);
lean_ctor_set(v___x_5220_, 1, v___x_5205_);
lean_ctor_set(v___x_5220_, 2, v___x_5218_);
lean_ctor_set(v___x_5220_, 3, v___x_5205_);
lean_ctor_set(v___x_5220_, 4, v___x_5205_);
lean_ctor_set(v___x_5220_, 5, v___x_5205_);
lean_ctor_set(v___x_5220_, 6, v___x_5205_);
lean_ctor_set(v___x_5220_, 7, v___x_5219_);
v___x_5221_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5222_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5222_, 0, v___x_5216_);
lean_ctor_set(v___x_5222_, 1, v___x_5220_);
lean_ctor_set(v___x_5222_, 2, v___x_5191_);
lean_ctor_set(v___x_5222_, 3, v___x_5210_);
lean_ctor_set(v___x_5222_, 4, v___x_5221_);
v___x_5223_ = lean_box(0);
v___x_5224_ = lean_st_mk_ref(v___x_5222_);
v___x_5225_ = l_Lean_Meta_addInstance(v_declName_5192_, v_attrKind_5194_, v_a_5201_, v___x_5215_, v___x_5224_, v___y_5195_, v___y_5196_);
lean_dec_ref_known(v___x_5215_, 7);
if (lean_obj_tag(v___x_5225_) == 0)
{
lean_object* v___x_5227_; uint8_t v_isShared_5228_; uint8_t v_isSharedCheck_5233_; 
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5225_);
if (v_isSharedCheck_5233_ == 0)
{
lean_object* v_unused_5234_; 
v_unused_5234_ = lean_ctor_get(v___x_5225_, 0);
lean_dec(v_unused_5234_);
v___x_5227_ = v___x_5225_;
v_isShared_5228_ = v_isSharedCheck_5233_;
goto v_resetjp_5226_;
}
else
{
lean_dec(v___x_5225_);
v___x_5227_ = lean_box(0);
v_isShared_5228_ = v_isSharedCheck_5233_;
goto v_resetjp_5226_;
}
v_resetjp_5226_:
{
lean_object* v___x_5229_; lean_object* v___x_5231_; 
v___x_5229_ = lean_st_ref_get(v___x_5224_);
lean_dec(v___x_5224_);
lean_dec(v___x_5229_);
if (v_isShared_5228_ == 0)
{
lean_ctor_set(v___x_5227_, 0, v___x_5223_);
v___x_5231_ = v___x_5227_;
goto v_reusejp_5230_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v___x_5223_);
v___x_5231_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5230_;
}
v_reusejp_5230_:
{
return v___x_5231_;
}
}
}
else
{
lean_dec(v___x_5224_);
return v___x_5225_;
}
}
else
{
lean_object* v_a_5235_; lean_object* v___x_5237_; uint8_t v_isShared_5238_; uint8_t v_isSharedCheck_5242_; 
lean_dec(v_declName_5192_);
lean_dec(v___x_5191_);
lean_dec(v___x_5190_);
v_a_5235_ = lean_ctor_get(v___x_5200_, 0);
v_isSharedCheck_5242_ = !lean_is_exclusive(v___x_5200_);
if (v_isSharedCheck_5242_ == 0)
{
v___x_5237_ = v___x_5200_;
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
else
{
lean_inc(v_a_5235_);
lean_dec(v___x_5200_);
v___x_5237_ = lean_box(0);
v_isShared_5238_ = v_isSharedCheck_5242_;
goto v_resetjp_5236_;
}
v_resetjp_5236_:
{
lean_object* v___x_5240_; 
if (v_isShared_5238_ == 0)
{
v___x_5240_ = v___x_5237_;
goto v_reusejp_5239_;
}
else
{
lean_object* v_reuseFailAlloc_5241_; 
v_reuseFailAlloc_5241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5241_, 0, v_a_5235_);
v___x_5240_ = v_reuseFailAlloc_5241_;
goto v_reusejp_5239_;
}
v_reusejp_5239_:
{
return v___x_5240_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_5243_, lean_object* v___x_5244_, lean_object* v_declName_5245_, lean_object* v_stx_5246_, lean_object* v_attrKind_5247_, lean_object* v___y_5248_, lean_object* v___y_5249_, lean_object* v___y_5250_){
_start:
{
uint8_t v_attrKind_boxed_5251_; lean_object* v_res_5252_; 
v_attrKind_boxed_5251_ = lean_unbox(v_attrKind_5247_);
v_res_5252_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_5243_, v___x_5244_, v_declName_5245_, v_stx_5246_, v_attrKind_boxed_5251_, v___y_5248_, v___y_5249_);
lean_dec(v___y_5249_);
lean_dec_ref(v___y_5248_);
lean_dec(v_stx_5246_);
return v_res_5252_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5253_; lean_object* v___f_5254_; 
v___x_5253_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_5254_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_5254_, 0, v___x_5253_);
return v___f_5254_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_5321_; lean_object* v___f_5322_; lean_object* v___x_5323_; lean_object* v___x_5324_; 
v___f_5321_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_5322_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5323_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5324_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5324_, 0, v___x_5323_);
lean_ctor_set(v___x_5324_, 1, v___f_5322_);
lean_ctor_set(v___x_5324_, 2, v___f_5321_);
return v___x_5324_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5326_; lean_object* v___x_5327_; 
v___x_5326_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5327_ = l_Lean_registerBuiltinAttribute(v___x_5326_);
return v___x_5327_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5328_){
_start:
{
lean_object* v_res_5329_; 
v_res_5329_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5329_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_5330_, lean_object* v_x_5331_, lean_object* v_x_5332_){
_start:
{
uint8_t v___x_5333_; 
v___x_5333_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_5331_, v_x_5332_);
return v___x_5333_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_5334_, lean_object* v_x_5335_, lean_object* v_x_5336_){
_start:
{
uint8_t v_res_5337_; lean_object* v_r_5338_; 
v_res_5337_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_5334_, v_x_5335_, v_x_5336_);
lean_dec(v_x_5336_);
lean_dec_ref(v_x_5335_);
v_r_5338_ = lean_box(v_res_5337_);
return v_r_5338_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_5339_, lean_object* v_msg_5340_, lean_object* v___y_5341_, lean_object* v___y_5342_){
_start:
{
lean_object* v___x_5344_; 
v___x_5344_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_5340_, v___y_5341_, v___y_5342_);
return v___x_5344_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_5345_, lean_object* v_msg_5346_, lean_object* v___y_5347_, lean_object* v___y_5348_, lean_object* v___y_5349_){
_start:
{
lean_object* v_res_5350_; 
v_res_5350_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_5345_, v_msg_5346_, v___y_5347_, v___y_5348_);
lean_dec(v___y_5348_);
lean_dec_ref(v___y_5347_);
return v_res_5350_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5351_, lean_object* v_x_5352_, size_t v_x_5353_, lean_object* v_x_5354_){
_start:
{
uint8_t v___x_5355_; 
v___x_5355_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5352_, v_x_5353_, v_x_5354_);
return v___x_5355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5356_, lean_object* v_x_5357_, lean_object* v_x_5358_, lean_object* v_x_5359_){
_start:
{
size_t v_x_3128__boxed_5360_; uint8_t v_res_5361_; lean_object* v_r_5362_; 
v_x_3128__boxed_5360_ = lean_unbox_usize(v_x_5358_);
lean_dec(v_x_5358_);
v_res_5361_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_5356_, v_x_5357_, v_x_3128__boxed_5360_, v_x_5359_);
lean_dec(v_x_5359_);
lean_dec_ref(v_x_5357_);
v_r_5362_ = lean_box(v_res_5361_);
return v_r_5362_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5363_, lean_object* v_keys_5364_, lean_object* v_vals_5365_, lean_object* v_heq_5366_, lean_object* v_i_5367_, lean_object* v_k_5368_){
_start:
{
uint8_t v___x_5369_; 
v___x_5369_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_5364_, v_i_5367_, v_k_5368_);
return v___x_5369_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5370_, lean_object* v_keys_5371_, lean_object* v_vals_5372_, lean_object* v_heq_5373_, lean_object* v_i_5374_, lean_object* v_k_5375_){
_start:
{
uint8_t v_res_5376_; lean_object* v_r_5377_; 
v_res_5376_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_5370_, v_keys_5371_, v_vals_5372_, v_heq_5373_, v_i_5374_, v_k_5375_);
lean_dec(v_k_5375_);
lean_dec_ref(v_vals_5372_);
lean_dec_ref(v_keys_5371_);
v_r_5377_ = lean_box(v_res_5376_);
return v_r_5377_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5380_; lean_object* v___x_5381_; lean_object* v___x_5382_; 
v___x_5380_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5381_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5382_ = l_Lean_addBuiltinDocString(v___x_5380_, v___x_5381_);
return v___x_5382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5383_){
_start:
{
lean_object* v_res_5384_; 
v_res_5384_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5384_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_5385_){
_start:
{
lean_object* v___x_5387_; lean_object* v___x_5388_; lean_object* v_env_5389_; lean_object* v___x_5390_; lean_object* v_ext_5391_; lean_object* v_toEnvExtension_5392_; lean_object* v_asyncMode_5393_; uint8_t v___x_5394_; lean_object* v___x_5395_; lean_object* v_discrTree_5396_; lean_object* v___x_5397_; 
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
v_discrTree_5396_ = lean_ctor_get(v___x_5395_, 0);
lean_inc_ref(v_discrTree_5396_);
lean_dec(v___x_5395_);
v___x_5397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5397_, 0, v_discrTree_5396_);
return v___x_5397_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_5398_, lean_object* v_a_5399_){
_start:
{
lean_object* v_res_5400_; 
v_res_5400_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5398_);
lean_dec(v_a_5398_);
return v_res_5400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_5401_, lean_object* v_a_5402_){
_start:
{
lean_object* v___x_5404_; 
v___x_5404_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5402_);
return v___x_5404_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_5405_, lean_object* v_a_5406_, lean_object* v_a_5407_){
_start:
{
lean_object* v_res_5408_; 
v_res_5408_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_5405_, v_a_5406_);
lean_dec(v_a_5406_);
lean_dec_ref(v_a_5405_);
return v_res_5408_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceClassChanges(lean_object* v_env_5409_, lean_object* v_className_5410_){
_start:
{
lean_object* v___x_5411_; lean_object* v_ext_5412_; lean_object* v_toEnvExtension_5413_; lean_object* v_asyncMode_5414_; lean_object* v___x_5415_; uint8_t v___x_5416_; lean_object* v___x_5417_; lean_object* v___x_5418_; 
v___x_5411_ = l_Lean_Meta_instanceExtension;
v_ext_5412_ = lean_ctor_get(v___x_5411_, 1);
v_toEnvExtension_5413_ = lean_ctor_get(v_ext_5412_, 0);
v_asyncMode_5414_ = lean_ctor_get(v_toEnvExtension_5413_, 2);
v___x_5415_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5416_ = 1;
v___x_5417_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5415_, v___x_5411_, v_env_5409_, v_asyncMode_5414_, v___x_5416_);
v___x_5418_ = l_Lean_Meta_Instances_getClassChanges(v___x_5417_, v_className_5410_);
lean_dec(v___x_5417_);
return v___x_5418_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceClassChanges___boxed(lean_object* v_env_5419_, lean_object* v_className_5420_){
_start:
{
lean_object* v_res_5421_; 
v_res_5421_ = l_Lean_Meta_getInstanceClassChanges(v_env_5419_, v_className_5420_);
lean_dec(v_className_5420_);
return v_res_5421_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_5422_){
_start:
{
lean_object* v___x_5424_; lean_object* v___x_5425_; lean_object* v_env_5426_; lean_object* v___x_5427_; lean_object* v_ext_5428_; lean_object* v_toEnvExtension_5429_; lean_object* v_asyncMode_5430_; uint8_t v___x_5431_; lean_object* v___x_5432_; lean_object* v_erased_5433_; lean_object* v___x_5434_; 
v___x_5424_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5425_ = lean_st_ref_get(v_a_5422_);
v_env_5426_ = lean_ctor_get(v___x_5425_, 0);
lean_inc_ref(v_env_5426_);
lean_dec(v___x_5425_);
v___x_5427_ = l_Lean_Meta_instanceExtension;
v_ext_5428_ = lean_ctor_get(v___x_5427_, 1);
v_toEnvExtension_5429_ = lean_ctor_get(v_ext_5428_, 0);
v_asyncMode_5430_ = lean_ctor_get(v_toEnvExtension_5429_, 2);
v___x_5431_ = 1;
v___x_5432_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5424_, v___x_5427_, v_env_5426_, v_asyncMode_5430_, v___x_5431_);
v_erased_5433_ = lean_ctor_get(v___x_5432_, 2);
lean_inc_ref(v_erased_5433_);
lean_dec(v___x_5432_);
v___x_5434_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5434_, 0, v_erased_5433_);
return v___x_5434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_5435_, lean_object* v_a_5436_){
_start:
{
lean_object* v_res_5437_; 
v_res_5437_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5435_);
lean_dec(v_a_5435_);
return v_res_5437_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_5438_, lean_object* v_a_5439_){
_start:
{
lean_object* v___x_5441_; 
v___x_5441_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5439_);
return v___x_5441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_5442_, lean_object* v_a_5443_, lean_object* v_a_5444_){
_start:
{
lean_object* v_res_5445_; 
v_res_5445_ = l_Lean_Meta_getErasedInstances(v_a_5442_, v_a_5443_);
lean_dec(v_a_5443_);
lean_dec_ref(v_a_5442_);
return v_res_5445_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_5446_, lean_object* v_declName_5447_){
_start:
{
lean_object* v___x_5448_; lean_object* v_ext_5449_; lean_object* v_toEnvExtension_5450_; lean_object* v_asyncMode_5451_; lean_object* v___x_5452_; uint8_t v___x_5453_; lean_object* v___x_5454_; lean_object* v_instanceNames_5455_; uint8_t v___x_5456_; 
v___x_5448_ = l_Lean_Meta_instanceExtension;
v_ext_5449_ = lean_ctor_get(v___x_5448_, 1);
v_toEnvExtension_5450_ = lean_ctor_get(v_ext_5449_, 0);
v_asyncMode_5451_ = lean_ctor_get(v_toEnvExtension_5450_, 2);
v___x_5452_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5453_ = 1;
v___x_5454_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5452_, v___x_5448_, v_env_5446_, v_asyncMode_5451_, v___x_5453_);
v_instanceNames_5455_ = lean_ctor_get(v___x_5454_, 1);
lean_inc_ref(v_instanceNames_5455_);
lean_dec(v___x_5454_);
v___x_5456_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_5455_, v_declName_5447_);
lean_dec_ref(v_instanceNames_5455_);
return v___x_5456_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_5457_, lean_object* v_declName_5458_){
_start:
{
uint8_t v_res_5459_; lean_object* v_r_5460_; 
v_res_5459_ = l_Lean_Meta_isInstanceCore(v_env_5457_, v_declName_5458_);
lean_dec(v_declName_5458_);
v_r_5460_ = lean_box(v_res_5459_);
return v_r_5460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_5461_, lean_object* v_a_5462_){
_start:
{
lean_object* v___x_5464_; lean_object* v_env_5465_; uint8_t v___x_5466_; lean_object* v___x_5467_; lean_object* v___x_5468_; 
v___x_5464_ = lean_st_ref_get(v_a_5462_);
v_env_5465_ = lean_ctor_get(v___x_5464_, 0);
lean_inc_ref(v_env_5465_);
lean_dec(v___x_5464_);
v___x_5466_ = l_Lean_Meta_isInstanceCore(v_env_5465_, v_declName_5461_);
v___x_5467_ = lean_box(v___x_5466_);
v___x_5468_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5468_, 0, v___x_5467_);
return v___x_5468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_5469_, lean_object* v_a_5470_, lean_object* v_a_5471_){
_start:
{
lean_object* v_res_5472_; 
v_res_5472_ = l_Lean_Meta_isInstance___redArg(v_declName_5469_, v_a_5470_);
lean_dec(v_a_5470_);
lean_dec(v_declName_5469_);
return v_res_5472_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_5473_, lean_object* v_a_5474_, lean_object* v_a_5475_){
_start:
{
lean_object* v___x_5477_; 
v___x_5477_ = l_Lean_Meta_isInstance___redArg(v_declName_5473_, v_a_5475_);
return v___x_5477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_5478_, lean_object* v_a_5479_, lean_object* v_a_5480_, lean_object* v_a_5481_){
_start:
{
lean_object* v_res_5482_; 
v_res_5482_ = l_Lean_Meta_isInstance(v_declName_5478_, v_a_5479_, v_a_5480_);
lean_dec(v_a_5480_);
lean_dec_ref(v_a_5479_);
lean_dec(v_declName_5478_);
return v_res_5482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_5483_, lean_object* v_a_5484_){
_start:
{
lean_object* v___x_5486_; lean_object* v___x_5487_; lean_object* v_env_5488_; lean_object* v___x_5489_; lean_object* v_ext_5490_; lean_object* v_toEnvExtension_5491_; lean_object* v_asyncMode_5492_; uint8_t v___x_5493_; lean_object* v___x_5494_; lean_object* v_instanceNames_5495_; lean_object* v___x_5496_; 
v___x_5486_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5487_ = lean_st_ref_get(v_a_5484_);
v_env_5488_ = lean_ctor_get(v___x_5487_, 0);
lean_inc_ref(v_env_5488_);
lean_dec(v___x_5487_);
v___x_5489_ = l_Lean_Meta_instanceExtension;
v_ext_5490_ = lean_ctor_get(v___x_5489_, 1);
v_toEnvExtension_5491_ = lean_ctor_get(v_ext_5490_, 0);
v_asyncMode_5492_ = lean_ctor_get(v_toEnvExtension_5491_, 2);
v___x_5493_ = 1;
v___x_5494_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5486_, v___x_5489_, v_env_5488_, v_asyncMode_5492_, v___x_5493_);
v_instanceNames_5495_ = lean_ctor_get(v___x_5494_, 1);
lean_inc_ref(v_instanceNames_5495_);
lean_dec(v___x_5494_);
v___x_5496_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0___redArg(v_instanceNames_5495_, v_declName_5483_);
lean_dec_ref(v_instanceNames_5495_);
if (lean_obj_tag(v___x_5496_) == 1)
{
lean_object* v_val_5497_; lean_object* v___x_5499_; uint8_t v_isShared_5500_; uint8_t v_isSharedCheck_5506_; 
v_val_5497_ = lean_ctor_get(v___x_5496_, 0);
v_isSharedCheck_5506_ = !lean_is_exclusive(v___x_5496_);
if (v_isSharedCheck_5506_ == 0)
{
v___x_5499_ = v___x_5496_;
v_isShared_5500_ = v_isSharedCheck_5506_;
goto v_resetjp_5498_;
}
else
{
lean_inc(v_val_5497_);
lean_dec(v___x_5496_);
v___x_5499_ = lean_box(0);
v_isShared_5500_ = v_isSharedCheck_5506_;
goto v_resetjp_5498_;
}
v_resetjp_5498_:
{
lean_object* v_priority_5501_; lean_object* v___x_5503_; 
v_priority_5501_ = lean_ctor_get(v_val_5497_, 2);
lean_inc(v_priority_5501_);
lean_dec(v_val_5497_);
if (v_isShared_5500_ == 0)
{
lean_ctor_set(v___x_5499_, 0, v_priority_5501_);
v___x_5503_ = v___x_5499_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5505_; 
v_reuseFailAlloc_5505_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5505_, 0, v_priority_5501_);
v___x_5503_ = v_reuseFailAlloc_5505_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
lean_object* v___x_5504_; 
v___x_5504_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5504_, 0, v___x_5503_);
return v___x_5504_;
}
}
}
else
{
lean_object* v___x_5507_; lean_object* v___x_5508_; 
lean_dec(v___x_5496_);
v___x_5507_ = lean_box(0);
v___x_5508_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5508_, 0, v___x_5507_);
return v___x_5508_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_5509_, lean_object* v_a_5510_, lean_object* v_a_5511_){
_start:
{
lean_object* v_res_5512_; 
v_res_5512_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5509_, v_a_5510_);
lean_dec(v_a_5510_);
lean_dec(v_declName_5509_);
return v_res_5512_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_5513_, lean_object* v_a_5514_, lean_object* v_a_5515_){
_start:
{
lean_object* v___x_5517_; 
v___x_5517_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5513_, v_a_5515_);
return v___x_5517_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_5518_, lean_object* v_a_5519_, lean_object* v_a_5520_, lean_object* v_a_5521_){
_start:
{
lean_object* v_res_5522_; 
v_res_5522_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_5518_, v_a_5519_, v_a_5520_);
lean_dec(v_a_5520_);
lean_dec_ref(v_a_5519_);
lean_dec(v_declName_5518_);
return v_res_5522_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_5523_, lean_object* v_a_5524_){
_start:
{
lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v_env_5528_; lean_object* v___x_5529_; lean_object* v_ext_5530_; lean_object* v_toEnvExtension_5531_; lean_object* v_asyncMode_5532_; uint8_t v___x_5533_; lean_object* v___x_5534_; lean_object* v_instanceNames_5535_; lean_object* v___x_5536_; 
v___x_5526_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5527_ = lean_st_ref_get(v_a_5524_);
v_env_5528_ = lean_ctor_get(v___x_5527_, 0);
lean_inc_ref(v_env_5528_);
lean_dec(v___x_5527_);
v___x_5529_ = l_Lean_Meta_instanceExtension;
v_ext_5530_ = lean_ctor_get(v___x_5529_, 1);
v_toEnvExtension_5531_ = lean_ctor_get(v_ext_5530_, 0);
v_asyncMode_5532_ = lean_ctor_get(v_toEnvExtension_5531_, 2);
v___x_5533_ = 1;
v___x_5534_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5526_, v___x_5529_, v_env_5528_, v_asyncMode_5532_, v___x_5533_);
v_instanceNames_5535_ = lean_ctor_get(v___x_5534_, 1);
lean_inc_ref(v_instanceNames_5535_);
lean_dec(v___x_5534_);
v___x_5536_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_Instances_getClassChanges_spec__0___redArg(v_instanceNames_5535_, v_declName_5523_);
lean_dec_ref(v_instanceNames_5535_);
if (lean_obj_tag(v___x_5536_) == 1)
{
lean_object* v_val_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5547_; 
v_val_5537_ = lean_ctor_get(v___x_5536_, 0);
v_isSharedCheck_5547_ = !lean_is_exclusive(v___x_5536_);
if (v_isSharedCheck_5547_ == 0)
{
v___x_5539_ = v___x_5536_;
v_isShared_5540_ = v_isSharedCheck_5547_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_val_5537_);
lean_dec(v___x_5536_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5547_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
uint8_t v_attrKind_5541_; lean_object* v___x_5542_; lean_object* v___x_5544_; 
v_attrKind_5541_ = lean_ctor_get_uint8(v_val_5537_, sizeof(void*)*5);
lean_dec(v_val_5537_);
v___x_5542_ = lean_box(v_attrKind_5541_);
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 0, v___x_5542_);
v___x_5544_ = v___x_5539_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v___x_5542_);
v___x_5544_ = v_reuseFailAlloc_5546_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
lean_object* v___x_5545_; 
v___x_5545_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5545_, 0, v___x_5544_);
return v___x_5545_;
}
}
}
else
{
lean_object* v___x_5548_; lean_object* v___x_5549_; 
lean_dec(v___x_5536_);
v___x_5548_ = lean_box(0);
v___x_5549_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5549_, 0, v___x_5548_);
return v___x_5549_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_5550_, lean_object* v_a_5551_, lean_object* v_a_5552_){
_start:
{
lean_object* v_res_5553_; 
v_res_5553_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5550_, v_a_5551_);
lean_dec(v_a_5551_);
lean_dec(v_declName_5550_);
return v_res_5553_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_5554_, lean_object* v_a_5555_, lean_object* v_a_5556_){
_start:
{
lean_object* v___x_5558_; 
v___x_5558_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5554_, v_a_5556_);
return v___x_5558_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_5559_, lean_object* v_a_5560_, lean_object* v_a_5561_, lean_object* v_a_5562_){
_start:
{
lean_object* v_res_5563_; 
v_res_5563_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_5559_, v_a_5560_, v_a_5561_);
lean_dec(v_a_5561_);
lean_dec_ref(v_a_5560_);
lean_dec(v_declName_5559_);
return v_res_5563_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5568_, lean_object* v_v_5569_, lean_object* v_t_5570_){
_start:
{
if (lean_obj_tag(v_t_5570_) == 0)
{
lean_object* v_size_5571_; lean_object* v_k_5572_; lean_object* v_v_5573_; lean_object* v_l_5574_; lean_object* v_r_5575_; lean_object* v___x_5577_; uint8_t v_isShared_5578_; uint8_t v_isSharedCheck_5856_; 
v_size_5571_ = lean_ctor_get(v_t_5570_, 0);
v_k_5572_ = lean_ctor_get(v_t_5570_, 1);
v_v_5573_ = lean_ctor_get(v_t_5570_, 2);
v_l_5574_ = lean_ctor_get(v_t_5570_, 3);
v_r_5575_ = lean_ctor_get(v_t_5570_, 4);
v_isSharedCheck_5856_ = !lean_is_exclusive(v_t_5570_);
if (v_isSharedCheck_5856_ == 0)
{
v___x_5577_ = v_t_5570_;
v_isShared_5578_ = v_isSharedCheck_5856_;
goto v_resetjp_5576_;
}
else
{
lean_inc(v_r_5575_);
lean_inc(v_l_5574_);
lean_inc(v_v_5573_);
lean_inc(v_k_5572_);
lean_inc(v_size_5571_);
lean_dec(v_t_5570_);
v___x_5577_ = lean_box(0);
v_isShared_5578_ = v_isSharedCheck_5856_;
goto v_resetjp_5576_;
}
v_resetjp_5576_:
{
uint8_t v___x_5579_; 
v___x_5579_ = lean_nat_dec_lt(v_k_5572_, v_k_5568_);
if (v___x_5579_ == 0)
{
uint8_t v___x_5580_; 
v___x_5580_ = lean_nat_dec_eq(v_k_5572_, v_k_5568_);
if (v___x_5580_ == 0)
{
lean_object* v_impl_5581_; lean_object* v___x_5582_; 
lean_dec(v_size_5571_);
v_impl_5581_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5568_, v_v_5569_, v_r_5575_);
v___x_5582_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5574_) == 0)
{
lean_object* v_size_5583_; lean_object* v_size_5584_; lean_object* v_k_5585_; lean_object* v_v_5586_; lean_object* v_l_5587_; lean_object* v_r_5588_; lean_object* v___x_5589_; lean_object* v___x_5590_; uint8_t v___x_5591_; 
v_size_5583_ = lean_ctor_get(v_l_5574_, 0);
v_size_5584_ = lean_ctor_get(v_impl_5581_, 0);
v_k_5585_ = lean_ctor_get(v_impl_5581_, 1);
v_v_5586_ = lean_ctor_get(v_impl_5581_, 2);
v_l_5587_ = lean_ctor_get(v_impl_5581_, 3);
lean_inc(v_l_5587_);
v_r_5588_ = lean_ctor_get(v_impl_5581_, 4);
v___x_5589_ = lean_unsigned_to_nat(3u);
v___x_5590_ = lean_nat_mul(v___x_5589_, v_size_5583_);
v___x_5591_ = lean_nat_dec_lt(v___x_5590_, v_size_5584_);
lean_dec(v___x_5590_);
if (v___x_5591_ == 0)
{
lean_object* v___x_5592_; lean_object* v___x_5593_; lean_object* v___x_5595_; 
lean_dec(v_l_5587_);
v___x_5592_ = lean_nat_add(v___x_5582_, v_size_5583_);
v___x_5593_ = lean_nat_add(v___x_5592_, v_size_5584_);
lean_dec(v___x_5592_);
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 4, v_impl_5581_);
lean_ctor_set(v___x_5577_, 0, v___x_5593_);
v___x_5595_ = v___x_5577_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5596_; 
v_reuseFailAlloc_5596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5596_, 0, v___x_5593_);
lean_ctor_set(v_reuseFailAlloc_5596_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5596_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5596_, 3, v_l_5574_);
lean_ctor_set(v_reuseFailAlloc_5596_, 4, v_impl_5581_);
v___x_5595_ = v_reuseFailAlloc_5596_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
return v___x_5595_;
}
}
else
{
lean_object* v___x_5598_; uint8_t v_isShared_5599_; uint8_t v_isSharedCheck_5660_; 
lean_inc(v_r_5588_);
lean_inc(v_v_5586_);
lean_inc(v_k_5585_);
lean_inc(v_size_5584_);
v_isSharedCheck_5660_ = !lean_is_exclusive(v_impl_5581_);
if (v_isSharedCheck_5660_ == 0)
{
lean_object* v_unused_5661_; lean_object* v_unused_5662_; lean_object* v_unused_5663_; lean_object* v_unused_5664_; lean_object* v_unused_5665_; 
v_unused_5661_ = lean_ctor_get(v_impl_5581_, 4);
lean_dec(v_unused_5661_);
v_unused_5662_ = lean_ctor_get(v_impl_5581_, 3);
lean_dec(v_unused_5662_);
v_unused_5663_ = lean_ctor_get(v_impl_5581_, 2);
lean_dec(v_unused_5663_);
v_unused_5664_ = lean_ctor_get(v_impl_5581_, 1);
lean_dec(v_unused_5664_);
v_unused_5665_ = lean_ctor_get(v_impl_5581_, 0);
lean_dec(v_unused_5665_);
v___x_5598_ = v_impl_5581_;
v_isShared_5599_ = v_isSharedCheck_5660_;
goto v_resetjp_5597_;
}
else
{
lean_dec(v_impl_5581_);
v___x_5598_ = lean_box(0);
v_isShared_5599_ = v_isSharedCheck_5660_;
goto v_resetjp_5597_;
}
v_resetjp_5597_:
{
lean_object* v_size_5600_; lean_object* v_k_5601_; lean_object* v_v_5602_; lean_object* v_l_5603_; lean_object* v_r_5604_; lean_object* v_size_5605_; lean_object* v___x_5606_; lean_object* v___x_5607_; uint8_t v___x_5608_; 
v_size_5600_ = lean_ctor_get(v_l_5587_, 0);
v_k_5601_ = lean_ctor_get(v_l_5587_, 1);
v_v_5602_ = lean_ctor_get(v_l_5587_, 2);
v_l_5603_ = lean_ctor_get(v_l_5587_, 3);
v_r_5604_ = lean_ctor_get(v_l_5587_, 4);
v_size_5605_ = lean_ctor_get(v_r_5588_, 0);
v___x_5606_ = lean_unsigned_to_nat(2u);
v___x_5607_ = lean_nat_mul(v___x_5606_, v_size_5605_);
v___x_5608_ = lean_nat_dec_lt(v_size_5600_, v___x_5607_);
lean_dec(v___x_5607_);
if (v___x_5608_ == 0)
{
lean_object* v___x_5610_; uint8_t v_isShared_5611_; uint8_t v_isSharedCheck_5636_; 
lean_inc(v_r_5604_);
lean_inc(v_l_5603_);
lean_inc(v_v_5602_);
lean_inc(v_k_5601_);
v_isSharedCheck_5636_ = !lean_is_exclusive(v_l_5587_);
if (v_isSharedCheck_5636_ == 0)
{
lean_object* v_unused_5637_; lean_object* v_unused_5638_; lean_object* v_unused_5639_; lean_object* v_unused_5640_; lean_object* v_unused_5641_; 
v_unused_5637_ = lean_ctor_get(v_l_5587_, 4);
lean_dec(v_unused_5637_);
v_unused_5638_ = lean_ctor_get(v_l_5587_, 3);
lean_dec(v_unused_5638_);
v_unused_5639_ = lean_ctor_get(v_l_5587_, 2);
lean_dec(v_unused_5639_);
v_unused_5640_ = lean_ctor_get(v_l_5587_, 1);
lean_dec(v_unused_5640_);
v_unused_5641_ = lean_ctor_get(v_l_5587_, 0);
lean_dec(v_unused_5641_);
v___x_5610_ = v_l_5587_;
v_isShared_5611_ = v_isSharedCheck_5636_;
goto v_resetjp_5609_;
}
else
{
lean_dec(v_l_5587_);
v___x_5610_ = lean_box(0);
v_isShared_5611_ = v_isSharedCheck_5636_;
goto v_resetjp_5609_;
}
v_resetjp_5609_:
{
lean_object* v___x_5612_; lean_object* v___x_5613_; lean_object* v___y_5615_; lean_object* v___y_5616_; lean_object* v___y_5617_; lean_object* v___y_5626_; 
v___x_5612_ = lean_nat_add(v___x_5582_, v_size_5583_);
v___x_5613_ = lean_nat_add(v___x_5612_, v_size_5584_);
lean_dec(v_size_5584_);
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
v___jp_5614_:
{
lean_object* v___x_5618_; lean_object* v___x_5620_; 
v___x_5618_ = lean_nat_add(v___y_5615_, v___y_5617_);
lean_dec(v___y_5617_);
lean_dec(v___y_5615_);
if (v_isShared_5611_ == 0)
{
lean_ctor_set(v___x_5610_, 4, v_r_5588_);
lean_ctor_set(v___x_5610_, 3, v_r_5604_);
lean_ctor_set(v___x_5610_, 2, v_v_5586_);
lean_ctor_set(v___x_5610_, 1, v_k_5585_);
lean_ctor_set(v___x_5610_, 0, v___x_5618_);
v___x_5620_ = v___x_5610_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5624_; 
v_reuseFailAlloc_5624_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5624_, 0, v___x_5618_);
lean_ctor_set(v_reuseFailAlloc_5624_, 1, v_k_5585_);
lean_ctor_set(v_reuseFailAlloc_5624_, 2, v_v_5586_);
lean_ctor_set(v_reuseFailAlloc_5624_, 3, v_r_5604_);
lean_ctor_set(v_reuseFailAlloc_5624_, 4, v_r_5588_);
v___x_5620_ = v_reuseFailAlloc_5624_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
lean_object* v___x_5622_; 
if (v_isShared_5599_ == 0)
{
lean_ctor_set(v___x_5598_, 4, v___x_5620_);
lean_ctor_set(v___x_5598_, 3, v___y_5616_);
lean_ctor_set(v___x_5598_, 2, v_v_5602_);
lean_ctor_set(v___x_5598_, 1, v_k_5601_);
lean_ctor_set(v___x_5598_, 0, v___x_5613_);
v___x_5622_ = v___x_5598_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v___x_5613_);
lean_ctor_set(v_reuseFailAlloc_5623_, 1, v_k_5601_);
lean_ctor_set(v_reuseFailAlloc_5623_, 2, v_v_5602_);
lean_ctor_set(v_reuseFailAlloc_5623_, 3, v___y_5616_);
lean_ctor_set(v_reuseFailAlloc_5623_, 4, v___x_5620_);
v___x_5622_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
return v___x_5622_;
}
}
}
v___jp_5625_:
{
lean_object* v___x_5627_; lean_object* v___x_5629_; 
v___x_5627_ = lean_nat_add(v___x_5612_, v___y_5626_);
lean_dec(v___y_5626_);
lean_dec(v___x_5612_);
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 4, v_l_5603_);
lean_ctor_set(v___x_5577_, 0, v___x_5627_);
v___x_5629_ = v___x_5577_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5633_; 
v_reuseFailAlloc_5633_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5633_, 0, v___x_5627_);
lean_ctor_set(v_reuseFailAlloc_5633_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5633_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5633_, 3, v_l_5574_);
lean_ctor_set(v_reuseFailAlloc_5633_, 4, v_l_5603_);
v___x_5629_ = v_reuseFailAlloc_5633_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
lean_object* v___x_5630_; 
v___x_5630_ = lean_nat_add(v___x_5582_, v_size_5605_);
if (lean_obj_tag(v_r_5604_) == 0)
{
lean_object* v_size_5631_; 
v_size_5631_ = lean_ctor_get(v_r_5604_, 0);
lean_inc(v_size_5631_);
v___y_5615_ = v___x_5630_;
v___y_5616_ = v___x_5629_;
v___y_5617_ = v_size_5631_;
goto v___jp_5614_;
}
else
{
lean_object* v___x_5632_; 
v___x_5632_ = lean_unsigned_to_nat(0u);
v___y_5615_ = v___x_5630_;
v___y_5616_ = v___x_5629_;
v___y_5617_ = v___x_5632_;
goto v___jp_5614_;
}
}
}
}
}
else
{
lean_object* v___x_5642_; lean_object* v___x_5643_; lean_object* v___x_5644_; lean_object* v___x_5646_; 
lean_del_object(v___x_5577_);
v___x_5642_ = lean_nat_add(v___x_5582_, v_size_5583_);
v___x_5643_ = lean_nat_add(v___x_5642_, v_size_5584_);
lean_dec(v_size_5584_);
v___x_5644_ = lean_nat_add(v___x_5642_, v_size_5600_);
lean_dec(v___x_5642_);
lean_inc_ref(v_l_5574_);
if (v_isShared_5599_ == 0)
{
lean_ctor_set(v___x_5598_, 4, v_l_5587_);
lean_ctor_set(v___x_5598_, 3, v_l_5574_);
lean_ctor_set(v___x_5598_, 2, v_v_5573_);
lean_ctor_set(v___x_5598_, 1, v_k_5572_);
lean_ctor_set(v___x_5598_, 0, v___x_5644_);
v___x_5646_ = v___x_5598_;
goto v_reusejp_5645_;
}
else
{
lean_object* v_reuseFailAlloc_5659_; 
v_reuseFailAlloc_5659_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5659_, 0, v___x_5644_);
lean_ctor_set(v_reuseFailAlloc_5659_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5659_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5659_, 3, v_l_5574_);
lean_ctor_set(v_reuseFailAlloc_5659_, 4, v_l_5587_);
v___x_5646_ = v_reuseFailAlloc_5659_;
goto v_reusejp_5645_;
}
v_reusejp_5645_:
{
lean_object* v___x_5648_; uint8_t v_isShared_5649_; uint8_t v_isSharedCheck_5653_; 
v_isSharedCheck_5653_ = !lean_is_exclusive(v_l_5574_);
if (v_isSharedCheck_5653_ == 0)
{
lean_object* v_unused_5654_; lean_object* v_unused_5655_; lean_object* v_unused_5656_; lean_object* v_unused_5657_; lean_object* v_unused_5658_; 
v_unused_5654_ = lean_ctor_get(v_l_5574_, 4);
lean_dec(v_unused_5654_);
v_unused_5655_ = lean_ctor_get(v_l_5574_, 3);
lean_dec(v_unused_5655_);
v_unused_5656_ = lean_ctor_get(v_l_5574_, 2);
lean_dec(v_unused_5656_);
v_unused_5657_ = lean_ctor_get(v_l_5574_, 1);
lean_dec(v_unused_5657_);
v_unused_5658_ = lean_ctor_get(v_l_5574_, 0);
lean_dec(v_unused_5658_);
v___x_5648_ = v_l_5574_;
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
else
{
lean_dec(v_l_5574_);
v___x_5648_ = lean_box(0);
v_isShared_5649_ = v_isSharedCheck_5653_;
goto v_resetjp_5647_;
}
v_resetjp_5647_:
{
lean_object* v___x_5651_; 
if (v_isShared_5649_ == 0)
{
lean_ctor_set(v___x_5648_, 4, v_r_5588_);
lean_ctor_set(v___x_5648_, 3, v___x_5646_);
lean_ctor_set(v___x_5648_, 2, v_v_5586_);
lean_ctor_set(v___x_5648_, 1, v_k_5585_);
lean_ctor_set(v___x_5648_, 0, v___x_5643_);
v___x_5651_ = v___x_5648_;
goto v_reusejp_5650_;
}
else
{
lean_object* v_reuseFailAlloc_5652_; 
v_reuseFailAlloc_5652_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5652_, 0, v___x_5643_);
lean_ctor_set(v_reuseFailAlloc_5652_, 1, v_k_5585_);
lean_ctor_set(v_reuseFailAlloc_5652_, 2, v_v_5586_);
lean_ctor_set(v_reuseFailAlloc_5652_, 3, v___x_5646_);
lean_ctor_set(v_reuseFailAlloc_5652_, 4, v_r_5588_);
v___x_5651_ = v_reuseFailAlloc_5652_;
goto v_reusejp_5650_;
}
v_reusejp_5650_:
{
return v___x_5651_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5666_; 
v_l_5666_ = lean_ctor_get(v_impl_5581_, 3);
lean_inc(v_l_5666_);
if (lean_obj_tag(v_l_5666_) == 0)
{
lean_object* v_r_5667_; lean_object* v_k_5668_; lean_object* v_v_5669_; lean_object* v___x_5671_; uint8_t v_isShared_5672_; uint8_t v_isSharedCheck_5692_; 
v_r_5667_ = lean_ctor_get(v_impl_5581_, 4);
v_k_5668_ = lean_ctor_get(v_impl_5581_, 1);
v_v_5669_ = lean_ctor_get(v_impl_5581_, 2);
v_isSharedCheck_5692_ = !lean_is_exclusive(v_impl_5581_);
if (v_isSharedCheck_5692_ == 0)
{
lean_object* v_unused_5693_; lean_object* v_unused_5694_; 
v_unused_5693_ = lean_ctor_get(v_impl_5581_, 3);
lean_dec(v_unused_5693_);
v_unused_5694_ = lean_ctor_get(v_impl_5581_, 0);
lean_dec(v_unused_5694_);
v___x_5671_ = v_impl_5581_;
v_isShared_5672_ = v_isSharedCheck_5692_;
goto v_resetjp_5670_;
}
else
{
lean_inc(v_r_5667_);
lean_inc(v_v_5669_);
lean_inc(v_k_5668_);
lean_dec(v_impl_5581_);
v___x_5671_ = lean_box(0);
v_isShared_5672_ = v_isSharedCheck_5692_;
goto v_resetjp_5670_;
}
v_resetjp_5670_:
{
lean_object* v_k_5673_; lean_object* v_v_5674_; lean_object* v___x_5676_; uint8_t v_isShared_5677_; uint8_t v_isSharedCheck_5688_; 
v_k_5673_ = lean_ctor_get(v_l_5666_, 1);
v_v_5674_ = lean_ctor_get(v_l_5666_, 2);
v_isSharedCheck_5688_ = !lean_is_exclusive(v_l_5666_);
if (v_isSharedCheck_5688_ == 0)
{
lean_object* v_unused_5689_; lean_object* v_unused_5690_; lean_object* v_unused_5691_; 
v_unused_5689_ = lean_ctor_get(v_l_5666_, 4);
lean_dec(v_unused_5689_);
v_unused_5690_ = lean_ctor_get(v_l_5666_, 3);
lean_dec(v_unused_5690_);
v_unused_5691_ = lean_ctor_get(v_l_5666_, 0);
lean_dec(v_unused_5691_);
v___x_5676_ = v_l_5666_;
v_isShared_5677_ = v_isSharedCheck_5688_;
goto v_resetjp_5675_;
}
else
{
lean_inc(v_v_5674_);
lean_inc(v_k_5673_);
lean_dec(v_l_5666_);
v___x_5676_ = lean_box(0);
v_isShared_5677_ = v_isSharedCheck_5688_;
goto v_resetjp_5675_;
}
v_resetjp_5675_:
{
lean_object* v___x_5678_; lean_object* v___x_5680_; 
v___x_5678_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5667_, 2);
if (v_isShared_5677_ == 0)
{
lean_ctor_set(v___x_5676_, 4, v_r_5667_);
lean_ctor_set(v___x_5676_, 3, v_r_5667_);
lean_ctor_set(v___x_5676_, 2, v_v_5573_);
lean_ctor_set(v___x_5676_, 1, v_k_5572_);
lean_ctor_set(v___x_5676_, 0, v___x_5582_);
v___x_5680_ = v___x_5676_;
goto v_reusejp_5679_;
}
else
{
lean_object* v_reuseFailAlloc_5687_; 
v_reuseFailAlloc_5687_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5687_, 0, v___x_5582_);
lean_ctor_set(v_reuseFailAlloc_5687_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5687_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5687_, 3, v_r_5667_);
lean_ctor_set(v_reuseFailAlloc_5687_, 4, v_r_5667_);
v___x_5680_ = v_reuseFailAlloc_5687_;
goto v_reusejp_5679_;
}
v_reusejp_5679_:
{
lean_object* v___x_5682_; 
lean_inc(v_r_5667_);
if (v_isShared_5672_ == 0)
{
lean_ctor_set(v___x_5671_, 3, v_r_5667_);
lean_ctor_set(v___x_5671_, 0, v___x_5582_);
v___x_5682_ = v___x_5671_;
goto v_reusejp_5681_;
}
else
{
lean_object* v_reuseFailAlloc_5686_; 
v_reuseFailAlloc_5686_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5686_, 0, v___x_5582_);
lean_ctor_set(v_reuseFailAlloc_5686_, 1, v_k_5668_);
lean_ctor_set(v_reuseFailAlloc_5686_, 2, v_v_5669_);
lean_ctor_set(v_reuseFailAlloc_5686_, 3, v_r_5667_);
lean_ctor_set(v_reuseFailAlloc_5686_, 4, v_r_5667_);
v___x_5682_ = v_reuseFailAlloc_5686_;
goto v_reusejp_5681_;
}
v_reusejp_5681_:
{
lean_object* v___x_5684_; 
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 4, v___x_5682_);
lean_ctor_set(v___x_5577_, 3, v___x_5680_);
lean_ctor_set(v___x_5577_, 2, v_v_5674_);
lean_ctor_set(v___x_5577_, 1, v_k_5673_);
lean_ctor_set(v___x_5577_, 0, v___x_5678_);
v___x_5684_ = v___x_5577_;
goto v_reusejp_5683_;
}
else
{
lean_object* v_reuseFailAlloc_5685_; 
v_reuseFailAlloc_5685_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5685_, 0, v___x_5678_);
lean_ctor_set(v_reuseFailAlloc_5685_, 1, v_k_5673_);
lean_ctor_set(v_reuseFailAlloc_5685_, 2, v_v_5674_);
lean_ctor_set(v_reuseFailAlloc_5685_, 3, v___x_5680_);
lean_ctor_set(v_reuseFailAlloc_5685_, 4, v___x_5682_);
v___x_5684_ = v_reuseFailAlloc_5685_;
goto v_reusejp_5683_;
}
v_reusejp_5683_:
{
return v___x_5684_;
}
}
}
}
}
}
else
{
lean_object* v_r_5695_; 
v_r_5695_ = lean_ctor_get(v_impl_5581_, 4);
lean_inc(v_r_5695_);
if (lean_obj_tag(v_r_5695_) == 0)
{
lean_object* v_k_5696_; lean_object* v_v_5697_; lean_object* v___x_5699_; uint8_t v_isShared_5700_; uint8_t v_isSharedCheck_5708_; 
v_k_5696_ = lean_ctor_get(v_impl_5581_, 1);
v_v_5697_ = lean_ctor_get(v_impl_5581_, 2);
v_isSharedCheck_5708_ = !lean_is_exclusive(v_impl_5581_);
if (v_isSharedCheck_5708_ == 0)
{
lean_object* v_unused_5709_; lean_object* v_unused_5710_; lean_object* v_unused_5711_; 
v_unused_5709_ = lean_ctor_get(v_impl_5581_, 4);
lean_dec(v_unused_5709_);
v_unused_5710_ = lean_ctor_get(v_impl_5581_, 3);
lean_dec(v_unused_5710_);
v_unused_5711_ = lean_ctor_get(v_impl_5581_, 0);
lean_dec(v_unused_5711_);
v___x_5699_ = v_impl_5581_;
v_isShared_5700_ = v_isSharedCheck_5708_;
goto v_resetjp_5698_;
}
else
{
lean_inc(v_v_5697_);
lean_inc(v_k_5696_);
lean_dec(v_impl_5581_);
v___x_5699_ = lean_box(0);
v_isShared_5700_ = v_isSharedCheck_5708_;
goto v_resetjp_5698_;
}
v_resetjp_5698_:
{
lean_object* v___x_5701_; lean_object* v___x_5703_; 
v___x_5701_ = lean_unsigned_to_nat(3u);
if (v_isShared_5700_ == 0)
{
lean_ctor_set(v___x_5699_, 4, v_l_5666_);
lean_ctor_set(v___x_5699_, 2, v_v_5573_);
lean_ctor_set(v___x_5699_, 1, v_k_5572_);
lean_ctor_set(v___x_5699_, 0, v___x_5582_);
v___x_5703_ = v___x_5699_;
goto v_reusejp_5702_;
}
else
{
lean_object* v_reuseFailAlloc_5707_; 
v_reuseFailAlloc_5707_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5707_, 0, v___x_5582_);
lean_ctor_set(v_reuseFailAlloc_5707_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5707_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5707_, 3, v_l_5666_);
lean_ctor_set(v_reuseFailAlloc_5707_, 4, v_l_5666_);
v___x_5703_ = v_reuseFailAlloc_5707_;
goto v_reusejp_5702_;
}
v_reusejp_5702_:
{
lean_object* v___x_5705_; 
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 4, v_r_5695_);
lean_ctor_set(v___x_5577_, 3, v___x_5703_);
lean_ctor_set(v___x_5577_, 2, v_v_5697_);
lean_ctor_set(v___x_5577_, 1, v_k_5696_);
lean_ctor_set(v___x_5577_, 0, v___x_5701_);
v___x_5705_ = v___x_5577_;
goto v_reusejp_5704_;
}
else
{
lean_object* v_reuseFailAlloc_5706_; 
v_reuseFailAlloc_5706_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5706_, 0, v___x_5701_);
lean_ctor_set(v_reuseFailAlloc_5706_, 1, v_k_5696_);
lean_ctor_set(v_reuseFailAlloc_5706_, 2, v_v_5697_);
lean_ctor_set(v_reuseFailAlloc_5706_, 3, v___x_5703_);
lean_ctor_set(v_reuseFailAlloc_5706_, 4, v_r_5695_);
v___x_5705_ = v_reuseFailAlloc_5706_;
goto v_reusejp_5704_;
}
v_reusejp_5704_:
{
return v___x_5705_;
}
}
}
}
else
{
lean_object* v___x_5712_; lean_object* v___x_5714_; 
v___x_5712_ = lean_unsigned_to_nat(2u);
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 4, v_impl_5581_);
lean_ctor_set(v___x_5577_, 3, v_r_5695_);
lean_ctor_set(v___x_5577_, 0, v___x_5712_);
v___x_5714_ = v___x_5577_;
goto v_reusejp_5713_;
}
else
{
lean_object* v_reuseFailAlloc_5715_; 
v_reuseFailAlloc_5715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5715_, 0, v___x_5712_);
lean_ctor_set(v_reuseFailAlloc_5715_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5715_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5715_, 3, v_r_5695_);
lean_ctor_set(v_reuseFailAlloc_5715_, 4, v_impl_5581_);
v___x_5714_ = v_reuseFailAlloc_5715_;
goto v_reusejp_5713_;
}
v_reusejp_5713_:
{
return v___x_5714_;
}
}
}
}
}
else
{
lean_object* v___x_5717_; 
lean_dec(v_v_5573_);
lean_dec(v_k_5572_);
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 2, v_v_5569_);
lean_ctor_set(v___x_5577_, 1, v_k_5568_);
v___x_5717_ = v___x_5577_;
goto v_reusejp_5716_;
}
else
{
lean_object* v_reuseFailAlloc_5718_; 
v_reuseFailAlloc_5718_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5718_, 0, v_size_5571_);
lean_ctor_set(v_reuseFailAlloc_5718_, 1, v_k_5568_);
lean_ctor_set(v_reuseFailAlloc_5718_, 2, v_v_5569_);
lean_ctor_set(v_reuseFailAlloc_5718_, 3, v_l_5574_);
lean_ctor_set(v_reuseFailAlloc_5718_, 4, v_r_5575_);
v___x_5717_ = v_reuseFailAlloc_5718_;
goto v_reusejp_5716_;
}
v_reusejp_5716_:
{
return v___x_5717_;
}
}
}
else
{
lean_object* v_impl_5719_; lean_object* v___x_5720_; 
lean_dec(v_size_5571_);
v_impl_5719_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5568_, v_v_5569_, v_l_5574_);
v___x_5720_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5575_) == 0)
{
lean_object* v_size_5721_; lean_object* v_size_5722_; lean_object* v_k_5723_; lean_object* v_v_5724_; lean_object* v_l_5725_; lean_object* v_r_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; uint8_t v___x_5729_; 
v_size_5721_ = lean_ctor_get(v_r_5575_, 0);
v_size_5722_ = lean_ctor_get(v_impl_5719_, 0);
v_k_5723_ = lean_ctor_get(v_impl_5719_, 1);
v_v_5724_ = lean_ctor_get(v_impl_5719_, 2);
v_l_5725_ = lean_ctor_get(v_impl_5719_, 3);
v_r_5726_ = lean_ctor_get(v_impl_5719_, 4);
lean_inc(v_r_5726_);
v___x_5727_ = lean_unsigned_to_nat(3u);
v___x_5728_ = lean_nat_mul(v___x_5727_, v_size_5721_);
v___x_5729_ = lean_nat_dec_lt(v___x_5728_, v_size_5722_);
lean_dec(v___x_5728_);
if (v___x_5729_ == 0)
{
lean_object* v___x_5730_; lean_object* v___x_5731_; lean_object* v___x_5733_; 
lean_dec(v_r_5726_);
v___x_5730_ = lean_nat_add(v___x_5720_, v_size_5722_);
v___x_5731_ = lean_nat_add(v___x_5730_, v_size_5721_);
lean_dec(v___x_5730_);
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 3, v_impl_5719_);
lean_ctor_set(v___x_5577_, 0, v___x_5731_);
v___x_5733_ = v___x_5577_;
goto v_reusejp_5732_;
}
else
{
lean_object* v_reuseFailAlloc_5734_; 
v_reuseFailAlloc_5734_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5734_, 0, v___x_5731_);
lean_ctor_set(v_reuseFailAlloc_5734_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5734_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5734_, 3, v_impl_5719_);
lean_ctor_set(v_reuseFailAlloc_5734_, 4, v_r_5575_);
v___x_5733_ = v_reuseFailAlloc_5734_;
goto v_reusejp_5732_;
}
v_reusejp_5732_:
{
return v___x_5733_;
}
}
else
{
lean_object* v___x_5736_; uint8_t v_isShared_5737_; uint8_t v_isSharedCheck_5800_; 
lean_inc(v_l_5725_);
lean_inc(v_v_5724_);
lean_inc(v_k_5723_);
lean_inc(v_size_5722_);
v_isSharedCheck_5800_ = !lean_is_exclusive(v_impl_5719_);
if (v_isSharedCheck_5800_ == 0)
{
lean_object* v_unused_5801_; lean_object* v_unused_5802_; lean_object* v_unused_5803_; lean_object* v_unused_5804_; lean_object* v_unused_5805_; 
v_unused_5801_ = lean_ctor_get(v_impl_5719_, 4);
lean_dec(v_unused_5801_);
v_unused_5802_ = lean_ctor_get(v_impl_5719_, 3);
lean_dec(v_unused_5802_);
v_unused_5803_ = lean_ctor_get(v_impl_5719_, 2);
lean_dec(v_unused_5803_);
v_unused_5804_ = lean_ctor_get(v_impl_5719_, 1);
lean_dec(v_unused_5804_);
v_unused_5805_ = lean_ctor_get(v_impl_5719_, 0);
lean_dec(v_unused_5805_);
v___x_5736_ = v_impl_5719_;
v_isShared_5737_ = v_isSharedCheck_5800_;
goto v_resetjp_5735_;
}
else
{
lean_dec(v_impl_5719_);
v___x_5736_ = lean_box(0);
v_isShared_5737_ = v_isSharedCheck_5800_;
goto v_resetjp_5735_;
}
v_resetjp_5735_:
{
lean_object* v_size_5738_; lean_object* v_size_5739_; lean_object* v_k_5740_; lean_object* v_v_5741_; lean_object* v_l_5742_; lean_object* v_r_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; uint8_t v___x_5746_; 
v_size_5738_ = lean_ctor_get(v_l_5725_, 0);
v_size_5739_ = lean_ctor_get(v_r_5726_, 0);
v_k_5740_ = lean_ctor_get(v_r_5726_, 1);
v_v_5741_ = lean_ctor_get(v_r_5726_, 2);
v_l_5742_ = lean_ctor_get(v_r_5726_, 3);
v_r_5743_ = lean_ctor_get(v_r_5726_, 4);
v___x_5744_ = lean_unsigned_to_nat(2u);
v___x_5745_ = lean_nat_mul(v___x_5744_, v_size_5738_);
v___x_5746_ = lean_nat_dec_lt(v_size_5739_, v___x_5745_);
lean_dec(v___x_5745_);
if (v___x_5746_ == 0)
{
lean_object* v___x_5748_; uint8_t v_isShared_5749_; uint8_t v_isSharedCheck_5775_; 
lean_inc(v_r_5743_);
lean_inc(v_l_5742_);
lean_inc(v_v_5741_);
lean_inc(v_k_5740_);
v_isSharedCheck_5775_ = !lean_is_exclusive(v_r_5726_);
if (v_isSharedCheck_5775_ == 0)
{
lean_object* v_unused_5776_; lean_object* v_unused_5777_; lean_object* v_unused_5778_; lean_object* v_unused_5779_; lean_object* v_unused_5780_; 
v_unused_5776_ = lean_ctor_get(v_r_5726_, 4);
lean_dec(v_unused_5776_);
v_unused_5777_ = lean_ctor_get(v_r_5726_, 3);
lean_dec(v_unused_5777_);
v_unused_5778_ = lean_ctor_get(v_r_5726_, 2);
lean_dec(v_unused_5778_);
v_unused_5779_ = lean_ctor_get(v_r_5726_, 1);
lean_dec(v_unused_5779_);
v_unused_5780_ = lean_ctor_get(v_r_5726_, 0);
lean_dec(v_unused_5780_);
v___x_5748_ = v_r_5726_;
v_isShared_5749_ = v_isSharedCheck_5775_;
goto v_resetjp_5747_;
}
else
{
lean_dec(v_r_5726_);
v___x_5748_ = lean_box(0);
v_isShared_5749_ = v_isSharedCheck_5775_;
goto v_resetjp_5747_;
}
v_resetjp_5747_:
{
lean_object* v___x_5750_; lean_object* v___x_5751_; lean_object* v___y_5753_; lean_object* v___y_5754_; lean_object* v___y_5755_; lean_object* v___x_5763_; lean_object* v___y_5765_; 
v___x_5750_ = lean_nat_add(v___x_5720_, v_size_5722_);
lean_dec(v_size_5722_);
v___x_5751_ = lean_nat_add(v___x_5750_, v_size_5721_);
lean_dec(v___x_5750_);
v___x_5763_ = lean_nat_add(v___x_5720_, v_size_5738_);
if (lean_obj_tag(v_l_5742_) == 0)
{
lean_object* v_size_5773_; 
v_size_5773_ = lean_ctor_get(v_l_5742_, 0);
lean_inc(v_size_5773_);
v___y_5765_ = v_size_5773_;
goto v___jp_5764_;
}
else
{
lean_object* v___x_5774_; 
v___x_5774_ = lean_unsigned_to_nat(0u);
v___y_5765_ = v___x_5774_;
goto v___jp_5764_;
}
v___jp_5752_:
{
lean_object* v___x_5756_; lean_object* v___x_5758_; 
v___x_5756_ = lean_nat_add(v___y_5753_, v___y_5755_);
lean_dec(v___y_5755_);
lean_dec(v___y_5753_);
if (v_isShared_5749_ == 0)
{
lean_ctor_set(v___x_5748_, 4, v_r_5575_);
lean_ctor_set(v___x_5748_, 3, v_r_5743_);
lean_ctor_set(v___x_5748_, 2, v_v_5573_);
lean_ctor_set(v___x_5748_, 1, v_k_5572_);
lean_ctor_set(v___x_5748_, 0, v___x_5756_);
v___x_5758_ = v___x_5748_;
goto v_reusejp_5757_;
}
else
{
lean_object* v_reuseFailAlloc_5762_; 
v_reuseFailAlloc_5762_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5762_, 0, v___x_5756_);
lean_ctor_set(v_reuseFailAlloc_5762_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5762_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5762_, 3, v_r_5743_);
lean_ctor_set(v_reuseFailAlloc_5762_, 4, v_r_5575_);
v___x_5758_ = v_reuseFailAlloc_5762_;
goto v_reusejp_5757_;
}
v_reusejp_5757_:
{
lean_object* v___x_5760_; 
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 4, v___x_5758_);
lean_ctor_set(v___x_5736_, 3, v___y_5754_);
lean_ctor_set(v___x_5736_, 2, v_v_5741_);
lean_ctor_set(v___x_5736_, 1, v_k_5740_);
lean_ctor_set(v___x_5736_, 0, v___x_5751_);
v___x_5760_ = v___x_5736_;
goto v_reusejp_5759_;
}
else
{
lean_object* v_reuseFailAlloc_5761_; 
v_reuseFailAlloc_5761_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5761_, 0, v___x_5751_);
lean_ctor_set(v_reuseFailAlloc_5761_, 1, v_k_5740_);
lean_ctor_set(v_reuseFailAlloc_5761_, 2, v_v_5741_);
lean_ctor_set(v_reuseFailAlloc_5761_, 3, v___y_5754_);
lean_ctor_set(v_reuseFailAlloc_5761_, 4, v___x_5758_);
v___x_5760_ = v_reuseFailAlloc_5761_;
goto v_reusejp_5759_;
}
v_reusejp_5759_:
{
return v___x_5760_;
}
}
}
v___jp_5764_:
{
lean_object* v___x_5766_; lean_object* v___x_5768_; 
v___x_5766_ = lean_nat_add(v___x_5763_, v___y_5765_);
lean_dec(v___y_5765_);
lean_dec(v___x_5763_);
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 4, v_l_5742_);
lean_ctor_set(v___x_5577_, 3, v_l_5725_);
lean_ctor_set(v___x_5577_, 2, v_v_5724_);
lean_ctor_set(v___x_5577_, 1, v_k_5723_);
lean_ctor_set(v___x_5577_, 0, v___x_5766_);
v___x_5768_ = v___x_5577_;
goto v_reusejp_5767_;
}
else
{
lean_object* v_reuseFailAlloc_5772_; 
v_reuseFailAlloc_5772_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5772_, 0, v___x_5766_);
lean_ctor_set(v_reuseFailAlloc_5772_, 1, v_k_5723_);
lean_ctor_set(v_reuseFailAlloc_5772_, 2, v_v_5724_);
lean_ctor_set(v_reuseFailAlloc_5772_, 3, v_l_5725_);
lean_ctor_set(v_reuseFailAlloc_5772_, 4, v_l_5742_);
v___x_5768_ = v_reuseFailAlloc_5772_;
goto v_reusejp_5767_;
}
v_reusejp_5767_:
{
lean_object* v___x_5769_; 
v___x_5769_ = lean_nat_add(v___x_5720_, v_size_5721_);
if (lean_obj_tag(v_r_5743_) == 0)
{
lean_object* v_size_5770_; 
v_size_5770_ = lean_ctor_get(v_r_5743_, 0);
lean_inc(v_size_5770_);
v___y_5753_ = v___x_5769_;
v___y_5754_ = v___x_5768_;
v___y_5755_ = v_size_5770_;
goto v___jp_5752_;
}
else
{
lean_object* v___x_5771_; 
v___x_5771_ = lean_unsigned_to_nat(0u);
v___y_5753_ = v___x_5769_;
v___y_5754_ = v___x_5768_;
v___y_5755_ = v___x_5771_;
goto v___jp_5752_;
}
}
}
}
}
else
{
lean_object* v___x_5781_; lean_object* v___x_5782_; lean_object* v___x_5783_; lean_object* v___x_5784_; lean_object* v___x_5786_; 
lean_del_object(v___x_5577_);
v___x_5781_ = lean_nat_add(v___x_5720_, v_size_5722_);
lean_dec(v_size_5722_);
v___x_5782_ = lean_nat_add(v___x_5781_, v_size_5721_);
lean_dec(v___x_5781_);
v___x_5783_ = lean_nat_add(v___x_5720_, v_size_5721_);
v___x_5784_ = lean_nat_add(v___x_5783_, v_size_5739_);
lean_dec(v___x_5783_);
lean_inc_ref(v_r_5575_);
if (v_isShared_5737_ == 0)
{
lean_ctor_set(v___x_5736_, 4, v_r_5575_);
lean_ctor_set(v___x_5736_, 3, v_r_5726_);
lean_ctor_set(v___x_5736_, 2, v_v_5573_);
lean_ctor_set(v___x_5736_, 1, v_k_5572_);
lean_ctor_set(v___x_5736_, 0, v___x_5784_);
v___x_5786_ = v___x_5736_;
goto v_reusejp_5785_;
}
else
{
lean_object* v_reuseFailAlloc_5799_; 
v_reuseFailAlloc_5799_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5799_, 0, v___x_5784_);
lean_ctor_set(v_reuseFailAlloc_5799_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5799_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5799_, 3, v_r_5726_);
lean_ctor_set(v_reuseFailAlloc_5799_, 4, v_r_5575_);
v___x_5786_ = v_reuseFailAlloc_5799_;
goto v_reusejp_5785_;
}
v_reusejp_5785_:
{
lean_object* v___x_5788_; uint8_t v_isShared_5789_; uint8_t v_isSharedCheck_5793_; 
v_isSharedCheck_5793_ = !lean_is_exclusive(v_r_5575_);
if (v_isSharedCheck_5793_ == 0)
{
lean_object* v_unused_5794_; lean_object* v_unused_5795_; lean_object* v_unused_5796_; lean_object* v_unused_5797_; lean_object* v_unused_5798_; 
v_unused_5794_ = lean_ctor_get(v_r_5575_, 4);
lean_dec(v_unused_5794_);
v_unused_5795_ = lean_ctor_get(v_r_5575_, 3);
lean_dec(v_unused_5795_);
v_unused_5796_ = lean_ctor_get(v_r_5575_, 2);
lean_dec(v_unused_5796_);
v_unused_5797_ = lean_ctor_get(v_r_5575_, 1);
lean_dec(v_unused_5797_);
v_unused_5798_ = lean_ctor_get(v_r_5575_, 0);
lean_dec(v_unused_5798_);
v___x_5788_ = v_r_5575_;
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
else
{
lean_dec(v_r_5575_);
v___x_5788_ = lean_box(0);
v_isShared_5789_ = v_isSharedCheck_5793_;
goto v_resetjp_5787_;
}
v_resetjp_5787_:
{
lean_object* v___x_5791_; 
if (v_isShared_5789_ == 0)
{
lean_ctor_set(v___x_5788_, 4, v___x_5786_);
lean_ctor_set(v___x_5788_, 3, v_l_5725_);
lean_ctor_set(v___x_5788_, 2, v_v_5724_);
lean_ctor_set(v___x_5788_, 1, v_k_5723_);
lean_ctor_set(v___x_5788_, 0, v___x_5782_);
v___x_5791_ = v___x_5788_;
goto v_reusejp_5790_;
}
else
{
lean_object* v_reuseFailAlloc_5792_; 
v_reuseFailAlloc_5792_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5792_, 0, v___x_5782_);
lean_ctor_set(v_reuseFailAlloc_5792_, 1, v_k_5723_);
lean_ctor_set(v_reuseFailAlloc_5792_, 2, v_v_5724_);
lean_ctor_set(v_reuseFailAlloc_5792_, 3, v_l_5725_);
lean_ctor_set(v_reuseFailAlloc_5792_, 4, v___x_5786_);
v___x_5791_ = v_reuseFailAlloc_5792_;
goto v_reusejp_5790_;
}
v_reusejp_5790_:
{
return v___x_5791_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5806_; 
v_l_5806_ = lean_ctor_get(v_impl_5719_, 3);
if (lean_obj_tag(v_l_5806_) == 0)
{
lean_object* v_r_5807_; lean_object* v_k_5808_; lean_object* v_v_5809_; lean_object* v___x_5811_; uint8_t v_isShared_5812_; uint8_t v_isSharedCheck_5820_; 
lean_inc_ref(v_l_5806_);
v_r_5807_ = lean_ctor_get(v_impl_5719_, 4);
v_k_5808_ = lean_ctor_get(v_impl_5719_, 1);
v_v_5809_ = lean_ctor_get(v_impl_5719_, 2);
v_isSharedCheck_5820_ = !lean_is_exclusive(v_impl_5719_);
if (v_isSharedCheck_5820_ == 0)
{
lean_object* v_unused_5821_; lean_object* v_unused_5822_; 
v_unused_5821_ = lean_ctor_get(v_impl_5719_, 3);
lean_dec(v_unused_5821_);
v_unused_5822_ = lean_ctor_get(v_impl_5719_, 0);
lean_dec(v_unused_5822_);
v___x_5811_ = v_impl_5719_;
v_isShared_5812_ = v_isSharedCheck_5820_;
goto v_resetjp_5810_;
}
else
{
lean_inc(v_r_5807_);
lean_inc(v_v_5809_);
lean_inc(v_k_5808_);
lean_dec(v_impl_5719_);
v___x_5811_ = lean_box(0);
v_isShared_5812_ = v_isSharedCheck_5820_;
goto v_resetjp_5810_;
}
v_resetjp_5810_:
{
lean_object* v___x_5813_; lean_object* v___x_5815_; 
v___x_5813_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5807_);
if (v_isShared_5812_ == 0)
{
lean_ctor_set(v___x_5811_, 3, v_r_5807_);
lean_ctor_set(v___x_5811_, 2, v_v_5573_);
lean_ctor_set(v___x_5811_, 1, v_k_5572_);
lean_ctor_set(v___x_5811_, 0, v___x_5720_);
v___x_5815_ = v___x_5811_;
goto v_reusejp_5814_;
}
else
{
lean_object* v_reuseFailAlloc_5819_; 
v_reuseFailAlloc_5819_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5819_, 0, v___x_5720_);
lean_ctor_set(v_reuseFailAlloc_5819_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5819_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5819_, 3, v_r_5807_);
lean_ctor_set(v_reuseFailAlloc_5819_, 4, v_r_5807_);
v___x_5815_ = v_reuseFailAlloc_5819_;
goto v_reusejp_5814_;
}
v_reusejp_5814_:
{
lean_object* v___x_5817_; 
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 4, v___x_5815_);
lean_ctor_set(v___x_5577_, 3, v_l_5806_);
lean_ctor_set(v___x_5577_, 2, v_v_5809_);
lean_ctor_set(v___x_5577_, 1, v_k_5808_);
lean_ctor_set(v___x_5577_, 0, v___x_5813_);
v___x_5817_ = v___x_5577_;
goto v_reusejp_5816_;
}
else
{
lean_object* v_reuseFailAlloc_5818_; 
v_reuseFailAlloc_5818_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5818_, 0, v___x_5813_);
lean_ctor_set(v_reuseFailAlloc_5818_, 1, v_k_5808_);
lean_ctor_set(v_reuseFailAlloc_5818_, 2, v_v_5809_);
lean_ctor_set(v_reuseFailAlloc_5818_, 3, v_l_5806_);
lean_ctor_set(v_reuseFailAlloc_5818_, 4, v___x_5815_);
v___x_5817_ = v_reuseFailAlloc_5818_;
goto v_reusejp_5816_;
}
v_reusejp_5816_:
{
return v___x_5817_;
}
}
}
}
else
{
lean_object* v_r_5823_; 
v_r_5823_ = lean_ctor_get(v_impl_5719_, 4);
lean_inc(v_r_5823_);
if (lean_obj_tag(v_r_5823_) == 0)
{
lean_object* v_k_5824_; lean_object* v_v_5825_; lean_object* v___x_5827_; uint8_t v_isShared_5828_; uint8_t v_isSharedCheck_5848_; 
lean_inc(v_l_5806_);
v_k_5824_ = lean_ctor_get(v_impl_5719_, 1);
v_v_5825_ = lean_ctor_get(v_impl_5719_, 2);
v_isSharedCheck_5848_ = !lean_is_exclusive(v_impl_5719_);
if (v_isSharedCheck_5848_ == 0)
{
lean_object* v_unused_5849_; lean_object* v_unused_5850_; lean_object* v_unused_5851_; 
v_unused_5849_ = lean_ctor_get(v_impl_5719_, 4);
lean_dec(v_unused_5849_);
v_unused_5850_ = lean_ctor_get(v_impl_5719_, 3);
lean_dec(v_unused_5850_);
v_unused_5851_ = lean_ctor_get(v_impl_5719_, 0);
lean_dec(v_unused_5851_);
v___x_5827_ = v_impl_5719_;
v_isShared_5828_ = v_isSharedCheck_5848_;
goto v_resetjp_5826_;
}
else
{
lean_inc(v_v_5825_);
lean_inc(v_k_5824_);
lean_dec(v_impl_5719_);
v___x_5827_ = lean_box(0);
v_isShared_5828_ = v_isSharedCheck_5848_;
goto v_resetjp_5826_;
}
v_resetjp_5826_:
{
lean_object* v_k_5829_; lean_object* v_v_5830_; lean_object* v___x_5832_; uint8_t v_isShared_5833_; uint8_t v_isSharedCheck_5844_; 
v_k_5829_ = lean_ctor_get(v_r_5823_, 1);
v_v_5830_ = lean_ctor_get(v_r_5823_, 2);
v_isSharedCheck_5844_ = !lean_is_exclusive(v_r_5823_);
if (v_isSharedCheck_5844_ == 0)
{
lean_object* v_unused_5845_; lean_object* v_unused_5846_; lean_object* v_unused_5847_; 
v_unused_5845_ = lean_ctor_get(v_r_5823_, 4);
lean_dec(v_unused_5845_);
v_unused_5846_ = lean_ctor_get(v_r_5823_, 3);
lean_dec(v_unused_5846_);
v_unused_5847_ = lean_ctor_get(v_r_5823_, 0);
lean_dec(v_unused_5847_);
v___x_5832_ = v_r_5823_;
v_isShared_5833_ = v_isSharedCheck_5844_;
goto v_resetjp_5831_;
}
else
{
lean_inc(v_v_5830_);
lean_inc(v_k_5829_);
lean_dec(v_r_5823_);
v___x_5832_ = lean_box(0);
v_isShared_5833_ = v_isSharedCheck_5844_;
goto v_resetjp_5831_;
}
v_resetjp_5831_:
{
lean_object* v___x_5834_; lean_object* v___x_5836_; 
v___x_5834_ = lean_unsigned_to_nat(3u);
if (v_isShared_5833_ == 0)
{
lean_ctor_set(v___x_5832_, 4, v_l_5806_);
lean_ctor_set(v___x_5832_, 3, v_l_5806_);
lean_ctor_set(v___x_5832_, 2, v_v_5825_);
lean_ctor_set(v___x_5832_, 1, v_k_5824_);
lean_ctor_set(v___x_5832_, 0, v___x_5720_);
v___x_5836_ = v___x_5832_;
goto v_reusejp_5835_;
}
else
{
lean_object* v_reuseFailAlloc_5843_; 
v_reuseFailAlloc_5843_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5843_, 0, v___x_5720_);
lean_ctor_set(v_reuseFailAlloc_5843_, 1, v_k_5824_);
lean_ctor_set(v_reuseFailAlloc_5843_, 2, v_v_5825_);
lean_ctor_set(v_reuseFailAlloc_5843_, 3, v_l_5806_);
lean_ctor_set(v_reuseFailAlloc_5843_, 4, v_l_5806_);
v___x_5836_ = v_reuseFailAlloc_5843_;
goto v_reusejp_5835_;
}
v_reusejp_5835_:
{
lean_object* v___x_5838_; 
if (v_isShared_5828_ == 0)
{
lean_ctor_set(v___x_5827_, 4, v_l_5806_);
lean_ctor_set(v___x_5827_, 2, v_v_5573_);
lean_ctor_set(v___x_5827_, 1, v_k_5572_);
lean_ctor_set(v___x_5827_, 0, v___x_5720_);
v___x_5838_ = v___x_5827_;
goto v_reusejp_5837_;
}
else
{
lean_object* v_reuseFailAlloc_5842_; 
v_reuseFailAlloc_5842_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5842_, 0, v___x_5720_);
lean_ctor_set(v_reuseFailAlloc_5842_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5842_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5842_, 3, v_l_5806_);
lean_ctor_set(v_reuseFailAlloc_5842_, 4, v_l_5806_);
v___x_5838_ = v_reuseFailAlloc_5842_;
goto v_reusejp_5837_;
}
v_reusejp_5837_:
{
lean_object* v___x_5840_; 
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 4, v___x_5838_);
lean_ctor_set(v___x_5577_, 3, v___x_5836_);
lean_ctor_set(v___x_5577_, 2, v_v_5830_);
lean_ctor_set(v___x_5577_, 1, v_k_5829_);
lean_ctor_set(v___x_5577_, 0, v___x_5834_);
v___x_5840_ = v___x_5577_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5841_; 
v_reuseFailAlloc_5841_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5841_, 0, v___x_5834_);
lean_ctor_set(v_reuseFailAlloc_5841_, 1, v_k_5829_);
lean_ctor_set(v_reuseFailAlloc_5841_, 2, v_v_5830_);
lean_ctor_set(v_reuseFailAlloc_5841_, 3, v___x_5836_);
lean_ctor_set(v_reuseFailAlloc_5841_, 4, v___x_5838_);
v___x_5840_ = v_reuseFailAlloc_5841_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
return v___x_5840_;
}
}
}
}
}
}
else
{
lean_object* v___x_5852_; lean_object* v___x_5854_; 
v___x_5852_ = lean_unsigned_to_nat(2u);
if (v_isShared_5578_ == 0)
{
lean_ctor_set(v___x_5577_, 4, v_r_5823_);
lean_ctor_set(v___x_5577_, 3, v_impl_5719_);
lean_ctor_set(v___x_5577_, 0, v___x_5852_);
v___x_5854_ = v___x_5577_;
goto v_reusejp_5853_;
}
else
{
lean_object* v_reuseFailAlloc_5855_; 
v_reuseFailAlloc_5855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5855_, 0, v___x_5852_);
lean_ctor_set(v_reuseFailAlloc_5855_, 1, v_k_5572_);
lean_ctor_set(v_reuseFailAlloc_5855_, 2, v_v_5573_);
lean_ctor_set(v_reuseFailAlloc_5855_, 3, v_impl_5719_);
lean_ctor_set(v_reuseFailAlloc_5855_, 4, v_r_5823_);
v___x_5854_ = v_reuseFailAlloc_5855_;
goto v_reusejp_5853_;
}
v_reusejp_5853_:
{
return v___x_5854_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5857_; lean_object* v___x_5858_; 
v___x_5857_ = lean_unsigned_to_nat(1u);
v___x_5858_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5858_, 0, v___x_5857_);
lean_ctor_set(v___x_5858_, 1, v_k_5568_);
lean_ctor_set(v___x_5858_, 2, v_v_5569_);
lean_ctor_set(v___x_5858_, 3, v_t_5570_);
lean_ctor_set(v___x_5858_, 4, v_t_5570_);
return v___x_5858_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5859_, lean_object* v_t_5860_){
_start:
{
if (lean_obj_tag(v_t_5860_) == 0)
{
lean_object* v_k_5861_; lean_object* v_l_5862_; lean_object* v_r_5863_; uint8_t v___x_5864_; 
v_k_5861_ = lean_ctor_get(v_t_5860_, 1);
v_l_5862_ = lean_ctor_get(v_t_5860_, 3);
v_r_5863_ = lean_ctor_get(v_t_5860_, 4);
v___x_5864_ = lean_nat_dec_lt(v_k_5861_, v_k_5859_);
if (v___x_5864_ == 0)
{
uint8_t v___x_5865_; 
v___x_5865_ = lean_nat_dec_eq(v_k_5861_, v_k_5859_);
if (v___x_5865_ == 0)
{
v_t_5860_ = v_r_5863_;
goto _start;
}
else
{
return v___x_5865_;
}
}
else
{
v_t_5860_ = v_l_5862_;
goto _start;
}
}
else
{
uint8_t v___x_5868_; 
v___x_5868_ = 0;
return v___x_5868_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5869_, lean_object* v_t_5870_){
_start:
{
uint8_t v_res_5871_; lean_object* v_r_5872_; 
v_res_5871_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5869_, v_t_5870_);
lean_dec(v_t_5870_);
lean_dec(v_k_5869_);
v_r_5872_ = lean_box(v_res_5871_);
return v_r_5872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5873_, lean_object* v_e_5874_){
_start:
{
lean_object* v_defaultInstances_5875_; lean_object* v_priorities_5876_; lean_object* v___x_5878_; uint8_t v_isShared_5879_; uint8_t v_isSharedCheck_5903_; 
v_defaultInstances_5875_ = lean_ctor_get(v_d_5873_, 0);
v_priorities_5876_ = lean_ctor_get(v_d_5873_, 1);
v_isSharedCheck_5903_ = !lean_is_exclusive(v_d_5873_);
if (v_isSharedCheck_5903_ == 0)
{
v___x_5878_ = v_d_5873_;
v_isShared_5879_ = v_isSharedCheck_5903_;
goto v_resetjp_5877_;
}
else
{
lean_inc(v_priorities_5876_);
lean_inc(v_defaultInstances_5875_);
lean_dec(v_d_5873_);
v___x_5878_ = lean_box(0);
v_isShared_5879_ = v_isSharedCheck_5903_;
goto v_resetjp_5877_;
}
v_resetjp_5877_:
{
lean_object* v_className_5880_; lean_object* v_instanceName_5881_; lean_object* v_priority_5882_; lean_object* v___y_5884_; uint8_t v___x_5900_; 
v_className_5880_ = lean_ctor_get(v_e_5874_, 0);
lean_inc(v_className_5880_);
v_instanceName_5881_ = lean_ctor_get(v_e_5874_, 1);
lean_inc(v_instanceName_5881_);
v_priority_5882_ = lean_ctor_get(v_e_5874_, 2);
lean_inc(v_priority_5882_);
lean_dec_ref(v_e_5874_);
v___x_5900_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5882_, v_priorities_5876_);
if (v___x_5900_ == 0)
{
lean_object* v___x_5901_; lean_object* v___x_5902_; 
v___x_5901_ = lean_box(0);
lean_inc(v_priority_5882_);
v___x_5902_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5882_, v___x_5901_, v_priorities_5876_);
v___y_5884_ = v___x_5902_;
goto v___jp_5883_;
}
else
{
v___y_5884_ = v_priorities_5876_;
goto v___jp_5883_;
}
v___jp_5883_:
{
lean_object* v___x_5885_; 
v___x_5885_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5875_, v_className_5880_);
if (lean_obj_tag(v___x_5885_) == 0)
{
lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; lean_object* v___x_5891_; 
v___x_5886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5886_, 0, v_instanceName_5881_);
lean_ctor_set(v___x_5886_, 1, v_priority_5882_);
v___x_5887_ = lean_box(0);
v___x_5888_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5888_, 0, v___x_5886_);
lean_ctor_set(v___x_5888_, 1, v___x_5887_);
v___x_5889_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5880_, v___x_5888_, v_defaultInstances_5875_);
if (v_isShared_5879_ == 0)
{
lean_ctor_set(v___x_5878_, 1, v___y_5884_);
lean_ctor_set(v___x_5878_, 0, v___x_5889_);
v___x_5891_ = v___x_5878_;
goto v_reusejp_5890_;
}
else
{
lean_object* v_reuseFailAlloc_5892_; 
v_reuseFailAlloc_5892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5892_, 0, v___x_5889_);
lean_ctor_set(v_reuseFailAlloc_5892_, 1, v___y_5884_);
v___x_5891_ = v_reuseFailAlloc_5892_;
goto v_reusejp_5890_;
}
v_reusejp_5890_:
{
return v___x_5891_;
}
}
else
{
lean_object* v_val_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5898_; 
v_val_5893_ = lean_ctor_get(v___x_5885_, 0);
lean_inc(v_val_5893_);
lean_dec_ref_known(v___x_5885_, 1);
v___x_5894_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5894_, 0, v_instanceName_5881_);
lean_ctor_set(v___x_5894_, 1, v_priority_5882_);
v___x_5895_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5894_);
lean_ctor_set(v___x_5895_, 1, v_val_5893_);
v___x_5896_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5880_, v___x_5895_, v_defaultInstances_5875_);
if (v_isShared_5879_ == 0)
{
lean_ctor_set(v___x_5878_, 1, v___y_5884_);
lean_ctor_set(v___x_5878_, 0, v___x_5896_);
v___x_5898_ = v___x_5878_;
goto v_reusejp_5897_;
}
else
{
lean_object* v_reuseFailAlloc_5899_; 
v_reuseFailAlloc_5899_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5899_, 0, v___x_5896_);
lean_ctor_set(v_reuseFailAlloc_5899_, 1, v___y_5884_);
v___x_5898_ = v_reuseFailAlloc_5899_;
goto v_reusejp_5897_;
}
v_reusejp_5897_:
{
return v___x_5898_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5904_, lean_object* v_k_5905_, lean_object* v_t_5906_){
_start:
{
uint8_t v___x_5907_; 
v___x_5907_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5905_, v_t_5906_);
return v___x_5907_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5908_, lean_object* v_k_5909_, lean_object* v_t_5910_){
_start:
{
uint8_t v_res_5911_; lean_object* v_r_5912_; 
v_res_5911_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5908_, v_k_5909_, v_t_5910_);
lean_dec(v_t_5910_);
lean_dec(v_k_5909_);
v_r_5912_ = lean_box(v_res_5911_);
return v_r_5912_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5913_, lean_object* v_k_5914_, lean_object* v_v_5915_, lean_object* v_t_5916_, lean_object* v_hl_5917_){
_start:
{
lean_object* v___x_5918_; 
v___x_5918_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5914_, v_v_5915_, v_t_5916_);
return v___x_5918_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object* v_env_5919_, lean_object* v_as_5920_, size_t v_i_5921_, size_t v_stop_5922_, lean_object* v_b_5923_){
_start:
{
lean_object* v___y_5925_; uint8_t v___x_5929_; 
v___x_5929_ = lean_usize_dec_eq(v_i_5921_, v_stop_5922_);
if (v___x_5929_ == 0)
{
lean_object* v___x_5930_; lean_object* v_instanceName_5931_; uint8_t v___x_5932_; lean_object* v___x_5933_; uint8_t v___x_5934_; 
v___x_5930_ = lean_array_uget_borrowed(v_as_5920_, v_i_5921_);
v_instanceName_5931_ = lean_ctor_get(v___x_5930_, 1);
v___x_5932_ = 1;
lean_inc_ref(v_env_5919_);
v___x_5933_ = l_Lean_Environment_setExporting(v_env_5919_, v___x_5932_);
lean_inc(v_instanceName_5931_);
v___x_5934_ = l_Lean_Environment_contains(v___x_5933_, v_instanceName_5931_, v___x_5929_);
if (v___x_5934_ == 0)
{
v___y_5925_ = v_b_5923_;
goto v___jp_5924_;
}
else
{
lean_object* v___x_5935_; 
lean_inc(v___x_5930_);
v___x_5935_ = lean_array_push(v_b_5923_, v___x_5930_);
v___y_5925_ = v___x_5935_;
goto v___jp_5924_;
}
}
else
{
lean_dec_ref(v_env_5919_);
return v_b_5923_;
}
v___jp_5924_:
{
size_t v___x_5926_; size_t v___x_5927_; 
v___x_5926_ = ((size_t)1ULL);
v___x_5927_ = lean_usize_add(v_i_5921_, v___x_5926_);
v_i_5921_ = v___x_5927_;
v_b_5923_ = v___y_5925_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_5936_, lean_object* v_as_5937_, lean_object* v_i_5938_, lean_object* v_stop_5939_, lean_object* v_b_5940_){
_start:
{
size_t v_i_boxed_5941_; size_t v_stop_boxed_5942_; lean_object* v_res_5943_; 
v_i_boxed_5941_ = lean_unbox_usize(v_i_5938_);
lean_dec(v_i_5938_);
v_stop_boxed_5942_ = lean_unbox_usize(v_stop_5939_);
lean_dec(v_stop_5939_);
v_res_5943_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5936_, v_as_5937_, v_i_boxed_5941_, v_stop_boxed_5942_, v_b_5940_);
lean_dec_ref(v_as_5937_);
return v_res_5943_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_env_5946_, lean_object* v_x_5947_, lean_object* v_entries_5948_){
_start:
{
lean_object* v_all_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; lean_object* v___x_5952_; uint8_t v___x_5953_; 
v_all_5949_ = lean_array_mk(v_entries_5948_);
v___x_5950_ = lean_unsigned_to_nat(0u);
v___x_5951_ = lean_array_get_size(v_all_5949_);
v___x_5952_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5953_ = lean_nat_dec_lt(v___x_5950_, v___x_5951_);
if (v___x_5953_ == 0)
{
lean_object* v___x_5954_; 
lean_dec_ref(v_env_5946_);
v___x_5954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5954_, 0, v___x_5952_);
lean_ctor_set(v___x_5954_, 1, v___x_5952_);
lean_ctor_set(v___x_5954_, 2, v_all_5949_);
return v___x_5954_;
}
else
{
size_t v___x_5955_; size_t v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; 
v___x_5955_ = ((size_t)0ULL);
v___x_5956_ = lean_usize_of_nat(v___x_5951_);
v___x_5957_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5946_, v_all_5949_, v___x_5955_, v___x_5956_, v___x_5952_);
lean_inc_ref(v___x_5957_);
v___x_5958_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5958_, 0, v___x_5957_);
lean_ctor_set(v___x_5958_, 1, v___x_5957_);
lean_ctor_set(v___x_5958_, 2, v_all_5949_);
return v___x_5958_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5959_, lean_object* v_x_5960_, lean_object* v_entries_5961_){
_start:
{
lean_object* v_res_5962_; 
v_res_5962_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5959_, v_x_5960_, v_entries_5961_);
lean_dec_ref(v_x_5960_);
return v_res_5962_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5963_){
_start:
{
lean_object* v___x_5964_; 
v___x_5964_ = lean_array_mk(v_es_5963_);
return v___x_5964_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5965_, size_t v_i_5966_, size_t v_stop_5967_, lean_object* v_b_5968_){
_start:
{
uint8_t v___x_5969_; 
v___x_5969_ = lean_usize_dec_eq(v_i_5966_, v_stop_5967_);
if (v___x_5969_ == 0)
{
lean_object* v___x_5970_; lean_object* v___x_5971_; size_t v___x_5972_; size_t v___x_5973_; 
v___x_5970_ = lean_array_uget_borrowed(v_as_5965_, v_i_5966_);
lean_inc(v___x_5970_);
v___x_5971_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5968_, v___x_5970_);
v___x_5972_ = ((size_t)1ULL);
v___x_5973_ = lean_usize_add(v_i_5966_, v___x_5972_);
v_i_5966_ = v___x_5973_;
v_b_5968_ = v___x_5971_;
goto _start;
}
else
{
return v_b_5968_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5975_, lean_object* v_i_5976_, lean_object* v_stop_5977_, lean_object* v_b_5978_){
_start:
{
size_t v_i_boxed_5979_; size_t v_stop_boxed_5980_; lean_object* v_res_5981_; 
v_i_boxed_5979_ = lean_unbox_usize(v_i_5976_);
lean_dec(v_i_5976_);
v_stop_boxed_5980_ = lean_unbox_usize(v_stop_5977_);
lean_dec(v_stop_5977_);
v_res_5981_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5975_, v_i_boxed_5979_, v_stop_boxed_5980_, v_b_5978_);
lean_dec_ref(v_as_5975_);
return v_res_5981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5982_, size_t v_i_5983_, size_t v_stop_5984_, lean_object* v_b_5985_){
_start:
{
lean_object* v___y_5987_; uint8_t v___x_5991_; 
v___x_5991_ = lean_usize_dec_eq(v_i_5983_, v_stop_5984_);
if (v___x_5991_ == 0)
{
lean_object* v___x_5992_; lean_object* v___x_5993_; lean_object* v___x_5994_; uint8_t v___x_5995_; 
v___x_5992_ = lean_array_uget_borrowed(v_as_5982_, v_i_5983_);
v___x_5993_ = lean_unsigned_to_nat(0u);
v___x_5994_ = lean_array_get_size(v___x_5992_);
v___x_5995_ = lean_nat_dec_lt(v___x_5993_, v___x_5994_);
if (v___x_5995_ == 0)
{
v___y_5987_ = v_b_5985_;
goto v___jp_5986_;
}
else
{
size_t v___x_5996_; size_t v___x_5997_; lean_object* v___x_5998_; 
v___x_5996_ = ((size_t)0ULL);
v___x_5997_ = lean_usize_of_nat(v___x_5994_);
v___x_5998_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5992_, v___x_5996_, v___x_5997_, v_b_5985_);
v___y_5987_ = v___x_5998_;
goto v___jp_5986_;
}
}
else
{
return v_b_5985_;
}
v___jp_5986_:
{
size_t v___x_5988_; size_t v___x_5989_; 
v___x_5988_ = ((size_t)1ULL);
v___x_5989_ = lean_usize_add(v_i_5983_, v___x_5988_);
v_i_5983_ = v___x_5989_;
v_b_5985_ = v___y_5987_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5999_, lean_object* v_i_6000_, lean_object* v_stop_6001_, lean_object* v_b_6002_){
_start:
{
size_t v_i_boxed_6003_; size_t v_stop_boxed_6004_; lean_object* v_res_6005_; 
v_i_boxed_6003_ = lean_unbox_usize(v_i_6000_);
lean_dec(v_i_6000_);
v_stop_boxed_6004_ = lean_unbox_usize(v_stop_6001_);
lean_dec(v_stop_6001_);
v_res_6005_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5999_, v_i_boxed_6003_, v_stop_boxed_6004_, v_b_6002_);
lean_dec_ref(v_as_5999_);
return v_res_6005_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_6006_, lean_object* v_as_6007_){
_start:
{
lean_object* v___x_6008_; lean_object* v___x_6009_; uint8_t v___x_6010_; 
v___x_6008_ = lean_unsigned_to_nat(0u);
v___x_6009_ = lean_array_get_size(v_as_6007_);
v___x_6010_ = lean_nat_dec_lt(v___x_6008_, v___x_6009_);
if (v___x_6010_ == 0)
{
return v_initState_6006_;
}
else
{
size_t v___x_6011_; size_t v___x_6012_; lean_object* v___x_6013_; 
v___x_6011_ = ((size_t)0ULL);
v___x_6012_ = lean_usize_of_nat(v___x_6009_);
v___x_6013_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_6007_, v___x_6011_, v___x_6012_, v_initState_6006_);
return v___x_6013_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_6014_, lean_object* v_as_6015_){
_start:
{
lean_object* v_res_6016_; 
v_res_6016_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_6014_, v_as_6015_);
lean_dec_ref(v_as_6015_);
return v_res_6016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_6017_){
_start:
{
lean_object* v___x_6018_; lean_object* v___x_6019_; 
v___x_6018_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_6019_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_6018_, v_es_6017_);
return v___x_6019_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_6020_){
_start:
{
lean_object* v_res_6021_; 
v_res_6021_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_6020_);
lean_dec_ref(v_es_6020_);
return v_res_6021_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6043_; lean_object* v___x_6044_; 
v___x_6043_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_6044_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_6043_);
return v___x_6044_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_6045_){
_start:
{
lean_object* v_res_6046_; 
v_res_6046_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_6046_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_addEntryFn_6047_, lean_object* v___x_6048_, lean_object* v_s_6049_){
_start:
{
lean_object* v_importedEntries_6050_; lean_object* v_state_6051_; lean_object* v___x_6053_; uint8_t v_isShared_6054_; uint8_t v_isSharedCheck_6059_; 
v_importedEntries_6050_ = lean_ctor_get(v_s_6049_, 0);
v_state_6051_ = lean_ctor_get(v_s_6049_, 1);
v_isSharedCheck_6059_ = !lean_is_exclusive(v_s_6049_);
if (v_isSharedCheck_6059_ == 0)
{
v___x_6053_ = v_s_6049_;
v_isShared_6054_ = v_isSharedCheck_6059_;
goto v_resetjp_6052_;
}
else
{
lean_inc(v_state_6051_);
lean_inc(v_importedEntries_6050_);
lean_dec(v_s_6049_);
v___x_6053_ = lean_box(0);
v_isShared_6054_ = v_isSharedCheck_6059_;
goto v_resetjp_6052_;
}
v_resetjp_6052_:
{
lean_object* v_state_6055_; lean_object* v___x_6057_; 
v_state_6055_ = lean_apply_2(v_addEntryFn_6047_, v_state_6051_, v___x_6048_);
if (v_isShared_6054_ == 0)
{
lean_ctor_set(v___x_6053_, 1, v_state_6055_);
v___x_6057_ = v___x_6053_;
goto v_reusejp_6056_;
}
else
{
lean_object* v_reuseFailAlloc_6058_; 
v_reuseFailAlloc_6058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_6058_, 0, v_importedEntries_6050_);
lean_ctor_set(v_reuseFailAlloc_6058_, 1, v_state_6055_);
v___x_6057_ = v_reuseFailAlloc_6058_;
goto v_reusejp_6056_;
}
v_reusejp_6056_:
{
return v___x_6057_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_6060_, lean_object* v___y_6061_, lean_object* v___y_6062_){
_start:
{
lean_object* v___x_6064_; lean_object* v_nextMacroScope_6065_; lean_object* v_ngen_6066_; lean_object* v_auxDeclNGen_6067_; lean_object* v_traceState_6068_; lean_object* v_recordedDeps_6069_; lean_object* v_messages_6070_; lean_object* v_infoState_6071_; lean_object* v_snapshotTasks_6072_; lean_object* v___x_6074_; uint8_t v_isShared_6075_; uint8_t v_isSharedCheck_6098_; 
v___x_6064_ = lean_st_ref_take(v___y_6062_);
v_nextMacroScope_6065_ = lean_ctor_get(v___x_6064_, 1);
v_ngen_6066_ = lean_ctor_get(v___x_6064_, 2);
v_auxDeclNGen_6067_ = lean_ctor_get(v___x_6064_, 3);
v_traceState_6068_ = lean_ctor_get(v___x_6064_, 4);
v_recordedDeps_6069_ = lean_ctor_get(v___x_6064_, 6);
v_messages_6070_ = lean_ctor_get(v___x_6064_, 7);
v_infoState_6071_ = lean_ctor_get(v___x_6064_, 8);
v_snapshotTasks_6072_ = lean_ctor_get(v___x_6064_, 9);
v_isSharedCheck_6098_ = !lean_is_exclusive(v___x_6064_);
if (v_isSharedCheck_6098_ == 0)
{
lean_object* v_unused_6099_; lean_object* v_unused_6100_; 
v_unused_6099_ = lean_ctor_get(v___x_6064_, 5);
lean_dec(v_unused_6099_);
v_unused_6100_ = lean_ctor_get(v___x_6064_, 0);
lean_dec(v_unused_6100_);
v___x_6074_ = v___x_6064_;
v_isShared_6075_ = v_isSharedCheck_6098_;
goto v_resetjp_6073_;
}
else
{
lean_inc(v_snapshotTasks_6072_);
lean_inc(v_infoState_6071_);
lean_inc(v_messages_6070_);
lean_inc(v_recordedDeps_6069_);
lean_inc(v_traceState_6068_);
lean_inc(v_auxDeclNGen_6067_);
lean_inc(v_ngen_6066_);
lean_inc(v_nextMacroScope_6065_);
lean_dec(v___x_6064_);
v___x_6074_ = lean_box(0);
v_isShared_6075_ = v_isSharedCheck_6098_;
goto v_resetjp_6073_;
}
v_resetjp_6073_:
{
lean_object* v___x_6076_; lean_object* v___x_6078_; 
v___x_6076_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__1);
if (v_isShared_6075_ == 0)
{
lean_ctor_set(v___x_6074_, 5, v___x_6076_);
lean_ctor_set(v___x_6074_, 0, v_env_6060_);
v___x_6078_ = v___x_6074_;
goto v_reusejp_6077_;
}
else
{
lean_object* v_reuseFailAlloc_6097_; 
v_reuseFailAlloc_6097_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_6097_, 0, v_env_6060_);
lean_ctor_set(v_reuseFailAlloc_6097_, 1, v_nextMacroScope_6065_);
lean_ctor_set(v_reuseFailAlloc_6097_, 2, v_ngen_6066_);
lean_ctor_set(v_reuseFailAlloc_6097_, 3, v_auxDeclNGen_6067_);
lean_ctor_set(v_reuseFailAlloc_6097_, 4, v_traceState_6068_);
lean_ctor_set(v_reuseFailAlloc_6097_, 5, v___x_6076_);
lean_ctor_set(v_reuseFailAlloc_6097_, 6, v_recordedDeps_6069_);
lean_ctor_set(v_reuseFailAlloc_6097_, 7, v_messages_6070_);
lean_ctor_set(v_reuseFailAlloc_6097_, 8, v_infoState_6071_);
lean_ctor_set(v_reuseFailAlloc_6097_, 9, v_snapshotTasks_6072_);
v___x_6078_ = v_reuseFailAlloc_6097_;
goto v_reusejp_6077_;
}
v_reusejp_6077_:
{
lean_object* v___x_6079_; lean_object* v___x_6080_; lean_object* v_mctx_6081_; lean_object* v_zetaDeltaFVarIds_6082_; lean_object* v_postponed_6083_; lean_object* v_diag_6084_; lean_object* v___x_6086_; uint8_t v_isShared_6087_; uint8_t v_isSharedCheck_6095_; 
v___x_6079_ = lean_st_ref_put(v___y_6062_, v___x_6078_);
v___x_6080_ = lean_st_ref_take(v___y_6061_);
v_mctx_6081_ = lean_ctor_get(v___x_6080_, 0);
v_zetaDeltaFVarIds_6082_ = lean_ctor_get(v___x_6080_, 2);
v_postponed_6083_ = lean_ctor_get(v___x_6080_, 3);
v_diag_6084_ = lean_ctor_get(v___x_6080_, 4);
v_isSharedCheck_6095_ = !lean_is_exclusive(v___x_6080_);
if (v_isSharedCheck_6095_ == 0)
{
lean_object* v_unused_6096_; 
v_unused_6096_ = lean_ctor_get(v___x_6080_, 1);
lean_dec(v_unused_6096_);
v___x_6086_ = v___x_6080_;
v_isShared_6087_ = v_isSharedCheck_6095_;
goto v_resetjp_6085_;
}
else
{
lean_inc(v_diag_6084_);
lean_inc(v_postponed_6083_);
lean_inc(v_zetaDeltaFVarIds_6082_);
lean_inc(v_mctx_6081_);
lean_dec(v___x_6080_);
v___x_6086_ = lean_box(0);
v_isShared_6087_ = v_isSharedCheck_6095_;
goto v_resetjp_6085_;
}
v_resetjp_6085_:
{
lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6091_; 
v___x_6088_ = lean_box(0);
v___x_6089_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__5, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__5_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__5);
if (v_isShared_6087_ == 0)
{
lean_ctor_set(v___x_6086_, 1, v___x_6089_);
v___x_6091_ = v___x_6086_;
goto v_reusejp_6090_;
}
else
{
lean_object* v_reuseFailAlloc_6094_; 
v_reuseFailAlloc_6094_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_6094_, 0, v_mctx_6081_);
lean_ctor_set(v_reuseFailAlloc_6094_, 1, v___x_6089_);
lean_ctor_set(v_reuseFailAlloc_6094_, 2, v_zetaDeltaFVarIds_6082_);
lean_ctor_set(v_reuseFailAlloc_6094_, 3, v_postponed_6083_);
lean_ctor_set(v_reuseFailAlloc_6094_, 4, v_diag_6084_);
v___x_6091_ = v_reuseFailAlloc_6094_;
goto v_reusejp_6090_;
}
v_reusejp_6090_:
{
lean_object* v___x_6092_; lean_object* v___x_6093_; 
v___x_6092_ = lean_st_ref_put(v___y_6061_, v___x_6091_);
v___x_6093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6088_);
return v___x_6093_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_6101_, lean_object* v___y_6102_, lean_object* v___y_6103_, lean_object* v___y_6104_){
_start:
{
lean_object* v_res_6105_; 
v_res_6105_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_6101_, v___y_6102_, v___y_6103_);
lean_dec(v___y_6103_);
lean_dec(v___y_6102_);
return v_res_6105_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__1(void){
_start:
{
lean_object* v___x_6107_; lean_object* v___x_6108_; 
v___x_6107_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__0));
v___x_6108_ = l_Lean_stringToMessageData(v___x_6107_);
return v___x_6108_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__3(void){
_start:
{
lean_object* v___x_6110_; lean_object* v___x_6111_; 
v___x_6110_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__2));
v___x_6111_ = l_Lean_stringToMessageData(v___x_6110_);
return v___x_6111_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__5(void){
_start:
{
lean_object* v___x_6113_; lean_object* v___x_6114_; 
v___x_6113_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__4));
v___x_6114_ = l_Lean_stringToMessageData(v___x_6113_);
return v___x_6114_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__7(void){
_start:
{
lean_object* v___x_6116_; lean_object* v___x_6117_; 
v___x_6116_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__6));
v___x_6117_ = l_Lean_stringToMessageData(v___x_6116_);
return v___x_6117_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__9(void){
_start:
{
lean_object* v___x_6119_; lean_object* v___x_6120_; 
v___x_6119_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__1___closed__8));
v___x_6120_ = l_Lean_stringToMessageData(v___x_6119_);
return v___x_6120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__1(lean_object* v_declName_6121_, lean_object* v_prio_6122_, lean_object* v_x_6123_, lean_object* v_type_6124_, lean_object* v___y_6125_, lean_object* v___y_6126_, lean_object* v___y_6127_, lean_object* v___y_6128_){
_start:
{
lean_object* v___x_6130_; 
v___x_6130_ = l_Lean_Expr_getAppFn(v_type_6124_);
if (lean_obj_tag(v___x_6130_) == 4)
{
lean_object* v_declName_6131_; lean_object* v___y_6133_; lean_object* v___y_6134_; lean_object* v___y_6135_; lean_object* v___y_6136_; lean_object* v___x_6153_; lean_object* v_env_6154_; uint8_t v___x_6155_; 
v_declName_6131_ = lean_ctor_get(v___x_6130_, 0);
lean_inc(v_declName_6131_);
lean_dec_ref_known(v___x_6130_, 2);
v___x_6153_ = lean_st_ref_get(v___y_6128_);
v_env_6154_ = lean_ctor_get(v___x_6153_, 0);
lean_inc_ref(v_env_6154_);
lean_dec(v___x_6153_);
v___x_6155_ = l_Lean_isClass(v_env_6154_, v_declName_6131_);
if (v___x_6155_ == 0)
{
lean_object* v___x_6156_; lean_object* v___x_6157_; lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; lean_object* v___x_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v___x_6164_; lean_object* v___x_6165_; lean_object* v___x_6166_; lean_object* v___x_6167_; lean_object* v___x_6168_; lean_object* v___x_6169_; 
lean_dec(v_prio_6122_);
v___x_6156_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__1, &l_Lean_Meta_addDefaultInstance___lam__1___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__1);
v___x_6157_ = l_Lean_MessageData_ofConstName(v_declName_6121_, v___x_6155_);
v___x_6158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6158_, 0, v___x_6156_);
lean_ctor_set(v___x_6158_, 1, v___x_6157_);
v___x_6159_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__3, &l_Lean_Meta_addDefaultInstance___lam__1___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__3);
v___x_6160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6160_, 0, v___x_6158_);
lean_ctor_set(v___x_6160_, 1, v___x_6159_);
lean_inc(v_declName_6131_);
v___x_6161_ = l_Lean_MessageData_ofName(v_declName_6131_);
v___x_6162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6162_, 0, v___x_6160_);
lean_ctor_set(v___x_6162_, 1, v___x_6161_);
v___x_6163_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__5, &l_Lean_Meta_addDefaultInstance___lam__1___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__5);
v___x_6164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6164_, 0, v___x_6162_);
lean_ctor_set(v___x_6164_, 1, v___x_6163_);
v___x_6165_ = l_Lean_MessageData_ofConstName(v_declName_6131_, v___x_6155_);
v___x_6166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6166_, 0, v___x_6164_);
lean_ctor_set(v___x_6166_, 1, v___x_6165_);
v___x_6167_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__7, &l_Lean_Meta_addDefaultInstance___lam__1___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__7);
v___x_6168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6168_, 0, v___x_6166_);
lean_ctor_set(v___x_6168_, 1, v___x_6167_);
v___x_6169_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6168_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_);
return v___x_6169_;
}
else
{
v___y_6133_ = v___y_6125_;
v___y_6134_ = v___y_6126_;
v___y_6135_ = v___y_6127_;
v___y_6136_ = v___y_6128_;
goto v___jp_6132_;
}
v___jp_6132_:
{
lean_object* v___x_6137_; lean_object* v_env_6138_; lean_object* v___x_6139_; lean_object* v_toEnvExtension_6140_; lean_object* v_addEntryFn_6141_; lean_object* v_asyncMode_6142_; uint8_t v_logWrites_6143_; lean_object* v___x_6144_; lean_object* v___f_6145_; lean_object* v___x_6146_; uint8_t v___x_6147_; 
v___x_6137_ = lean_st_ref_get(v___y_6136_);
v_env_6138_ = lean_ctor_get(v___x_6137_, 0);
lean_inc_ref(v_env_6138_);
lean_dec(v___x_6137_);
v___x_6139_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6140_ = lean_ctor_get(v___x_6139_, 0);
v_addEntryFn_6141_ = lean_ctor_get(v___x_6139_, 3);
v_asyncMode_6142_ = lean_ctor_get(v_toEnvExtension_6140_, 2);
v_logWrites_6143_ = lean_ctor_get_uint8(v_toEnvExtension_6140_, sizeof(void*)*6);
v___x_6144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6144_, 0, v_declName_6131_);
lean_ctor_set(v___x_6144_, 1, v_declName_6121_);
lean_ctor_set(v___x_6144_, 2, v_prio_6122_);
lean_inc(v_addEntryFn_6141_);
v___f_6145_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0), 3, 2);
lean_closure_set(v___f_6145_, 0, v_addEntryFn_6141_);
lean_closure_set(v___f_6145_, 1, v___x_6144_);
v___x_6146_ = lean_box(0);
v___x_6147_ = 1;
if (v_logWrites_6143_ == 0)
{
lean_object* v___x_6148_; lean_object* v___x_6149_; 
lean_inc_ref(v_toEnvExtension_6140_);
v___x_6148_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_6140_, v_env_6138_, v___f_6145_, v_asyncMode_6142_, v___x_6146_, v___x_6147_);
v___x_6149_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_6148_, v___y_6134_, v___y_6136_);
return v___x_6149_;
}
else
{
lean_object* v___x_6150_; lean_object* v___x_6151_; lean_object* v___x_6152_; 
lean_inc_ref_n(v_toEnvExtension_6140_, 2);
v___x_6150_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_6140_, v_env_6138_);
lean_dec_ref(v_env_6138_);
v___x_6151_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_6140_, v___x_6150_, v___f_6145_, v_asyncMode_6142_, v___x_6146_, v___x_6147_);
v___x_6152_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_6151_, v___y_6134_, v___y_6136_);
return v___x_6152_;
}
}
}
else
{
lean_object* v___x_6170_; uint8_t v___x_6171_; lean_object* v___x_6172_; lean_object* v___x_6173_; lean_object* v___x_6174_; lean_object* v___x_6175_; lean_object* v___x_6176_; 
lean_dec_ref(v___x_6130_);
lean_dec(v_prio_6122_);
v___x_6170_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__1, &l_Lean_Meta_addDefaultInstance___lam__1___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__1);
v___x_6171_ = 0;
v___x_6172_ = l_Lean_MessageData_ofConstName(v_declName_6121_, v___x_6171_);
v___x_6173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6173_, 0, v___x_6170_);
lean_ctor_set(v___x_6173_, 1, v___x_6172_);
v___x_6174_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__1___closed__9, &l_Lean_Meta_addDefaultInstance___lam__1___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__1___closed__9);
v___x_6175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6175_, 0, v___x_6173_);
lean_ctor_set(v___x_6175_, 1, v___x_6174_);
v___x_6176_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6175_, v___y_6125_, v___y_6126_, v___y_6127_, v___y_6128_);
return v___x_6176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__1___boxed(lean_object* v_declName_6177_, lean_object* v_prio_6178_, lean_object* v_x_6179_, lean_object* v_type_6180_, lean_object* v___y_6181_, lean_object* v___y_6182_, lean_object* v___y_6183_, lean_object* v___y_6184_, lean_object* v___y_6185_){
_start:
{
lean_object* v_res_6186_; 
v_res_6186_ = l_Lean_Meta_addDefaultInstance___lam__1(v_declName_6177_, v_prio_6178_, v_x_6179_, v_type_6180_, v___y_6181_, v___y_6182_, v___y_6183_, v___y_6184_);
lean_dec(v___y_6184_);
lean_dec_ref(v___y_6183_);
lean_dec(v___y_6182_);
lean_dec_ref(v___y_6181_);
lean_dec_ref(v_type_6180_);
lean_dec_ref(v_x_6179_);
return v_res_6186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_6187_, lean_object* v_prio_6188_, lean_object* v_a_6189_, lean_object* v_a_6190_, lean_object* v_a_6191_, lean_object* v_a_6192_){
_start:
{
lean_object* v___f_6194_; lean_object* v___x_6195_; lean_object* v_env_6196_; uint8_t v___x_6197_; lean_object* v___x_6198_; 
lean_inc_n(v_declName_6187_, 2);
v___f_6194_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__1___boxed), 9, 2);
lean_closure_set(v___f_6194_, 0, v_declName_6187_);
lean_closure_set(v___f_6194_, 1, v_prio_6188_);
v___x_6195_ = lean_st_ref_get(v_a_6192_);
v_env_6196_ = lean_ctor_get(v___x_6195_, 0);
lean_inc_ref(v_env_6196_);
lean_dec(v___x_6195_);
v___x_6197_ = 0;
v___x_6198_ = l_Lean_Environment_find_x3f(v_env_6196_, v_declName_6187_, v___x_6197_);
if (lean_obj_tag(v___x_6198_) == 0)
{
lean_object* v___x_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; lean_object* v___x_6203_; lean_object* v___x_6204_; 
lean_dec_ref(v___f_6194_);
v___x_6199_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6___redArg___closed__1);
v___x_6200_ = l_Lean_MessageData_ofConstName(v_declName_6187_, v___x_6197_);
v___x_6201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6201_, 0, v___x_6199_);
lean_ctor_set(v___x_6201_, 1, v___x_6200_);
v___x_6202_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_6203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6203_, 0, v___x_6201_);
lean_ctor_set(v___x_6203_, 1, v___x_6202_);
v___x_6204_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6203_, v_a_6189_, v_a_6190_, v_a_6191_, v_a_6192_);
return v___x_6204_;
}
else
{
lean_object* v_val_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; 
lean_dec(v_declName_6187_);
v_val_6205_ = lean_ctor_get(v___x_6198_, 0);
lean_inc(v_val_6205_);
lean_dec_ref_known(v___x_6198_, 1);
v___x_6206_ = l_Lean_ConstantInfo_type(v_val_6205_);
lean_dec(v_val_6205_);
v___x_6207_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_6206_, v___f_6194_, v___x_6197_, v___x_6197_, v_a_6189_, v_a_6190_, v_a_6191_, v_a_6192_);
return v___x_6207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_6208_, lean_object* v_prio_6209_, lean_object* v_a_6210_, lean_object* v_a_6211_, lean_object* v_a_6212_, lean_object* v_a_6213_, lean_object* v_a_6214_){
_start:
{
lean_object* v_res_6215_; 
v_res_6215_ = l_Lean_Meta_addDefaultInstance(v_declName_6208_, v_prio_6209_, v_a_6210_, v_a_6211_, v_a_6212_, v_a_6213_);
lean_dec(v_a_6213_);
lean_dec_ref(v_a_6212_);
lean_dec(v_a_6211_);
lean_dec_ref(v_a_6210_);
return v_res_6215_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_6216_, lean_object* v___y_6217_, lean_object* v___y_6218_, lean_object* v___y_6219_, lean_object* v___y_6220_){
_start:
{
lean_object* v___x_6222_; 
v___x_6222_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_6216_, v___y_6218_, v___y_6220_);
return v___x_6222_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_6223_, lean_object* v___y_6224_, lean_object* v___y_6225_, lean_object* v___y_6226_, lean_object* v___y_6227_, lean_object* v___y_6228_){
_start:
{
lean_object* v_res_6229_; 
v_res_6229_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_6223_, v___y_6224_, v___y_6225_, v___y_6226_, v___y_6227_);
lean_dec(v___y_6227_);
lean_dec_ref(v___y_6226_);
lean_dec(v___y_6225_);
lean_dec_ref(v___y_6224_);
return v_res_6229_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6231_; lean_object* v___x_6232_; 
v___x_6231_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_6232_ = l_Lean_stringToMessageData(v___x_6231_);
return v___x_6232_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_6234_; lean_object* v___x_6235_; 
v___x_6234_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_6235_ = l_Lean_stringToMessageData(v___x_6234_);
return v___x_6235_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_6239_, uint8_t v_kind_6240_, lean_object* v___y_6241_, lean_object* v___y_6242_){
_start:
{
lean_object* v___x_6244_; lean_object* v___x_6245_; lean_object* v___x_6246_; lean_object* v___x_6247_; lean_object* v___x_6248_; lean_object* v___y_6250_; 
v___x_6244_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_6245_ = l_Lean_MessageData_ofName(v_name_6239_);
v___x_6246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6246_, 0, v___x_6244_);
lean_ctor_set(v___x_6246_, 1, v___x_6245_);
v___x_6247_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_6248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6248_, 0, v___x_6246_);
lean_ctor_set(v___x_6248_, 1, v___x_6247_);
switch(v_kind_6240_)
{
case 0:
{
lean_object* v___x_6257_; 
v___x_6257_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_6250_ = v___x_6257_;
goto v___jp_6249_;
}
case 1:
{
lean_object* v___x_6258_; 
v___x_6258_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_6250_ = v___x_6258_;
goto v___jp_6249_;
}
default: 
{
lean_object* v___x_6259_; 
v___x_6259_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_6250_ = v___x_6259_;
goto v___jp_6249_;
}
}
v___jp_6249_:
{
lean_object* v___x_6251_; lean_object* v___x_6252_; lean_object* v___x_6253_; lean_object* v___x_6254_; lean_object* v___x_6255_; lean_object* v___x_6256_; 
lean_inc_ref(v___y_6250_);
v___x_6251_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6251_, 0, v___y_6250_);
v___x_6252_ = l_Lean_MessageData_ofFormat(v___x_6251_);
v___x_6253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6253_, 0, v___x_6248_);
lean_ctor_set(v___x_6253_, 1, v___x_6252_);
v___x_6254_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_6255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6255_, 0, v___x_6253_);
lean_ctor_set(v___x_6255_, 1, v___x_6254_);
v___x_6256_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6255_, v___y_6241_, v___y_6242_);
return v___x_6256_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_6260_, lean_object* v_kind_6261_, lean_object* v___y_6262_, lean_object* v___y_6263_, lean_object* v___y_6264_){
_start:
{
uint8_t v_kind_boxed_6265_; lean_object* v_res_6266_; 
v_kind_boxed_6265_ = lean_unbox(v_kind_6261_);
v_res_6266_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6260_, v_kind_boxed_6265_, v___y_6262_, v___y_6263_);
lean_dec(v___y_6263_);
lean_dec_ref(v___y_6262_);
return v_res_6266_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6267_, lean_object* v___x_6268_, lean_object* v___x_6269_, lean_object* v_declName_6270_, lean_object* v_stx_6271_, uint8_t v_kind_6272_, lean_object* v___y_6273_, lean_object* v___y_6274_){
_start:
{
lean_object* v___x_6276_; lean_object* v___x_6277_; lean_object* v___x_6278_; 
v___x_6276_ = lean_unsigned_to_nat(1u);
v___x_6277_ = l_Lean_Syntax_getArg(v_stx_6271_, v___x_6276_);
v___x_6278_ = l_Lean_getAttrParamOptPrio(v___x_6277_, v___y_6273_, v___y_6274_);
if (lean_obj_tag(v___x_6278_) == 0)
{
lean_object* v_a_6279_; lean_object* v___y_6281_; lean_object* v___y_6282_; uint8_t v___x_6316_; uint8_t v___x_6317_; 
v_a_6279_ = lean_ctor_get(v___x_6278_, 0);
lean_inc(v_a_6279_);
lean_dec_ref_known(v___x_6278_, 1);
v___x_6316_ = 0;
v___x_6317_ = l_Lean_instBEqAttributeKind_beq(v_kind_6272_, v___x_6316_);
if (v___x_6317_ == 0)
{
lean_object* v___x_6318_; 
lean_dec(v_a_6279_);
lean_dec(v_declName_6270_);
lean_dec(v___x_6268_);
lean_dec(v___x_6267_);
v___x_6318_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_6269_, v_kind_6272_, v___y_6273_, v___y_6274_);
return v___x_6318_;
}
else
{
lean_dec(v___x_6269_);
v___y_6281_ = v___y_6273_;
v___y_6282_ = v___y_6274_;
goto v___jp_6280_;
}
v___jp_6280_:
{
uint8_t v___x_6283_; uint8_t v___x_6284_; lean_object* v___x_6285_; lean_object* v___x_6286_; lean_object* v___x_6287_; lean_object* v___x_6288_; lean_object* v___x_6289_; size_t v___x_6290_; lean_object* v___x_6291_; lean_object* v___x_6292_; lean_object* v___x_6293_; lean_object* v___x_6294_; lean_object* v___x_6295_; lean_object* v___x_6296_; lean_object* v___x_6297_; lean_object* v___x_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; lean_object* v___x_6302_; lean_object* v___x_6303_; lean_object* v___x_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; 
v___x_6283_ = 0;
v___x_6284_ = 1;
v___x_6285_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6286_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6287_ = lean_unsigned_to_nat(32u);
v___x_6288_ = lean_mk_empty_array_with_capacity(v___x_6287_);
v___x_6289_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__1_spec__3_spec__6_spec__8_spec__11_spec__12___redArg___closed__2);
v___x_6290_ = ((size_t)5ULL);
lean_inc_n(v___x_6267_, 7);
v___x_6291_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6291_, 0, v___x_6289_);
lean_ctor_set(v___x_6291_, 1, v___x_6288_);
lean_ctor_set(v___x_6291_, 2, v___x_6267_);
lean_ctor_set(v___x_6291_, 3, v___x_6267_);
lean_ctor_set_usize(v___x_6291_, 4, v___x_6290_);
v___x_6292_ = lean_box(1);
lean_inc_ref(v___x_6291_);
v___x_6293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6293_, 0, v___x_6286_);
lean_ctor_set(v___x_6293_, 1, v___x_6291_);
lean_ctor_set(v___x_6293_, 2, v___x_6292_);
v___x_6294_ = lean_mk_empty_array_with_capacity(v___x_6267_);
v___x_6295_ = lean_box(0);
lean_inc(v___x_6268_);
v___x_6296_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6296_, 0, v___x_6285_);
lean_ctor_set(v___x_6296_, 1, v___x_6268_);
lean_ctor_set(v___x_6296_, 2, v___x_6293_);
lean_ctor_set(v___x_6296_, 3, v___x_6294_);
lean_ctor_set(v___x_6296_, 4, v___x_6295_);
lean_ctor_set(v___x_6296_, 5, v___x_6267_);
lean_ctor_set(v___x_6296_, 6, v___x_6295_);
lean_ctor_set_uint8(v___x_6296_, sizeof(void*)*7, v___x_6283_);
lean_ctor_set_uint8(v___x_6296_, sizeof(void*)*7 + 1, v___x_6283_);
lean_ctor_set_uint8(v___x_6296_, sizeof(void*)*7 + 2, v___x_6283_);
lean_ctor_set_uint8(v___x_6296_, sizeof(void*)*7 + 3, v___x_6284_);
v___x_6297_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6297_, 0, v___x_6267_);
lean_ctor_set(v___x_6297_, 1, v___x_6267_);
lean_ctor_set(v___x_6297_, 2, v___x_6267_);
lean_ctor_set(v___x_6297_, 3, v___x_6267_);
lean_ctor_set(v___x_6297_, 4, v___x_6286_);
lean_ctor_set(v___x_6297_, 5, v___x_6286_);
lean_ctor_set(v___x_6297_, 6, v___x_6286_);
lean_ctor_set(v___x_6297_, 7, v___x_6286_);
lean_ctor_set(v___x_6297_, 8, v___x_6286_);
lean_ctor_set(v___x_6297_, 9, v___x_6286_);
lean_ctor_set(v___x_6297_, 10, v___x_6286_);
v___x_6298_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__3___redArg___closed__2);
v___x_6299_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6300_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6300_, 0, v___x_6286_);
lean_ctor_set(v___x_6300_, 1, v___x_6286_);
lean_ctor_set(v___x_6300_, 2, v___x_6267_);
v___x_6301_ = lean_alloc_ctor(0, 8, 0);
lean_ctor_set(v___x_6301_, 0, v___x_6298_);
lean_ctor_set(v___x_6301_, 1, v___x_6286_);
lean_ctor_set(v___x_6301_, 2, v___x_6299_);
lean_ctor_set(v___x_6301_, 3, v___x_6286_);
lean_ctor_set(v___x_6301_, 4, v___x_6286_);
lean_ctor_set(v___x_6301_, 5, v___x_6286_);
lean_ctor_set(v___x_6301_, 6, v___x_6286_);
lean_ctor_set(v___x_6301_, 7, v___x_6300_);
v___x_6302_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6303_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6303_, 0, v___x_6297_);
lean_ctor_set(v___x_6303_, 1, v___x_6301_);
lean_ctor_set(v___x_6303_, 2, v___x_6268_);
lean_ctor_set(v___x_6303_, 3, v___x_6291_);
lean_ctor_set(v___x_6303_, 4, v___x_6302_);
v___x_6304_ = lean_box(0);
v___x_6305_ = lean_st_mk_ref(v___x_6303_);
v___x_6306_ = l_Lean_Meta_addDefaultInstance(v_declName_6270_, v_a_6279_, v___x_6296_, v___x_6305_, v___y_6281_, v___y_6282_);
lean_dec_ref_known(v___x_6296_, 7);
if (lean_obj_tag(v___x_6306_) == 0)
{
lean_object* v___x_6308_; uint8_t v_isShared_6309_; uint8_t v_isSharedCheck_6314_; 
v_isSharedCheck_6314_ = !lean_is_exclusive(v___x_6306_);
if (v_isSharedCheck_6314_ == 0)
{
lean_object* v_unused_6315_; 
v_unused_6315_ = lean_ctor_get(v___x_6306_, 0);
lean_dec(v_unused_6315_);
v___x_6308_ = v___x_6306_;
v_isShared_6309_ = v_isSharedCheck_6314_;
goto v_resetjp_6307_;
}
else
{
lean_dec(v___x_6306_);
v___x_6308_ = lean_box(0);
v_isShared_6309_ = v_isSharedCheck_6314_;
goto v_resetjp_6307_;
}
v_resetjp_6307_:
{
lean_object* v___x_6310_; lean_object* v___x_6312_; 
v___x_6310_ = lean_st_ref_get(v___x_6305_);
lean_dec(v___x_6305_);
lean_dec(v___x_6310_);
if (v_isShared_6309_ == 0)
{
lean_ctor_set(v___x_6308_, 0, v___x_6304_);
v___x_6312_ = v___x_6308_;
goto v_reusejp_6311_;
}
else
{
lean_object* v_reuseFailAlloc_6313_; 
v_reuseFailAlloc_6313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6313_, 0, v___x_6304_);
v___x_6312_ = v_reuseFailAlloc_6313_;
goto v_reusejp_6311_;
}
v_reusejp_6311_:
{
return v___x_6312_;
}
}
}
else
{
lean_dec(v___x_6305_);
return v___x_6306_;
}
}
}
else
{
lean_object* v_a_6319_; lean_object* v___x_6321_; uint8_t v_isShared_6322_; uint8_t v_isSharedCheck_6326_; 
lean_dec(v_declName_6270_);
lean_dec(v___x_6269_);
lean_dec(v___x_6268_);
lean_dec(v___x_6267_);
v_a_6319_ = lean_ctor_get(v___x_6278_, 0);
v_isSharedCheck_6326_ = !lean_is_exclusive(v___x_6278_);
if (v_isSharedCheck_6326_ == 0)
{
v___x_6321_ = v___x_6278_;
v_isShared_6322_ = v_isSharedCheck_6326_;
goto v_resetjp_6320_;
}
else
{
lean_inc(v_a_6319_);
lean_dec(v___x_6278_);
v___x_6321_ = lean_box(0);
v_isShared_6322_ = v_isSharedCheck_6326_;
goto v_resetjp_6320_;
}
v_resetjp_6320_:
{
lean_object* v___x_6324_; 
if (v_isShared_6322_ == 0)
{
v___x_6324_ = v___x_6321_;
goto v_reusejp_6323_;
}
else
{
lean_object* v_reuseFailAlloc_6325_; 
v_reuseFailAlloc_6325_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6325_, 0, v_a_6319_);
v___x_6324_ = v_reuseFailAlloc_6325_;
goto v_reusejp_6323_;
}
v_reusejp_6323_:
{
return v___x_6324_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6327_, lean_object* v___x_6328_, lean_object* v___x_6329_, lean_object* v_declName_6330_, lean_object* v_stx_6331_, lean_object* v_kind_6332_, lean_object* v___y_6333_, lean_object* v___y_6334_, lean_object* v___y_6335_){
_start:
{
uint8_t v_kind_boxed_6336_; lean_object* v_res_6337_; 
v_kind_boxed_6336_ = lean_unbox(v_kind_6332_);
v_res_6337_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6327_, v___x_6328_, v___x_6329_, v_declName_6330_, v_stx_6331_, v_kind_boxed_6336_, v___y_6333_, v___y_6334_);
lean_dec(v___y_6334_);
lean_dec_ref(v___y_6333_);
lean_dec(v_stx_6331_);
return v_res_6337_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6339_; lean_object* v___x_6340_; 
v___x_6339_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6340_ = l_Lean_stringToMessageData(v___x_6339_);
return v___x_6340_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6342_; lean_object* v___x_6343_; 
v___x_6342_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6343_ = l_Lean_stringToMessageData(v___x_6342_);
return v___x_6343_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6344_, lean_object* v_decl_6345_, lean_object* v___y_6346_, lean_object* v___y_6347_){
_start:
{
lean_object* v___x_6349_; lean_object* v___x_6350_; lean_object* v___x_6351_; lean_object* v___x_6352_; lean_object* v___x_6353_; lean_object* v___x_6354_; 
v___x_6349_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6350_ = l_Lean_MessageData_ofName(v___x_6344_);
v___x_6351_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6351_, 0, v___x_6349_);
lean_ctor_set(v___x_6351_, 1, v___x_6350_);
v___x_6352_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6353_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6353_, 0, v___x_6351_);
lean_ctor_set(v___x_6353_, 1, v___x_6352_);
v___x_6354_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6353_, v___y_6346_, v___y_6347_);
return v___x_6354_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6355_, lean_object* v_decl_6356_, lean_object* v___y_6357_, lean_object* v___y_6358_, lean_object* v___y_6359_){
_start:
{
lean_object* v_res_6360_; 
v_res_6360_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6355_, v_decl_6356_, v___y_6357_, v___y_6358_);
lean_dec(v___y_6358_);
lean_dec_ref(v___y_6357_);
lean_dec(v_decl_6356_);
return v_res_6360_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6393_; lean_object* v___x_6394_; lean_object* v___x_6395_; 
v___x_6393_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6394_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6395_ = l_Lean_registerBuiltinAttribute(v___x_6394_);
if (lean_obj_tag(v___x_6395_) == 0)
{
lean_object* v___x_6396_; uint8_t v___x_6397_; lean_object* v___x_6398_; 
lean_dec_ref_known(v___x_6395_, 1);
v___x_6396_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_6397_ = 0;
v___x_6398_ = l_Lean_registerTraceClass(v___x_6396_, v___x_6397_, v___x_6393_);
return v___x_6398_;
}
else
{
return v___x_6395_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_6399_){
_start:
{
lean_object* v_res_6400_; 
v_res_6400_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_6400_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_6401_, lean_object* v_name_6402_, uint8_t v_kind_6403_, lean_object* v___y_6404_, lean_object* v___y_6405_){
_start:
{
lean_object* v___x_6407_; 
v___x_6407_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6402_, v_kind_6403_, v___y_6404_, v___y_6405_);
return v___x_6407_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_6408_, lean_object* v_name_6409_, lean_object* v_kind_6410_, lean_object* v___y_6411_, lean_object* v___y_6412_, lean_object* v___y_6413_){
_start:
{
uint8_t v_kind_boxed_6414_; lean_object* v_res_6415_; 
v_kind_boxed_6414_ = lean_unbox(v_kind_6410_);
v_res_6415_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_6408_, v_name_6409_, v_kind_boxed_6414_, v___y_6411_, v___y_6412_);
lean_dec(v___y_6412_);
lean_dec_ref(v___y_6411_);
return v_res_6415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_6416_, lean_object* v_toPure_6417_, lean_object* v_____do__lift_6418_){
_start:
{
lean_object* v___x_6419_; lean_object* v_toEnvExtension_6420_; lean_object* v_asyncMode_6421_; lean_object* v___x_6422_; lean_object* v___x_6423_; lean_object* v_priorities_6424_; lean_object* v___x_6425_; 
v___x_6419_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6420_ = lean_ctor_get(v___x_6419_, 0);
v_asyncMode_6421_ = lean_ctor_get(v_toEnvExtension_6420_, 2);
v___x_6422_ = lean_box(0);
v___x_6423_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6416_, v___x_6419_, v_____do__lift_6418_, v_asyncMode_6421_, v___x_6422_);
v_priorities_6424_ = lean_ctor_get(v___x_6423_, 1);
lean_inc(v_priorities_6424_);
lean_dec(v___x_6423_);
v___x_6425_ = lean_apply_2(v_toPure_6417_, lean_box(0), v_priorities_6424_);
return v___x_6425_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_6426_, lean_object* v_inst_6427_){
_start:
{
lean_object* v_toApplicative_6428_; lean_object* v_toBind_6429_; lean_object* v_getEnv_6430_; lean_object* v_toPure_6431_; lean_object* v___x_6432_; lean_object* v___f_6433_; lean_object* v___x_6434_; 
v_toApplicative_6428_ = lean_ctor_get(v_inst_6426_, 0);
lean_inc_ref(v_toApplicative_6428_);
v_toBind_6429_ = lean_ctor_get(v_inst_6426_, 1);
lean_inc(v_toBind_6429_);
lean_dec_ref(v_inst_6426_);
v_getEnv_6430_ = lean_ctor_get(v_inst_6427_, 0);
lean_inc(v_getEnv_6430_);
lean_dec_ref(v_inst_6427_);
v_toPure_6431_ = lean_ctor_get(v_toApplicative_6428_, 1);
lean_inc(v_toPure_6431_);
lean_dec_ref(v_toApplicative_6428_);
v___x_6432_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6433_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6433_, 0, v___x_6432_);
lean_closure_set(v___f_6433_, 1, v_toPure_6431_);
v___x_6434_ = lean_apply_4(v_toBind_6429_, lean_box(0), lean_box(0), v_getEnv_6430_, v___f_6433_);
return v___x_6434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_6435_, lean_object* v_inst_6436_, lean_object* v_inst_6437_){
_start:
{
lean_object* v___x_6438_; 
v___x_6438_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_6436_, v_inst_6437_);
return v___x_6438_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_6439_, uint8_t v_isExporting_6440_, lean_object* v_x_6441_){
_start:
{
lean_object* v_fst_6442_; uint8_t v___x_6443_; 
v_fst_6442_ = lean_ctor_get(v_x_6441_, 0);
lean_inc(v_fst_6442_);
lean_dec_ref(v_x_6441_);
v___x_6443_ = l_Lean_Environment_contains(v_env_6439_, v_fst_6442_, v_isExporting_6440_);
return v___x_6443_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_6444_, lean_object* v_isExporting_6445_, lean_object* v_x_6446_){
_start:
{
uint8_t v_isExporting_boxed_6447_; uint8_t v_res_6448_; lean_object* v_r_6449_; 
v_isExporting_boxed_6447_ = lean_unbox(v_isExporting_6445_);
v_res_6448_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_6444_, v_isExporting_boxed_6447_, v_x_6446_);
v_r_6449_ = lean_box(v_res_6448_);
return v_r_6449_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_6450_, lean_object* v_toPure_6451_, lean_object* v_className_6452_, lean_object* v_env_6453_){
_start:
{
lean_object* v___y_6455_; lean_object* v___x_6463_; lean_object* v_toEnvExtension_6464_; lean_object* v_asyncMode_6465_; lean_object* v___x_6466_; lean_object* v___x_6467_; lean_object* v_defaultInstances_6468_; lean_object* v___x_6469_; 
v___x_6463_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6464_ = lean_ctor_get(v___x_6463_, 0);
v_asyncMode_6465_ = lean_ctor_get(v_toEnvExtension_6464_, 2);
v___x_6466_ = lean_box(0);
lean_inc_ref(v_env_6453_);
v___x_6467_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6450_, v___x_6463_, v_env_6453_, v_asyncMode_6465_, v___x_6466_);
v_defaultInstances_6468_ = lean_ctor_get(v___x_6467_, 0);
lean_inc(v_defaultInstances_6468_);
lean_dec(v___x_6467_);
v___x_6469_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_6468_, v_className_6452_);
lean_dec(v_defaultInstances_6468_);
if (lean_obj_tag(v___x_6469_) == 0)
{
lean_object* v___x_6470_; 
v___x_6470_ = lean_box(0);
v___y_6455_ = v___x_6470_;
goto v___jp_6454_;
}
else
{
lean_object* v_val_6471_; 
v_val_6471_ = lean_ctor_get(v___x_6469_, 0);
lean_inc(v_val_6471_);
lean_dec_ref_known(v___x_6469_, 1);
v___y_6455_ = v_val_6471_;
goto v___jp_6454_;
}
v___jp_6454_:
{
uint8_t v_isExporting_6456_; 
v_isExporting_6456_ = lean_ctor_get_uint8(v_env_6453_, sizeof(void*)*13);
if (v_isExporting_6456_ == 0)
{
lean_object* v___x_6457_; 
lean_dec_ref(v_env_6453_);
v___x_6457_ = lean_apply_2(v_toPure_6451_, lean_box(0), v___y_6455_);
return v___x_6457_;
}
else
{
lean_object* v___x_6458_; lean_object* v___f_6459_; lean_object* v___x_6460_; lean_object* v___x_6461_; lean_object* v___x_6462_; 
v___x_6458_ = lean_box(v_isExporting_6456_);
v___f_6459_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6459_, 0, v_env_6453_);
lean_closure_set(v___f_6459_, 1, v___x_6458_);
v___x_6460_ = lean_box(0);
v___x_6461_ = l_List_filterTR_loop___redArg(v___f_6459_, v___y_6455_, v___x_6460_);
v___x_6462_ = lean_apply_2(v_toPure_6451_, lean_box(0), v___x_6461_);
return v___x_6462_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_6472_, lean_object* v_toPure_6473_, lean_object* v_className_6474_, lean_object* v_env_6475_){
_start:
{
lean_object* v_res_6476_; 
v_res_6476_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_6472_, v_toPure_6473_, v_className_6474_, v_env_6475_);
lean_dec(v_className_6474_);
return v_res_6476_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_6477_, lean_object* v_inst_6478_, lean_object* v_className_6479_){
_start:
{
lean_object* v_toApplicative_6480_; lean_object* v_toBind_6481_; lean_object* v_getEnv_6482_; lean_object* v_toPure_6483_; lean_object* v___x_6484_; lean_object* v___f_6485_; lean_object* v___x_6486_; 
v_toApplicative_6480_ = lean_ctor_get(v_inst_6477_, 0);
lean_inc_ref(v_toApplicative_6480_);
v_toBind_6481_ = lean_ctor_get(v_inst_6477_, 1);
lean_inc(v_toBind_6481_);
lean_dec_ref(v_inst_6477_);
v_getEnv_6482_ = lean_ctor_get(v_inst_6478_, 0);
lean_inc(v_getEnv_6482_);
lean_dec_ref(v_inst_6478_);
v_toPure_6483_ = lean_ctor_get(v_toApplicative_6480_, 1);
lean_inc(v_toPure_6483_);
lean_dec_ref(v_toApplicative_6480_);
v___x_6484_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6485_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_6485_, 0, v___x_6484_);
lean_closure_set(v___f_6485_, 1, v_toPure_6483_);
lean_closure_set(v___f_6485_, 2, v_className_6479_);
v___x_6486_ = lean_apply_4(v_toBind_6481_, lean_box(0), lean_box(0), v_getEnv_6482_, v___f_6485_);
return v___x_6486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6487_, lean_object* v_inst_6488_, lean_object* v_inst_6489_, lean_object* v_className_6490_){
_start:
{
lean_object* v___x_6491_; 
v___x_6491_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6488_, v_inst_6489_, v_className_6490_);
return v___x_6491_;
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
res = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_638191375____hygCtx___hyg_2_();
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
