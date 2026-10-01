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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray___redArg();
lean_object* l_Lean_stringToMessageData(lean_object*);
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
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Name_str___override(lean_object*, lean_object*);
lean_object* l_Lean_Name_num___override(lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_isClass(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_defaultInstanceExtension;
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Meta_addDefaultInstance___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 27, .m_capacity = 27, .m_length = 26, .m_data = "invalid default instance `"};
static const lean_object* l_Lean_Meta_addDefaultInstance___lam__0___closed__0 = (const lean_object*)&l_Lean_Meta_addDefaultInstance___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDefaultInstance___lam__0___closed__1;
static const lean_string_object l_Lean_Meta_addDefaultInstance___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "`, it has type `("};
static const lean_object* l_Lean_Meta_addDefaultInstance___lam__0___closed__2 = (const lean_object*)&l_Lean_Meta_addDefaultInstance___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDefaultInstance___lam__0___closed__3;
static const lean_string_object l_Lean_Meta_addDefaultInstance___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = " ...)`, but `"};
static const lean_object* l_Lean_Meta_addDefaultInstance___lam__0___closed__4 = (const lean_object*)&l_Lean_Meta_addDefaultInstance___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDefaultInstance___lam__0___closed__5;
static const lean_string_object l_Lean_Meta_addDefaultInstance___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "` is not a type class"};
static const lean_object* l_Lean_Meta_addDefaultInstance___lam__0___closed__6 = (const lean_object*)&l_Lean_Meta_addDefaultInstance___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDefaultInstance___lam__0___closed__7;
static const lean_string_object l_Lean_Meta_addDefaultInstance___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 64, .m_capacity = 64, .m_length = 63, .m_data = "`, type must be of the form `(C ...)` where `C` is a type class"};
static const lean_object* l_Lean_Meta_addDefaultInstance___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_addDefaultInstance___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addDefaultInstance___lam__0___closed__9;
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_1287_; lean_object* v___f_1288_; lean_object* v___f_1289_; lean_object* v___x_1290_; lean_object* v___x_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; 
v___x_1287_ = 1;
v___f_1288_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_));
v___f_1289_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_));
v___x_1290_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__2, &l_Lean_Meta_instInhabitedInstances_default___closed__2_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__2);
v___x_1291_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_));
v___x_1292_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_));
v___x_1293_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_1293_, 0, v___x_1292_);
lean_ctor_set(v___x_1293_, 1, v___x_1291_);
lean_ctor_set(v___x_1293_, 2, v___x_1290_);
lean_ctor_set(v___x_1293_, 3, v___f_1289_);
lean_ctor_set(v___x_1293_, 4, v___f_1288_);
lean_ctor_set_uint8(v___x_1293_, sizeof(void*)*5, v___x_1287_);
return v___x_1293_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1295_; lean_object* v___x_1296_; 
v___x_1295_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_);
v___x_1296_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1295_);
return v___x_1296_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2____boxed(lean_object* v_a_1297_){
_start:
{
lean_object* v_res_1298_; 
v_res_1298_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_583220288____hygCtx___hyg_2_();
return v_res_1298_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object* v_k_1299_, uint8_t v_allowLevelAssignments_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_, lean_object* v___y_1304_){
_start:
{
lean_object* v___x_1306_; 
v___x_1306_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1300_, v_k_1299_, v___y_1301_, v___y_1302_, v___y_1303_, v___y_1304_);
if (lean_obj_tag(v___x_1306_) == 0)
{
lean_object* v_a_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1314_; 
v_a_1307_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1314_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1314_ == 0)
{
v___x_1309_ = v___x_1306_;
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_a_1307_);
lean_dec(v___x_1306_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1314_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v___x_1312_; 
if (v_isShared_1310_ == 0)
{
v___x_1312_ = v___x_1309_;
goto v_reusejp_1311_;
}
else
{
lean_object* v_reuseFailAlloc_1313_; 
v_reuseFailAlloc_1313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1313_, 0, v_a_1307_);
v___x_1312_ = v_reuseFailAlloc_1313_;
goto v_reusejp_1311_;
}
v_reusejp_1311_:
{
return v___x_1312_;
}
}
}
else
{
lean_object* v_a_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1322_; 
v_a_1315_ = lean_ctor_get(v___x_1306_, 0);
v_isSharedCheck_1322_ = !lean_is_exclusive(v___x_1306_);
if (v_isSharedCheck_1322_ == 0)
{
v___x_1317_ = v___x_1306_;
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_a_1315_);
lean_dec(v___x_1306_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1322_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___x_1320_; 
if (v_isShared_1318_ == 0)
{
v___x_1320_ = v___x_1317_;
goto v_reusejp_1319_;
}
else
{
lean_object* v_reuseFailAlloc_1321_; 
v_reuseFailAlloc_1321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1321_, 0, v_a_1315_);
v___x_1320_ = v_reuseFailAlloc_1321_;
goto v_reusejp_1319_;
}
v_reusejp_1319_:
{
return v___x_1320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object* v_k_1323_, lean_object* v_allowLevelAssignments_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1330_; lean_object* v_res_1331_; 
v_allowLevelAssignments_boxed_1330_ = lean_unbox(v_allowLevelAssignments_1324_);
v_res_1331_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1323_, v_allowLevelAssignments_boxed_1330_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
lean_dec(v___y_1328_);
lean_dec_ref(v___y_1327_);
lean_dec(v___y_1326_);
lean_dec_ref(v___y_1325_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object* v_00_u03b1_1332_, lean_object* v_k_1333_, uint8_t v_allowLevelAssignments_1334_, lean_object* v___y_1335_, lean_object* v___y_1336_, lean_object* v___y_1337_, lean_object* v___y_1338_){
_start:
{
lean_object* v___x_1340_; 
v___x_1340_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1333_, v_allowLevelAssignments_1334_, v___y_1335_, v___y_1336_, v___y_1337_, v___y_1338_);
return v___x_1340_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object* v_00_u03b1_1341_, lean_object* v_k_1342_, lean_object* v_allowLevelAssignments_1343_, lean_object* v___y_1344_, lean_object* v___y_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1349_; lean_object* v_res_1350_; 
v_allowLevelAssignments_boxed_1349_ = lean_unbox(v_allowLevelAssignments_1343_);
v_res_1350_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(v_00_u03b1_1341_, v_k_1342_, v_allowLevelAssignments_boxed_1349_, v___y_1344_, v___y_1345_, v___y_1346_, v___y_1347_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
lean_dec(v___y_1345_);
lean_dec_ref(v___y_1344_);
return v_res_1350_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1351_, lean_object* v___x_1352_, uint8_t v___x_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_){
_start:
{
lean_object* v___x_1359_; 
v___x_1359_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1351_, v___x_1352_, v___x_1353_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
if (lean_obj_tag(v___x_1359_) == 0)
{
lean_object* v_a_1360_; lean_object* v_snd_1361_; lean_object* v_snd_1362_; uint8_t v___x_1363_; lean_object* v___x_1364_; 
v_a_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc(v_a_1360_);
lean_dec_ref_known(v___x_1359_, 1);
v_snd_1361_ = lean_ctor_get(v_a_1360_, 1);
lean_inc(v_snd_1361_);
lean_dec(v_a_1360_);
v_snd_1362_ = lean_ctor_get(v_snd_1361_, 1);
lean_inc(v_snd_1362_);
lean_dec(v_snd_1361_);
v___x_1363_ = 0;
v___x_1364_ = l_Lean_Meta_DiscrTree_mkPath(v_snd_1362_, v___x_1363_, v___y_1354_, v___y_1355_, v___y_1356_, v___y_1357_);
return v___x_1364_;
}
else
{
lean_object* v_a_1365_; lean_object* v___x_1367_; uint8_t v_isShared_1368_; uint8_t v_isSharedCheck_1372_; 
v_a_1365_ = lean_ctor_get(v___x_1359_, 0);
v_isSharedCheck_1372_ = !lean_is_exclusive(v___x_1359_);
if (v_isSharedCheck_1372_ == 0)
{
v___x_1367_ = v___x_1359_;
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
else
{
lean_inc(v_a_1365_);
lean_dec(v___x_1359_);
v___x_1367_ = lean_box(0);
v_isShared_1368_ = v_isSharedCheck_1372_;
goto v_resetjp_1366_;
}
v_resetjp_1366_:
{
lean_object* v___x_1370_; 
if (v_isShared_1368_ == 0)
{
v___x_1370_ = v___x_1367_;
goto v_reusejp_1369_;
}
else
{
lean_object* v_reuseFailAlloc_1371_; 
v_reuseFailAlloc_1371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1371_, 0, v_a_1365_);
v___x_1370_ = v_reuseFailAlloc_1371_;
goto v_reusejp_1369_;
}
v_reusejp_1369_:
{
return v___x_1370_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object* v_a_1373_, lean_object* v___x_1374_, lean_object* v___x_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v___x_497__boxed_1381_; lean_object* v_res_1382_; 
v___x_497__boxed_1381_ = lean_unbox(v___x_1375_);
v_res_1382_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1373_, v___x_1374_, v___x_497__boxed_1381_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1382_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object* v_e_1383_, lean_object* v_a_1384_, lean_object* v_a_1385_, lean_object* v_a_1386_, lean_object* v_a_1387_){
_start:
{
lean_object* v___x_1389_; 
lean_inc(v_a_1387_);
lean_inc_ref(v_a_1386_);
lean_inc(v_a_1385_);
lean_inc_ref(v_a_1384_);
v___x_1389_ = lean_infer_type(v_e_1383_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_);
if (lean_obj_tag(v___x_1389_) == 0)
{
lean_object* v_a_1390_; lean_object* v___x_1391_; uint8_t v___x_1392_; lean_object* v___x_1393_; lean_object* v___f_1394_; uint8_t v___x_1395_; lean_object* v___x_1396_; 
v_a_1390_ = lean_ctor_get(v___x_1389_, 0);
lean_inc(v_a_1390_);
lean_dec_ref_known(v___x_1389_, 1);
v___x_1391_ = lean_box(0);
v___x_1392_ = 0;
v___x_1393_ = lean_box(v___x_1392_);
v___f_1394_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1394_, 0, v_a_1390_);
lean_closure_set(v___f_1394_, 1, v___x_1391_);
lean_closure_set(v___f_1394_, 2, v___x_1393_);
v___x_1395_ = 0;
v___x_1396_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v___f_1394_, v___x_1395_, v_a_1384_, v_a_1385_, v_a_1386_, v_a_1387_);
return v___x_1396_;
}
else
{
lean_object* v_a_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1404_; 
v_a_1397_ = lean_ctor_get(v___x_1389_, 0);
v_isSharedCheck_1404_ = !lean_is_exclusive(v___x_1389_);
if (v_isSharedCheck_1404_ == 0)
{
v___x_1399_ = v___x_1389_;
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_a_1397_);
lean_dec(v___x_1389_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1404_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v___x_1402_; 
if (v_isShared_1400_ == 0)
{
v___x_1402_ = v___x_1399_;
goto v_reusejp_1401_;
}
else
{
lean_object* v_reuseFailAlloc_1403_; 
v_reuseFailAlloc_1403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1403_, 0, v_a_1397_);
v___x_1402_ = v_reuseFailAlloc_1403_;
goto v_reusejp_1401_;
}
v_reusejp_1401_:
{
return v___x_1402_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object* v_e_1405_, lean_object* v_a_1406_, lean_object* v_a_1407_, lean_object* v_a_1408_, lean_object* v_a_1409_, lean_object* v_a_1410_){
_start:
{
lean_object* v_res_1411_; 
v_res_1411_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_e_1405_, v_a_1406_, v_a_1407_, v_a_1408_, v_a_1409_);
lean_dec(v_a_1409_);
lean_dec_ref(v_a_1408_);
lean_dec(v_a_1407_);
lean_dec_ref(v_a_1406_);
return v_res_1411_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1412_, lean_object* v_b_1413_, lean_object* v_c_1414_, lean_object* v___y_1415_, lean_object* v___y_1416_, lean_object* v___y_1417_, lean_object* v___y_1418_){
_start:
{
lean_object* v___x_1420_; 
lean_inc(v___y_1418_);
lean_inc_ref(v___y_1417_);
lean_inc(v___y_1416_);
lean_inc_ref(v___y_1415_);
v___x_1420_ = lean_apply_7(v_k_1412_, v_b_1413_, v_c_1414_, v___y_1415_, v___y_1416_, v___y_1417_, v___y_1418_, lean_box(0));
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1421_, lean_object* v_b_1422_, lean_object* v_c_1423_, lean_object* v___y_1424_, lean_object* v___y_1425_, lean_object* v___y_1426_, lean_object* v___y_1427_, lean_object* v___y_1428_){
_start:
{
lean_object* v_res_1429_; 
v_res_1429_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1421_, v_b_1422_, v_c_1423_, v___y_1424_, v___y_1425_, v___y_1426_, v___y_1427_);
lean_dec(v___y_1427_);
lean_dec_ref(v___y_1426_);
lean_dec(v___y_1425_);
lean_dec_ref(v___y_1424_);
return v_res_1429_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object* v_type_1430_, lean_object* v_k_1431_, uint8_t v_cleanupAnnotations_1432_, uint8_t v_whnfType_1433_, lean_object* v___y_1434_, lean_object* v___y_1435_, lean_object* v___y_1436_, lean_object* v___y_1437_){
_start:
{
lean_object* v___f_1439_; lean_object* v___x_1440_; 
v___f_1439_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1439_, 0, v_k_1431_);
v___x_1440_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1430_, v___f_1439_, v_cleanupAnnotations_1432_, v_whnfType_1433_, v___y_1434_, v___y_1435_, v___y_1436_, v___y_1437_);
if (lean_obj_tag(v___x_1440_) == 0)
{
lean_object* v_a_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1448_; 
v_a_1441_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1443_ = v___x_1440_;
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
else
{
lean_inc(v_a_1441_);
lean_dec(v___x_1440_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1448_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1446_; 
if (v_isShared_1444_ == 0)
{
v___x_1446_ = v___x_1443_;
goto v_reusejp_1445_;
}
else
{
lean_object* v_reuseFailAlloc_1447_; 
v_reuseFailAlloc_1447_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1447_, 0, v_a_1441_);
v___x_1446_ = v_reuseFailAlloc_1447_;
goto v_reusejp_1445_;
}
v_reusejp_1445_:
{
return v___x_1446_;
}
}
}
else
{
lean_object* v_a_1449_; lean_object* v___x_1451_; uint8_t v_isShared_1452_; uint8_t v_isSharedCheck_1456_; 
v_a_1449_ = lean_ctor_get(v___x_1440_, 0);
v_isSharedCheck_1456_ = !lean_is_exclusive(v___x_1440_);
if (v_isSharedCheck_1456_ == 0)
{
v___x_1451_ = v___x_1440_;
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
else
{
lean_inc(v_a_1449_);
lean_dec(v___x_1440_);
v___x_1451_ = lean_box(0);
v_isShared_1452_ = v_isSharedCheck_1456_;
goto v_resetjp_1450_;
}
v_resetjp_1450_:
{
lean_object* v___x_1454_; 
if (v_isShared_1452_ == 0)
{
v___x_1454_ = v___x_1451_;
goto v_reusejp_1453_;
}
else
{
lean_object* v_reuseFailAlloc_1455_; 
v_reuseFailAlloc_1455_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1455_, 0, v_a_1449_);
v___x_1454_ = v_reuseFailAlloc_1455_;
goto v_reusejp_1453_;
}
v_reusejp_1453_:
{
return v___x_1454_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object* v_type_1457_, lean_object* v_k_1458_, lean_object* v_cleanupAnnotations_1459_, lean_object* v_whnfType_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_, lean_object* v___y_1464_, lean_object* v___y_1465_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1466_; uint8_t v_whnfType_boxed_1467_; lean_object* v_res_1468_; 
v_cleanupAnnotations_boxed_1466_ = lean_unbox(v_cleanupAnnotations_1459_);
v_whnfType_boxed_1467_ = lean_unbox(v_whnfType_1460_);
v_res_1468_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1457_, v_k_1458_, v_cleanupAnnotations_boxed_1466_, v_whnfType_boxed_1467_, v___y_1461_, v___y_1462_, v___y_1463_, v___y_1464_);
lean_dec(v___y_1464_);
lean_dec_ref(v___y_1463_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
return v_res_1468_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object* v_00_u03b1_1469_, lean_object* v_type_1470_, lean_object* v_k_1471_, uint8_t v_cleanupAnnotations_1472_, uint8_t v_whnfType_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; 
v___x_1479_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1470_, v_k_1471_, v_cleanupAnnotations_1472_, v_whnfType_1473_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
return v___x_1479_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object* v_00_u03b1_1480_, lean_object* v_type_1481_, lean_object* v_k_1482_, lean_object* v_cleanupAnnotations_1483_, lean_object* v_whnfType_1484_, lean_object* v___y_1485_, lean_object* v___y_1486_, lean_object* v___y_1487_, lean_object* v___y_1488_, lean_object* v___y_1489_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1490_; uint8_t v_whnfType_boxed_1491_; lean_object* v_res_1492_; 
v_cleanupAnnotations_boxed_1490_ = lean_unbox(v_cleanupAnnotations_1483_);
v_whnfType_boxed_1491_ = lean_unbox(v_whnfType_1484_);
v_res_1492_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(v_00_u03b1_1480_, v_type_1481_, v_k_1482_, v_cleanupAnnotations_boxed_1490_, v_whnfType_boxed_1491_, v___y_1485_, v___y_1486_, v___y_1487_, v___y_1488_);
lean_dec(v___y_1488_);
lean_dec_ref(v___y_1487_);
lean_dec(v___y_1486_);
lean_dec_ref(v___y_1485_);
return v_res_1492_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object* v_as_1496_, size_t v_sz_1497_, size_t v_i_1498_, lean_object* v_b_1499_, lean_object* v___y_1500_, lean_object* v___y_1501_, lean_object* v___y_1502_, lean_object* v___y_1503_){
_start:
{
lean_object* v_a_1506_; uint8_t v___x_1510_; 
v___x_1510_ = lean_usize_dec_lt(v_i_1498_, v_sz_1497_);
if (v___x_1510_ == 0)
{
lean_object* v___x_1511_; 
v___x_1511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1511_, 0, v_b_1499_);
return v___x_1511_;
}
else
{
lean_object* v_fst_1512_; lean_object* v_snd_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1560_; 
v_fst_1512_ = lean_ctor_get(v_b_1499_, 0);
v_snd_1513_ = lean_ctor_get(v_b_1499_, 1);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_b_1499_);
if (v_isSharedCheck_1560_ == 0)
{
v___x_1515_ = v_b_1499_;
v_isShared_1516_ = v_isSharedCheck_1560_;
goto v_resetjp_1514_;
}
else
{
lean_inc(v_snd_1513_);
lean_inc(v_fst_1512_);
lean_dec(v_b_1499_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1560_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v_next_1522_; 
v_next_1522_ = lean_ctor_get(v_snd_1513_, 0);
lean_inc(v_next_1522_);
if (lean_obj_tag(v_next_1522_) == 0)
{
goto v___jp_1517_;
}
else
{
lean_object* v_upperBound_1523_; lean_object* v_val_1524_; lean_object* v___x_1526_; uint8_t v_isShared_1527_; uint8_t v_isSharedCheck_1559_; 
v_upperBound_1523_ = lean_ctor_get(v_snd_1513_, 1);
v_val_1524_ = lean_ctor_get(v_next_1522_, 0);
v_isSharedCheck_1559_ = !lean_is_exclusive(v_next_1522_);
if (v_isSharedCheck_1559_ == 0)
{
v___x_1526_ = v_next_1522_;
v_isShared_1527_ = v_isSharedCheck_1559_;
goto v_resetjp_1525_;
}
else
{
lean_inc(v_val_1524_);
lean_dec(v_next_1522_);
v___x_1526_ = lean_box(0);
v_isShared_1527_ = v_isSharedCheck_1559_;
goto v_resetjp_1525_;
}
v_resetjp_1525_:
{
uint8_t v___x_1528_; 
v___x_1528_ = lean_nat_dec_lt(v_val_1524_, v_upperBound_1523_);
if (v___x_1528_ == 0)
{
lean_del_object(v___x_1526_);
lean_dec(v_val_1524_);
goto v___jp_1517_;
}
else
{
lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1556_; 
lean_inc(v_upperBound_1523_);
lean_del_object(v___x_1515_);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_snd_1513_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; lean_object* v_unused_1558_; 
v_unused_1557_ = lean_ctor_get(v_snd_1513_, 1);
lean_dec(v_unused_1557_);
v_unused_1558_ = lean_ctor_get(v_snd_1513_, 0);
lean_dec(v_unused_1558_);
v___x_1530_ = v_snd_1513_;
v_isShared_1531_ = v_isSharedCheck_1556_;
goto v_resetjp_1529_;
}
else
{
lean_dec(v_snd_1513_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1556_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v_a_1532_; lean_object* v___x_1533_; lean_object* v___x_1534_; lean_object* v___x_1536_; 
v_a_1532_ = lean_array_uget_borrowed(v_as_1496_, v_i_1498_);
v___x_1533_ = lean_unsigned_to_nat(1u);
v___x_1534_ = lean_nat_add(v_val_1524_, v___x_1533_);
if (v_isShared_1527_ == 0)
{
lean_ctor_set(v___x_1526_, 0, v___x_1534_);
v___x_1536_ = v___x_1526_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
lean_object* v___x_1538_; 
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 0, v___x_1536_);
v___x_1538_ = v___x_1530_;
goto v_reusejp_1537_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v___x_1536_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_upperBound_1523_);
v___x_1538_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1537_;
}
v_reusejp_1537_:
{
lean_object* v___x_1539_; 
lean_inc(v___y_1503_);
lean_inc_ref(v___y_1502_);
lean_inc(v___y_1501_);
lean_inc_ref(v___y_1500_);
lean_inc(v_a_1532_);
v___x_1539_ = lean_infer_type(v_a_1532_, v___y_1500_, v___y_1501_, v___y_1502_, v___y_1503_);
if (lean_obj_tag(v___x_1539_) == 0)
{
lean_object* v_a_1540_; lean_object* v___x_1541_; uint8_t v___x_1542_; 
v_a_1540_ = lean_ctor_get(v___x_1539_, 0);
lean_inc(v_a_1540_);
lean_dec_ref_known(v___x_1539_, 1);
v___x_1541_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1));
v___x_1542_ = l_Lean_Expr_isAppOf(v_a_1540_, v___x_1541_);
lean_dec(v_a_1540_);
if (v___x_1542_ == 0)
{
lean_object* v___x_1543_; 
lean_dec(v_val_1524_);
v___x_1543_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1543_, 0, v_fst_1512_);
lean_ctor_set(v___x_1543_, 1, v___x_1538_);
v_a_1506_ = v___x_1543_;
goto v___jp_1505_;
}
else
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
v___x_1544_ = lean_array_push(v_fst_1512_, v_val_1524_);
v___x_1545_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1545_, 0, v___x_1544_);
lean_ctor_set(v___x_1545_, 1, v___x_1538_);
v_a_1506_ = v___x_1545_;
goto v___jp_1505_;
}
}
else
{
lean_object* v_a_1546_; lean_object* v___x_1548_; uint8_t v_isShared_1549_; uint8_t v_isSharedCheck_1553_; 
lean_dec_ref(v___x_1538_);
lean_dec(v_val_1524_);
lean_dec(v_fst_1512_);
v_a_1546_ = lean_ctor_get(v___x_1539_, 0);
v_isSharedCheck_1553_ = !lean_is_exclusive(v___x_1539_);
if (v_isSharedCheck_1553_ == 0)
{
v___x_1548_ = v___x_1539_;
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
else
{
lean_inc(v_a_1546_);
lean_dec(v___x_1539_);
v___x_1548_ = lean_box(0);
v_isShared_1549_ = v_isSharedCheck_1553_;
goto v_resetjp_1547_;
}
v_resetjp_1547_:
{
lean_object* v___x_1551_; 
if (v_isShared_1549_ == 0)
{
v___x_1551_ = v___x_1548_;
goto v_reusejp_1550_;
}
else
{
lean_object* v_reuseFailAlloc_1552_; 
v_reuseFailAlloc_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1552_, 0, v_a_1546_);
v___x_1551_ = v_reuseFailAlloc_1552_;
goto v_reusejp_1550_;
}
v_reusejp_1550_:
{
return v___x_1551_;
}
}
}
}
}
}
}
}
}
v___jp_1517_:
{
lean_object* v___x_1519_; 
if (v_isShared_1516_ == 0)
{
v___x_1519_ = v___x_1515_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1521_; 
v_reuseFailAlloc_1521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1521_, 0, v_fst_1512_);
lean_ctor_set(v_reuseFailAlloc_1521_, 1, v_snd_1513_);
v___x_1519_ = v_reuseFailAlloc_1521_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
lean_object* v___x_1520_; 
v___x_1520_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1520_, 0, v___x_1519_);
return v___x_1520_;
}
}
}
}
v___jp_1505_:
{
size_t v___x_1507_; size_t v___x_1508_; 
v___x_1507_ = ((size_t)1ULL);
v___x_1508_ = lean_usize_add(v_i_1498_, v___x_1507_);
v_i_1498_ = v___x_1508_;
v_b_1499_ = v_a_1506_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object* v_as_1561_, lean_object* v_sz_1562_, lean_object* v_i_1563_, lean_object* v_b_1564_, lean_object* v___y_1565_, lean_object* v___y_1566_, lean_object* v___y_1567_, lean_object* v___y_1568_, lean_object* v___y_1569_){
_start:
{
size_t v_sz_boxed_1570_; size_t v_i_boxed_1571_; lean_object* v_res_1572_; 
v_sz_boxed_1570_ = lean_unbox_usize(v_sz_1562_);
lean_dec(v_sz_1562_);
v_i_boxed_1571_ = lean_unbox_usize(v_i_1563_);
lean_dec(v_i_1563_);
v_res_1572_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_as_1561_, v_sz_boxed_1570_, v_i_boxed_1571_, v_b_1564_, v___y_1565_, v___y_1566_, v___y_1567_, v___y_1568_);
lean_dec(v___y_1568_);
lean_dec_ref(v___y_1567_);
lean_dec(v___y_1566_);
lean_dec_ref(v___y_1565_);
lean_dec_ref(v_as_1561_);
return v_res_1572_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object* v_declName_1577_, lean_object* v_args_1578_, lean_object* v_x_1579_, lean_object* v___y_1580_, lean_object* v___y_1581_, lean_object* v___y_1582_, lean_object* v___y_1583_){
_start:
{
lean_object* v___x_1585_; lean_object* v___y_1587_; lean_object* v_env_1612_; lean_object* v___x_1613_; 
v___x_1585_ = lean_st_ref_get(v___y_1583_);
v_env_1612_ = lean_ctor_get(v___x_1585_, 0);
lean_inc_ref(v_env_1612_);
lean_dec(v___x_1585_);
v___x_1613_ = l_Lean_getOutParamPositions_x3f(v_env_1612_, v_declName_1577_);
if (lean_obj_tag(v___x_1613_) == 0)
{
lean_object* v___x_1614_; 
v___x_1614_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___y_1587_ = v___x_1614_;
goto v___jp_1586_;
}
else
{
lean_object* v_val_1615_; 
v_val_1615_ = lean_ctor_get(v___x_1613_, 0);
lean_inc(v_val_1615_);
lean_dec_ref_known(v___x_1613_, 1);
v___y_1587_ = v_val_1615_;
goto v___jp_1586_;
}
v___jp_1586_:
{
lean_object* v___x_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; size_t v_sz_1592_; size_t v___x_1593_; lean_object* v___x_1594_; 
v___x_1588_ = lean_array_get_size(v_args_1578_);
v___x_1589_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_1590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
lean_ctor_set(v___x_1590_, 1, v___x_1588_);
v___x_1591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1591_, 0, v___y_1587_);
lean_ctor_set(v___x_1591_, 1, v___x_1590_);
v_sz_1592_ = lean_array_size(v_args_1578_);
v___x_1593_ = ((size_t)0ULL);
v___x_1594_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_args_1578_, v_sz_1592_, v___x_1593_, v___x_1591_, v___y_1580_, v___y_1581_, v___y_1582_, v___y_1583_);
if (lean_obj_tag(v___x_1594_) == 0)
{
lean_object* v_a_1595_; lean_object* v___x_1597_; uint8_t v_isShared_1598_; uint8_t v_isSharedCheck_1603_; 
v_a_1595_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1603_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1603_ == 0)
{
v___x_1597_ = v___x_1594_;
v_isShared_1598_ = v_isSharedCheck_1603_;
goto v_resetjp_1596_;
}
else
{
lean_inc(v_a_1595_);
lean_dec(v___x_1594_);
v___x_1597_ = lean_box(0);
v_isShared_1598_ = v_isSharedCheck_1603_;
goto v_resetjp_1596_;
}
v_resetjp_1596_:
{
lean_object* v_fst_1599_; lean_object* v___x_1601_; 
v_fst_1599_ = lean_ctor_get(v_a_1595_, 0);
lean_inc(v_fst_1599_);
lean_dec(v_a_1595_);
if (v_isShared_1598_ == 0)
{
lean_ctor_set(v___x_1597_, 0, v_fst_1599_);
v___x_1601_ = v___x_1597_;
goto v_reusejp_1600_;
}
else
{
lean_object* v_reuseFailAlloc_1602_; 
v_reuseFailAlloc_1602_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1602_, 0, v_fst_1599_);
v___x_1601_ = v_reuseFailAlloc_1602_;
goto v_reusejp_1600_;
}
v_reusejp_1600_:
{
return v___x_1601_;
}
}
}
else
{
lean_object* v_a_1604_; lean_object* v___x_1606_; uint8_t v_isShared_1607_; uint8_t v_isSharedCheck_1611_; 
v_a_1604_ = lean_ctor_get(v___x_1594_, 0);
v_isSharedCheck_1611_ = !lean_is_exclusive(v___x_1594_);
if (v_isSharedCheck_1611_ == 0)
{
v___x_1606_ = v___x_1594_;
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
else
{
lean_inc(v_a_1604_);
lean_dec(v___x_1594_);
v___x_1606_ = lean_box(0);
v_isShared_1607_ = v_isSharedCheck_1611_;
goto v_resetjp_1605_;
}
v_resetjp_1605_:
{
lean_object* v___x_1609_; 
if (v_isShared_1607_ == 0)
{
v___x_1609_ = v___x_1606_;
goto v_reusejp_1608_;
}
else
{
lean_object* v_reuseFailAlloc_1610_; 
v_reuseFailAlloc_1610_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1610_, 0, v_a_1604_);
v___x_1609_ = v_reuseFailAlloc_1610_;
goto v_reusejp_1608_;
}
v_reusejp_1608_:
{
return v___x_1609_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object* v_declName_1616_, lean_object* v_args_1617_, lean_object* v_x_1618_, lean_object* v___y_1619_, lean_object* v___y_1620_, lean_object* v___y_1621_, lean_object* v___y_1622_, lean_object* v___y_1623_){
_start:
{
lean_object* v_res_1624_; 
v_res_1624_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(v_declName_1616_, v_args_1617_, v_x_1618_, v___y_1619_, v___y_1620_, v___y_1621_, v___y_1622_);
lean_dec(v___y_1622_);
lean_dec_ref(v___y_1621_);
lean_dec(v___y_1620_);
lean_dec_ref(v___y_1619_);
lean_dec_ref(v_x_1618_);
lean_dec_ref(v_args_1617_);
lean_dec(v_declName_1616_);
return v_res_1624_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object* v_classTy_1625_, lean_object* v_a_1626_, lean_object* v_a_1627_, lean_object* v_a_1628_, lean_object* v_a_1629_){
_start:
{
lean_object* v___x_1631_; 
v___x_1631_ = l_Lean_Expr_getAppFn(v_classTy_1625_);
if (lean_obj_tag(v___x_1631_) == 4)
{
lean_object* v_declName_1632_; lean_object* v___f_1633_; lean_object* v___x_1634_; 
v_declName_1632_ = lean_ctor_get(v___x_1631_, 0);
lean_inc(v_declName_1632_);
v___f_1633_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1633_, 0, v_declName_1632_);
lean_inc(v_a_1629_);
lean_inc_ref(v_a_1628_);
lean_inc(v_a_1627_);
lean_inc_ref(v_a_1626_);
v___x_1634_ = lean_infer_type(v___x_1631_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_a_1635_; uint8_t v___x_1636_; lean_object* v___x_1637_; 
v_a_1635_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_a_1635_);
lean_dec_ref_known(v___x_1634_, 1);
v___x_1636_ = 0;
v___x_1637_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_1635_, v___f_1633_, v___x_1636_, v___x_1636_, v_a_1626_, v_a_1627_, v_a_1628_, v_a_1629_);
return v___x_1637_;
}
else
{
lean_object* v_a_1638_; lean_object* v___x_1640_; uint8_t v_isShared_1641_; uint8_t v_isSharedCheck_1645_; 
lean_dec_ref(v___f_1633_);
v_a_1638_ = lean_ctor_get(v___x_1634_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v___x_1634_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1640_ = v___x_1634_;
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
else
{
lean_inc(v_a_1638_);
lean_dec(v___x_1634_);
v___x_1640_ = lean_box(0);
v_isShared_1641_ = v_isSharedCheck_1645_;
goto v_resetjp_1639_;
}
v_resetjp_1639_:
{
lean_object* v___x_1643_; 
if (v_isShared_1641_ == 0)
{
v___x_1643_ = v___x_1640_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v_a_1638_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
return v___x_1643_;
}
}
}
}
else
{
lean_object* v___x_1646_; lean_object* v___x_1647_; 
lean_dec_ref(v___x_1631_);
v___x_1646_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_1647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1647_, 0, v___x_1646_);
return v___x_1647_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object* v_classTy_1648_, lean_object* v_a_1649_, lean_object* v_a_1650_, lean_object* v_a_1651_, lean_object* v_a_1652_, lean_object* v_a_1653_){
_start:
{
lean_object* v_res_1654_; 
v_res_1654_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_classTy_1648_, v_a_1649_, v_a_1650_, v_a_1651_, v_a_1652_);
lean_dec(v_a_1652_);
lean_dec_ref(v_a_1651_);
lean_dec(v_a_1650_);
lean_dec_ref(v_a_1649_);
lean_dec_ref(v_classTy_1648_);
return v_res_1654_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_a_1655_, lean_object* v_as_1656_, lean_object* v_j_1657_){
_start:
{
lean_object* v___x_1658_; uint8_t v___x_1659_; 
v___x_1658_ = lean_array_get_size(v_as_1656_);
v___x_1659_ = lean_nat_dec_lt(v_j_1657_, v___x_1658_);
if (v___x_1659_ == 0)
{
lean_object* v___x_1660_; 
lean_dec(v_j_1657_);
v___x_1660_ = lean_box(0);
return v___x_1660_;
}
else
{
lean_object* v___x_1661_; lean_object* v___x_1662_; uint8_t v___x_1663_; 
v___x_1661_ = lean_array_fget_borrowed(v_as_1656_, v_j_1657_);
v___x_1662_ = l_Lean_Expr_mvarId_x21(v___x_1661_);
v___x_1663_ = l_Lean_instBEqMVarId_beq(v___x_1662_, v_a_1655_);
lean_dec(v___x_1662_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; 
v___x_1664_ = lean_unsigned_to_nat(1u);
v___x_1665_ = lean_nat_add(v_j_1657_, v___x_1664_);
lean_dec(v_j_1657_);
v_j_1657_ = v___x_1665_;
goto _start;
}
else
{
lean_object* v___x_1667_; 
v___x_1667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1667_, 0, v_j_1657_);
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_a_1668_, lean_object* v_as_1669_, lean_object* v_j_1670_){
_start:
{
lean_object* v_res_1671_; 
v_res_1671_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1668_, v_as_1669_, v_j_1670_);
lean_dec_ref(v_as_1669_);
lean_dec(v_a_1668_);
return v_res_1671_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1672_, lean_object* v_x_1673_, lean_object* v_x_1674_, lean_object* v_x_1675_){
_start:
{
lean_object* v_ks_1676_; lean_object* v_vs_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1701_; 
v_ks_1676_ = lean_ctor_get(v_x_1672_, 0);
v_vs_1677_ = lean_ctor_get(v_x_1672_, 1);
v_isSharedCheck_1701_ = !lean_is_exclusive(v_x_1672_);
if (v_isSharedCheck_1701_ == 0)
{
v___x_1679_ = v_x_1672_;
v_isShared_1680_ = v_isSharedCheck_1701_;
goto v_resetjp_1678_;
}
else
{
lean_inc(v_vs_1677_);
lean_inc(v_ks_1676_);
lean_dec(v_x_1672_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1701_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; uint8_t v___x_1682_; 
v___x_1681_ = lean_array_get_size(v_ks_1676_);
v___x_1682_ = lean_nat_dec_lt(v_x_1673_, v___x_1681_);
if (v___x_1682_ == 0)
{
lean_object* v___x_1683_; lean_object* v___x_1684_; lean_object* v___x_1686_; 
lean_dec(v_x_1673_);
v___x_1683_ = lean_array_push(v_ks_1676_, v_x_1674_);
v___x_1684_ = lean_array_push(v_vs_1677_, v_x_1675_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v___x_1684_);
lean_ctor_set(v___x_1679_, 0, v___x_1683_);
v___x_1686_ = v___x_1679_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v___x_1683_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
else
{
lean_object* v_k_x27_1688_; uint8_t v___x_1689_; 
v_k_x27_1688_ = lean_array_fget_borrowed(v_ks_1676_, v_x_1673_);
v___x_1689_ = l_Lean_instBEqMVarId_beq(v_x_1674_, v_k_x27_1688_);
if (v___x_1689_ == 0)
{
lean_object* v___x_1691_; 
if (v_isShared_1680_ == 0)
{
v___x_1691_ = v___x_1679_;
goto v_reusejp_1690_;
}
else
{
lean_object* v_reuseFailAlloc_1695_; 
v_reuseFailAlloc_1695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1695_, 0, v_ks_1676_);
lean_ctor_set(v_reuseFailAlloc_1695_, 1, v_vs_1677_);
v___x_1691_ = v_reuseFailAlloc_1695_;
goto v_reusejp_1690_;
}
v_reusejp_1690_:
{
lean_object* v___x_1692_; lean_object* v___x_1693_; 
v___x_1692_ = lean_unsigned_to_nat(1u);
v___x_1693_ = lean_nat_add(v_x_1673_, v___x_1692_);
lean_dec(v_x_1673_);
v_x_1672_ = v___x_1691_;
v_x_1673_ = v___x_1693_;
goto _start;
}
}
else
{
lean_object* v___x_1696_; lean_object* v___x_1697_; lean_object* v___x_1699_; 
v___x_1696_ = lean_array_fset(v_ks_1676_, v_x_1673_, v_x_1674_);
v___x_1697_ = lean_array_fset(v_vs_1677_, v_x_1673_, v_x_1675_);
lean_dec(v_x_1673_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 1, v___x_1697_);
lean_ctor_set(v___x_1679_, 0, v___x_1696_);
v___x_1699_ = v___x_1679_;
goto v_reusejp_1698_;
}
else
{
lean_object* v_reuseFailAlloc_1700_; 
v_reuseFailAlloc_1700_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1700_, 0, v___x_1696_);
lean_ctor_set(v_reuseFailAlloc_1700_, 1, v___x_1697_);
v___x_1699_ = v_reuseFailAlloc_1700_;
goto v_reusejp_1698_;
}
v_reusejp_1698_:
{
return v___x_1699_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1702_, lean_object* v_k_1703_, lean_object* v_v_1704_){
_start:
{
lean_object* v___x_1705_; lean_object* v___x_1706_; 
v___x_1705_ = lean_unsigned_to_nat(0u);
v___x_1706_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1702_, v___x_1705_, v_k_1703_, v_v_1704_);
return v___x_1706_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1707_, size_t v_x_1708_, size_t v_x_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_){
_start:
{
if (lean_obj_tag(v_x_1707_) == 0)
{
lean_object* v_es_1712_; size_t v___x_1713_; size_t v___x_1714_; lean_object* v_j_1715_; lean_object* v___x_1716_; uint8_t v___x_1717_; 
v_es_1712_ = lean_ctor_get(v_x_1707_, 0);
v___x_1713_ = ((size_t)31ULL);
v___x_1714_ = lean_usize_land(v_x_1708_, v___x_1713_);
v_j_1715_ = lean_usize_to_nat(v___x_1714_);
v___x_1716_ = lean_array_get_size(v_es_1712_);
v___x_1717_ = lean_nat_dec_lt(v_j_1715_, v___x_1716_);
if (v___x_1717_ == 0)
{
lean_dec(v_j_1715_);
lean_dec(v_x_1711_);
lean_dec(v_x_1710_);
return v_x_1707_;
}
else
{
lean_object* v___x_1719_; uint8_t v_isShared_1720_; uint8_t v_isSharedCheck_1756_; 
lean_inc_ref(v_es_1712_);
v_isSharedCheck_1756_ = !lean_is_exclusive(v_x_1707_);
if (v_isSharedCheck_1756_ == 0)
{
lean_object* v_unused_1757_; 
v_unused_1757_ = lean_ctor_get(v_x_1707_, 0);
lean_dec(v_unused_1757_);
v___x_1719_ = v_x_1707_;
v_isShared_1720_ = v_isSharedCheck_1756_;
goto v_resetjp_1718_;
}
else
{
lean_dec(v_x_1707_);
v___x_1719_ = lean_box(0);
v_isShared_1720_ = v_isSharedCheck_1756_;
goto v_resetjp_1718_;
}
v_resetjp_1718_:
{
lean_object* v_v_1721_; lean_object* v___x_1722_; lean_object* v_xs_x27_1723_; lean_object* v___y_1725_; 
v_v_1721_ = lean_array_fget(v_es_1712_, v_j_1715_);
v___x_1722_ = lean_box(0);
v_xs_x27_1723_ = lean_array_fset(v_es_1712_, v_j_1715_, v___x_1722_);
switch(lean_obj_tag(v_v_1721_))
{
case 0:
{
lean_object* v_key_1730_; lean_object* v_val_1731_; lean_object* v___x_1733_; uint8_t v_isShared_1734_; uint8_t v_isSharedCheck_1741_; 
v_key_1730_ = lean_ctor_get(v_v_1721_, 0);
v_val_1731_ = lean_ctor_get(v_v_1721_, 1);
v_isSharedCheck_1741_ = !lean_is_exclusive(v_v_1721_);
if (v_isSharedCheck_1741_ == 0)
{
v___x_1733_ = v_v_1721_;
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
else
{
lean_inc(v_val_1731_);
lean_inc(v_key_1730_);
lean_dec(v_v_1721_);
v___x_1733_ = lean_box(0);
v_isShared_1734_ = v_isSharedCheck_1741_;
goto v_resetjp_1732_;
}
v_resetjp_1732_:
{
uint8_t v___x_1735_; 
v___x_1735_ = l_Lean_instBEqMVarId_beq(v_x_1710_, v_key_1730_);
if (v___x_1735_ == 0)
{
lean_object* v___x_1736_; lean_object* v___x_1737_; 
lean_del_object(v___x_1733_);
v___x_1736_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1730_, v_val_1731_, v_x_1710_, v_x_1711_);
v___x_1737_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1737_, 0, v___x_1736_);
v___y_1725_ = v___x_1737_;
goto v___jp_1724_;
}
else
{
lean_object* v___x_1739_; 
lean_dec(v_val_1731_);
lean_dec(v_key_1730_);
if (v_isShared_1734_ == 0)
{
lean_ctor_set(v___x_1733_, 1, v_x_1711_);
lean_ctor_set(v___x_1733_, 0, v_x_1710_);
v___x_1739_ = v___x_1733_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v_x_1710_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_x_1711_);
v___x_1739_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
v___y_1725_ = v___x_1739_;
goto v___jp_1724_;
}
}
}
}
case 1:
{
lean_object* v_node_1742_; lean_object* v___x_1744_; uint8_t v_isShared_1745_; uint8_t v_isSharedCheck_1754_; 
v_node_1742_ = lean_ctor_get(v_v_1721_, 0);
v_isSharedCheck_1754_ = !lean_is_exclusive(v_v_1721_);
if (v_isSharedCheck_1754_ == 0)
{
v___x_1744_ = v_v_1721_;
v_isShared_1745_ = v_isSharedCheck_1754_;
goto v_resetjp_1743_;
}
else
{
lean_inc(v_node_1742_);
lean_dec(v_v_1721_);
v___x_1744_ = lean_box(0);
v_isShared_1745_ = v_isSharedCheck_1754_;
goto v_resetjp_1743_;
}
v_resetjp_1743_:
{
size_t v___x_1746_; size_t v___x_1747_; size_t v___x_1748_; size_t v___x_1749_; lean_object* v___x_1750_; lean_object* v___x_1752_; 
v___x_1746_ = ((size_t)5ULL);
v___x_1747_ = lean_usize_shift_right(v_x_1708_, v___x_1746_);
v___x_1748_ = ((size_t)1ULL);
v___x_1749_ = lean_usize_add(v_x_1709_, v___x_1748_);
v___x_1750_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_node_1742_, v___x_1747_, v___x_1749_, v_x_1710_, v_x_1711_);
if (v_isShared_1745_ == 0)
{
lean_ctor_set(v___x_1744_, 0, v___x_1750_);
v___x_1752_ = v___x_1744_;
goto v_reusejp_1751_;
}
else
{
lean_object* v_reuseFailAlloc_1753_; 
v_reuseFailAlloc_1753_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1753_, 0, v___x_1750_);
v___x_1752_ = v_reuseFailAlloc_1753_;
goto v_reusejp_1751_;
}
v_reusejp_1751_:
{
v___y_1725_ = v___x_1752_;
goto v___jp_1724_;
}
}
}
default: 
{
lean_object* v___x_1755_; 
v___x_1755_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1755_, 0, v_x_1710_);
lean_ctor_set(v___x_1755_, 1, v_x_1711_);
v___y_1725_ = v___x_1755_;
goto v___jp_1724_;
}
}
v___jp_1724_:
{
lean_object* v___x_1726_; lean_object* v___x_1728_; 
v___x_1726_ = lean_array_fset(v_xs_x27_1723_, v_j_1715_, v___y_1725_);
lean_dec(v_j_1715_);
if (v_isShared_1720_ == 0)
{
lean_ctor_set(v___x_1719_, 0, v___x_1726_);
v___x_1728_ = v___x_1719_;
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
}
}
else
{
lean_object* v_ks_1758_; lean_object* v_vs_1759_; lean_object* v___x_1761_; uint8_t v_isShared_1762_; uint8_t v_isSharedCheck_1777_; 
v_ks_1758_ = lean_ctor_get(v_x_1707_, 0);
v_vs_1759_ = lean_ctor_get(v_x_1707_, 1);
v_isSharedCheck_1777_ = !lean_is_exclusive(v_x_1707_);
if (v_isSharedCheck_1777_ == 0)
{
v___x_1761_ = v_x_1707_;
v_isShared_1762_ = v_isSharedCheck_1777_;
goto v_resetjp_1760_;
}
else
{
lean_inc(v_vs_1759_);
lean_inc(v_ks_1758_);
lean_dec(v_x_1707_);
v___x_1761_ = lean_box(0);
v_isShared_1762_ = v_isSharedCheck_1777_;
goto v_resetjp_1760_;
}
v_resetjp_1760_:
{
lean_object* v___x_1764_; 
if (v_isShared_1762_ == 0)
{
v___x_1764_ = v___x_1761_;
goto v_reusejp_1763_;
}
else
{
lean_object* v_reuseFailAlloc_1776_; 
v_reuseFailAlloc_1776_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1776_, 0, v_ks_1758_);
lean_ctor_set(v_reuseFailAlloc_1776_, 1, v_vs_1759_);
v___x_1764_ = v_reuseFailAlloc_1776_;
goto v_reusejp_1763_;
}
v_reusejp_1763_:
{
lean_object* v_newNode_1765_; size_t v___x_1766_; uint8_t v___x_1767_; 
v_newNode_1765_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v___x_1764_, v_x_1710_, v_x_1711_);
v___x_1766_ = ((size_t)7ULL);
v___x_1767_ = lean_usize_dec_le(v___x_1766_, v_x_1709_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; lean_object* v___x_1769_; uint8_t v___x_1770_; 
v___x_1768_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1765_);
v___x_1769_ = lean_unsigned_to_nat(4u);
v___x_1770_ = lean_nat_dec_lt(v___x_1768_, v___x_1769_);
lean_dec(v___x_1768_);
if (v___x_1770_ == 0)
{
lean_object* v_ks_1771_; lean_object* v_vs_1772_; lean_object* v___x_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; 
v_ks_1771_ = lean_ctor_get(v_newNode_1765_, 0);
lean_inc_ref(v_ks_1771_);
v_vs_1772_ = lean_ctor_get(v_newNode_1765_, 1);
lean_inc_ref(v_vs_1772_);
lean_dec_ref(v_newNode_1765_);
v___x_1773_ = lean_unsigned_to_nat(0u);
v___x_1774_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0);
v___x_1775_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_x_1709_, v_ks_1771_, v_vs_1772_, v___x_1773_, v___x_1774_);
lean_dec_ref(v_vs_1772_);
lean_dec_ref(v_ks_1771_);
return v___x_1775_;
}
else
{
return v_newNode_1765_;
}
}
else
{
return v_newNode_1765_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(size_t v_depth_1778_, lean_object* v_keys_1779_, lean_object* v_vals_1780_, lean_object* v_i_1781_, lean_object* v_entries_1782_){
_start:
{
lean_object* v___x_1783_; uint8_t v___x_1784_; 
v___x_1783_ = lean_array_get_size(v_keys_1779_);
v___x_1784_ = lean_nat_dec_lt(v_i_1781_, v___x_1783_);
if (v___x_1784_ == 0)
{
lean_dec(v_i_1781_);
return v_entries_1782_;
}
else
{
lean_object* v_k_1785_; lean_object* v_v_1786_; uint64_t v___x_1787_; size_t v_h_1788_; size_t v___x_1789_; lean_object* v___x_1790_; size_t v___x_1791_; size_t v___x_1792_; size_t v___x_1793_; size_t v_h_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_k_1785_ = lean_array_fget_borrowed(v_keys_1779_, v_i_1781_);
v_v_1786_ = lean_array_fget_borrowed(v_vals_1780_, v_i_1781_);
v___x_1787_ = l_Lean_instHashableMVarId_hash(v_k_1785_);
v_h_1788_ = lean_uint64_to_usize(v___x_1787_);
v___x_1789_ = ((size_t)5ULL);
v___x_1790_ = lean_unsigned_to_nat(1u);
v___x_1791_ = ((size_t)1ULL);
v___x_1792_ = lean_usize_sub(v_depth_1778_, v___x_1791_);
v___x_1793_ = lean_usize_mul(v___x_1789_, v___x_1792_);
v_h_1794_ = lean_usize_shift_right(v_h_1788_, v___x_1793_);
v___x_1795_ = lean_nat_add(v_i_1781_, v___x_1790_);
lean_dec(v_i_1781_);
lean_inc(v_v_1786_);
lean_inc(v_k_1785_);
v___x_1796_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_entries_1782_, v_h_1794_, v_depth_1778_, v_k_1785_, v_v_1786_);
v_i_1781_ = v___x_1795_;
v_entries_1782_ = v___x_1796_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1798_, lean_object* v_keys_1799_, lean_object* v_vals_1800_, lean_object* v_i_1801_, lean_object* v_entries_1802_){
_start:
{
size_t v_depth_boxed_1803_; lean_object* v_res_1804_; 
v_depth_boxed_1803_ = lean_unbox_usize(v_depth_1798_);
lean_dec(v_depth_1798_);
v_res_1804_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1803_, v_keys_1799_, v_vals_1800_, v_i_1801_, v_entries_1802_);
lean_dec_ref(v_vals_1800_);
lean_dec_ref(v_keys_1799_);
return v_res_1804_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1805_, lean_object* v_x_1806_, lean_object* v_x_1807_, lean_object* v_x_1808_, lean_object* v_x_1809_){
_start:
{
size_t v_x_1607__boxed_1810_; size_t v_x_1608__boxed_1811_; lean_object* v_res_1812_; 
v_x_1607__boxed_1810_ = lean_unbox_usize(v_x_1806_);
lean_dec(v_x_1806_);
v_x_1608__boxed_1811_ = lean_unbox_usize(v_x_1807_);
lean_dec(v_x_1807_);
v_res_1812_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1805_, v_x_1607__boxed_1810_, v_x_1608__boxed_1811_, v_x_1808_, v_x_1809_);
return v_res_1812_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(lean_object* v_x_1813_, lean_object* v_x_1814_, lean_object* v_x_1815_){
_start:
{
uint64_t v___x_1816_; size_t v___x_1817_; size_t v___x_1818_; lean_object* v___x_1819_; 
v___x_1816_ = l_Lean_instHashableMVarId_hash(v_x_1814_);
v___x_1817_ = lean_uint64_to_usize(v___x_1816_);
v___x_1818_ = ((size_t)1ULL);
v___x_1819_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1813_, v___x_1817_, v___x_1818_, v_x_1814_, v_x_1815_);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(lean_object* v_mvarId_1820_, lean_object* v_val_1821_, lean_object* v___y_1822_){
_start:
{
lean_object* v___x_1824_; lean_object* v_mctx_1825_; lean_object* v_cache_1826_; lean_object* v_zetaDeltaFVarIds_1827_; lean_object* v_postponed_1828_; lean_object* v_diag_1829_; lean_object* v___x_1831_; uint8_t v_isShared_1832_; uint8_t v_isSharedCheck_1858_; 
v___x_1824_ = lean_st_ref_take(v___y_1822_);
v_mctx_1825_ = lean_ctor_get(v___x_1824_, 0);
v_cache_1826_ = lean_ctor_get(v___x_1824_, 1);
v_zetaDeltaFVarIds_1827_ = lean_ctor_get(v___x_1824_, 2);
v_postponed_1828_ = lean_ctor_get(v___x_1824_, 3);
v_diag_1829_ = lean_ctor_get(v___x_1824_, 4);
v_isSharedCheck_1858_ = !lean_is_exclusive(v___x_1824_);
if (v_isSharedCheck_1858_ == 0)
{
v___x_1831_ = v___x_1824_;
v_isShared_1832_ = v_isSharedCheck_1858_;
goto v_resetjp_1830_;
}
else
{
lean_inc(v_diag_1829_);
lean_inc(v_postponed_1828_);
lean_inc(v_zetaDeltaFVarIds_1827_);
lean_inc(v_cache_1826_);
lean_inc(v_mctx_1825_);
lean_dec(v___x_1824_);
v___x_1831_ = lean_box(0);
v_isShared_1832_ = v_isSharedCheck_1858_;
goto v_resetjp_1830_;
}
v_resetjp_1830_:
{
lean_object* v_depth_1833_; lean_object* v_levelAssignDepth_1834_; lean_object* v_lmvarCounter_1835_; lean_object* v_mvarCounter_1836_; lean_object* v_lDecls_1837_; lean_object* v_decls_1838_; lean_object* v_userNames_1839_; lean_object* v_lAssignment_1840_; lean_object* v_eAssignment_1841_; lean_object* v_dAssignment_1842_; lean_object* v_instanceTypedMVars_1843_; lean_object* v___x_1845_; uint8_t v_isShared_1846_; uint8_t v_isSharedCheck_1857_; 
v_depth_1833_ = lean_ctor_get(v_mctx_1825_, 0);
v_levelAssignDepth_1834_ = lean_ctor_get(v_mctx_1825_, 1);
v_lmvarCounter_1835_ = lean_ctor_get(v_mctx_1825_, 2);
v_mvarCounter_1836_ = lean_ctor_get(v_mctx_1825_, 3);
v_lDecls_1837_ = lean_ctor_get(v_mctx_1825_, 4);
v_decls_1838_ = lean_ctor_get(v_mctx_1825_, 5);
v_userNames_1839_ = lean_ctor_get(v_mctx_1825_, 6);
v_lAssignment_1840_ = lean_ctor_get(v_mctx_1825_, 7);
v_eAssignment_1841_ = lean_ctor_get(v_mctx_1825_, 8);
v_dAssignment_1842_ = lean_ctor_get(v_mctx_1825_, 9);
v_instanceTypedMVars_1843_ = lean_ctor_get(v_mctx_1825_, 10);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_mctx_1825_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1845_ = v_mctx_1825_;
v_isShared_1846_ = v_isSharedCheck_1857_;
goto v_resetjp_1844_;
}
else
{
lean_inc(v_instanceTypedMVars_1843_);
lean_inc(v_dAssignment_1842_);
lean_inc(v_eAssignment_1841_);
lean_inc(v_lAssignment_1840_);
lean_inc(v_userNames_1839_);
lean_inc(v_decls_1838_);
lean_inc(v_lDecls_1837_);
lean_inc(v_mvarCounter_1836_);
lean_inc(v_lmvarCounter_1835_);
lean_inc(v_levelAssignDepth_1834_);
lean_inc(v_depth_1833_);
lean_dec(v_mctx_1825_);
v___x_1845_ = lean_box(0);
v_isShared_1846_ = v_isSharedCheck_1857_;
goto v_resetjp_1844_;
}
v_resetjp_1844_:
{
lean_object* v___x_1847_; lean_object* v___x_1848_; lean_object* v___x_1850_; 
v___x_1847_ = lean_box(0);
v___x_1848_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_eAssignment_1841_, v_mvarId_1820_, v_val_1821_);
if (v_isShared_1846_ == 0)
{
lean_ctor_set(v___x_1845_, 8, v___x_1848_);
v___x_1850_ = v___x_1845_;
goto v_reusejp_1849_;
}
else
{
lean_object* v_reuseFailAlloc_1856_; 
v_reuseFailAlloc_1856_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1856_, 0, v_depth_1833_);
lean_ctor_set(v_reuseFailAlloc_1856_, 1, v_levelAssignDepth_1834_);
lean_ctor_set(v_reuseFailAlloc_1856_, 2, v_lmvarCounter_1835_);
lean_ctor_set(v_reuseFailAlloc_1856_, 3, v_mvarCounter_1836_);
lean_ctor_set(v_reuseFailAlloc_1856_, 4, v_lDecls_1837_);
lean_ctor_set(v_reuseFailAlloc_1856_, 5, v_decls_1838_);
lean_ctor_set(v_reuseFailAlloc_1856_, 6, v_userNames_1839_);
lean_ctor_set(v_reuseFailAlloc_1856_, 7, v_lAssignment_1840_);
lean_ctor_set(v_reuseFailAlloc_1856_, 8, v___x_1848_);
lean_ctor_set(v_reuseFailAlloc_1856_, 9, v_dAssignment_1842_);
lean_ctor_set(v_reuseFailAlloc_1856_, 10, v_instanceTypedMVars_1843_);
v___x_1850_ = v_reuseFailAlloc_1856_;
goto v_reusejp_1849_;
}
v_reusejp_1849_:
{
lean_object* v___x_1852_; 
if (v_isShared_1832_ == 0)
{
lean_ctor_set(v___x_1831_, 0, v___x_1850_);
v___x_1852_ = v___x_1831_;
goto v_reusejp_1851_;
}
else
{
lean_object* v_reuseFailAlloc_1855_; 
v_reuseFailAlloc_1855_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1855_, 0, v___x_1850_);
lean_ctor_set(v_reuseFailAlloc_1855_, 1, v_cache_1826_);
lean_ctor_set(v_reuseFailAlloc_1855_, 2, v_zetaDeltaFVarIds_1827_);
lean_ctor_set(v_reuseFailAlloc_1855_, 3, v_postponed_1828_);
lean_ctor_set(v_reuseFailAlloc_1855_, 4, v_diag_1829_);
v___x_1852_ = v_reuseFailAlloc_1855_;
goto v_reusejp_1851_;
}
v_reusejp_1851_:
{
lean_object* v___x_1853_; lean_object* v___x_1854_; 
v___x_1853_ = lean_st_ref_put(v___y_1822_, v___x_1852_);
v___x_1854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1854_, 0, v___x_1847_);
return v___x_1854_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg___boxed(lean_object* v_mvarId_1859_, lean_object* v_val_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1859_, v_val_1860_, v___y_1861_);
lean_dec(v___y_1861_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(lean_object* v_argMVars_1864_, lean_object* v_argVars_1865_, lean_object* v_as_1866_, size_t v_sz_1867_, size_t v_i_1868_, lean_object* v_b_1869_, lean_object* v___y_1870_, lean_object* v___y_1871_, lean_object* v___y_1872_, lean_object* v___y_1873_){
_start:
{
uint8_t v___x_1875_; 
v___x_1875_ = lean_usize_dec_lt(v_i_1868_, v_sz_1867_);
if (v___x_1875_ == 0)
{
lean_object* v___x_1876_; 
v___x_1876_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1876_, 0, v_b_1869_);
return v___x_1876_;
}
else
{
lean_object* v___x_1877_; lean_object* v_a_1878_; lean_object* v___y_1880_; lean_object* v___y_1881_; lean_object* v___y_1882_; lean_object* v___y_1883_; lean_object* v___x_1899_; lean_object* v___x_1900_; 
v___x_1877_ = lean_box(0);
v_a_1878_ = lean_array_uget_borrowed(v_as_1866_, v_i_1868_);
v___x_1899_ = lean_unsigned_to_nat(0u);
v___x_1900_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1878_, v_argMVars_1864_, v___x_1899_);
if (lean_obj_tag(v___x_1900_) == 1)
{
lean_object* v_val_1901_; lean_object* v___x_1902_; lean_object* v___x_1903_; lean_object* v___x_1904_; 
v_val_1901_ = lean_ctor_get(v___x_1900_, 0);
lean_inc(v_val_1901_);
lean_dec_ref_known(v___x_1900_, 1);
v___x_1902_ = l_Lean_instInhabitedExpr;
v___x_1903_ = lean_array_get_borrowed(v___x_1902_, v_argVars_1865_, v_val_1901_);
lean_dec(v_val_1901_);
lean_inc(v___x_1903_);
lean_inc(v_a_1878_);
v___x_1904_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_a_1878_, v___x_1903_, v___y_1871_);
if (lean_obj_tag(v___x_1904_) == 0)
{
lean_dec_ref_known(v___x_1904_, 1);
v___y_1880_ = v___y_1870_;
v___y_1881_ = v___y_1871_;
v___y_1882_ = v___y_1872_;
v___y_1883_ = v___y_1873_;
goto v___jp_1879_;
}
else
{
return v___x_1904_;
}
}
else
{
lean_dec(v___x_1900_);
v___y_1880_ = v___y_1870_;
v___y_1881_ = v___y_1871_;
v___y_1882_ = v___y_1872_;
v___y_1883_ = v___y_1873_;
goto v___jp_1879_;
}
v___jp_1879_:
{
lean_object* v___x_1884_; lean_object* v___x_1885_; 
lean_inc(v_a_1878_);
v___x_1884_ = l_Lean_Expr_mvar___override(v_a_1878_);
lean_inc(v___y_1883_);
lean_inc_ref(v___y_1882_);
lean_inc(v___y_1881_);
lean_inc_ref(v___y_1880_);
v___x_1885_ = lean_infer_type(v___x_1884_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1885_) == 0)
{
lean_object* v_a_1886_; lean_object* v___x_1887_; 
v_a_1886_ = lean_ctor_get(v___x_1885_, 0);
lean_inc(v_a_1886_);
lean_dec_ref_known(v___x_1885_, 1);
v___x_1887_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1864_, v_argVars_1865_, v_a_1886_, v___y_1880_, v___y_1881_, v___y_1882_, v___y_1883_);
if (lean_obj_tag(v___x_1887_) == 0)
{
size_t v___x_1888_; size_t v___x_1889_; 
lean_dec_ref_known(v___x_1887_, 1);
v___x_1888_ = ((size_t)1ULL);
v___x_1889_ = lean_usize_add(v_i_1868_, v___x_1888_);
v_i_1868_ = v___x_1889_;
v_b_1869_ = v___x_1877_;
goto _start;
}
else
{
return v___x_1887_;
}
}
else
{
lean_object* v_a_1891_; lean_object* v___x_1893_; uint8_t v_isShared_1894_; uint8_t v_isSharedCheck_1898_; 
v_a_1891_ = lean_ctor_get(v___x_1885_, 0);
v_isSharedCheck_1898_ = !lean_is_exclusive(v___x_1885_);
if (v_isSharedCheck_1898_ == 0)
{
v___x_1893_ = v___x_1885_;
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
else
{
lean_inc(v_a_1891_);
lean_dec(v___x_1885_);
v___x_1893_ = lean_box(0);
v_isShared_1894_ = v_isSharedCheck_1898_;
goto v_resetjp_1892_;
}
v_resetjp_1892_:
{
lean_object* v___x_1896_; 
if (v_isShared_1894_ == 0)
{
v___x_1896_ = v___x_1893_;
goto v_reusejp_1895_;
}
else
{
lean_object* v_reuseFailAlloc_1897_; 
v_reuseFailAlloc_1897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1897_, 0, v_a_1891_);
v___x_1896_ = v_reuseFailAlloc_1897_;
goto v_reusejp_1895_;
}
v_reusejp_1895_:
{
return v___x_1896_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1905_, lean_object* v_argVars_1906_, lean_object* v_e_1907_, lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_Meta_getMVars(v_e_1907_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
if (lean_obj_tag(v___x_1913_) == 0)
{
lean_object* v_a_1914_; lean_object* v___x_1915_; size_t v_sz_1916_; size_t v___x_1917_; lean_object* v___x_1918_; 
v_a_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc(v_a_1914_);
lean_dec_ref_known(v___x_1913_, 1);
v___x_1915_ = lean_box(0);
v_sz_1916_ = lean_array_size(v_a_1914_);
v___x_1917_ = ((size_t)0ULL);
v___x_1918_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1905_, v_argVars_1906_, v_a_1914_, v_sz_1916_, v___x_1917_, v___x_1915_, v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_);
lean_dec(v_a_1914_);
if (lean_obj_tag(v___x_1918_) == 0)
{
lean_object* v___x_1920_; uint8_t v_isShared_1921_; uint8_t v_isSharedCheck_1925_; 
v_isSharedCheck_1925_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1925_ == 0)
{
lean_object* v_unused_1926_; 
v_unused_1926_ = lean_ctor_get(v___x_1918_, 0);
lean_dec(v_unused_1926_);
v___x_1920_ = v___x_1918_;
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
else
{
lean_dec(v___x_1918_);
v___x_1920_ = lean_box(0);
v_isShared_1921_ = v_isSharedCheck_1925_;
goto v_resetjp_1919_;
}
v_resetjp_1919_:
{
lean_object* v___x_1923_; 
if (v_isShared_1921_ == 0)
{
lean_ctor_set(v___x_1920_, 0, v___x_1915_);
v___x_1923_ = v___x_1920_;
goto v_reusejp_1922_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v___x_1915_);
v___x_1923_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1922_;
}
v_reusejp_1922_:
{
return v___x_1923_;
}
}
}
else
{
return v___x_1918_;
}
}
else
{
lean_object* v_a_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1934_; 
v_a_1927_ = lean_ctor_get(v___x_1913_, 0);
v_isSharedCheck_1934_ = !lean_is_exclusive(v___x_1913_);
if (v_isSharedCheck_1934_ == 0)
{
v___x_1929_ = v___x_1913_;
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_a_1927_);
lean_dec(v___x_1913_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1934_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1933_; 
v_reuseFailAlloc_1933_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1933_, 0, v_a_1927_);
v___x_1932_ = v_reuseFailAlloc_1933_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
return v___x_1932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1935_, lean_object* v_argVars_1936_, lean_object* v_e_1937_, lean_object* v_a_1938_, lean_object* v_a_1939_, lean_object* v_a_1940_, lean_object* v_a_1941_, lean_object* v_a_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1935_, v_argVars_1936_, v_e_1937_, v_a_1938_, v_a_1939_, v_a_1940_, v_a_1941_);
lean_dec(v_a_1941_);
lean_dec_ref(v_a_1940_);
lean_dec(v_a_1939_);
lean_dec_ref(v_a_1938_);
lean_dec_ref(v_argVars_1936_);
lean_dec_ref(v_argMVars_1935_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2___boxed(lean_object* v_argMVars_1944_, lean_object* v_argVars_1945_, lean_object* v_as_1946_, lean_object* v_sz_1947_, lean_object* v_i_1948_, lean_object* v_b_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
size_t v_sz_boxed_1955_; size_t v_i_boxed_1956_; lean_object* v_res_1957_; 
v_sz_boxed_1955_ = lean_unbox_usize(v_sz_1947_);
lean_dec(v_sz_1947_);
v_i_boxed_1956_ = lean_unbox_usize(v_i_1948_);
lean_dec(v_i_1948_);
v_res_1957_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1944_, v_argVars_1945_, v_as_1946_, v_sz_boxed_1955_, v_i_boxed_1956_, v_b_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
lean_dec_ref(v_as_1946_);
lean_dec_ref(v_argVars_1945_);
lean_dec_ref(v_argMVars_1944_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_mvarId_1958_, lean_object* v_val_1959_, lean_object* v___y_1960_, lean_object* v___y_1961_, lean_object* v___y_1962_, lean_object* v___y_1963_){
_start:
{
lean_object* v___x_1965_; 
v___x_1965_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1958_, v_val_1959_, v___y_1961_);
return v___x_1965_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_mvarId_1966_, lean_object* v_val_1967_, lean_object* v___y_1968_, lean_object* v___y_1969_, lean_object* v___y_1970_, lean_object* v___y_1971_, lean_object* v___y_1972_){
_start:
{
lean_object* v_res_1973_; 
v_res_1973_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_mvarId_1966_, v_val_1967_, v___y_1968_, v___y_1969_, v___y_1970_, v___y_1971_);
lean_dec(v___y_1971_);
lean_dec_ref(v___y_1970_);
lean_dec(v___y_1969_);
lean_dec_ref(v___y_1968_);
return v_res_1973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1(lean_object* v_00_u03b2_1974_, lean_object* v_x_1975_, lean_object* v_x_1976_, lean_object* v_x_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_x_1975_, v_x_1976_, v_x_1977_);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1979_, lean_object* v_x_1980_, size_t v_x_1981_, size_t v_x_1982_, lean_object* v_x_1983_, lean_object* v_x_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1980_, v_x_1981_, v_x_1982_, v_x_1983_, v_x_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1986_, lean_object* v_x_1987_, lean_object* v_x_1988_, lean_object* v_x_1989_, lean_object* v_x_1990_, lean_object* v_x_1991_){
_start:
{
size_t v_x_1965__boxed_1992_; size_t v_x_1966__boxed_1993_; lean_object* v_res_1994_; 
v_x_1965__boxed_1992_ = lean_unbox_usize(v_x_1988_);
lean_dec(v_x_1988_);
v_x_1966__boxed_1993_ = lean_unbox_usize(v_x_1989_);
lean_dec(v_x_1989_);
v_res_1994_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(v_00_u03b2_1986_, v_x_1987_, v_x_1965__boxed_1992_, v_x_1966__boxed_1993_, v_x_1990_, v_x_1991_);
return v_res_1994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1995_, lean_object* v_n_1996_, lean_object* v_k_1997_, lean_object* v_v_1998_){
_start:
{
lean_object* v___x_1999_; 
v___x_1999_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v_n_1996_, v_k_1997_, v_v_1998_);
return v___x_1999_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_2000_, size_t v_depth_2001_, lean_object* v_keys_2002_, lean_object* v_vals_2003_, lean_object* v_heq_2004_, lean_object* v_i_2005_, lean_object* v_entries_2006_){
_start:
{
lean_object* v___x_2007_; 
v___x_2007_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_2001_, v_keys_2002_, v_vals_2003_, v_i_2005_, v_entries_2006_);
return v___x_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_2008_, lean_object* v_depth_2009_, lean_object* v_keys_2010_, lean_object* v_vals_2011_, lean_object* v_heq_2012_, lean_object* v_i_2013_, lean_object* v_entries_2014_){
_start:
{
size_t v_depth_boxed_2015_; lean_object* v_res_2016_; 
v_depth_boxed_2015_ = lean_unbox_usize(v_depth_2009_);
lean_dec(v_depth_2009_);
v_res_2016_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_2008_, v_depth_boxed_2015_, v_keys_2010_, v_vals_2011_, v_heq_2012_, v_i_2013_, v_entries_2014_);
lean_dec_ref(v_vals_2011_);
lean_dec_ref(v_keys_2010_);
return v_res_2016_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_2017_, lean_object* v_x_2018_, lean_object* v_x_2019_, lean_object* v_x_2020_, lean_object* v_x_2021_){
_start:
{
lean_object* v___x_2022_; 
v___x_2022_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_x_2018_, v_x_2019_, v_x_2020_, v_x_2021_);
return v___x_2022_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_2023_, lean_object* v___y_2024_){
_start:
{
uint8_t v___x_2026_; 
v___x_2026_ = l_Lean_Expr_hasMVar(v_e_2023_);
if (v___x_2026_ == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2027_, 0, v_e_2023_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; lean_object* v_mctx_2029_; lean_object* v___x_2030_; lean_object* v_fst_2031_; lean_object* v_snd_2032_; lean_object* v___x_2033_; lean_object* v_cache_2034_; lean_object* v_zetaDeltaFVarIds_2035_; lean_object* v_postponed_2036_; lean_object* v_diag_2037_; lean_object* v___x_2039_; uint8_t v_isShared_2040_; uint8_t v_isSharedCheck_2046_; 
v___x_2028_ = lean_st_ref_get(v___y_2024_);
v_mctx_2029_ = lean_ctor_get(v___x_2028_, 0);
lean_inc_ref(v_mctx_2029_);
lean_dec(v___x_2028_);
v___x_2030_ = l_Lean_instantiateMVarsCore(v_mctx_2029_, v_e_2023_);
v_fst_2031_ = lean_ctor_get(v___x_2030_, 0);
lean_inc(v_fst_2031_);
v_snd_2032_ = lean_ctor_get(v___x_2030_, 1);
lean_inc(v_snd_2032_);
lean_dec_ref(v___x_2030_);
v___x_2033_ = lean_st_ref_take(v___y_2024_);
v_cache_2034_ = lean_ctor_get(v___x_2033_, 1);
v_zetaDeltaFVarIds_2035_ = lean_ctor_get(v___x_2033_, 2);
v_postponed_2036_ = lean_ctor_get(v___x_2033_, 3);
v_diag_2037_ = lean_ctor_get(v___x_2033_, 4);
v_isSharedCheck_2046_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; 
v_unused_2047_ = lean_ctor_get(v___x_2033_, 0);
lean_dec(v_unused_2047_);
v___x_2039_ = v___x_2033_;
v_isShared_2040_ = v_isSharedCheck_2046_;
goto v_resetjp_2038_;
}
else
{
lean_inc(v_diag_2037_);
lean_inc(v_postponed_2036_);
lean_inc(v_zetaDeltaFVarIds_2035_);
lean_inc(v_cache_2034_);
lean_dec(v___x_2033_);
v___x_2039_ = lean_box(0);
v_isShared_2040_ = v_isSharedCheck_2046_;
goto v_resetjp_2038_;
}
v_resetjp_2038_:
{
lean_object* v___x_2042_; 
if (v_isShared_2040_ == 0)
{
lean_ctor_set(v___x_2039_, 0, v_snd_2032_);
v___x_2042_ = v___x_2039_;
goto v_reusejp_2041_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v_snd_2032_);
lean_ctor_set(v_reuseFailAlloc_2045_, 1, v_cache_2034_);
lean_ctor_set(v_reuseFailAlloc_2045_, 2, v_zetaDeltaFVarIds_2035_);
lean_ctor_set(v_reuseFailAlloc_2045_, 3, v_postponed_2036_);
lean_ctor_set(v_reuseFailAlloc_2045_, 4, v_diag_2037_);
v___x_2042_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2041_;
}
v_reusejp_2041_:
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
v___x_2043_ = lean_st_ref_put(v___y_2024_, v___x_2042_);
v___x_2044_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2044_, 0, v_fst_2031_);
return v___x_2044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_2048_, lean_object* v___y_2049_, lean_object* v___y_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_2048_, v___y_2049_);
lean_dec(v___y_2049_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_2052_, lean_object* v___y_2053_, lean_object* v___y_2054_, lean_object* v___y_2055_, lean_object* v___y_2056_){
_start:
{
lean_object* v___x_2058_; 
v___x_2058_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_2052_, v___y_2054_);
return v___x_2058_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_){
_start:
{
lean_object* v_res_2065_; 
v_res_2065_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_2059_, v___y_2060_, v___y_2061_, v___y_2062_, v___y_2063_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec(v___y_2061_);
lean_dec_ref(v___y_2060_);
return v_res_2065_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_2066_, lean_object* v_opt_2067_){
_start:
{
lean_object* v_name_2068_; lean_object* v_defValue_2069_; lean_object* v_map_2070_; lean_object* v___x_2071_; 
v_name_2068_ = lean_ctor_get(v_opt_2067_, 0);
v_defValue_2069_ = lean_ctor_get(v_opt_2067_, 1);
v_map_2070_ = lean_ctor_get(v_opts_2066_, 0);
v___x_2071_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_2070_, v_name_2068_);
if (lean_obj_tag(v___x_2071_) == 0)
{
uint8_t v___x_2072_; 
v___x_2072_ = lean_unbox(v_defValue_2069_);
return v___x_2072_;
}
else
{
lean_object* v_val_2073_; 
v_val_2073_ = lean_ctor_get(v___x_2071_, 0);
lean_inc(v_val_2073_);
lean_dec_ref_known(v___x_2071_, 1);
if (lean_obj_tag(v_val_2073_) == 1)
{
uint8_t v_v_2074_; 
v_v_2074_ = lean_ctor_get_uint8(v_val_2073_, 0);
lean_dec_ref_known(v_val_2073_, 0);
return v_v_2074_;
}
else
{
uint8_t v___x_2075_; 
lean_dec(v_val_2073_);
v___x_2075_ = lean_unbox(v_defValue_2069_);
return v___x_2075_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_2076_, lean_object* v_opt_2077_){
_start:
{
uint8_t v_res_2078_; lean_object* v_r_2079_; 
v_res_2078_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_2076_, v_opt_2077_);
lean_dec_ref(v_opt_2077_);
lean_dec_ref(v_opts_2076_);
v_r_2079_ = lean_box(v_res_2078_);
return v_r_2079_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_2080_, lean_object* v_as_2081_, size_t v_i_2082_, size_t v_stop_2083_){
_start:
{
uint8_t v___x_2084_; 
v___x_2084_ = lean_usize_dec_eq(v_i_2082_, v_stop_2083_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; uint8_t v___x_2086_; 
v___x_2085_ = lean_array_uget_borrowed(v_as_2081_, v_i_2082_);
v___x_2086_ = lean_nat_dec_eq(v_a_2080_, v___x_2085_);
if (v___x_2086_ == 0)
{
size_t v___x_2087_; size_t v___x_2088_; 
v___x_2087_ = ((size_t)1ULL);
v___x_2088_ = lean_usize_add(v_i_2082_, v___x_2087_);
v_i_2082_ = v___x_2088_;
goto _start;
}
else
{
return v___x_2086_;
}
}
else
{
uint8_t v___x_2090_; 
v___x_2090_ = 0;
return v___x_2090_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_2091_, lean_object* v_as_2092_, lean_object* v_i_2093_, lean_object* v_stop_2094_){
_start:
{
size_t v_i_boxed_2095_; size_t v_stop_boxed_2096_; uint8_t v_res_2097_; lean_object* v_r_2098_; 
v_i_boxed_2095_ = lean_unbox_usize(v_i_2093_);
lean_dec(v_i_2093_);
v_stop_boxed_2096_ = lean_unbox_usize(v_stop_2094_);
lean_dec(v_stop_2094_);
v_res_2097_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_2091_, v_as_2092_, v_i_boxed_2095_, v_stop_boxed_2096_);
lean_dec_ref(v_as_2092_);
lean_dec(v_a_2091_);
v_r_2098_ = lean_box(v_res_2097_);
return v_r_2098_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_2099_, lean_object* v_a_2100_){
_start:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; uint8_t v___x_2103_; 
v___x_2101_ = lean_unsigned_to_nat(0u);
v___x_2102_ = lean_array_get_size(v_as_2099_);
v___x_2103_ = lean_nat_dec_lt(v___x_2101_, v___x_2102_);
if (v___x_2103_ == 0)
{
return v___x_2103_;
}
else
{
if (v___x_2103_ == 0)
{
return v___x_2103_;
}
else
{
size_t v___x_2104_; size_t v___x_2105_; uint8_t v___x_2106_; 
v___x_2104_ = ((size_t)0ULL);
v___x_2105_ = lean_usize_of_nat(v___x_2102_);
v___x_2106_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_2100_, v_as_2099_, v___x_2104_, v___x_2105_);
return v___x_2106_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_2107_, lean_object* v_a_2108_){
_start:
{
uint8_t v_res_2109_; lean_object* v_r_2110_; 
v_res_2109_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_2107_, v_a_2108_);
lean_dec(v_a_2108_);
lean_dec_ref(v_as_2107_);
v_r_2110_ = lean_box(v_res_2109_);
return v_r_2110_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_2111_, lean_object* v_fst_2112_, lean_object* v_argVars_2113_, lean_object* v_as_2114_, size_t v_sz_2115_, size_t v_i_2116_, lean_object* v_b_2117_, lean_object* v___y_2118_, lean_object* v___y_2119_, lean_object* v___y_2120_, lean_object* v___y_2121_){
_start:
{
lean_object* v_a_2124_; uint8_t v___x_2128_; 
v___x_2128_ = lean_usize_dec_lt(v_i_2116_, v_sz_2115_);
if (v___x_2128_ == 0)
{
lean_object* v___x_2129_; 
v___x_2129_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2129_, 0, v_b_2117_);
return v___x_2129_;
}
else
{
lean_object* v_next_2130_; 
v_next_2130_ = lean_ctor_get(v_b_2117_, 0);
lean_inc(v_next_2130_);
if (lean_obj_tag(v_next_2130_) == 0)
{
lean_object* v___x_2131_; 
v___x_2131_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2131_, 0, v_b_2117_);
return v___x_2131_;
}
else
{
lean_object* v_upperBound_2132_; lean_object* v_val_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2164_; 
v_upperBound_2132_ = lean_ctor_get(v_b_2117_, 1);
v_val_2133_ = lean_ctor_get(v_next_2130_, 0);
v_isSharedCheck_2164_ = !lean_is_exclusive(v_next_2130_);
if (v_isSharedCheck_2164_ == 0)
{
v___x_2135_ = v_next_2130_;
v_isShared_2136_ = v_isSharedCheck_2164_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_val_2133_);
lean_dec(v_next_2130_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2164_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
uint8_t v___x_2137_; 
v___x_2137_ = lean_nat_dec_lt(v_val_2133_, v_upperBound_2132_);
if (v___x_2137_ == 0)
{
lean_object* v___x_2138_; 
lean_del_object(v___x_2135_);
lean_dec(v_val_2133_);
v___x_2138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2138_, 0, v_b_2117_);
return v___x_2138_;
}
else
{
lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2161_; 
lean_inc(v_upperBound_2132_);
v_isSharedCheck_2161_ = !lean_is_exclusive(v_b_2117_);
if (v_isSharedCheck_2161_ == 0)
{
lean_object* v_unused_2162_; lean_object* v_unused_2163_; 
v_unused_2162_ = lean_ctor_get(v_b_2117_, 1);
lean_dec(v_unused_2162_);
v_unused_2163_ = lean_ctor_get(v_b_2117_, 0);
lean_dec(v_unused_2163_);
v___x_2140_ = v_b_2117_;
v_isShared_2141_ = v_isSharedCheck_2161_;
goto v_resetjp_2139_;
}
else
{
lean_dec(v_b_2117_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2161_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2142_; lean_object* v___x_2143_; lean_object* v___x_2145_; 
v___x_2142_ = lean_unsigned_to_nat(1u);
v___x_2143_ = lean_nat_add(v_val_2133_, v___x_2142_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 0, v___x_2143_);
v___x_2145_ = v___x_2135_;
goto v_reusejp_2144_;
}
else
{
lean_object* v_reuseFailAlloc_2160_; 
v_reuseFailAlloc_2160_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2160_, 0, v___x_2143_);
v___x_2145_ = v_reuseFailAlloc_2160_;
goto v_reusejp_2144_;
}
v_reusejp_2144_:
{
lean_object* v___x_2147_; 
if (v_isShared_2141_ == 0)
{
lean_ctor_set(v___x_2140_, 0, v___x_2145_);
v___x_2147_ = v___x_2140_;
goto v_reusejp_2146_;
}
else
{
lean_object* v_reuseFailAlloc_2159_; 
v_reuseFailAlloc_2159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2159_, 0, v___x_2145_);
lean_ctor_set(v_reuseFailAlloc_2159_, 1, v_upperBound_2132_);
v___x_2147_ = v_reuseFailAlloc_2159_;
goto v_reusejp_2146_;
}
v_reusejp_2146_:
{
uint8_t v___x_2148_; 
v___x_2148_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2111_, v_val_2133_);
lean_dec(v_val_2133_);
if (v___x_2148_ == 0)
{
lean_object* v_a_2149_; lean_object* v___x_2150_; 
v_a_2149_ = lean_array_uget_borrowed(v_as_2114_, v_i_2116_);
lean_inc(v_a_2149_);
v___x_2150_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2112_, v_argVars_2113_, v_a_2149_, v___y_2118_, v___y_2119_, v___y_2120_, v___y_2121_);
if (lean_obj_tag(v___x_2150_) == 0)
{
lean_dec_ref_known(v___x_2150_, 1);
v_a_2124_ = v___x_2147_;
goto v___jp_2123_;
}
else
{
lean_object* v_a_2151_; lean_object* v___x_2153_; uint8_t v_isShared_2154_; uint8_t v_isSharedCheck_2158_; 
lean_dec_ref(v___x_2147_);
v_a_2151_ = lean_ctor_get(v___x_2150_, 0);
v_isSharedCheck_2158_ = !lean_is_exclusive(v___x_2150_);
if (v_isSharedCheck_2158_ == 0)
{
v___x_2153_ = v___x_2150_;
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
else
{
lean_inc(v_a_2151_);
lean_dec(v___x_2150_);
v___x_2153_ = lean_box(0);
v_isShared_2154_ = v_isSharedCheck_2158_;
goto v_resetjp_2152_;
}
v_resetjp_2152_:
{
lean_object* v___x_2156_; 
if (v_isShared_2154_ == 0)
{
v___x_2156_ = v___x_2153_;
goto v_reusejp_2155_;
}
else
{
lean_object* v_reuseFailAlloc_2157_; 
v_reuseFailAlloc_2157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2157_, 0, v_a_2151_);
v___x_2156_ = v_reuseFailAlloc_2157_;
goto v_reusejp_2155_;
}
v_reusejp_2155_:
{
return v___x_2156_;
}
}
}
}
else
{
v_a_2124_ = v___x_2147_;
goto v___jp_2123_;
}
}
}
}
}
}
}
}
v___jp_2123_:
{
size_t v___x_2125_; size_t v___x_2126_; 
v___x_2125_ = ((size_t)1ULL);
v___x_2126_ = lean_usize_add(v_i_2116_, v___x_2125_);
v_i_2116_ = v___x_2126_;
v_b_2117_ = v_a_2124_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2165_, lean_object* v_fst_2166_, lean_object* v_argVars_2167_, lean_object* v_as_2168_, lean_object* v_sz_2169_, lean_object* v_i_2170_, lean_object* v_b_2171_, lean_object* v___y_2172_, lean_object* v___y_2173_, lean_object* v___y_2174_, lean_object* v___y_2175_, lean_object* v___y_2176_){
_start:
{
size_t v_sz_boxed_2177_; size_t v_i_boxed_2178_; lean_object* v_res_2179_; 
v_sz_boxed_2177_ = lean_unbox_usize(v_sz_2169_);
lean_dec(v_sz_2169_);
v_i_boxed_2178_ = lean_unbox_usize(v_i_2170_);
lean_dec(v_i_2170_);
v_res_2179_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2165_, v_fst_2166_, v_argVars_2167_, v_as_2168_, v_sz_boxed_2177_, v_i_boxed_2178_, v_b_2171_, v___y_2172_, v___y_2173_, v___y_2174_, v___y_2175_);
lean_dec(v___y_2175_);
lean_dec_ref(v___y_2174_);
lean_dec(v___y_2173_);
lean_dec_ref(v___y_2172_);
lean_dec_ref(v_as_2168_);
lean_dec_ref(v_argVars_2167_);
lean_dec_ref(v_fst_2166_);
lean_dec_ref(v_a_2165_);
return v_res_2179_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2180_, lean_object* v_a_2181_, lean_object* v___x_2182_, lean_object* v_a_2183_, lean_object* v_b_2184_){
_start:
{
uint8_t v___x_2186_; 
v___x_2186_ = lean_nat_dec_lt(v_a_2183_, v_upperBound_2180_);
if (v___x_2186_ == 0)
{
lean_object* v___x_2187_; 
lean_dec(v_a_2183_);
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v_b_2184_);
return v___x_2187_;
}
else
{
lean_object* v_snd_2188_; lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2228_; 
v_snd_2188_ = lean_ctor_get(v_b_2184_, 1);
v_isSharedCheck_2228_ = !lean_is_exclusive(v_b_2184_);
if (v_isSharedCheck_2228_ == 0)
{
lean_object* v_unused_2229_; 
v_unused_2229_ = lean_ctor_get(v_b_2184_, 0);
lean_dec(v_unused_2229_);
v___x_2190_ = v_b_2184_;
v_isShared_2191_ = v_isSharedCheck_2228_;
goto v_resetjp_2189_;
}
else
{
lean_inc(v_snd_2188_);
lean_dec(v_b_2184_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2228_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v_array_2192_; lean_object* v_start_2193_; lean_object* v_stop_2194_; lean_object* v___x_2195_; uint8_t v___x_2196_; 
v_array_2192_ = lean_ctor_get(v_snd_2188_, 0);
v_start_2193_ = lean_ctor_get(v_snd_2188_, 1);
v_stop_2194_ = lean_ctor_get(v_snd_2188_, 2);
v___x_2195_ = lean_box(0);
v___x_2196_ = lean_nat_dec_lt(v_start_2193_, v_stop_2194_);
if (v___x_2196_ == 0)
{
lean_object* v___x_2198_; 
lean_dec(v_a_2183_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 0, v___x_2195_);
v___x_2198_ = v___x_2190_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2200_; 
v_reuseFailAlloc_2200_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2200_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2200_, 1, v_snd_2188_);
v___x_2198_ = v_reuseFailAlloc_2200_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
lean_object* v___x_2199_; 
v___x_2199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2199_, 0, v___x_2198_);
return v___x_2199_;
}
}
else
{
lean_object* v___x_2202_; uint8_t v_isShared_2203_; uint8_t v_isSharedCheck_2224_; 
lean_inc(v_stop_2194_);
lean_inc(v_start_2193_);
lean_inc_ref(v_array_2192_);
v_isSharedCheck_2224_ = !lean_is_exclusive(v_snd_2188_);
if (v_isSharedCheck_2224_ == 0)
{
lean_object* v_unused_2225_; lean_object* v_unused_2226_; lean_object* v_unused_2227_; 
v_unused_2225_ = lean_ctor_get(v_snd_2188_, 2);
lean_dec(v_unused_2225_);
v_unused_2226_ = lean_ctor_get(v_snd_2188_, 1);
lean_dec(v_unused_2226_);
v_unused_2227_ = lean_ctor_get(v_snd_2188_, 0);
lean_dec(v_unused_2227_);
v___x_2202_ = v_snd_2188_;
v_isShared_2203_ = v_isSharedCheck_2224_;
goto v_resetjp_2201_;
}
else
{
lean_dec(v_snd_2188_);
v___x_2202_ = lean_box(0);
v_isShared_2203_ = v_isSharedCheck_2224_;
goto v_resetjp_2201_;
}
v_resetjp_2201_:
{
lean_object* v___x_2204_; lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2208_; 
v___x_2204_ = lean_array_fget(v_array_2192_, v_start_2193_);
v___x_2205_ = lean_unsigned_to_nat(1u);
v___x_2206_ = lean_nat_add(v_start_2193_, v___x_2205_);
lean_dec(v_start_2193_);
if (v_isShared_2203_ == 0)
{
lean_ctor_set(v___x_2202_, 1, v___x_2206_);
v___x_2208_ = v___x_2202_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2223_; 
v_reuseFailAlloc_2223_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2223_, 0, v_array_2192_);
lean_ctor_set(v_reuseFailAlloc_2223_, 1, v___x_2206_);
lean_ctor_set(v_reuseFailAlloc_2223_, 2, v_stop_2194_);
v___x_2208_ = v_reuseFailAlloc_2223_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
uint8_t v___x_2215_; 
v___x_2215_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2181_, v_a_2183_);
if (v___x_2215_ == 0)
{
uint8_t v___x_2216_; 
v___x_2216_ = l_Lean_Expr_hasExprMVar(v___x_2204_);
lean_dec(v___x_2204_);
if (v___x_2216_ == 0)
{
goto v___jp_2209_;
}
else
{
lean_object* v___x_2217_; uint8_t v___x_2218_; lean_object* v___x_2219_; lean_object* v___x_2220_; lean_object* v___x_2221_; lean_object* v___x_2222_; 
lean_del_object(v___x_2190_);
lean_dec(v_a_2183_);
v___x_2217_ = lean_unsigned_to_nat(0u);
v___x_2218_ = lean_nat_dec_eq(v___x_2182_, v___x_2217_);
v___x_2219_ = lean_box(v___x_2218_);
v___x_2220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2220_, 0, v___x_2219_);
v___x_2221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2221_, 0, v___x_2220_);
lean_ctor_set(v___x_2221_, 1, v___x_2208_);
v___x_2222_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2222_, 0, v___x_2221_);
return v___x_2222_;
}
}
else
{
lean_dec(v___x_2204_);
goto v___jp_2209_;
}
v___jp_2209_:
{
lean_object* v___x_2211_; 
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 1, v___x_2208_);
lean_ctor_set(v___x_2190_, 0, v___x_2195_);
v___x_2211_ = v___x_2190_;
goto v_reusejp_2210_;
}
else
{
lean_object* v_reuseFailAlloc_2214_; 
v_reuseFailAlloc_2214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2214_, 0, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2214_, 1, v___x_2208_);
v___x_2211_ = v_reuseFailAlloc_2214_;
goto v_reusejp_2210_;
}
v_reusejp_2210_:
{
lean_object* v___x_2212_; 
v___x_2212_ = lean_nat_add(v_a_2183_, v___x_2205_);
lean_dec(v_a_2183_);
v_a_2183_ = v___x_2212_;
v_b_2184_ = v___x_2211_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2230_, lean_object* v_a_2231_, lean_object* v___x_2232_, lean_object* v_a_2233_, lean_object* v_b_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v_res_2236_; 
v_res_2236_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2230_, v_a_2231_, v___x_2232_, v_a_2233_, v_b_2234_);
lean_dec(v___x_2232_);
lean_dec_ref(v_a_2231_);
lean_dec(v_upperBound_2230_);
return v_res_2236_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2237_; lean_object* v_dummy_2238_; 
v___x_2237_ = lean_box(0);
v_dummy_2238_ = l_Lean_Expr_sort___override(v___x_2237_);
return v_dummy_2238_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2239_, lean_object* v___x_2240_, uint8_t v___x_2241_, lean_object* v_x_2242_, lean_object* v_argTy_2243_, lean_object* v___y_2244_, lean_object* v___y_2245_, lean_object* v___y_2246_, lean_object* v___y_2247_){
_start:
{
lean_object* v___x_2249_; 
lean_inc(v___y_2247_);
lean_inc_ref(v___y_2246_);
lean_inc(v___y_2245_);
lean_inc_ref(v___y_2244_);
v___x_2249_ = lean_whnf(v_argTy_2243_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2249_) == 0)
{
lean_object* v_a_2250_; lean_object* v___x_2251_; 
v_a_2250_ = lean_ctor_get(v___x_2249_, 0);
lean_inc(v_a_2250_);
lean_dec_ref_known(v___x_2249_, 1);
v___x_2251_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2250_, v___y_2244_, v___y_2245_, v___y_2246_, v___y_2247_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v_dummy_2253_; lean_object* v_nargs_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___x_2260_; lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
lean_inc(v_a_2252_);
lean_dec_ref_known(v___x_2251_, 1);
v_dummy_2253_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2254_ = l_Lean_Expr_getAppNumArgs(v_a_2250_);
lean_inc(v_nargs_2254_);
v___x_2255_ = lean_mk_array(v_nargs_2254_, v_dummy_2253_);
v___x_2256_ = lean_unsigned_to_nat(1u);
v___x_2257_ = lean_nat_sub(v_nargs_2254_, v___x_2256_);
lean_dec(v_nargs_2254_);
v___x_2258_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2250_, v___x_2255_, v___x_2257_);
v___x_2259_ = lean_array_get_size(v___x_2258_);
lean_inc(v___x_2239_);
v___x_2260_ = l_Array_toSubarray___redArg(v___x_2258_, v___x_2239_, v___x_2259_);
v___x_2261_ = lean_box(0);
v___x_2262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2262_, 0, v___x_2261_);
lean_ctor_set(v___x_2262_, 1, v___x_2260_);
v___x_2263_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2259_, v_a_2252_, v___x_2240_, v___x_2239_, v___x_2262_);
lean_dec(v_a_2252_);
if (lean_obj_tag(v___x_2263_) == 0)
{
lean_object* v_a_2264_; lean_object* v___x_2266_; uint8_t v_isShared_2267_; uint8_t v_isSharedCheck_2277_; 
v_a_2264_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2277_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2277_ == 0)
{
v___x_2266_ = v___x_2263_;
v_isShared_2267_ = v_isSharedCheck_2277_;
goto v_resetjp_2265_;
}
else
{
lean_inc(v_a_2264_);
lean_dec(v___x_2263_);
v___x_2266_ = lean_box(0);
v_isShared_2267_ = v_isSharedCheck_2277_;
goto v_resetjp_2265_;
}
v_resetjp_2265_:
{
lean_object* v_fst_2268_; 
v_fst_2268_ = lean_ctor_get(v_a_2264_, 0);
lean_inc(v_fst_2268_);
lean_dec(v_a_2264_);
if (lean_obj_tag(v_fst_2268_) == 0)
{
lean_object* v___x_2269_; lean_object* v___x_2271_; 
v___x_2269_ = lean_box(v___x_2241_);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v___x_2269_);
v___x_2271_ = v___x_2266_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(0, 1, 0);
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
lean_object* v_val_2273_; lean_object* v___x_2275_; 
v_val_2273_ = lean_ctor_get(v_fst_2268_, 0);
lean_inc(v_val_2273_);
lean_dec_ref_known(v_fst_2268_, 1);
if (v_isShared_2267_ == 0)
{
lean_ctor_set(v___x_2266_, 0, v_val_2273_);
v___x_2275_ = v___x_2266_;
goto v_reusejp_2274_;
}
else
{
lean_object* v_reuseFailAlloc_2276_; 
v_reuseFailAlloc_2276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2276_, 0, v_val_2273_);
v___x_2275_ = v_reuseFailAlloc_2276_;
goto v_reusejp_2274_;
}
v_reusejp_2274_:
{
return v___x_2275_;
}
}
}
}
else
{
lean_object* v_a_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2285_; 
v_a_2278_ = lean_ctor_get(v___x_2263_, 0);
v_isSharedCheck_2285_ = !lean_is_exclusive(v___x_2263_);
if (v_isSharedCheck_2285_ == 0)
{
v___x_2280_ = v___x_2263_;
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_a_2278_);
lean_dec(v___x_2263_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2285_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2281_ == 0)
{
v___x_2283_ = v___x_2280_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2284_; 
v_reuseFailAlloc_2284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2284_, 0, v_a_2278_);
v___x_2283_ = v_reuseFailAlloc_2284_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
return v___x_2283_;
}
}
}
}
else
{
lean_object* v_a_2286_; lean_object* v___x_2288_; uint8_t v_isShared_2289_; uint8_t v_isSharedCheck_2293_; 
lean_dec(v_a_2250_);
lean_dec(v___x_2239_);
v_a_2286_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2293_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2293_ == 0)
{
v___x_2288_ = v___x_2251_;
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
else
{
lean_inc(v_a_2286_);
lean_dec(v___x_2251_);
v___x_2288_ = lean_box(0);
v_isShared_2289_ = v_isSharedCheck_2293_;
goto v_resetjp_2287_;
}
v_resetjp_2287_:
{
lean_object* v___x_2291_; 
if (v_isShared_2289_ == 0)
{
v___x_2291_ = v___x_2288_;
goto v_reusejp_2290_;
}
else
{
lean_object* v_reuseFailAlloc_2292_; 
v_reuseFailAlloc_2292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2292_, 0, v_a_2286_);
v___x_2291_ = v_reuseFailAlloc_2292_;
goto v_reusejp_2290_;
}
v_reusejp_2290_:
{
return v___x_2291_;
}
}
}
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2301_; 
lean_dec(v___x_2239_);
v_a_2294_ = lean_ctor_get(v___x_2249_, 0);
v_isSharedCheck_2301_ = !lean_is_exclusive(v___x_2249_);
if (v_isSharedCheck_2301_ == 0)
{
v___x_2296_ = v___x_2249_;
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_a_2294_);
lean_dec(v___x_2249_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2301_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2299_; 
if (v_isShared_2297_ == 0)
{
v___x_2299_ = v___x_2296_;
goto v_reusejp_2298_;
}
else
{
lean_object* v_reuseFailAlloc_2300_; 
v_reuseFailAlloc_2300_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2300_, 0, v_a_2294_);
v___x_2299_ = v_reuseFailAlloc_2300_;
goto v_reusejp_2298_;
}
v_reusejp_2298_:
{
return v___x_2299_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2302_, lean_object* v___x_2303_, lean_object* v___x_2304_, lean_object* v_x_2305_, lean_object* v_argTy_2306_, lean_object* v___y_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
uint8_t v___x_22646__boxed_2312_; lean_object* v_res_2313_; 
v___x_22646__boxed_2312_ = lean_unbox(v___x_2304_);
v_res_2313_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2302_, v___x_2303_, v___x_22646__boxed_2312_, v_x_2305_, v_argTy_2306_, v___y_2307_, v___y_2308_, v___y_2309_, v___y_2310_);
lean_dec(v___y_2310_);
lean_dec_ref(v___y_2309_);
lean_dec(v___y_2308_);
lean_dec_ref(v___y_2307_);
lean_dec_ref(v_x_2305_);
lean_dec(v___x_2303_);
return v_res_2313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2317_, lean_object* v_projInfo_x3f_2318_, lean_object* v___x_2319_, lean_object* v_argVars_2320_, lean_object* v_as_2321_, size_t v_sz_2322_, size_t v_i_2323_, lean_object* v_b_2324_, lean_object* v___y_2325_, lean_object* v___y_2326_, lean_object* v___y_2327_, lean_object* v___y_2328_){
_start:
{
uint8_t v___x_2330_; 
v___x_2330_ = lean_usize_dec_lt(v_i_2323_, v_sz_2322_);
if (v___x_2330_ == 0)
{
lean_object* v___x_2331_; 
lean_dec(v___x_2319_);
v___x_2331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2331_, 0, v_b_2324_);
return v___x_2331_;
}
else
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___f_2337_; uint8_t v___x_2338_; lean_object* v_a_2339_; lean_object* v___y_2346_; lean_object* v___x_2360_; lean_object* v___x_2361_; 
lean_dec_ref(v_b_2324_);
v___x_2332_ = lean_box(0);
v___x_2333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2334_ = l_Lean_instInhabitedExpr;
v___x_2335_ = lean_unsigned_to_nat(0u);
v___x_2336_ = lean_box(v___x_2330_);
lean_inc(v___x_2319_);
v___f_2337_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2337_, 0, v___x_2335_);
lean_closure_set(v___f_2337_, 1, v___x_2319_);
lean_closure_set(v___f_2337_, 2, v___x_2336_);
v___x_2338_ = lean_nat_dec_eq(v___x_2319_, v___x_2335_);
v_a_2339_ = lean_array_uget_borrowed(v_as_2321_, v_i_2323_);
v___x_2360_ = lean_array_get_borrowed(v___x_2334_, v_fst_2317_, v_a_2339_);
lean_inc(v___y_2328_);
lean_inc_ref(v___y_2327_);
lean_inc(v___y_2326_);
lean_inc_ref(v___y_2325_);
lean_inc(v___x_2360_);
v___x_2361_ = lean_infer_type(v___x_2360_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
if (lean_obj_tag(v___x_2361_) == 0)
{
lean_object* v_a_2362_; lean_object* v___x_2363_; 
v_a_2362_ = lean_ctor_get(v___x_2361_, 0);
lean_inc(v_a_2362_);
lean_dec_ref_known(v___x_2361_, 1);
v___x_2363_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2362_, v___y_2326_);
if (lean_obj_tag(v___x_2363_) == 0)
{
if (lean_obj_tag(v_projInfo_x3f_2318_) == 1)
{
lean_object* v_val_2364_; lean_object* v_a_2365_; lean_object* v_numParams_2366_; uint8_t v___x_2367_; 
v_val_2364_ = lean_ctor_get(v_projInfo_x3f_2318_, 0);
v_a_2365_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2365_);
lean_dec_ref_known(v___x_2363_, 1);
v_numParams_2366_ = lean_ctor_get(v_val_2364_, 1);
v___x_2367_ = lean_nat_dec_eq(v_numParams_2366_, v_a_2339_);
if (v___x_2367_ == 0)
{
lean_object* v___x_2368_; 
v___x_2368_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2365_, v___f_2337_, v___x_2338_, v___x_2338_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
v___y_2346_ = v___x_2368_;
goto v___jp_2345_;
}
else
{
lean_object* v___x_2369_; 
lean_dec_ref(v___f_2337_);
lean_dec(v___x_2319_);
v___x_2369_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2317_, v_argVars_2320_, v_a_2365_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
if (lean_obj_tag(v___x_2369_) == 0)
{
lean_dec_ref_known(v___x_2369_, 1);
goto v___jp_2340_;
}
else
{
lean_object* v_a_2370_; lean_object* v___x_2372_; uint8_t v_isShared_2373_; uint8_t v_isSharedCheck_2377_; 
v_a_2370_ = lean_ctor_get(v___x_2369_, 0);
v_isSharedCheck_2377_ = !lean_is_exclusive(v___x_2369_);
if (v_isSharedCheck_2377_ == 0)
{
v___x_2372_ = v___x_2369_;
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
else
{
lean_inc(v_a_2370_);
lean_dec(v___x_2369_);
v___x_2372_ = lean_box(0);
v_isShared_2373_ = v_isSharedCheck_2377_;
goto v_resetjp_2371_;
}
v_resetjp_2371_:
{
lean_object* v___x_2375_; 
if (v_isShared_2373_ == 0)
{
v___x_2375_ = v___x_2372_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v_a_2370_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
else
{
lean_object* v_a_2378_; lean_object* v___x_2379_; 
v_a_2378_ = lean_ctor_get(v___x_2363_, 0);
lean_inc(v_a_2378_);
lean_dec_ref_known(v___x_2363_, 1);
v___x_2379_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2378_, v___f_2337_, v___x_2338_, v___x_2338_, v___y_2325_, v___y_2326_, v___y_2327_, v___y_2328_);
v___y_2346_ = v___x_2379_;
goto v___jp_2345_;
}
}
else
{
lean_object* v_a_2380_; lean_object* v___x_2382_; uint8_t v_isShared_2383_; uint8_t v_isSharedCheck_2387_; 
lean_dec_ref(v___f_2337_);
lean_dec(v___x_2319_);
v_a_2380_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2387_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2387_ == 0)
{
v___x_2382_ = v___x_2363_;
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
else
{
lean_inc(v_a_2380_);
lean_dec(v___x_2363_);
v___x_2382_ = lean_box(0);
v_isShared_2383_ = v_isSharedCheck_2387_;
goto v_resetjp_2381_;
}
v_resetjp_2381_:
{
lean_object* v___x_2385_; 
if (v_isShared_2383_ == 0)
{
v___x_2385_ = v___x_2382_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2386_; 
v_reuseFailAlloc_2386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2386_, 0, v_a_2380_);
v___x_2385_ = v_reuseFailAlloc_2386_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
return v___x_2385_;
}
}
}
}
else
{
lean_object* v_a_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2395_; 
lean_dec_ref(v___f_2337_);
lean_dec(v___x_2319_);
v_a_2388_ = lean_ctor_get(v___x_2361_, 0);
v_isSharedCheck_2395_ = !lean_is_exclusive(v___x_2361_);
if (v_isSharedCheck_2395_ == 0)
{
v___x_2390_ = v___x_2361_;
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_a_2388_);
lean_dec(v___x_2361_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2395_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2391_ == 0)
{
v___x_2393_ = v___x_2390_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2394_; 
v_reuseFailAlloc_2394_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2394_, 0, v_a_2388_);
v___x_2393_ = v_reuseFailAlloc_2394_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
return v___x_2393_;
}
}
}
v___jp_2340_:
{
lean_object* v___x_2341_; lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; 
lean_inc(v_a_2339_);
v___x_2341_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2341_, 0, v_a_2339_);
v___x_2342_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2342_, 0, v___x_2341_);
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v___x_2332_);
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v___x_2343_);
return v___x_2344_;
}
v___jp_2345_:
{
if (lean_obj_tag(v___y_2346_) == 0)
{
lean_object* v_a_2347_; uint8_t v___x_2348_; 
v_a_2347_ = lean_ctor_get(v___y_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___y_2346_, 1);
v___x_2348_ = lean_unbox(v_a_2347_);
lean_dec(v_a_2347_);
if (v___x_2348_ == 0)
{
size_t v___x_2349_; size_t v___x_2350_; 
v___x_2349_ = ((size_t)1ULL);
v___x_2350_ = lean_usize_add(v_i_2323_, v___x_2349_);
v_i_2323_ = v___x_2350_;
v_b_2324_ = v___x_2333_;
goto _start;
}
else
{
lean_dec(v___x_2319_);
goto v___jp_2340_;
}
}
else
{
lean_object* v_a_2352_; lean_object* v___x_2354_; uint8_t v_isShared_2355_; uint8_t v_isSharedCheck_2359_; 
lean_dec(v___x_2319_);
v_a_2352_ = lean_ctor_get(v___y_2346_, 0);
v_isSharedCheck_2359_ = !lean_is_exclusive(v___y_2346_);
if (v_isSharedCheck_2359_ == 0)
{
v___x_2354_ = v___y_2346_;
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
else
{
lean_inc(v_a_2352_);
lean_dec(v___y_2346_);
v___x_2354_ = lean_box(0);
v_isShared_2355_ = v_isSharedCheck_2359_;
goto v_resetjp_2353_;
}
v_resetjp_2353_:
{
lean_object* v___x_2357_; 
if (v_isShared_2355_ == 0)
{
v___x_2357_ = v___x_2354_;
goto v_reusejp_2356_;
}
else
{
lean_object* v_reuseFailAlloc_2358_; 
v_reuseFailAlloc_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2358_, 0, v_a_2352_);
v___x_2357_ = v_reuseFailAlloc_2358_;
goto v_reusejp_2356_;
}
v_reusejp_2356_:
{
return v___x_2357_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2396_, lean_object* v_projInfo_x3f_2397_, lean_object* v___x_2398_, lean_object* v_argVars_2399_, lean_object* v_as_2400_, lean_object* v_sz_2401_, lean_object* v_i_2402_, lean_object* v_b_2403_, lean_object* v___y_2404_, lean_object* v___y_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_){
_start:
{
size_t v_sz_boxed_2409_; size_t v_i_boxed_2410_; lean_object* v_res_2411_; 
v_sz_boxed_2409_ = lean_unbox_usize(v_sz_2401_);
lean_dec(v_sz_2401_);
v_i_boxed_2410_ = lean_unbox_usize(v_i_2402_);
lean_dec(v_i_2402_);
v_res_2411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2396_, v_projInfo_x3f_2397_, v___x_2398_, v_argVars_2399_, v_as_2400_, v_sz_boxed_2409_, v_i_boxed_2410_, v_b_2403_, v___y_2404_, v___y_2405_, v___y_2406_, v___y_2407_);
lean_dec(v___y_2407_);
lean_dec_ref(v___y_2406_);
lean_dec(v___y_2405_);
lean_dec_ref(v___y_2404_);
lean_dec_ref(v_as_2400_);
lean_dec_ref(v_argVars_2399_);
lean_dec(v_projInfo_x3f_2397_);
lean_dec_ref(v_fst_2396_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2412_, lean_object* v_as_2413_, size_t v_i_2414_, size_t v_stop_2415_, lean_object* v_b_2416_){
_start:
{
lean_object* v___y_2418_; uint8_t v___x_2422_; 
v___x_2422_ = lean_usize_dec_eq(v_i_2414_, v_stop_2415_);
if (v___x_2422_ == 0)
{
lean_object* v___x_2423_; uint8_t v___x_2424_; 
v___x_2423_ = lean_array_uget_borrowed(v_as_2413_, v_i_2414_);
v___x_2424_ = lean_nat_dec_eq(v___x_2423_, v_next_2412_);
if (v___x_2424_ == 0)
{
lean_object* v___x_2425_; 
lean_inc(v___x_2423_);
v___x_2425_ = lean_array_push(v_b_2416_, v___x_2423_);
v___y_2418_ = v___x_2425_;
goto v___jp_2417_;
}
else
{
v___y_2418_ = v_b_2416_;
goto v___jp_2417_;
}
}
else
{
return v_b_2416_;
}
v___jp_2417_:
{
size_t v___x_2419_; size_t v___x_2420_; 
v___x_2419_ = ((size_t)1ULL);
v___x_2420_ = lean_usize_add(v_i_2414_, v___x_2419_);
v_i_2414_ = v___x_2420_;
v_b_2416_ = v___y_2418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2426_, lean_object* v_as_2427_, lean_object* v_i_2428_, lean_object* v_stop_2429_, lean_object* v_b_2430_){
_start:
{
size_t v_i_boxed_2431_; size_t v_stop_boxed_2432_; lean_object* v_res_2433_; 
v_i_boxed_2431_ = lean_unbox_usize(v_i_2428_);
lean_dec(v_i_2428_);
v_stop_boxed_2432_ = lean_unbox_usize(v_stop_2429_);
lean_dec(v_stop_2429_);
v_res_2433_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2426_, v_as_2427_, v_i_boxed_2431_, v_stop_boxed_2432_, v_b_2430_);
lean_dec_ref(v_as_2427_);
lean_dec(v_next_2426_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object* v_fst_2434_, lean_object* v___x_2435_, lean_object* v_fst_2436_, lean_object* v_argVars_2437_, lean_object* v_snd_2438_, lean_object* v_next_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_){
_start:
{
lean_object* v___x_2445_; lean_object* v___y_2447_; lean_object* v___x_2487_; lean_object* v___x_2488_; lean_object* v___x_2489_; uint8_t v___x_2490_; 
lean_inc(v_next_2439_);
v___x_2445_ = lean_array_push(v_fst_2434_, v_next_2439_);
v___x_2487_ = lean_unsigned_to_nat(0u);
v___x_2488_ = lean_array_get_size(v_snd_2438_);
v___x_2489_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2490_ = lean_nat_dec_lt(v___x_2487_, v___x_2488_);
if (v___x_2490_ == 0)
{
v___y_2447_ = v___x_2489_;
goto v___jp_2446_;
}
else
{
uint8_t v___x_2491_; 
v___x_2491_ = lean_nat_dec_le(v___x_2488_, v___x_2488_);
if (v___x_2491_ == 0)
{
if (v___x_2490_ == 0)
{
v___y_2447_ = v___x_2489_;
goto v___jp_2446_;
}
else
{
size_t v___x_2492_; size_t v___x_2493_; lean_object* v___x_2494_; 
v___x_2492_ = ((size_t)0ULL);
v___x_2493_ = lean_usize_of_nat(v___x_2488_);
v___x_2494_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2439_, v_snd_2438_, v___x_2492_, v___x_2493_, v___x_2489_);
v___y_2447_ = v___x_2494_;
goto v___jp_2446_;
}
}
else
{
size_t v___x_2495_; size_t v___x_2496_; lean_object* v___x_2497_; 
v___x_2495_ = ((size_t)0ULL);
v___x_2496_ = lean_usize_of_nat(v___x_2488_);
v___x_2497_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2439_, v_snd_2438_, v___x_2495_, v___x_2496_, v___x_2489_);
v___y_2447_ = v___x_2497_;
goto v___jp_2446_;
}
}
v___jp_2446_:
{
lean_object* v___x_2448_; lean_object* v___x_2449_; 
v___x_2448_ = lean_array_get_borrowed(v___x_2435_, v_fst_2436_, v_next_2439_);
lean_dec(v_next_2439_);
lean_inc(v___y_2443_);
lean_inc_ref(v___y_2442_);
lean_inc(v___y_2441_);
lean_inc_ref(v___y_2440_);
lean_inc(v___x_2448_);
v___x_2449_ = lean_infer_type(v___x_2448_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2449_) == 0)
{
lean_object* v_a_2450_; lean_object* v___x_2451_; 
v_a_2450_ = lean_ctor_get(v___x_2449_, 0);
lean_inc(v_a_2450_);
lean_dec_ref_known(v___x_2449_, 1);
v___x_2451_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2436_, v_argVars_2437_, v_a_2450_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2451_) == 0)
{
lean_object* v___x_2452_; 
lean_dec_ref_known(v___x_2451_, 1);
lean_inc(v___x_2448_);
v___x_2452_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2436_, v_argVars_2437_, v___x_2448_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
if (lean_obj_tag(v___x_2452_) == 0)
{
lean_object* v___x_2454_; uint8_t v_isShared_2455_; uint8_t v_isSharedCheck_2461_; 
v_isSharedCheck_2461_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2461_ == 0)
{
lean_object* v_unused_2462_; 
v_unused_2462_ = lean_ctor_get(v___x_2452_, 0);
lean_dec(v_unused_2462_);
v___x_2454_ = v___x_2452_;
v_isShared_2455_ = v_isSharedCheck_2461_;
goto v_resetjp_2453_;
}
else
{
lean_dec(v___x_2452_);
v___x_2454_ = lean_box(0);
v_isShared_2455_ = v_isSharedCheck_2461_;
goto v_resetjp_2453_;
}
v_resetjp_2453_:
{
lean_object* v___x_2456_; lean_object* v___x_2457_; lean_object* v___x_2459_; 
v___x_2456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2456_, 0, v___x_2445_);
lean_ctor_set(v___x_2456_, 1, v___y_2447_);
v___x_2457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2457_, 0, v___x_2456_);
if (v_isShared_2455_ == 0)
{
lean_ctor_set(v___x_2454_, 0, v___x_2457_);
v___x_2459_ = v___x_2454_;
goto v_reusejp_2458_;
}
else
{
lean_object* v_reuseFailAlloc_2460_; 
v_reuseFailAlloc_2460_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2460_, 0, v___x_2457_);
v___x_2459_ = v_reuseFailAlloc_2460_;
goto v_reusejp_2458_;
}
v_reusejp_2458_:
{
return v___x_2459_;
}
}
}
else
{
lean_object* v_a_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2470_; 
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___x_2445_);
v_a_2463_ = lean_ctor_get(v___x_2452_, 0);
v_isSharedCheck_2470_ = !lean_is_exclusive(v___x_2452_);
if (v_isSharedCheck_2470_ == 0)
{
v___x_2465_ = v___x_2452_;
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_a_2463_);
lean_dec(v___x_2452_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2470_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2468_; 
if (v_isShared_2466_ == 0)
{
v___x_2468_ = v___x_2465_;
goto v_reusejp_2467_;
}
else
{
lean_object* v_reuseFailAlloc_2469_; 
v_reuseFailAlloc_2469_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2469_, 0, v_a_2463_);
v___x_2468_ = v_reuseFailAlloc_2469_;
goto v_reusejp_2467_;
}
v_reusejp_2467_:
{
return v___x_2468_;
}
}
}
}
else
{
lean_object* v_a_2471_; lean_object* v___x_2473_; uint8_t v_isShared_2474_; uint8_t v_isSharedCheck_2478_; 
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___x_2445_);
v_a_2471_ = lean_ctor_get(v___x_2451_, 0);
v_isSharedCheck_2478_ = !lean_is_exclusive(v___x_2451_);
if (v_isSharedCheck_2478_ == 0)
{
v___x_2473_ = v___x_2451_;
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
else
{
lean_inc(v_a_2471_);
lean_dec(v___x_2451_);
v___x_2473_ = lean_box(0);
v_isShared_2474_ = v_isSharedCheck_2478_;
goto v_resetjp_2472_;
}
v_resetjp_2472_:
{
lean_object* v___x_2476_; 
if (v_isShared_2474_ == 0)
{
v___x_2476_ = v___x_2473_;
goto v_reusejp_2475_;
}
else
{
lean_object* v_reuseFailAlloc_2477_; 
v_reuseFailAlloc_2477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2477_, 0, v_a_2471_);
v___x_2476_ = v_reuseFailAlloc_2477_;
goto v_reusejp_2475_;
}
v_reusejp_2475_:
{
return v___x_2476_;
}
}
}
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v___y_2447_);
lean_dec_ref(v___x_2445_);
v_a_2479_ = lean_ctor_get(v___x_2449_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2449_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2449_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2449_);
v___x_2481_ = lean_box(0);
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
v_resetjp_2480_:
{
lean_object* v___x_2484_; 
if (v_isShared_2482_ == 0)
{
v___x_2484_ = v___x_2481_;
goto v_reusejp_2483_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_a_2479_);
v___x_2484_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2483_;
}
v_reusejp_2483_:
{
return v___x_2484_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object* v_fst_2498_, lean_object* v___x_2499_, lean_object* v_fst_2500_, lean_object* v_argVars_2501_, lean_object* v_snd_2502_, lean_object* v_next_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_, lean_object* v___y_2508_){
_start:
{
lean_object* v_res_2509_; 
v_res_2509_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2498_, v___x_2499_, v_fst_2500_, v_argVars_2501_, v_snd_2502_, v_next_2503_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_);
lean_dec(v___y_2507_);
lean_dec_ref(v___y_2506_);
lean_dec(v___y_2505_);
lean_dec_ref(v___y_2504_);
lean_dec(v_snd_2502_);
lean_dec_ref(v_argVars_2501_);
lean_dec_ref(v_fst_2500_);
lean_dec_ref(v___x_2499_);
return v_res_2509_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_, lean_object* v___y_2514_){
_start:
{
lean_object* v___x_2516_; lean_object* v_env_2517_; lean_object* v___x_2518_; lean_object* v_toCold_2519_; lean_object* v_mctx_2520_; lean_object* v_lctx_2521_; lean_object* v_options_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2525_; 
v___x_2516_ = lean_st_ref_get(v___y_2514_);
v_env_2517_ = lean_ctor_get(v___x_2516_, 0);
lean_inc_ref(v_env_2517_);
lean_dec(v___x_2516_);
v___x_2518_ = lean_st_ref_get(v___y_2512_);
v_toCold_2519_ = lean_ctor_get(v___y_2513_, 0);
v_mctx_2520_ = lean_ctor_get(v___x_2518_, 0);
lean_inc_ref(v_mctx_2520_);
lean_dec(v___x_2518_);
v_lctx_2521_ = lean_ctor_get(v___y_2511_, 2);
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
lean_ctor_set(v___x_2524_, 1, v_msgData_2510_);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0(uint8_t v_suppressElabErrors_3338_, uint8_t v___y_3339_, lean_object* v_x_3340_){
_start:
{
if (lean_obj_tag(v_x_3340_) == 1)
{
lean_object* v_pre_3341_; 
v_pre_3341_ = lean_ctor_get(v_x_3340_, 0);
switch(lean_obj_tag(v_pre_3341_))
{
case 1:
{
lean_object* v_pre_3342_; 
v_pre_3342_ = lean_ctor_get(v_pre_3341_, 0);
switch(lean_obj_tag(v_pre_3342_))
{
case 0:
{
lean_object* v_str_3343_; lean_object* v_str_3344_; lean_object* v___x_3345_; uint8_t v___x_3346_; 
v_str_3343_ = lean_ctor_get(v_x_3340_, 1);
v_str_3344_ = lean_ctor_get(v_pre_3341_, 1);
v___x_3345_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__0));
v___x_3346_ = lean_string_dec_eq(v_str_3344_, v___x_3345_);
if (v___x_3346_ == 0)
{
lean_object* v___x_3347_; uint8_t v___x_3348_; 
v___x_3347_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__1));
v___x_3348_ = lean_string_dec_eq(v_str_3344_, v___x_3347_);
if (v___x_3348_ == 0)
{
return v___x_3348_;
}
else
{
lean_object* v___x_3349_; uint8_t v___x_3350_; 
v___x_3349_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__2));
v___x_3350_ = lean_string_dec_eq(v_str_3343_, v___x_3349_);
if (v___x_3350_ == 0)
{
return v___x_3350_;
}
else
{
return v_suppressElabErrors_3338_;
}
}
}
else
{
lean_object* v___x_3351_; uint8_t v___x_3352_; 
v___x_3351_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__3));
v___x_3352_ = lean_string_dec_eq(v_str_3343_, v___x_3351_);
if (v___x_3352_ == 0)
{
return v___x_3352_;
}
else
{
return v_suppressElabErrors_3338_;
}
}
}
case 1:
{
lean_object* v_pre_3353_; 
v_pre_3353_ = lean_ctor_get(v_pre_3342_, 0);
if (lean_obj_tag(v_pre_3353_) == 0)
{
lean_object* v_str_3354_; lean_object* v_str_3355_; lean_object* v_str_3356_; lean_object* v___x_3357_; uint8_t v___x_3358_; 
v_str_3354_ = lean_ctor_get(v_x_3340_, 1);
v_str_3355_ = lean_ctor_get(v_pre_3341_, 1);
v_str_3356_ = lean_ctor_get(v_pre_3342_, 1);
v___x_3357_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__4));
v___x_3358_ = lean_string_dec_eq(v_str_3356_, v___x_3357_);
if (v___x_3358_ == 0)
{
return v___x_3358_;
}
else
{
lean_object* v___x_3359_; uint8_t v___x_3360_; 
v___x_3359_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__5));
v___x_3360_ = lean_string_dec_eq(v_str_3355_, v___x_3359_);
if (v___x_3360_ == 0)
{
return v___x_3360_;
}
else
{
lean_object* v___x_3361_; uint8_t v___x_3362_; 
v___x_3361_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__6));
v___x_3362_ = lean_string_dec_eq(v_str_3354_, v___x_3361_);
if (v___x_3362_ == 0)
{
return v___x_3362_;
}
else
{
return v_suppressElabErrors_3338_;
}
}
}
}
else
{
return v___y_3339_;
}
}
default: 
{
return v___y_3339_;
}
}
}
case 0:
{
lean_object* v_str_3363_; lean_object* v___x_3364_; uint8_t v___x_3365_; 
v_str_3363_ = lean_ctor_get(v_x_3340_, 1);
v___x_3364_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3365_ = lean_string_dec_eq(v_str_3363_, v___x_3364_);
if (v___x_3365_ == 0)
{
return v___x_3365_;
}
else
{
return v_suppressElabErrors_3338_;
}
}
default: 
{
return v___y_3339_;
}
}
}
else
{
return v___y_3339_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___boxed(lean_object* v_suppressElabErrors_3366_, lean_object* v___y_3367_, lean_object* v_x_3368_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3369_; uint8_t v___y_10347__boxed_3370_; uint8_t v_res_3371_; lean_object* v_r_3372_; 
v_suppressElabErrors_boxed_3369_ = lean_unbox(v_suppressElabErrors_3366_);
v___y_10347__boxed_3370_ = lean_unbox(v___y_3367_);
v_res_3371_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0(v_suppressElabErrors_boxed_3369_, v___y_10347__boxed_3370_, v_x_3368_);
lean_dec(v_x_3368_);
v_r_3372_ = lean_box(v_res_3371_);
return v_r_3372_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4(lean_object* v_ref_3373_, lean_object* v_msgData_3374_, uint8_t v_severity_3375_, uint8_t v_isSilent_3376_, lean_object* v___y_3377_, lean_object* v___y_3378_, lean_object* v___y_3379_, lean_object* v___y_3380_){
_start:
{
uint8_t v___y_3383_; lean_object* v___y_3384_; lean_object* v___y_3385_; uint8_t v___y_3386_; lean_object* v___y_3387_; lean_object* v___y_3388_; lean_object* v___y_3389_; lean_object* v_toCold_3390_; lean_object* v___y_3391_; lean_object* v___y_3420_; lean_object* v___y_3421_; uint8_t v___y_3422_; uint8_t v___y_3423_; uint8_t v___y_3424_; lean_object* v___y_3425_; lean_object* v___y_3426_; lean_object* v___y_3427_; uint8_t v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3449_; uint8_t v___y_3450_; uint8_t v___y_3451_; lean_object* v___y_3452_; lean_object* v___y_3453_; uint8_t v___y_3457_; uint8_t v___y_3458_; uint8_t v___y_3459_; uint8_t v___x_3470_; uint8_t v___y_3472_; uint8_t v___y_3473_; uint8_t v___y_3474_; uint8_t v___y_3476_; uint8_t v___x_3484_; 
v___x_3470_ = 2;
v___x_3484_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3375_, v___x_3470_);
if (v___x_3484_ == 0)
{
v___y_3476_ = v___x_3484_;
goto v___jp_3475_;
}
else
{
uint8_t v___x_3485_; 
lean_inc_ref(v_msgData_3374_);
v___x_3485_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3374_);
v___y_3476_ = v___x_3485_;
goto v___jp_3475_;
}
v___jp_3382_:
{
lean_object* v_currNamespace_3392_; lean_object* v_openDecls_3393_; lean_object* v___x_3394_; lean_object* v___x_3395_; lean_object* v___x_3396_; lean_object* v___x_3397_; lean_object* v_env_3398_; lean_object* v_nextMacroScope_3399_; lean_object* v_ngen_3400_; lean_object* v_auxDeclNGen_3401_; lean_object* v_traceState_3402_; lean_object* v_cache_3403_; lean_object* v_recordedDeps_3404_; lean_object* v_messages_3405_; lean_object* v_infoState_3406_; lean_object* v_snapshotTasks_3407_; lean_object* v___x_3409_; uint8_t v_isShared_3410_; uint8_t v_isSharedCheck_3418_; 
v_currNamespace_3392_ = lean_ctor_get(v_toCold_3390_, 4);
v_openDecls_3393_ = lean_ctor_get(v_toCold_3390_, 5);
lean_inc(v_openDecls_3393_);
lean_inc(v_currNamespace_3392_);
v___x_3394_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3394_, 0, v_currNamespace_3392_);
lean_ctor_set(v___x_3394_, 1, v_openDecls_3393_);
v___x_3395_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3395_, 0, v___x_3394_);
lean_ctor_set(v___x_3395_, 1, v___y_3388_);
lean_inc_ref(v___y_3384_);
lean_inc_ref(v___y_3387_);
v___x_3396_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3396_, 0, v___y_3387_);
lean_ctor_set(v___x_3396_, 1, v___y_3389_);
lean_ctor_set(v___x_3396_, 2, v___y_3385_);
lean_ctor_set(v___x_3396_, 3, v___y_3384_);
lean_ctor_set(v___x_3396_, 4, v___x_3395_);
lean_ctor_set_uint8(v___x_3396_, sizeof(void*)*5, v___y_3386_);
lean_ctor_set_uint8(v___x_3396_, sizeof(void*)*5 + 1, v___y_3383_);
lean_ctor_set_uint8(v___x_3396_, sizeof(void*)*5 + 2, v_isSilent_3376_);
v___x_3397_ = lean_st_ref_take(v___y_3391_);
v_env_3398_ = lean_ctor_get(v___x_3397_, 0);
v_nextMacroScope_3399_ = lean_ctor_get(v___x_3397_, 1);
v_ngen_3400_ = lean_ctor_get(v___x_3397_, 2);
v_auxDeclNGen_3401_ = lean_ctor_get(v___x_3397_, 3);
v_traceState_3402_ = lean_ctor_get(v___x_3397_, 4);
v_cache_3403_ = lean_ctor_get(v___x_3397_, 5);
v_recordedDeps_3404_ = lean_ctor_get(v___x_3397_, 6);
v_messages_3405_ = lean_ctor_get(v___x_3397_, 7);
v_infoState_3406_ = lean_ctor_get(v___x_3397_, 8);
v_snapshotTasks_3407_ = lean_ctor_get(v___x_3397_, 9);
v_isSharedCheck_3418_ = !lean_is_exclusive(v___x_3397_);
if (v_isSharedCheck_3418_ == 0)
{
v___x_3409_ = v___x_3397_;
v_isShared_3410_ = v_isSharedCheck_3418_;
goto v_resetjp_3408_;
}
else
{
lean_inc(v_snapshotTasks_3407_);
lean_inc(v_infoState_3406_);
lean_inc(v_messages_3405_);
lean_inc(v_recordedDeps_3404_);
lean_inc(v_cache_3403_);
lean_inc(v_traceState_3402_);
lean_inc(v_auxDeclNGen_3401_);
lean_inc(v_ngen_3400_);
lean_inc(v_nextMacroScope_3399_);
lean_inc(v_env_3398_);
lean_dec(v___x_3397_);
v___x_3409_ = lean_box(0);
v_isShared_3410_ = v_isSharedCheck_3418_;
goto v_resetjp_3408_;
}
v_resetjp_3408_:
{
lean_object* v___x_3411_; lean_object* v___x_3412_; lean_object* v___x_3414_; 
v___x_3411_ = lean_box(0);
v___x_3412_ = l_Lean_MessageLog_add(v___x_3396_, v_messages_3405_);
if (v_isShared_3410_ == 0)
{
lean_ctor_set(v___x_3409_, 7, v___x_3412_);
v___x_3414_ = v___x_3409_;
goto v_reusejp_3413_;
}
else
{
lean_object* v_reuseFailAlloc_3417_; 
v_reuseFailAlloc_3417_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_3417_, 0, v_env_3398_);
lean_ctor_set(v_reuseFailAlloc_3417_, 1, v_nextMacroScope_3399_);
lean_ctor_set(v_reuseFailAlloc_3417_, 2, v_ngen_3400_);
lean_ctor_set(v_reuseFailAlloc_3417_, 3, v_auxDeclNGen_3401_);
lean_ctor_set(v_reuseFailAlloc_3417_, 4, v_traceState_3402_);
lean_ctor_set(v_reuseFailAlloc_3417_, 5, v_cache_3403_);
lean_ctor_set(v_reuseFailAlloc_3417_, 6, v_recordedDeps_3404_);
lean_ctor_set(v_reuseFailAlloc_3417_, 7, v___x_3412_);
lean_ctor_set(v_reuseFailAlloc_3417_, 8, v_infoState_3406_);
lean_ctor_set(v_reuseFailAlloc_3417_, 9, v_snapshotTasks_3407_);
v___x_3414_ = v_reuseFailAlloc_3417_;
goto v_reusejp_3413_;
}
v_reusejp_3413_:
{
lean_object* v___x_3415_; lean_object* v___x_3416_; 
v___x_3415_ = lean_st_ref_put(v___y_3391_, v___x_3414_);
v___x_3416_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3416_, 0, v___x_3411_);
return v___x_3416_;
}
}
}
v___jp_3419_:
{
lean_object* v_fileName_3428_; lean_object* v_fileMap_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v_a_3432_; lean_object* v___x_3434_; uint8_t v_isShared_3435_; uint8_t v_isSharedCheck_3445_; 
v_fileName_3428_ = lean_ctor_get(v___y_3425_, 0);
v_fileMap_3429_ = lean_ctor_get(v___y_3425_, 1);
v___x_3430_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3374_);
v___x_3431_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3430_, v___y_3377_, v___y_3378_, v___y_3379_, v___y_3380_);
v_a_3432_ = lean_ctor_get(v___x_3431_, 0);
v_isSharedCheck_3445_ = !lean_is_exclusive(v___x_3431_);
if (v_isSharedCheck_3445_ == 0)
{
v___x_3434_ = v___x_3431_;
v_isShared_3435_ = v_isSharedCheck_3445_;
goto v_resetjp_3433_;
}
else
{
lean_inc(v_a_3432_);
lean_dec(v___x_3431_);
v___x_3434_ = lean_box(0);
v_isShared_3435_ = v_isSharedCheck_3445_;
goto v_resetjp_3433_;
}
v_resetjp_3433_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; lean_object* v___x_3439_; 
lean_inc_ref_n(v_fileMap_3429_, 2);
v___x_3436_ = l_Lean_FileMap_toPosition(v_fileMap_3429_, v___y_3426_);
lean_dec(v___y_3426_);
v___x_3437_ = l_Lean_FileMap_toPosition(v_fileMap_3429_, v___y_3427_);
lean_dec(v___y_3427_);
v___x_3438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
v___x_3439_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3423_ == 0)
{
lean_del_object(v___x_3434_);
lean_dec_ref(v___y_3420_);
v___y_3383_ = v___y_3422_;
v___y_3384_ = v___x_3439_;
v___y_3385_ = v___x_3438_;
v___y_3386_ = v___y_3424_;
v___y_3387_ = v_fileName_3428_;
v___y_3388_ = v_a_3432_;
v___y_3389_ = v___x_3436_;
v_toCold_3390_ = v___y_3421_;
v___y_3391_ = v___y_3380_;
goto v___jp_3382_;
}
else
{
uint8_t v___x_3440_; 
lean_inc(v_a_3432_);
v___x_3440_ = l_Lean_MessageData_hasTag(v___y_3420_, v_a_3432_);
if (v___x_3440_ == 0)
{
lean_object* v___x_3441_; lean_object* v___x_3443_; 
lean_dec_ref_known(v___x_3438_, 1);
lean_dec_ref(v___x_3436_);
lean_dec(v_a_3432_);
v___x_3441_ = lean_box(0);
if (v_isShared_3435_ == 0)
{
lean_ctor_set(v___x_3434_, 0, v___x_3441_);
v___x_3443_ = v___x_3434_;
goto v_reusejp_3442_;
}
else
{
lean_object* v_reuseFailAlloc_3444_; 
v_reuseFailAlloc_3444_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3444_, 0, v___x_3441_);
v___x_3443_ = v_reuseFailAlloc_3444_;
goto v_reusejp_3442_;
}
v_reusejp_3442_:
{
return v___x_3443_;
}
}
else
{
lean_del_object(v___x_3434_);
v___y_3383_ = v___y_3422_;
v___y_3384_ = v___x_3439_;
v___y_3385_ = v___x_3438_;
v___y_3386_ = v___y_3424_;
v___y_3387_ = v_fileName_3428_;
v___y_3388_ = v_a_3432_;
v___y_3389_ = v___x_3436_;
v_toCold_3390_ = v___y_3421_;
v___y_3391_ = v___y_3380_;
goto v___jp_3382_;
}
}
}
}
v___jp_3446_:
{
lean_object* v___x_3454_; 
v___x_3454_ = l_Lean_Syntax_getTailPos_x3f(v___y_3452_, v___y_3451_);
lean_dec(v___y_3452_);
if (lean_obj_tag(v___x_3454_) == 0)
{
lean_inc(v___y_3453_);
v___y_3420_ = v___y_3448_;
v___y_3421_ = v___y_3449_;
v___y_3422_ = v___y_3450_;
v___y_3423_ = v___y_3447_;
v___y_3424_ = v___y_3451_;
v___y_3425_ = v___y_3449_;
v___y_3426_ = v___y_3453_;
v___y_3427_ = v___y_3453_;
goto v___jp_3419_;
}
else
{
lean_object* v_val_3455_; 
v_val_3455_ = lean_ctor_get(v___x_3454_, 0);
lean_inc(v_val_3455_);
lean_dec_ref_known(v___x_3454_, 1);
v___y_3420_ = v___y_3448_;
v___y_3421_ = v___y_3449_;
v___y_3422_ = v___y_3450_;
v___y_3423_ = v___y_3447_;
v___y_3424_ = v___y_3451_;
v___y_3425_ = v___y_3449_;
v___y_3426_ = v___y_3453_;
v___y_3427_ = v_val_3455_;
goto v___jp_3419_;
}
}
v___jp_3456_:
{
lean_object* v_toCold_3460_; lean_object* v_ref_3461_; uint8_t v_suppressElabErrors_3462_; lean_object* v___x_3463_; lean_object* v___x_3464_; lean_object* v___f_3465_; lean_object* v_ref_3466_; lean_object* v___x_3467_; 
v_toCold_3460_ = lean_ctor_get(v___y_3379_, 0);
v_ref_3461_ = lean_ctor_get(v___y_3379_, 2);
v_suppressElabErrors_3462_ = lean_ctor_get_uint8(v___y_3379_, sizeof(void*)*3 + 2);
v___x_3463_ = lean_box(v_suppressElabErrors_3462_);
v___x_3464_ = lean_box(v___y_3457_);
v___f_3465_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3465_, 0, v___x_3463_);
lean_closure_set(v___f_3465_, 1, v___x_3464_);
v_ref_3466_ = l_Lean_replaceRef(v_ref_3373_, v_ref_3461_);
v___x_3467_ = l_Lean_Syntax_getPos_x3f(v_ref_3466_, v___y_3458_);
if (lean_obj_tag(v___x_3467_) == 0)
{
lean_object* v___x_3468_; 
v___x_3468_ = lean_unsigned_to_nat(0u);
v___y_3447_ = v_suppressElabErrors_3462_;
v___y_3448_ = v___f_3465_;
v___y_3449_ = v_toCold_3460_;
v___y_3450_ = v___y_3459_;
v___y_3451_ = v___y_3458_;
v___y_3452_ = v_ref_3466_;
v___y_3453_ = v___x_3468_;
goto v___jp_3446_;
}
else
{
lean_object* v_val_3469_; 
v_val_3469_ = lean_ctor_get(v___x_3467_, 0);
lean_inc(v_val_3469_);
lean_dec_ref_known(v___x_3467_, 1);
v___y_3447_ = v_suppressElabErrors_3462_;
v___y_3448_ = v___f_3465_;
v___y_3449_ = v_toCold_3460_;
v___y_3450_ = v___y_3459_;
v___y_3451_ = v___y_3458_;
v___y_3452_ = v_ref_3466_;
v___y_3453_ = v_val_3469_;
goto v___jp_3446_;
}
}
v___jp_3471_:
{
if (v___y_3474_ == 0)
{
v___y_3457_ = v___y_3472_;
v___y_3458_ = v___y_3473_;
v___y_3459_ = v_severity_3375_;
goto v___jp_3456_;
}
else
{
v___y_3457_ = v___y_3472_;
v___y_3458_ = v___y_3473_;
v___y_3459_ = v___x_3470_;
goto v___jp_3456_;
}
}
v___jp_3475_:
{
if (v___y_3476_ == 0)
{
uint8_t v___x_3477_; uint8_t v___x_3478_; 
v___x_3477_ = 1;
v___x_3478_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3375_, v___x_3477_);
if (v___x_3478_ == 0)
{
v___y_3472_ = v___y_3476_;
v___y_3473_ = v___y_3476_;
v___y_3474_ = v___x_3478_;
goto v___jp_3471_;
}
else
{
lean_object* v___x_3479_; lean_object* v___x_3480_; uint8_t v___x_3481_; 
v___x_3479_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_3379_);
v___x_3480_ = l_Lean_warningAsError;
v___x_3481_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_3479_, v___x_3480_);
lean_dec_ref(v___x_3479_);
v___y_3472_ = v___y_3476_;
v___y_3473_ = v___y_3476_;
v___y_3474_ = v___x_3481_;
goto v___jp_3471_;
}
}
else
{
lean_object* v___x_3482_; lean_object* v___x_3483_; 
lean_dec_ref(v_msgData_3374_);
v___x_3482_ = lean_box(0);
v___x_3483_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3483_, 0, v___x_3482_);
return v___x_3483_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_3486_, lean_object* v_msgData_3487_, lean_object* v_severity_3488_, lean_object* v_isSilent_3489_, lean_object* v___y_3490_, lean_object* v___y_3491_, lean_object* v___y_3492_, lean_object* v___y_3493_, lean_object* v___y_3494_){
_start:
{
uint8_t v_severity_boxed_3495_; uint8_t v_isSilent_boxed_3496_; lean_object* v_res_3497_; 
v_severity_boxed_3495_ = lean_unbox(v_severity_3488_);
v_isSilent_boxed_3496_ = lean_unbox(v_isSilent_3489_);
v_res_3497_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4(v_ref_3486_, v_msgData_3487_, v_severity_boxed_3495_, v_isSilent_boxed_3496_, v___y_3490_, v___y_3491_, v___y_3492_, v___y_3493_);
lean_dec(v___y_3493_);
lean_dec_ref(v___y_3492_);
lean_dec(v___y_3491_);
lean_dec_ref(v___y_3490_);
lean_dec(v_ref_3486_);
return v_res_3497_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(lean_object* v_msgData_3498_, uint8_t v_severity_3499_, uint8_t v_isSilent_3500_, lean_object* v___y_3501_, lean_object* v___y_3502_, lean_object* v___y_3503_, lean_object* v___y_3504_){
_start:
{
lean_object* v_ref_3506_; lean_object* v___x_3507_; 
v_ref_3506_ = lean_ctor_get(v___y_3503_, 2);
v___x_3507_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4(v_ref_3506_, v_msgData_3498_, v_severity_3499_, v_isSilent_3500_, v___y_3501_, v___y_3502_, v___y_3503_, v___y_3504_);
return v___x_3507_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___boxed(lean_object* v_msgData_3508_, lean_object* v_severity_3509_, lean_object* v_isSilent_3510_, lean_object* v___y_3511_, lean_object* v___y_3512_, lean_object* v___y_3513_, lean_object* v___y_3514_, lean_object* v___y_3515_){
_start:
{
uint8_t v_severity_boxed_3516_; uint8_t v_isSilent_boxed_3517_; lean_object* v_res_3518_; 
v_severity_boxed_3516_ = lean_unbox(v_severity_3509_);
v_isSilent_boxed_3517_ = lean_unbox(v_isSilent_3510_);
v_res_3518_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(v_msgData_3508_, v_severity_boxed_3516_, v_isSilent_boxed_3517_, v___y_3511_, v___y_3512_, v___y_3513_, v___y_3514_);
lean_dec(v___y_3514_);
lean_dec_ref(v___y_3513_);
lean_dec(v___y_3512_);
lean_dec_ref(v___y_3511_);
return v_res_3518_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_msgData_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
uint8_t v___x_3525_; uint8_t v___x_3526_; lean_object* v___x_3527_; 
v___x_3525_ = 1;
v___x_3526_ = 0;
v___x_3527_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(v_msgData_3519_, v___x_3525_, v___x_3526_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
return v___x_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_msgData_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v_res_3534_; 
v_res_3534_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_msgData_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
lean_dec(v___y_3532_);
lean_dec_ref(v___y_3531_);
lean_dec(v___y_3530_);
lean_dec_ref(v___y_3529_);
return v_res_3534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(lean_object* v_as_3535_, size_t v_sz_3536_, size_t v_i_3537_, lean_object* v_b_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_){
_start:
{
lean_object* v_a_3545_; uint8_t v___x_3549_; 
v___x_3549_ = lean_usize_dec_lt(v_i_3537_, v_sz_3536_);
if (v___x_3549_ == 0)
{
lean_object* v___x_3550_; 
v___x_3550_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3550_, 0, v_b_3538_);
return v___x_3550_;
}
else
{
lean_object* v___x_3551_; lean_object* v_a_3552_; lean_object* v___x_3553_; lean_object* v___x_3554_; 
v___x_3551_ = lean_box(0);
v_a_3552_ = lean_array_uget_borrowed(v_as_3535_, v_i_3537_);
v___x_3553_ = l_Lean_Expr_fvarId_x21(v_a_3552_);
lean_inc(v___x_3553_);
v___x_3554_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_3553_, v___y_3540_, v___y_3541_, v___y_3542_);
if (lean_obj_tag(v___x_3554_) == 0)
{
lean_object* v_a_3555_; uint8_t v___x_3556_; uint8_t v___x_3557_; 
v_a_3555_ = lean_ctor_get(v___x_3554_, 0);
lean_inc(v_a_3555_);
lean_dec_ref_known(v___x_3554_, 1);
v___x_3556_ = lean_unbox(v_a_3555_);
lean_dec(v_a_3555_);
v___x_3557_ = l_Lean_BinderInfo_isInstImplicit(v___x_3556_);
if (v___x_3557_ == 0)
{
lean_dec(v___x_3553_);
v_a_3545_ = v___x_3551_;
goto v___jp_3544_;
}
else
{
lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; 
v___x_3558_ = lean_st_ref_take(v___y_3539_);
v___x_3559_ = l_Lean_CollectFVars_State_add(v___x_3558_, v___x_3553_);
v___x_3560_ = lean_st_ref_put(v___y_3539_, v___x_3559_);
v_a_3545_ = v___x_3551_;
goto v___jp_3544_;
}
}
else
{
lean_object* v_a_3561_; lean_object* v___x_3563_; uint8_t v_isShared_3564_; uint8_t v_isSharedCheck_3568_; 
lean_dec(v___x_3553_);
v_a_3561_ = lean_ctor_get(v___x_3554_, 0);
v_isSharedCheck_3568_ = !lean_is_exclusive(v___x_3554_);
if (v_isSharedCheck_3568_ == 0)
{
v___x_3563_ = v___x_3554_;
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
else
{
lean_inc(v_a_3561_);
lean_dec(v___x_3554_);
v___x_3563_ = lean_box(0);
v_isShared_3564_ = v_isSharedCheck_3568_;
goto v_resetjp_3562_;
}
v_resetjp_3562_:
{
lean_object* v___x_3566_; 
if (v_isShared_3564_ == 0)
{
v___x_3566_ = v___x_3563_;
goto v_reusejp_3565_;
}
else
{
lean_object* v_reuseFailAlloc_3567_; 
v_reuseFailAlloc_3567_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3567_, 0, v_a_3561_);
v___x_3566_ = v_reuseFailAlloc_3567_;
goto v_reusejp_3565_;
}
v_reusejp_3565_:
{
return v___x_3566_;
}
}
}
}
v___jp_3544_:
{
size_t v___x_3546_; size_t v___x_3547_; 
v___x_3546_ = ((size_t)1ULL);
v___x_3547_ = lean_usize_add(v_i_3537_, v___x_3546_);
v_i_3537_ = v___x_3547_;
v_b_3538_ = v_a_3545_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg___boxed(lean_object* v_as_3569_, lean_object* v_sz_3570_, lean_object* v_i_3571_, lean_object* v_b_3572_, lean_object* v___y_3573_, lean_object* v___y_3574_, lean_object* v___y_3575_, lean_object* v___y_3576_, lean_object* v___y_3577_){
_start:
{
size_t v_sz_boxed_3578_; size_t v_i_boxed_3579_; lean_object* v_res_3580_; 
v_sz_boxed_3578_ = lean_unbox_usize(v_sz_3570_);
lean_dec(v_sz_3570_);
v_i_boxed_3579_ = lean_unbox_usize(v_i_3571_);
lean_dec(v_i_3571_);
v_res_3580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(v_as_3569_, v_sz_boxed_3578_, v_i_boxed_3579_, v_b_3572_, v___y_3573_, v___y_3574_, v___y_3575_, v___y_3576_);
lean_dec(v___y_3576_);
lean_dec_ref(v___y_3575_);
lean_dec_ref(v___y_3574_);
lean_dec(v___y_3573_);
lean_dec_ref(v_as_3569_);
return v_res_3580_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(lean_object* v_k_3581_, lean_object* v_t_3582_){
_start:
{
if (lean_obj_tag(v_t_3582_) == 0)
{
lean_object* v_k_3583_; lean_object* v_l_3584_; lean_object* v_r_3585_; uint8_t v___x_3586_; 
v_k_3583_ = lean_ctor_get(v_t_3582_, 1);
v_l_3584_ = lean_ctor_get(v_t_3582_, 3);
v_r_3585_ = lean_ctor_get(v_t_3582_, 4);
v___x_3586_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3581_, v_k_3583_);
switch(v___x_3586_)
{
case 0:
{
v_t_3582_ = v_l_3584_;
goto _start;
}
case 1:
{
uint8_t v___x_3588_; 
v___x_3588_ = 1;
return v___x_3588_;
}
default: 
{
v_t_3582_ = v_r_3585_;
goto _start;
}
}
}
else
{
uint8_t v___x_3590_; 
v___x_3590_ = 0;
return v___x_3590_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg___boxed(lean_object* v_k_3591_, lean_object* v_t_3592_){
_start:
{
uint8_t v_res_3593_; lean_object* v_r_3594_; 
v_res_3593_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_k_3591_, v_t_3592_);
lean_dec(v_t_3592_);
lean_dec(v_k_3591_);
v_r_3594_ = lean_box(v_res_3593_);
return v_r_3594_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3596_; lean_object* v___x_3597_; 
v___x_3596_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__0));
v___x_3597_ = l_Lean_stringToMessageData(v___x_3596_);
return v___x_3597_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3599_; lean_object* v___x_3600_; 
v___x_3599_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__2));
v___x_3600_ = l_Lean_stringToMessageData(v___x_3599_);
return v___x_3600_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object* v_a_3601_, lean_object* v_as_3602_, size_t v_sz_3603_, size_t v_i_3604_, lean_object* v_b_3605_, lean_object* v___y_3606_, lean_object* v___y_3607_, lean_object* v___y_3608_){
_start:
{
lean_object* v_a_3611_; uint8_t v___x_3615_; 
v___x_3615_ = lean_usize_dec_lt(v_i_3604_, v_sz_3603_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; 
v___x_3616_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3616_, 0, v_b_3605_);
return v___x_3616_;
}
else
{
lean_object* v_snd_3617_; 
v_snd_3617_ = lean_ctor_get(v_b_3605_, 1);
lean_inc(v_snd_3617_);
if (lean_obj_tag(v_snd_3617_) == 0)
{
lean_object* v_fst_3618_; lean_object* v___x_3620_; uint8_t v_isShared_3621_; uint8_t v_isSharedCheck_3626_; 
v_fst_3618_ = lean_ctor_get(v_b_3605_, 0);
v_isSharedCheck_3626_ = !lean_is_exclusive(v_b_3605_);
if (v_isSharedCheck_3626_ == 0)
{
lean_object* v_unused_3627_; 
v_unused_3627_ = lean_ctor_get(v_b_3605_, 1);
lean_dec(v_unused_3627_);
v___x_3620_ = v_b_3605_;
v_isShared_3621_ = v_isSharedCheck_3626_;
goto v_resetjp_3619_;
}
else
{
lean_inc(v_fst_3618_);
lean_dec(v_b_3605_);
v___x_3620_ = lean_box(0);
v_isShared_3621_ = v_isSharedCheck_3626_;
goto v_resetjp_3619_;
}
v_resetjp_3619_:
{
lean_object* v___x_3623_; 
if (v_isShared_3621_ == 0)
{
v___x_3623_ = v___x_3620_;
goto v_reusejp_3622_;
}
else
{
lean_object* v_reuseFailAlloc_3625_; 
v_reuseFailAlloc_3625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3625_, 0, v_fst_3618_);
lean_ctor_set(v_reuseFailAlloc_3625_, 1, v_snd_3617_);
v___x_3623_ = v_reuseFailAlloc_3625_;
goto v_reusejp_3622_;
}
v_reusejp_3622_:
{
lean_object* v___x_3624_; 
v___x_3624_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3624_, 0, v___x_3623_);
return v___x_3624_;
}
}
}
else
{
lean_object* v_fst_3628_; lean_object* v___x_3630_; uint8_t v_isShared_3631_; uint8_t v_isSharedCheck_3685_; 
v_fst_3628_ = lean_ctor_get(v_b_3605_, 0);
v_isSharedCheck_3685_ = !lean_is_exclusive(v_b_3605_);
if (v_isSharedCheck_3685_ == 0)
{
lean_object* v_unused_3686_; 
v_unused_3686_ = lean_ctor_get(v_b_3605_, 1);
lean_dec(v_unused_3686_);
v___x_3630_ = v_b_3605_;
v_isShared_3631_ = v_isSharedCheck_3685_;
goto v_resetjp_3629_;
}
else
{
lean_inc(v_fst_3628_);
lean_dec(v_b_3605_);
v___x_3630_ = lean_box(0);
v_isShared_3631_ = v_isSharedCheck_3685_;
goto v_resetjp_3629_;
}
v_resetjp_3629_:
{
lean_object* v_val_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3684_; 
v_val_3632_ = lean_ctor_get(v_snd_3617_, 0);
v_isSharedCheck_3684_ = !lean_is_exclusive(v_snd_3617_);
if (v_isSharedCheck_3684_ == 0)
{
v___x_3634_ = v_snd_3617_;
v_isShared_3635_ = v_isSharedCheck_3684_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_val_3632_);
lean_dec(v_snd_3617_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3684_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v_fvarSet_3636_; lean_object* v_a_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3641_; 
v_fvarSet_3636_ = lean_ctor_get(v_a_3601_, 1);
v_a_3637_ = lean_array_uget_borrowed(v_as_3602_, v_i_3604_);
v___x_3638_ = lean_unsigned_to_nat(1u);
v___x_3639_ = lean_nat_add(v_val_3632_, v___x_3638_);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3639_);
v___x_3641_ = v___x_3634_;
goto v_reusejp_3640_;
}
else
{
lean_object* v_reuseFailAlloc_3683_; 
v_reuseFailAlloc_3683_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3683_, 0, v___x_3639_);
v___x_3641_ = v_reuseFailAlloc_3683_;
goto v_reusejp_3640_;
}
v_reusejp_3640_:
{
lean_object* v___x_3642_; uint8_t v___x_3643_; 
v___x_3642_ = l_Lean_Expr_fvarId_x21(v_a_3637_);
v___x_3643_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v___x_3642_, v_fvarSet_3636_);
if (v___x_3643_ == 0)
{
lean_object* v___x_3644_; 
v___x_3644_ = l_Lean_FVarId_getDecl___redArg(v___x_3642_, v___y_3606_, v___y_3607_, v___y_3608_);
if (lean_obj_tag(v___x_3644_) == 0)
{
lean_object* v_a_3645_; lean_object* v___x_3646_; 
v_a_3645_ = lean_ctor_get(v___x_3644_, 0);
lean_inc(v_a_3645_);
lean_dec_ref_known(v___x_3644_, 1);
v___x_3646_ = l_Lean_LocalDecl_ppAsBinder(v_a_3645_);
if (lean_obj_tag(v___x_3646_) == 1)
{
lean_object* v_val_3647_; lean_object* v___x_3649_; uint8_t v_isShared_3650_; uint8_t v_isSharedCheck_3668_; 
v_val_3647_ = lean_ctor_get(v___x_3646_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3646_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3649_ = v___x_3646_;
v_isShared_3650_ = v_isSharedCheck_3668_;
goto v_resetjp_3648_;
}
else
{
lean_inc(v_val_3647_);
lean_dec(v___x_3646_);
v___x_3649_ = lean_box(0);
v_isShared_3650_ = v_isSharedCheck_3668_;
goto v_resetjp_3648_;
}
v_resetjp_3648_:
{
lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3654_; 
v___x_3651_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1);
v___x_3652_ = l_Nat_reprFast(v_val_3632_);
if (v_isShared_3650_ == 0)
{
lean_ctor_set_tag(v___x_3649_, 3);
lean_ctor_set(v___x_3649_, 0, v___x_3652_);
v___x_3654_ = v___x_3649_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; lean_object* v___x_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; lean_object* v___x_3660_; lean_object* v___x_3661_; lean_object* v___x_3662_; lean_object* v___x_3663_; lean_object* v___x_3665_; 
v___x_3655_ = l_Lean_MessageData_ofFormat(v___x_3654_);
v___x_3656_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3656_, 0, v___x_3651_);
lean_ctor_set(v___x_3656_, 1, v___x_3655_);
v___x_3657_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3);
v___x_3658_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3658_, 0, v___x_3656_);
lean_ctor_set(v___x_3658_, 1, v___x_3657_);
v___x_3659_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3659_, 0, v___x_3658_);
lean_ctor_set(v___x_3659_, 1, v_val_3647_);
v___x_3660_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3661_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3661_, 0, v___x_3659_);
lean_ctor_set(v___x_3661_, 1, v___x_3660_);
v___x_3662_ = l_Lean_indentD(v___x_3661_);
v___x_3663_ = lean_array_push(v_fst_3628_, v___x_3662_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 1, v___x_3641_);
lean_ctor_set(v___x_3630_, 0, v___x_3663_);
v___x_3665_ = v___x_3630_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v___x_3663_);
lean_ctor_set(v_reuseFailAlloc_3666_, 1, v___x_3641_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
v_a_3611_ = v___x_3665_;
goto v___jp_3610_;
}
}
}
}
else
{
lean_object* v___x_3670_; 
lean_dec(v___x_3646_);
lean_dec(v_val_3632_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 1, v___x_3641_);
v___x_3670_ = v___x_3630_;
goto v_reusejp_3669_;
}
else
{
lean_object* v_reuseFailAlloc_3671_; 
v_reuseFailAlloc_3671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3671_, 0, v_fst_3628_);
lean_ctor_set(v_reuseFailAlloc_3671_, 1, v___x_3641_);
v___x_3670_ = v_reuseFailAlloc_3671_;
goto v_reusejp_3669_;
}
v_reusejp_3669_:
{
v_a_3611_ = v___x_3670_;
goto v___jp_3610_;
}
}
}
else
{
lean_object* v_a_3672_; lean_object* v___x_3674_; uint8_t v_isShared_3675_; uint8_t v_isSharedCheck_3679_; 
lean_dec_ref(v___x_3641_);
lean_dec(v_val_3632_);
lean_del_object(v___x_3630_);
lean_dec(v_fst_3628_);
v_a_3672_ = lean_ctor_get(v___x_3644_, 0);
v_isSharedCheck_3679_ = !lean_is_exclusive(v___x_3644_);
if (v_isSharedCheck_3679_ == 0)
{
v___x_3674_ = v___x_3644_;
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
else
{
lean_inc(v_a_3672_);
lean_dec(v___x_3644_);
v___x_3674_ = lean_box(0);
v_isShared_3675_ = v_isSharedCheck_3679_;
goto v_resetjp_3673_;
}
v_resetjp_3673_:
{
lean_object* v___x_3677_; 
if (v_isShared_3675_ == 0)
{
v___x_3677_ = v___x_3674_;
goto v_reusejp_3676_;
}
else
{
lean_object* v_reuseFailAlloc_3678_; 
v_reuseFailAlloc_3678_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3678_, 0, v_a_3672_);
v___x_3677_ = v_reuseFailAlloc_3678_;
goto v_reusejp_3676_;
}
v_reusejp_3676_:
{
return v___x_3677_;
}
}
}
}
else
{
lean_object* v___x_3681_; 
lean_dec(v___x_3642_);
lean_dec(v_val_3632_);
if (v_isShared_3631_ == 0)
{
lean_ctor_set(v___x_3630_, 1, v___x_3641_);
v___x_3681_ = v___x_3630_;
goto v_reusejp_3680_;
}
else
{
lean_object* v_reuseFailAlloc_3682_; 
v_reuseFailAlloc_3682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3682_, 0, v_fst_3628_);
lean_ctor_set(v_reuseFailAlloc_3682_, 1, v___x_3641_);
v___x_3681_ = v_reuseFailAlloc_3682_;
goto v_reusejp_3680_;
}
v_reusejp_3680_:
{
v_a_3611_ = v___x_3681_;
goto v___jp_3610_;
}
}
}
}
}
}
}
v___jp_3610_:
{
size_t v___x_3612_; size_t v___x_3613_; 
v___x_3612_ = ((size_t)1ULL);
v___x_3613_ = lean_usize_add(v_i_3604_, v___x_3612_);
v_i_3604_ = v___x_3613_;
v_b_3605_ = v_a_3611_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object* v_a_3687_, lean_object* v_as_3688_, lean_object* v_sz_3689_, lean_object* v_i_3690_, lean_object* v_b_3691_, lean_object* v___y_3692_, lean_object* v___y_3693_, lean_object* v___y_3694_, lean_object* v___y_3695_){
_start:
{
size_t v_sz_boxed_3696_; size_t v_i_boxed_3697_; lean_object* v_res_3698_; 
v_sz_boxed_3696_ = lean_unbox_usize(v_sz_3689_);
lean_dec(v_sz_3689_);
v_i_boxed_3697_ = lean_unbox_usize(v_i_3690_);
lean_dec(v_i_3690_);
v_res_3698_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_a_3687_, v_as_3688_, v_sz_boxed_3696_, v_i_boxed_3697_, v_b_3691_, v___y_3692_, v___y_3693_, v___y_3694_);
lean_dec(v___y_3694_);
lean_dec_ref(v___y_3693_);
lean_dec_ref(v___y_3692_);
lean_dec_ref(v_as_3688_);
lean_dec_ref(v_a_3687_);
return v_res_3698_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3700_; lean_object* v___x_3701_; 
v___x_3700_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0));
v___x_3701_ = l_Lean_stringToMessageData(v___x_3700_);
return v___x_3701_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3703_; lean_object* v___x_3704_; 
v___x_3703_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2));
v___x_3704_ = l_Lean_stringToMessageData(v___x_3703_);
return v___x_3704_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3705_; lean_object* v___x_3706_; lean_object* v___x_3707_; 
v___x_3705_ = lean_box(0);
v___x_3706_ = lean_unsigned_to_nat(16u);
v___x_3707_ = lean_mk_array(v___x_3706_, v___x_3705_);
return v___x_3707_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; lean_object* v___x_3710_; 
v___x_3708_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4);
v___x_3709_ = lean_unsigned_to_nat(0u);
v___x_3710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3710_, 0, v___x_3709_);
lean_ctor_set(v___x_3710_, 1, v___x_3708_);
return v___x_3710_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3719_; lean_object* v___x_3720_; 
v___x_3719_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9));
v___x_3720_ = l_Lean_stringToMessageData(v___x_3719_);
return v___x_3720_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12(void){
_start:
{
lean_object* v___x_3722_; lean_object* v___x_3723_; 
v___x_3722_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11));
v___x_3723_ = l_Lean_stringToMessageData(v___x_3722_);
return v___x_3723_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v___x_3725_, lean_object* v___x_3726_, lean_object* v_args_3727_, lean_object* v_ty_3728_, lean_object* v___y_3729_, lean_object* v___y_3730_, lean_object* v___y_3731_, lean_object* v___y_3732_){
_start:
{
lean_object* v___y_3735_; lean_object* v___y_3736_; lean_object* v___y_3737_; lean_object* v___x_3751_; lean_object* v___x_3752_; lean_object* v___x_3753_; lean_object* v___x_3754_; lean_object* v___x_3755_; lean_object* v___y_3811_; lean_object* v___x_3812_; 
v___x_3751_ = lean_unsigned_to_nat(0u);
v___x_3752_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5);
v___x_3753_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6));
v___x_3754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3754_, 0, v___x_3752_);
lean_ctor_set(v___x_3754_, 1, v___x_3726_);
lean_ctor_set(v___x_3754_, 2, v___x_3753_);
v___x_3755_ = lean_st_mk_ref(v___x_3754_);
v___x_3812_ = l_Lean_Expr_collectFVars(v_ty_3728_, v___x_3755_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3812_) == 0)
{
lean_object* v___x_3813_; size_t v_sz_3814_; size_t v___x_3815_; lean_object* v___x_3816_; 
lean_dec_ref_known(v___x_3812_, 1);
v___x_3813_ = lean_box(0);
v_sz_3814_ = lean_array_size(v_args_3727_);
v___x_3815_ = ((size_t)0ULL);
v___x_3816_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(v_args_3727_, v_sz_3814_, v___x_3815_, v___x_3813_, v___x_3755_, v___y_3729_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3816_) == 0)
{
lean_dec_ref_known(v___x_3816_, 1);
goto v___jp_3756_;
}
else
{
v___y_3811_ = v___x_3816_;
goto v___jp_3810_;
}
}
else
{
v___y_3811_ = v___x_3812_;
goto v___jp_3810_;
}
v___jp_3734_:
{
lean_object* v___x_3738_; lean_object* v___x_3739_; lean_object* v___x_3740_; lean_object* v___x_3741_; lean_object* v___x_3742_; lean_object* v___x_3743_; lean_object* v___x_3744_; lean_object* v___x_3745_; lean_object* v___x_3746_; lean_object* v___x_3747_; uint8_t v___x_3748_; 
lean_inc_ref(v___y_3737_);
v___x_3738_ = l_Lean_stringToMessageData(v___y_3737_);
v___x_3739_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3739_, 0, v___y_3736_);
lean_ctor_set(v___x_3739_, 1, v___x_3738_);
v___x_3740_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1);
v___x_3741_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3741_, 0, v___x_3739_);
lean_ctor_set(v___x_3741_, 1, v___x_3740_);
v___x_3742_ = lean_array_to_list(v___y_3735_);
v___x_3743_ = l_Lean_MessageData_nil;
v___x_3744_ = l_Lean_MessageData_joinSep(v___x_3742_, v___x_3743_);
v___x_3745_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3745_, 0, v___x_3741_);
lean_ctor_set(v___x_3745_, 1, v___x_3744_);
v___x_3746_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3);
v___x_3747_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3747_, 0, v___x_3745_);
lean_ctor_set(v___x_3747_, 1, v___x_3746_);
v___x_3748_ = l_Lean_Expr_hasSorry(v___x_3725_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; 
v___x_3749_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3747_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
return v___x_3749_;
}
else
{
lean_object* v___x_3750_; 
v___x_3750_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(v___x_3747_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
return v___x_3750_;
}
}
v___jp_3756_:
{
lean_object* v___x_3757_; lean_object* v___x_3758_; 
v___x_3757_ = lean_st_ref_get(v___x_3755_);
lean_dec(v___x_3755_);
v___x_3758_ = l_Lean_CollectFVars_State_addDependencies(v___x_3757_, v___y_3729_, v___y_3730_, v___y_3731_, v___y_3732_);
if (lean_obj_tag(v___x_3758_) == 0)
{
lean_object* v_a_3759_; lean_object* v___x_3760_; lean_object* v___x_3761_; size_t v_sz_3762_; size_t v___x_3763_; lean_object* v___x_3764_; 
v_a_3759_ = lean_ctor_get(v___x_3758_, 0);
lean_inc(v_a_3759_);
lean_dec_ref_known(v___x_3758_, 1);
v___x_3760_ = lean_unsigned_to_nat(1u);
v___x_3761_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8));
v_sz_3762_ = lean_array_size(v_args_3727_);
v___x_3763_ = ((size_t)0ULL);
v___x_3764_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_a_3759_, v_args_3727_, v_sz_3762_, v___x_3763_, v___x_3761_, v___y_3729_, v___y_3731_, v___y_3732_);
lean_dec(v_a_3759_);
if (lean_obj_tag(v___x_3764_) == 0)
{
lean_object* v_a_3765_; lean_object* v___x_3767_; uint8_t v_isShared_3768_; uint8_t v_isSharedCheck_3793_; 
v_a_3765_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3793_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3793_ == 0)
{
v___x_3767_ = v___x_3764_;
v_isShared_3768_ = v_isSharedCheck_3793_;
goto v_resetjp_3766_;
}
else
{
lean_inc(v_a_3765_);
lean_dec(v___x_3764_);
v___x_3767_ = lean_box(0);
v_isShared_3768_ = v_isSharedCheck_3793_;
goto v_resetjp_3766_;
}
v_resetjp_3766_:
{
lean_object* v_fst_3769_; lean_object* v___x_3771_; uint8_t v_isShared_3772_; uint8_t v_isSharedCheck_3791_; 
v_fst_3769_ = lean_ctor_get(v_a_3765_, 0);
v_isSharedCheck_3791_ = !lean_is_exclusive(v_a_3765_);
if (v_isSharedCheck_3791_ == 0)
{
lean_object* v_unused_3792_; 
v_unused_3792_ = lean_ctor_get(v_a_3765_, 1);
lean_dec(v_unused_3792_);
v___x_3771_ = v_a_3765_;
v_isShared_3772_ = v_isSharedCheck_3791_;
goto v_resetjp_3770_;
}
else
{
lean_inc(v_fst_3769_);
lean_dec(v_a_3765_);
v___x_3771_ = lean_box(0);
v_isShared_3772_ = v_isSharedCheck_3791_;
goto v_resetjp_3770_;
}
v_resetjp_3770_:
{
lean_object* v___x_3773_; uint8_t v___x_3774_; 
v___x_3773_ = lean_array_get_size(v_fst_3769_);
v___x_3774_ = lean_nat_dec_eq(v___x_3773_, v___x_3751_);
if (v___x_3774_ == 0)
{
lean_object* v___x_3775_; lean_object* v___x_3776_; lean_object* v___x_3777_; lean_object* v___x_3778_; lean_object* v___x_3780_; 
lean_del_object(v___x_3767_);
v___x_3775_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10);
v___x_3776_ = l_Nat_reprFast(v___x_3773_);
v___x_3777_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3777_, 0, v___x_3776_);
v___x_3778_ = l_Lean_MessageData_ofFormat(v___x_3777_);
if (v_isShared_3772_ == 0)
{
lean_ctor_set_tag(v___x_3771_, 7);
lean_ctor_set(v___x_3771_, 1, v___x_3778_);
lean_ctor_set(v___x_3771_, 0, v___x_3775_);
v___x_3780_ = v___x_3771_;
goto v_reusejp_3779_;
}
else
{
lean_object* v_reuseFailAlloc_3786_; 
v_reuseFailAlloc_3786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3786_, 0, v___x_3775_);
lean_ctor_set(v_reuseFailAlloc_3786_, 1, v___x_3778_);
v___x_3780_ = v_reuseFailAlloc_3786_;
goto v_reusejp_3779_;
}
v_reusejp_3779_:
{
lean_object* v___x_3781_; lean_object* v___x_3782_; uint8_t v___x_3783_; 
v___x_3781_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12);
v___x_3782_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3782_, 0, v___x_3780_);
lean_ctor_set(v___x_3782_, 1, v___x_3781_);
v___x_3783_ = lean_nat_dec_eq(v___x_3773_, v___x_3760_);
if (v___x_3783_ == 0)
{
lean_object* v___x_3784_; 
v___x_3784_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13));
v___y_3735_ = v_fst_3769_;
v___y_3736_ = v___x_3782_;
v___y_3737_ = v___x_3784_;
goto v___jp_3734_;
}
else
{
lean_object* v___x_3785_; 
v___x_3785_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___y_3735_ = v_fst_3769_;
v___y_3736_ = v___x_3782_;
v___y_3737_ = v___x_3785_;
goto v___jp_3734_;
}
}
}
else
{
lean_object* v___x_3787_; lean_object* v___x_3789_; 
lean_del_object(v___x_3771_);
lean_dec(v_fst_3769_);
v___x_3787_ = lean_box(0);
if (v_isShared_3768_ == 0)
{
lean_ctor_set(v___x_3767_, 0, v___x_3787_);
v___x_3789_ = v___x_3767_;
goto v_reusejp_3788_;
}
else
{
lean_object* v_reuseFailAlloc_3790_; 
v_reuseFailAlloc_3790_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3790_, 0, v___x_3787_);
v___x_3789_ = v_reuseFailAlloc_3790_;
goto v_reusejp_3788_;
}
v_reusejp_3788_:
{
return v___x_3789_;
}
}
}
}
}
else
{
lean_object* v_a_3794_; lean_object* v___x_3796_; uint8_t v_isShared_3797_; uint8_t v_isSharedCheck_3801_; 
v_a_3794_ = lean_ctor_get(v___x_3764_, 0);
v_isSharedCheck_3801_ = !lean_is_exclusive(v___x_3764_);
if (v_isSharedCheck_3801_ == 0)
{
v___x_3796_ = v___x_3764_;
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
else
{
lean_inc(v_a_3794_);
lean_dec(v___x_3764_);
v___x_3796_ = lean_box(0);
v_isShared_3797_ = v_isSharedCheck_3801_;
goto v_resetjp_3795_;
}
v_resetjp_3795_:
{
lean_object* v___x_3799_; 
if (v_isShared_3797_ == 0)
{
v___x_3799_ = v___x_3796_;
goto v_reusejp_3798_;
}
else
{
lean_object* v_reuseFailAlloc_3800_; 
v_reuseFailAlloc_3800_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3800_, 0, v_a_3794_);
v___x_3799_ = v_reuseFailAlloc_3800_;
goto v_reusejp_3798_;
}
v_reusejp_3798_:
{
return v___x_3799_;
}
}
}
}
else
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3809_; 
v_a_3802_ = lean_ctor_get(v___x_3758_, 0);
v_isSharedCheck_3809_ = !lean_is_exclusive(v___x_3758_);
if (v_isSharedCheck_3809_ == 0)
{
v___x_3804_ = v___x_3758_;
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3758_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3809_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
lean_object* v___x_3807_; 
if (v_isShared_3805_ == 0)
{
v___x_3807_ = v___x_3804_;
goto v_reusejp_3806_;
}
else
{
lean_object* v_reuseFailAlloc_3808_; 
v_reuseFailAlloc_3808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3808_, 0, v_a_3802_);
v___x_3807_ = v_reuseFailAlloc_3808_;
goto v_reusejp_3806_;
}
v_reusejp_3806_:
{
return v___x_3807_;
}
}
}
}
v___jp_3810_:
{
if (lean_obj_tag(v___y_3811_) == 0)
{
lean_dec_ref_known(v___y_3811_, 1);
goto v___jp_3756_;
}
else
{
lean_dec(v___x_3755_);
return v___y_3811_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v___x_3817_, lean_object* v___x_3818_, lean_object* v_args_3819_, lean_object* v_ty_3820_, lean_object* v___y_3821_, lean_object* v___y_3822_, lean_object* v___y_3823_, lean_object* v___y_3824_, lean_object* v___y_3825_){
_start:
{
lean_object* v_res_3826_; 
v_res_3826_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v___x_3817_, v___x_3818_, v_args_3819_, v_ty_3820_, v___y_3821_, v___y_3822_, v___y_3823_, v___y_3824_);
lean_dec(v___y_3824_);
lean_dec_ref(v___y_3823_);
lean_dec(v___y_3822_);
lean_dec_ref(v___y_3821_);
lean_dec_ref(v_args_3819_);
lean_dec_ref(v___x_3817_);
return v_res_3826_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object* v_e_3827_){
_start:
{
lean_object* v___x_3828_; 
v___x_3828_ = l_Lean_Expr_cleanupAnnotations(v_e_3827_);
switch(lean_obj_tag(v___x_3828_))
{
case 7:
{
lean_object* v_body_3829_; uint8_t v_binderInfo_3830_; uint8_t v___x_3831_; 
v_body_3829_ = lean_ctor_get(v___x_3828_, 2);
lean_inc_ref(v_body_3829_);
v_binderInfo_3830_ = lean_ctor_get_uint8(v___x_3828_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3828_, 3);
v___x_3831_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3830_);
if (v___x_3831_ == 0)
{
lean_object* v___x_3832_; uint8_t v___x_3833_; 
v___x_3832_ = lean_unsigned_to_nat(0u);
v___x_3833_ = lean_expr_has_loose_bvar(v_body_3829_, v___x_3832_);
if (v___x_3833_ == 0)
{
uint8_t v___x_3834_; 
lean_dec_ref(v_body_3829_);
v___x_3834_ = 1;
return v___x_3834_;
}
else
{
v_e_3827_ = v_body_3829_;
goto _start;
}
}
else
{
v_e_3827_ = v_body_3829_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3837_; 
v_body_3837_ = lean_ctor_get(v___x_3828_, 3);
lean_inc_ref(v_body_3837_);
lean_dec_ref_known(v___x_3828_, 4);
v_e_3827_ = v_body_3837_;
goto _start;
}
default: 
{
uint8_t v___x_3839_; 
lean_dec_ref(v___x_3828_);
v___x_3839_ = 0;
return v___x_3839_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object* v_e_3840_){
_start:
{
uint8_t v_res_3841_; lean_object* v_r_3842_; 
v_res_3841_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(v_e_3840_);
v_r_3842_ = lean_box(v_res_3841_);
return v_r_3842_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_cinfo_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_, lean_object* v_a_3846_, lean_object* v_a_3847_){
_start:
{
lean_object* v___x_3849_; uint8_t v___x_3850_; 
v___x_3849_ = l_Lean_ConstantInfo_type(v_cinfo_3843_);
lean_inc_ref(v___x_3849_);
v___x_3850_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(v___x_3849_);
if (v___x_3850_ == 0)
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
lean_dec_ref(v___x_3849_);
v___x_3851_ = lean_box(0);
v___x_3852_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3852_, 0, v___x_3851_);
return v___x_3852_;
}
else
{
lean_object* v___x_3853_; lean_object* v___f_3854_; uint8_t v___x_3855_; lean_object* v___x_3856_; 
v___x_3853_ = lean_box(1);
lean_inc_ref(v___x_3849_);
v___f_3854_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3854_, 0, v___x_3849_);
lean_closure_set(v___f_3854_, 1, v___x_3853_);
v___x_3855_ = 0;
v___x_3856_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v___x_3849_, v___f_3854_, v___x_3855_, v_a_3844_, v_a_3845_, v_a_3846_, v_a_3847_);
return v___x_3856_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_cinfo_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_Meta_checkImpossibleInstance(v_cinfo_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
lean_dec_ref(v_a_3858_);
lean_dec_ref(v_cinfo_3857_);
return v_res_3863_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object* v_00_u03b2_3864_, lean_object* v_k_3865_, lean_object* v_t_3866_){
_start:
{
uint8_t v___x_3867_; 
v___x_3867_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_k_3865_, v_t_3866_);
return v___x_3867_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_00_u03b2_3868_, lean_object* v_k_3869_, lean_object* v_t_3870_){
_start:
{
uint8_t v_res_3871_; lean_object* v_r_3872_; 
v_res_3871_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_00_u03b2_3868_, v_k_3869_, v_t_3870_);
lean_dec(v_t_3870_);
lean_dec(v_k_3869_);
v_r_3872_ = lean_box(v_res_3871_);
return v_r_3872_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v_a_3873_, lean_object* v_as_3874_, size_t v_sz_3875_, size_t v_i_3876_, lean_object* v_b_3877_, lean_object* v___y_3878_, lean_object* v___y_3879_, lean_object* v___y_3880_, lean_object* v___y_3881_){
_start:
{
lean_object* v___x_3883_; 
v___x_3883_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_a_3873_, v_as_3874_, v_sz_3875_, v_i_3876_, v_b_3877_, v___y_3878_, v___y_3880_, v___y_3881_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v_a_3884_, lean_object* v_as_3885_, lean_object* v_sz_3886_, lean_object* v_i_3887_, lean_object* v_b_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_, lean_object* v___y_3893_){
_start:
{
size_t v_sz_boxed_3894_; size_t v_i_boxed_3895_; lean_object* v_res_3896_; 
v_sz_boxed_3894_ = lean_unbox_usize(v_sz_3886_);
lean_dec(v_sz_3886_);
v_i_boxed_3895_ = lean_unbox_usize(v_i_3887_);
lean_dec(v_i_3887_);
v_res_3896_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1(v_a_3884_, v_as_3885_, v_sz_boxed_3894_, v_i_boxed_3895_, v_b_3888_, v___y_3889_, v___y_3890_, v___y_3891_, v___y_3892_);
lean_dec(v___y_3892_);
lean_dec_ref(v___y_3891_);
lean_dec(v___y_3890_);
lean_dec_ref(v___y_3889_);
lean_dec_ref(v_as_3885_);
lean_dec_ref(v_a_3884_);
return v_res_3896_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object* v_as_3897_, size_t v_sz_3898_, size_t v_i_3899_, lean_object* v_b_3900_, lean_object* v___y_3901_, lean_object* v___y_3902_, lean_object* v___y_3903_, lean_object* v___y_3904_, lean_object* v___y_3905_){
_start:
{
lean_object* v___x_3907_; 
v___x_3907_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(v_as_3897_, v_sz_3898_, v_i_3899_, v_b_3900_, v___y_3901_, v___y_3902_, v___y_3904_, v___y_3905_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object* v_as_3908_, lean_object* v_sz_3909_, lean_object* v_i_3910_, lean_object* v_b_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_, lean_object* v___y_3915_, lean_object* v___y_3916_, lean_object* v___y_3917_){
_start:
{
size_t v_sz_boxed_3918_; size_t v_i_boxed_3919_; lean_object* v_res_3920_; 
v_sz_boxed_3918_ = lean_unbox_usize(v_sz_3909_);
lean_dec(v_sz_3909_);
v_i_boxed_3919_ = lean_unbox_usize(v_i_3910_);
lean_dec(v_i_3910_);
v_res_3920_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3(v_as_3908_, v_sz_boxed_3918_, v_i_boxed_3919_, v_b_3911_, v___y_3912_, v___y_3913_, v___y_3914_, v___y_3915_, v___y_3916_);
lean_dec(v___y_3916_);
lean_dec_ref(v___y_3915_);
lean_dec(v___y_3914_);
lean_dec_ref(v___y_3913_);
lean_dec(v___y_3912_);
lean_dec_ref(v_as_3908_);
return v_res_3920_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3922_; lean_object* v___x_3923_; 
v___x_3922_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3923_ = l_Lean_stringToMessageData(v___x_3922_);
return v___x_3923_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3925_; lean_object* v___x_3926_; 
v___x_3925_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3926_ = l_Lean_stringToMessageData(v___x_3925_);
return v___x_3926_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; 
v___x_3928_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3929_ = l_Lean_stringToMessageData(v___x_3928_);
return v___x_3929_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_c_3930_, lean_object* v_x_3931_, lean_object* v_target_3932_, lean_object* v___y_3933_, lean_object* v___y_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v___x_3938_; 
lean_inc_ref(v_target_3932_);
v___x_3938_ = l_Lean_Meta_isClass_x3f(v_target_3932_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
if (lean_obj_tag(v___x_3938_) == 0)
{
lean_object* v_a_3939_; lean_object* v___x_3941_; uint8_t v_isShared_3942_; uint8_t v_isSharedCheck_3957_; 
v_a_3939_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3957_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3957_ == 0)
{
v___x_3941_ = v___x_3938_;
v_isShared_3942_ = v_isSharedCheck_3957_;
goto v_resetjp_3940_;
}
else
{
lean_inc(v_a_3939_);
lean_dec(v___x_3938_);
v___x_3941_ = lean_box(0);
v_isShared_3942_ = v_isSharedCheck_3957_;
goto v_resetjp_3940_;
}
v_resetjp_3940_:
{
if (lean_obj_tag(v_a_3939_) == 0)
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; lean_object* v___x_3948_; lean_object* v___x_3949_; lean_object* v___x_3950_; lean_object* v___x_3951_; lean_object* v___x_3952_; 
lean_del_object(v___x_3941_);
v___x_3943_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3944_ = l_Lean_MessageData_ofExpr(v_c_3930_);
v___x_3945_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3943_);
lean_ctor_set(v___x_3945_, 1, v___x_3944_);
v___x_3946_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3945_);
lean_ctor_set(v___x_3947_, 1, v___x_3946_);
v___x_3948_ = l_Lean_MessageData_ofExpr(v_target_3932_);
v___x_3949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3949_, 0, v___x_3947_);
lean_ctor_set(v___x_3949_, 1, v___x_3948_);
v___x_3950_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3951_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3951_, 0, v___x_3949_);
lean_ctor_set(v___x_3951_, 1, v___x_3950_);
v___x_3952_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3951_, v___y_3933_, v___y_3934_, v___y_3935_, v___y_3936_);
return v___x_3952_;
}
else
{
lean_object* v___x_3953_; lean_object* v___x_3955_; 
lean_dec_ref_known(v_a_3939_, 1);
lean_dec_ref(v_target_3932_);
lean_dec_ref(v_c_3930_);
v___x_3953_ = lean_box(0);
if (v_isShared_3942_ == 0)
{
lean_ctor_set(v___x_3941_, 0, v___x_3953_);
v___x_3955_ = v___x_3941_;
goto v_reusejp_3954_;
}
else
{
lean_object* v_reuseFailAlloc_3956_; 
v_reuseFailAlloc_3956_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3956_, 0, v___x_3953_);
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
else
{
lean_object* v_a_3958_; lean_object* v___x_3960_; uint8_t v_isShared_3961_; uint8_t v_isSharedCheck_3965_; 
lean_dec_ref(v_target_3932_);
lean_dec_ref(v_c_3930_);
v_a_3958_ = lean_ctor_get(v___x_3938_, 0);
v_isSharedCheck_3965_ = !lean_is_exclusive(v___x_3938_);
if (v_isSharedCheck_3965_ == 0)
{
v___x_3960_ = v___x_3938_;
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
else
{
lean_inc(v_a_3958_);
lean_dec(v___x_3938_);
v___x_3960_ = lean_box(0);
v_isShared_3961_ = v_isSharedCheck_3965_;
goto v_resetjp_3959_;
}
v_resetjp_3959_:
{
lean_object* v___x_3963_; 
if (v_isShared_3961_ == 0)
{
v___x_3963_ = v___x_3960_;
goto v_reusejp_3962_;
}
else
{
lean_object* v_reuseFailAlloc_3964_; 
v_reuseFailAlloc_3964_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3964_, 0, v_a_3958_);
v___x_3963_ = v_reuseFailAlloc_3964_;
goto v_reusejp_3962_;
}
v_reusejp_3962_:
{
return v___x_3963_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_c_3966_, lean_object* v_x_3967_, lean_object* v_target_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_, lean_object* v___y_3973_){
_start:
{
lean_object* v_res_3974_; 
v_res_3974_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_c_3966_, v_x_3967_, v_target_3968_, v___y_3969_, v___y_3970_, v___y_3971_, v___y_3972_);
lean_dec(v___y_3972_);
lean_dec_ref(v___y_3971_);
lean_dec(v___y_3970_);
lean_dec_ref(v___y_3969_);
lean_dec_ref(v_x_3967_);
return v_res_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_c_3975_, lean_object* v_a_3976_, lean_object* v_a_3977_, lean_object* v_a_3978_, lean_object* v_a_3979_){
_start:
{
lean_object* v___f_3981_; lean_object* v___x_3982_; 
lean_inc_ref(v_c_3975_);
v___f_3981_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3981_, 0, v_c_3975_);
lean_inc(v_a_3979_);
lean_inc_ref(v_a_3978_);
lean_inc(v_a_3977_);
lean_inc_ref(v_a_3976_);
v___x_3982_ = lean_infer_type(v_c_3975_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
if (lean_obj_tag(v___x_3982_) == 0)
{
lean_object* v_a_3983_; uint8_t v___x_3984_; lean_object* v___x_3985_; 
v_a_3983_ = lean_ctor_get(v___x_3982_, 0);
lean_inc(v_a_3983_);
lean_dec_ref_known(v___x_3982_, 1);
v___x_3984_ = 0;
v___x_3985_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3983_, v___f_3981_, v___x_3984_, v___x_3984_, v_a_3976_, v_a_3977_, v_a_3978_, v_a_3979_);
return v___x_3985_;
}
else
{
lean_object* v_a_3986_; lean_object* v___x_3988_; uint8_t v_isShared_3989_; uint8_t v_isSharedCheck_3993_; 
lean_dec_ref(v___f_3981_);
v_a_3986_ = lean_ctor_get(v___x_3982_, 0);
v_isSharedCheck_3993_ = !lean_is_exclusive(v___x_3982_);
if (v_isSharedCheck_3993_ == 0)
{
v___x_3988_ = v___x_3982_;
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
else
{
lean_inc(v_a_3986_);
lean_dec(v___x_3982_);
v___x_3988_ = lean_box(0);
v_isShared_3989_ = v_isSharedCheck_3993_;
goto v_resetjp_3987_;
}
v_resetjp_3987_:
{
lean_object* v___x_3991_; 
if (v_isShared_3989_ == 0)
{
v___x_3991_ = v___x_3988_;
goto v_reusejp_3990_;
}
else
{
lean_object* v_reuseFailAlloc_3992_; 
v_reuseFailAlloc_3992_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3992_, 0, v_a_3986_);
v___x_3991_ = v_reuseFailAlloc_3992_;
goto v_reusejp_3990_;
}
v_reusejp_3990_:
{
return v___x_3991_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_c_3994_, lean_object* v_a_3995_, lean_object* v_a_3996_, lean_object* v_a_3997_, lean_object* v_a_3998_, lean_object* v_a_3999_){
_start:
{
lean_object* v_res_4000_; 
v_res_4000_ = l_Lean_Meta_checkNonClassInstance(v_c_3994_, v_a_3995_, v_a_3996_, v_a_3997_, v_a_3998_);
lean_dec(v_a_3998_);
lean_dec_ref(v_a_3997_);
lean_dec(v_a_3996_);
lean_dec_ref(v_a_3995_);
return v_res_4000_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v___x_4014_; lean_object* v_env_4015_; lean_object* v___x_4016_; lean_object* v___x_4017_; 
v___x_4014_ = lean_st_ref_get(v___y_4012_);
v_env_4015_ = lean_ctor_get(v___x_4014_, 0);
lean_inc_ref(v_env_4015_);
lean_dec(v___x_4014_);
v___x_4016_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_4015_, v_declName_4011_);
v___x_4017_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4017_, 0, v___x_4016_);
return v___x_4017_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_){
_start:
{
lean_object* v_res_4021_; 
v_res_4021_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4018_, v___y_4019_);
lean_dec(v___y_4019_);
return v_res_4021_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_4022_, lean_object* v___y_4023_, lean_object* v___y_4024_, lean_object* v___y_4025_, lean_object* v___y_4026_){
_start:
{
lean_object* v___x_4028_; 
v___x_4028_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4022_, v___y_4026_);
return v___x_4028_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_4029_, lean_object* v___y_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_){
_start:
{
lean_object* v_res_4035_; 
v_res_4035_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_4029_, v___y_4030_, v___y_4031_, v___y_4032_, v___y_4033_);
lean_dec(v___y_4033_);
lean_dec_ref(v___y_4032_);
lean_dec(v___y_4031_);
lean_dec_ref(v___y_4030_);
return v_res_4035_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_4036_; lean_object* v___x_4037_; 
v___x_4036_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4037_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4037_, 0, v___x_4036_);
return v___x_4037_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_4038_; lean_object* v___x_4039_; 
v___x_4038_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_4039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4039_, 0, v___x_4038_);
lean_ctor_set(v___x_4039_, 1, v___x_4038_);
return v___x_4039_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_4040_; lean_object* v___x_4041_; 
v___x_4040_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_4041_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4041_, 0, v___x_4040_);
lean_ctor_set(v___x_4041_, 1, v___x_4040_);
lean_ctor_set(v___x_4041_, 2, v___x_4040_);
lean_ctor_set(v___x_4041_, 3, v___x_4040_);
lean_ctor_set(v___x_4041_, 4, v___x_4040_);
lean_ctor_set(v___x_4041_, 5, v___x_4040_);
return v___x_4041_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_4042_, lean_object* v_b_4043_, uint8_t v_kind_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_, lean_object* v___y_4047_){
_start:
{
lean_object* v_toCold_4049_; lean_object* v_currNamespace_4050_; lean_object* v___x_4051_; lean_object* v_env_4052_; lean_object* v_nextMacroScope_4053_; lean_object* v_ngen_4054_; lean_object* v_auxDeclNGen_4055_; lean_object* v_traceState_4056_; lean_object* v_recordedDeps_4057_; lean_object* v_messages_4058_; lean_object* v_infoState_4059_; lean_object* v_snapshotTasks_4060_; lean_object* v___x_4062_; uint8_t v_isShared_4063_; uint8_t v_isSharedCheck_4087_; 
v_toCold_4049_ = lean_ctor_get(v___y_4046_, 0);
v_currNamespace_4050_ = lean_ctor_get(v_toCold_4049_, 4);
v___x_4051_ = lean_st_ref_take(v___y_4047_);
v_env_4052_ = lean_ctor_get(v___x_4051_, 0);
v_nextMacroScope_4053_ = lean_ctor_get(v___x_4051_, 1);
v_ngen_4054_ = lean_ctor_get(v___x_4051_, 2);
v_auxDeclNGen_4055_ = lean_ctor_get(v___x_4051_, 3);
v_traceState_4056_ = lean_ctor_get(v___x_4051_, 4);
v_recordedDeps_4057_ = lean_ctor_get(v___x_4051_, 6);
v_messages_4058_ = lean_ctor_get(v___x_4051_, 7);
v_infoState_4059_ = lean_ctor_get(v___x_4051_, 8);
v_snapshotTasks_4060_ = lean_ctor_get(v___x_4051_, 9);
v_isSharedCheck_4087_ = !lean_is_exclusive(v___x_4051_);
if (v_isSharedCheck_4087_ == 0)
{
lean_object* v_unused_4088_; 
v_unused_4088_ = lean_ctor_get(v___x_4051_, 5);
lean_dec(v_unused_4088_);
v___x_4062_ = v___x_4051_;
v_isShared_4063_ = v_isSharedCheck_4087_;
goto v_resetjp_4061_;
}
else
{
lean_inc(v_snapshotTasks_4060_);
lean_inc(v_infoState_4059_);
lean_inc(v_messages_4058_);
lean_inc(v_recordedDeps_4057_);
lean_inc(v_traceState_4056_);
lean_inc(v_auxDeclNGen_4055_);
lean_inc(v_ngen_4054_);
lean_inc(v_nextMacroScope_4053_);
lean_inc(v_env_4052_);
lean_dec(v___x_4051_);
v___x_4062_ = lean_box(0);
v_isShared_4063_ = v_isSharedCheck_4087_;
goto v_resetjp_4061_;
}
v_resetjp_4061_:
{
lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4067_; 
lean_inc(v_currNamespace_4050_);
v___x_4064_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_4052_, v_ext_4042_, v_b_4043_, v_kind_4044_, v_currNamespace_4050_);
v___x_4065_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_4063_ == 0)
{
lean_ctor_set(v___x_4062_, 5, v___x_4065_);
lean_ctor_set(v___x_4062_, 0, v___x_4064_);
v___x_4067_ = v___x_4062_;
goto v_reusejp_4066_;
}
else
{
lean_object* v_reuseFailAlloc_4086_; 
v_reuseFailAlloc_4086_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4086_, 0, v___x_4064_);
lean_ctor_set(v_reuseFailAlloc_4086_, 1, v_nextMacroScope_4053_);
lean_ctor_set(v_reuseFailAlloc_4086_, 2, v_ngen_4054_);
lean_ctor_set(v_reuseFailAlloc_4086_, 3, v_auxDeclNGen_4055_);
lean_ctor_set(v_reuseFailAlloc_4086_, 4, v_traceState_4056_);
lean_ctor_set(v_reuseFailAlloc_4086_, 5, v___x_4065_);
lean_ctor_set(v_reuseFailAlloc_4086_, 6, v_recordedDeps_4057_);
lean_ctor_set(v_reuseFailAlloc_4086_, 7, v_messages_4058_);
lean_ctor_set(v_reuseFailAlloc_4086_, 8, v_infoState_4059_);
lean_ctor_set(v_reuseFailAlloc_4086_, 9, v_snapshotTasks_4060_);
v___x_4067_ = v_reuseFailAlloc_4086_;
goto v_reusejp_4066_;
}
v_reusejp_4066_:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; lean_object* v_mctx_4070_; lean_object* v_zetaDeltaFVarIds_4071_; lean_object* v_postponed_4072_; lean_object* v_diag_4073_; lean_object* v___x_4075_; uint8_t v_isShared_4076_; uint8_t v_isSharedCheck_4084_; 
v___x_4068_ = lean_st_ref_put(v___y_4047_, v___x_4067_);
v___x_4069_ = lean_st_ref_take(v___y_4045_);
v_mctx_4070_ = lean_ctor_get(v___x_4069_, 0);
v_zetaDeltaFVarIds_4071_ = lean_ctor_get(v___x_4069_, 2);
v_postponed_4072_ = lean_ctor_get(v___x_4069_, 3);
v_diag_4073_ = lean_ctor_get(v___x_4069_, 4);
v_isSharedCheck_4084_ = !lean_is_exclusive(v___x_4069_);
if (v_isSharedCheck_4084_ == 0)
{
lean_object* v_unused_4085_; 
v_unused_4085_ = lean_ctor_get(v___x_4069_, 1);
lean_dec(v_unused_4085_);
v___x_4075_ = v___x_4069_;
v_isShared_4076_ = v_isSharedCheck_4084_;
goto v_resetjp_4074_;
}
else
{
lean_inc(v_diag_4073_);
lean_inc(v_postponed_4072_);
lean_inc(v_zetaDeltaFVarIds_4071_);
lean_inc(v_mctx_4070_);
lean_dec(v___x_4069_);
v___x_4075_ = lean_box(0);
v_isShared_4076_ = v_isSharedCheck_4084_;
goto v_resetjp_4074_;
}
v_resetjp_4074_:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; lean_object* v___x_4080_; 
v___x_4077_ = lean_box(0);
v___x_4078_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4076_ == 0)
{
lean_ctor_set(v___x_4075_, 1, v___x_4078_);
v___x_4080_ = v___x_4075_;
goto v_reusejp_4079_;
}
else
{
lean_object* v_reuseFailAlloc_4083_; 
v_reuseFailAlloc_4083_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4083_, 0, v_mctx_4070_);
lean_ctor_set(v_reuseFailAlloc_4083_, 1, v___x_4078_);
lean_ctor_set(v_reuseFailAlloc_4083_, 2, v_zetaDeltaFVarIds_4071_);
lean_ctor_set(v_reuseFailAlloc_4083_, 3, v_postponed_4072_);
lean_ctor_set(v_reuseFailAlloc_4083_, 4, v_diag_4073_);
v___x_4080_ = v_reuseFailAlloc_4083_;
goto v_reusejp_4079_;
}
v_reusejp_4079_:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = lean_st_ref_put(v___y_4045_, v___x_4080_);
v___x_4082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4082_, 0, v___x_4077_);
return v___x_4082_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_4089_, lean_object* v_b_4090_, lean_object* v_kind_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_){
_start:
{
uint8_t v_kind_boxed_4096_; lean_object* v_res_4097_; 
v_kind_boxed_4096_ = lean_unbox(v_kind_4091_);
v_res_4097_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_4089_, v_b_4090_, v_kind_boxed_4096_, v___y_4092_, v___y_4093_, v___y_4094_);
lean_dec(v___y_4094_);
lean_dec_ref(v___y_4093_);
lean_dec(v___y_4092_);
return v_res_4097_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_4098_, lean_object* v_00_u03b2_4099_, lean_object* v_00_u03c3_4100_, lean_object* v_ext_4101_, lean_object* v_b_4102_, uint8_t v_kind_4103_, lean_object* v___y_4104_, lean_object* v___y_4105_, lean_object* v___y_4106_, lean_object* v___y_4107_){
_start:
{
lean_object* v___x_4109_; 
v___x_4109_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_4101_, v_b_4102_, v_kind_4103_, v___y_4105_, v___y_4106_, v___y_4107_);
return v___x_4109_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_4110_, lean_object* v_00_u03b2_4111_, lean_object* v_00_u03c3_4112_, lean_object* v_ext_4113_, lean_object* v_b_4114_, lean_object* v_kind_4115_, lean_object* v___y_4116_, lean_object* v___y_4117_, lean_object* v___y_4118_, lean_object* v___y_4119_, lean_object* v___y_4120_){
_start:
{
uint8_t v_kind_boxed_4121_; lean_object* v_res_4122_; 
v_kind_boxed_4121_ = lean_unbox(v_kind_4115_);
v_res_4122_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_4110_, v_00_u03b2_4111_, v_00_u03c3_4112_, v_ext_4113_, v_b_4114_, v_kind_boxed_4121_, v___y_4116_, v___y_4117_, v___y_4118_, v___y_4119_);
lean_dec(v___y_4119_);
lean_dec_ref(v___y_4118_);
lean_dec(v___y_4117_);
lean_dec_ref(v___y_4116_);
return v_res_4122_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_4123_, lean_object* v___y_4124_){
_start:
{
lean_object* v___x_4126_; lean_object* v_env_4127_; uint8_t v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; 
v___x_4126_ = lean_st_ref_get(v___y_4124_);
v_env_4127_ = lean_ctor_get(v___x_4126_, 0);
lean_inc_ref(v_env_4127_);
lean_dec(v___x_4126_);
v___x_4128_ = l_Lean_getReducibilityStatusCore(v_env_4127_, v_declName_4123_);
v___x_4129_ = lean_box(v___x_4128_);
v___x_4130_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4129_);
return v___x_4130_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_4131_, lean_object* v___y_4132_, lean_object* v___y_4133_){
_start:
{
lean_object* v_res_4134_; 
v_res_4134_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4131_, v___y_4132_);
lean_dec(v___y_4132_);
return v_res_4134_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_4135_, lean_object* v___y_4136_, lean_object* v___y_4137_, lean_object* v___y_4138_, lean_object* v___y_4139_){
_start:
{
lean_object* v___x_4141_; 
v___x_4141_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4135_, v___y_4139_);
return v___x_4141_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_4142_, lean_object* v___y_4143_, lean_object* v___y_4144_, lean_object* v___y_4145_, lean_object* v___y_4146_, lean_object* v___y_4147_){
_start:
{
lean_object* v_res_4148_; 
v_res_4148_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_4142_, v___y_4143_, v___y_4144_, v___y_4145_, v___y_4146_);
lean_dec(v___y_4146_);
lean_dec_ref(v___y_4145_);
lean_dec(v___y_4144_);
lean_dec_ref(v___y_4143_);
return v_res_4148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_4149_, lean_object* v_msg_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v_toCold_4156_; lean_object* v_currRecDepth_4157_; lean_object* v_ref_4158_; uint16_t v_optionFlags_4159_; uint8_t v_suppressElabErrors_4160_; uint8_t v_isRecordingDeps_4161_; lean_object* v_ref_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
v_toCold_4156_ = lean_ctor_get(v___y_4153_, 0);
v_currRecDepth_4157_ = lean_ctor_get(v___y_4153_, 1);
v_ref_4158_ = lean_ctor_get(v___y_4153_, 2);
v_optionFlags_4159_ = lean_ctor_get_uint16(v___y_4153_, sizeof(void*)*3);
v_suppressElabErrors_4160_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*3 + 2);
v_isRecordingDeps_4161_ = lean_ctor_get_uint8(v___y_4153_, sizeof(void*)*3 + 3);
v_ref_4162_ = l_Lean_replaceRef(v_ref_4149_, v_ref_4158_);
lean_inc(v_currRecDepth_4157_);
lean_inc_ref(v_toCold_4156_);
v___x_4163_ = lean_alloc_ctor(0, 3, 4);
lean_ctor_set(v___x_4163_, 0, v_toCold_4156_);
lean_ctor_set(v___x_4163_, 1, v_currRecDepth_4157_);
lean_ctor_set(v___x_4163_, 2, v_ref_4162_);
lean_ctor_set_uint16(v___x_4163_, sizeof(void*)*3, v_optionFlags_4159_);
lean_ctor_set_uint8(v___x_4163_, sizeof(void*)*3 + 2, v_suppressElabErrors_4160_);
lean_ctor_set_uint8(v___x_4163_, sizeof(void*)*3 + 3, v_isRecordingDeps_4161_);
v___x_4164_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_4150_, v___y_4151_, v___y_4152_, v___x_4163_, v___y_4154_);
lean_dec_ref_known(v___x_4163_, 3);
return v___x_4164_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_4165_, lean_object* v_msg_4166_, lean_object* v___y_4167_, lean_object* v___y_4168_, lean_object* v___y_4169_, lean_object* v___y_4170_, lean_object* v___y_4171_){
_start:
{
lean_object* v_res_4172_; 
v_res_4172_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4165_, v_msg_4166_, v___y_4167_, v___y_4168_, v___y_4169_, v___y_4170_);
lean_dec(v___y_4170_);
lean_dec_ref(v___y_4169_);
lean_dec(v___y_4168_);
lean_dec_ref(v___y_4167_);
lean_dec(v_ref_4165_);
return v_res_4172_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_4173_; lean_object* v___x_4174_; 
v___x_4173_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4174_, 0, v___x_4173_);
return v___x_4174_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; 
v___x_4175_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4176_ = lean_unsigned_to_nat(0u);
v___x_4177_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4176_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
lean_ctor_set(v___x_4177_, 2, v___x_4176_);
lean_ctor_set(v___x_4177_, 3, v___x_4176_);
lean_ctor_set(v___x_4177_, 4, v___x_4175_);
lean_ctor_set(v___x_4177_, 5, v___x_4175_);
lean_ctor_set(v___x_4177_, 6, v___x_4175_);
lean_ctor_set(v___x_4177_, 7, v___x_4175_);
lean_ctor_set(v___x_4177_, 8, v___x_4175_);
lean_ctor_set(v___x_4177_, 9, v___x_4175_);
lean_ctor_set(v___x_4177_, 10, v___x_4175_);
return v___x_4177_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; 
v___x_4178_ = lean_unsigned_to_nat(32u);
v___x_4179_ = lean_mk_empty_array_with_capacity(v___x_4178_);
v___x_4180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4180_, 0, v___x_4179_);
return v___x_4180_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
size_t v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4184_; lean_object* v___x_4185_; lean_object* v___x_4186_; 
v___x_4181_ = ((size_t)5ULL);
v___x_4182_ = lean_unsigned_to_nat(0u);
v___x_4183_ = lean_unsigned_to_nat(32u);
v___x_4184_ = lean_mk_empty_array_with_capacity(v___x_4183_);
v___x_4185_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4186_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4186_, 0, v___x_4185_);
lean_ctor_set(v___x_4186_, 1, v___x_4184_);
lean_ctor_set(v___x_4186_, 2, v___x_4182_);
lean_ctor_set(v___x_4186_, 3, v___x_4182_);
lean_ctor_set_usize(v___x_4186_, 4, v___x_4181_);
return v___x_4186_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; 
v___x_4187_ = lean_box(1);
v___x_4188_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4189_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4190_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4189_);
lean_ctor_set(v___x_4190_, 1, v___x_4188_);
lean_ctor_set(v___x_4190_, 2, v___x_4187_);
return v___x_4190_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_4192_; lean_object* v___x_4193_; 
v___x_4192_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5));
v___x_4193_ = l_Lean_stringToMessageData(v___x_4192_);
return v___x_4193_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_4195_; lean_object* v___x_4196_; 
v___x_4195_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7));
v___x_4196_ = l_Lean_stringToMessageData(v___x_4195_);
return v___x_4196_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10(void){
_start:
{
lean_object* v___x_4198_; lean_object* v___x_4199_; 
v___x_4198_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9));
v___x_4199_ = l_Lean_stringToMessageData(v___x_4198_);
return v___x_4199_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12(void){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4201_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11));
v___x_4202_ = l_Lean_stringToMessageData(v___x_4201_);
return v___x_4202_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14(void){
_start:
{
lean_object* v___x_4204_; lean_object* v___x_4205_; 
v___x_4204_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13));
v___x_4205_ = l_Lean_stringToMessageData(v___x_4204_);
return v___x_4205_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16(void){
_start:
{
lean_object* v___x_4207_; lean_object* v___x_4208_; 
v___x_4207_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15));
v___x_4208_ = l_Lean_stringToMessageData(v___x_4207_);
return v___x_4208_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18(void){
_start:
{
lean_object* v___x_4210_; lean_object* v___x_4211_; 
v___x_4210_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17));
v___x_4211_ = l_Lean_stringToMessageData(v___x_4210_);
return v___x_4211_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_4212_, lean_object* v_declHint_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v_env_4218_; uint8_t v___x_4219_; 
v___x_4216_ = lean_box(0);
v___x_4217_ = lean_st_ref_get(v___y_4214_);
v_env_4218_ = lean_ctor_get(v___x_4217_, 0);
lean_inc_ref(v_env_4218_);
lean_dec(v___x_4217_);
v___x_4219_ = l_Lean_Name_isAnonymous(v_declHint_4213_);
if (v___x_4219_ == 0)
{
uint8_t v_isExporting_4220_; 
v_isExporting_4220_ = lean_ctor_get_uint8(v_env_4218_, sizeof(void*)*8);
if (v_isExporting_4220_ == 0)
{
lean_object* v___x_4221_; 
lean_dec_ref(v_env_4218_);
lean_dec(v_declHint_4213_);
v___x_4221_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4221_, 0, v_msg_4212_);
return v___x_4221_;
}
else
{
lean_object* v___x_4222_; uint8_t v___x_4223_; 
lean_inc_ref(v_env_4218_);
v___x_4222_ = l_Lean_Environment_setExporting(v_env_4218_, v___x_4219_);
lean_inc(v_declHint_4213_);
lean_inc_ref(v___x_4222_);
v___x_4223_ = l_Lean_Environment_contains(v___x_4222_, v_declHint_4213_, v_isExporting_4220_);
if (v___x_4223_ == 0)
{
lean_object* v___x_4224_; 
lean_dec_ref(v___x_4222_);
lean_dec_ref(v_env_4218_);
lean_dec(v_declHint_4213_);
v___x_4224_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4224_, 0, v_msg_4212_);
return v___x_4224_;
}
else
{
lean_object* v___x_4225_; lean_object* v___x_4226_; lean_object* v___x_4227_; lean_object* v___x_4228_; lean_object* v___x_4229_; lean_object* v_c_4230_; lean_object* v___x_4231_; 
v___x_4225_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4226_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_4227_ = l_Lean_Options_empty;
v___x_4228_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4228_, 0, v___x_4222_);
lean_ctor_set(v___x_4228_, 1, v___x_4225_);
lean_ctor_set(v___x_4228_, 2, v___x_4226_);
lean_ctor_set(v___x_4228_, 3, v___x_4227_);
lean_inc(v_declHint_4213_);
v___x_4229_ = l_Lean_MessageData_ofConstName(v_declHint_4213_, v___x_4219_);
v_c_4230_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4230_, 0, v___x_4228_);
lean_ctor_set(v_c_4230_, 1, v___x_4229_);
v___x_4231_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4218_, v_declHint_4213_);
if (lean_obj_tag(v___x_4231_) == 0)
{
lean_object* v___x_4232_; lean_object* v___x_4233_; lean_object* v___x_4234_; lean_object* v___x_4235_; lean_object* v___x_4236_; lean_object* v___x_4237_; lean_object* v___x_4238_; 
lean_dec_ref(v_env_4218_);
lean_dec(v_declHint_4213_);
v___x_4232_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6);
v___x_4233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4233_, 0, v___x_4232_);
lean_ctor_set(v___x_4233_, 1, v_c_4230_);
v___x_4234_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8);
v___x_4235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4235_, 0, v___x_4233_);
lean_ctor_set(v___x_4235_, 1, v___x_4234_);
v___x_4236_ = l_Lean_MessageData_note(v___x_4235_);
v___x_4237_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4237_, 0, v_msg_4212_);
lean_ctor_set(v___x_4237_, 1, v___x_4236_);
v___x_4238_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4238_, 0, v___x_4237_);
return v___x_4238_;
}
else
{
lean_object* v_val_4239_; lean_object* v___x_4241_; uint8_t v_isShared_4242_; uint8_t v_isSharedCheck_4273_; 
v_val_4239_ = lean_ctor_get(v___x_4231_, 0);
v_isSharedCheck_4273_ = !lean_is_exclusive(v___x_4231_);
if (v_isSharedCheck_4273_ == 0)
{
v___x_4241_ = v___x_4231_;
v_isShared_4242_ = v_isSharedCheck_4273_;
goto v_resetjp_4240_;
}
else
{
lean_inc(v_val_4239_);
lean_dec(v___x_4231_);
v___x_4241_ = lean_box(0);
v_isShared_4242_ = v_isSharedCheck_4273_;
goto v_resetjp_4240_;
}
v_resetjp_4240_:
{
lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v_mod_4245_; uint8_t v___x_4246_; 
v___x_4243_ = l_Lean_Environment_header(v_env_4218_);
lean_dec_ref(v_env_4218_);
v___x_4244_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4243_);
v_mod_4245_ = lean_array_get(v___x_4216_, v___x_4244_, v_val_4239_);
lean_dec(v_val_4239_);
lean_dec_ref(v___x_4244_);
v___x_4246_ = l_Lean_isPrivateName(v_declHint_4213_);
lean_dec(v_declHint_4213_);
if (v___x_4246_ == 0)
{
lean_object* v___x_4247_; lean_object* v___x_4248_; lean_object* v___x_4249_; lean_object* v___x_4250_; lean_object* v___x_4251_; lean_object* v___x_4252_; lean_object* v___x_4253_; lean_object* v___x_4254_; lean_object* v___x_4255_; lean_object* v___x_4256_; lean_object* v___x_4258_; 
v___x_4247_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10);
v___x_4248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4248_, 0, v___x_4247_);
lean_ctor_set(v___x_4248_, 1, v_c_4230_);
v___x_4249_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12);
v___x_4250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4250_, 0, v___x_4248_);
lean_ctor_set(v___x_4250_, 1, v___x_4249_);
v___x_4251_ = l_Lean_MessageData_ofName(v_mod_4245_);
v___x_4252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4252_, 0, v___x_4250_);
lean_ctor_set(v___x_4252_, 1, v___x_4251_);
v___x_4253_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14);
v___x_4254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4254_, 0, v___x_4252_);
lean_ctor_set(v___x_4254_, 1, v___x_4253_);
v___x_4255_ = l_Lean_MessageData_note(v___x_4254_);
v___x_4256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4256_, 0, v_msg_4212_);
lean_ctor_set(v___x_4256_, 1, v___x_4255_);
if (v_isShared_4242_ == 0)
{
lean_ctor_set_tag(v___x_4241_, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4256_);
v___x_4258_ = v___x_4241_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v___x_4256_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
else
{
lean_object* v___x_4260_; lean_object* v___x_4261_; lean_object* v___x_4262_; lean_object* v___x_4263_; lean_object* v___x_4264_; lean_object* v___x_4265_; lean_object* v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4271_; 
v___x_4260_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6);
v___x_4261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4261_, 0, v___x_4260_);
lean_ctor_set(v___x_4261_, 1, v_c_4230_);
v___x_4262_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16);
v___x_4263_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4263_, 0, v___x_4261_);
lean_ctor_set(v___x_4263_, 1, v___x_4262_);
v___x_4264_ = l_Lean_MessageData_ofName(v_mod_4245_);
v___x_4265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4265_, 0, v___x_4263_);
lean_ctor_set(v___x_4265_, 1, v___x_4264_);
v___x_4266_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18);
v___x_4267_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4267_, 0, v___x_4265_);
lean_ctor_set(v___x_4267_, 1, v___x_4266_);
v___x_4268_ = l_Lean_MessageData_note(v___x_4267_);
v___x_4269_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4269_, 0, v_msg_4212_);
lean_ctor_set(v___x_4269_, 1, v___x_4268_);
if (v_isShared_4242_ == 0)
{
lean_ctor_set_tag(v___x_4241_, 0);
lean_ctor_set(v___x_4241_, 0, v___x_4269_);
v___x_4271_ = v___x_4241_;
goto v_reusejp_4270_;
}
else
{
lean_object* v_reuseFailAlloc_4272_; 
v_reuseFailAlloc_4272_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4272_, 0, v___x_4269_);
v___x_4271_ = v_reuseFailAlloc_4272_;
goto v_reusejp_4270_;
}
v_reusejp_4270_:
{
return v___x_4271_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4274_; 
lean_dec_ref(v_env_4218_);
lean_dec(v_declHint_4213_);
v___x_4274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4274_, 0, v_msg_4212_);
return v___x_4274_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_4275_, lean_object* v_declHint_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4275_, v_declHint_4276_, v___y_4277_);
lean_dec(v___y_4277_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(lean_object* v_msg_4280_, lean_object* v_declHint_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_, lean_object* v___y_4285_){
_start:
{
lean_object* v___x_4287_; lean_object* v_a_4288_; lean_object* v___x_4290_; uint8_t v_isShared_4291_; uint8_t v_isSharedCheck_4297_; 
v___x_4287_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4280_, v_declHint_4281_, v___y_4285_);
v_a_4288_ = lean_ctor_get(v___x_4287_, 0);
v_isSharedCheck_4297_ = !lean_is_exclusive(v___x_4287_);
if (v_isSharedCheck_4297_ == 0)
{
v___x_4290_ = v___x_4287_;
v_isShared_4291_ = v_isSharedCheck_4297_;
goto v_resetjp_4289_;
}
else
{
lean_inc(v_a_4288_);
lean_dec(v___x_4287_);
v___x_4290_ = lean_box(0);
v_isShared_4291_ = v_isSharedCheck_4297_;
goto v_resetjp_4289_;
}
v_resetjp_4289_:
{
lean_object* v___x_4292_; lean_object* v___x_4293_; lean_object* v___x_4295_; 
v___x_4292_ = l_Lean_unknownIdentifierMessageTag;
v___x_4293_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4293_, 0, v___x_4292_);
lean_ctor_set(v___x_4293_, 1, v_a_4288_);
if (v_isShared_4291_ == 0)
{
lean_ctor_set(v___x_4290_, 0, v___x_4293_);
v___x_4295_ = v___x_4290_;
goto v_reusejp_4294_;
}
else
{
lean_object* v_reuseFailAlloc_4296_; 
v_reuseFailAlloc_4296_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4296_, 0, v___x_4293_);
v___x_4295_ = v_reuseFailAlloc_4296_;
goto v_reusejp_4294_;
}
v_reusejp_4294_:
{
return v___x_4295_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_4298_, lean_object* v_declHint_4299_, lean_object* v___y_4300_, lean_object* v___y_4301_, lean_object* v___y_4302_, lean_object* v___y_4303_, lean_object* v___y_4304_){
_start:
{
lean_object* v_res_4305_; 
v_res_4305_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4298_, v_declHint_4299_, v___y_4300_, v___y_4301_, v___y_4302_, v___y_4303_);
lean_dec(v___y_4303_);
lean_dec_ref(v___y_4302_);
lean_dec(v___y_4301_);
lean_dec_ref(v___y_4300_);
return v_res_4305_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_ref_4306_, lean_object* v_msg_4307_, lean_object* v_declHint_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___x_4314_; lean_object* v_a_4315_; lean_object* v___x_4316_; 
v___x_4314_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4307_, v_declHint_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
lean_inc(v_a_4315_);
lean_dec_ref(v___x_4314_);
v___x_4316_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4306_, v_a_4315_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
return v___x_4316_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_ref_4317_, lean_object* v_msg_4318_, lean_object* v_declHint_4319_, lean_object* v___y_4320_, lean_object* v___y_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_){
_start:
{
lean_object* v_res_4325_; 
v_res_4325_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4317_, v_msg_4318_, v_declHint_4319_, v___y_4320_, v___y_4321_, v___y_4322_, v___y_4323_);
lean_dec(v___y_4323_);
lean_dec_ref(v___y_4322_);
lean_dec(v___y_4321_);
lean_dec_ref(v___y_4320_);
lean_dec(v_ref_4317_);
return v_res_4325_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_4327_; lean_object* v___x_4328_; 
v___x_4327_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_4328_ = l_Lean_stringToMessageData(v___x_4327_);
return v___x_4328_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_4329_, lean_object* v_constName_4330_, lean_object* v___y_4331_, lean_object* v___y_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_){
_start:
{
lean_object* v___x_4336_; uint8_t v___x_4337_; lean_object* v___x_4338_; lean_object* v___x_4339_; lean_object* v___x_4340_; lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4336_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_4337_ = 0;
lean_inc(v_constName_4330_);
v___x_4338_ = l_Lean_MessageData_ofConstName(v_constName_4330_, v___x_4337_);
v___x_4339_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4339_, 0, v___x_4336_);
lean_ctor_set(v___x_4339_, 1, v___x_4338_);
v___x_4340_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4341_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4341_, 0, v___x_4339_);
lean_ctor_set(v___x_4341_, 1, v___x_4340_);
v___x_4342_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4329_, v___x_4341_, v_constName_4330_, v___y_4331_, v___y_4332_, v___y_4333_, v___y_4334_);
return v___x_4342_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_4343_, lean_object* v_constName_4344_, lean_object* v___y_4345_, lean_object* v___y_4346_, lean_object* v___y_4347_, lean_object* v___y_4348_, lean_object* v___y_4349_){
_start:
{
lean_object* v_res_4350_; 
v_res_4350_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4343_, v_constName_4344_, v___y_4345_, v___y_4346_, v___y_4347_, v___y_4348_);
lean_dec(v___y_4348_);
lean_dec_ref(v___y_4347_);
lean_dec(v___y_4346_);
lean_dec_ref(v___y_4345_);
lean_dec(v_ref_4343_);
return v_res_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_4351_, lean_object* v___y_4352_, lean_object* v___y_4353_, lean_object* v___y_4354_, lean_object* v___y_4355_){
_start:
{
lean_object* v_ref_4357_; lean_object* v___x_4358_; 
v_ref_4357_ = lean_ctor_get(v___y_4354_, 2);
v___x_4358_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4357_, v_constName_4351_, v___y_4352_, v___y_4353_, v___y_4354_, v___y_4355_);
return v___x_4358_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_4359_, lean_object* v___y_4360_, lean_object* v___y_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_){
_start:
{
lean_object* v_res_4365_; 
v_res_4365_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4359_, v___y_4360_, v___y_4361_, v___y_4362_, v___y_4363_);
lean_dec(v___y_4363_);
lean_dec_ref(v___y_4362_);
lean_dec(v___y_4361_);
lean_dec_ref(v___y_4360_);
return v_res_4365_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_, lean_object* v___y_4369_, lean_object* v___y_4370_){
_start:
{
lean_object* v___x_4372_; lean_object* v_env_4373_; uint8_t v___x_4374_; lean_object* v___x_4375_; 
v___x_4372_ = lean_st_ref_get(v___y_4370_);
v_env_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc_ref(v_env_4373_);
lean_dec(v___x_4372_);
v___x_4374_ = 0;
lean_inc(v_constName_4366_);
v___x_4375_ = l_Lean_Environment_find_x3f(v_env_4373_, v_constName_4366_, v___x_4374_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v___x_4376_; 
v___x_4376_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4366_, v___y_4367_, v___y_4368_, v___y_4369_, v___y_4370_);
return v___x_4376_;
}
else
{
lean_object* v_val_4377_; lean_object* v___x_4379_; uint8_t v_isShared_4380_; uint8_t v_isSharedCheck_4384_; 
lean_dec(v_constName_4366_);
v_val_4377_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4384_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4384_ == 0)
{
v___x_4379_ = v___x_4375_;
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
else
{
lean_inc(v_val_4377_);
lean_dec(v___x_4375_);
v___x_4379_ = lean_box(0);
v_isShared_4380_ = v_isSharedCheck_4384_;
goto v_resetjp_4378_;
}
v_resetjp_4378_:
{
lean_object* v___x_4382_; 
if (v_isShared_4380_ == 0)
{
lean_ctor_set_tag(v___x_4379_, 0);
v___x_4382_ = v___x_4379_;
goto v_reusejp_4381_;
}
else
{
lean_object* v_reuseFailAlloc_4383_; 
v_reuseFailAlloc_4383_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4383_, 0, v_val_4377_);
v___x_4382_ = v_reuseFailAlloc_4383_;
goto v_reusejp_4381_;
}
v_reusejp_4381_:
{
return v___x_4382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_4385_, lean_object* v___y_4386_, lean_object* v___y_4387_, lean_object* v___y_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_){
_start:
{
lean_object* v_res_4391_; 
v_res_4391_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_4385_, v___y_4386_, v___y_4387_, v___y_4388_, v___y_4389_);
lean_dec(v___y_4389_);
lean_dec_ref(v___y_4388_);
lean_dec(v___y_4387_);
lean_dec_ref(v___y_4386_);
return v_res_4391_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4392_, lean_object* v___y_4393_, lean_object* v___y_4394_, lean_object* v___y_4395_, lean_object* v___y_4396_){
_start:
{
lean_object* v___x_4398_; lean_object* v_env_4399_; uint8_t v___x_4400_; lean_object* v___x_4401_; 
v___x_4398_ = lean_st_ref_get(v___y_4396_);
v_env_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc_ref(v_env_4399_);
lean_dec(v___x_4398_);
v___x_4400_ = 0;
lean_inc(v_constName_4392_);
v___x_4401_ = l_Lean_Environment_findConstVal_x3f(v_env_4399_, v_constName_4392_, v___x_4400_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v___x_4402_; 
v___x_4402_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4392_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
return v___x_4402_;
}
else
{
lean_object* v_val_4403_; lean_object* v___x_4405_; uint8_t v_isShared_4406_; uint8_t v_isSharedCheck_4410_; 
lean_dec(v_constName_4392_);
v_val_4403_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4410_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4410_ == 0)
{
v___x_4405_ = v___x_4401_;
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
else
{
lean_inc(v_val_4403_);
lean_dec(v___x_4401_);
v___x_4405_ = lean_box(0);
v_isShared_4406_ = v_isSharedCheck_4410_;
goto v_resetjp_4404_;
}
v_resetjp_4404_:
{
lean_object* v___x_4408_; 
if (v_isShared_4406_ == 0)
{
lean_ctor_set_tag(v___x_4405_, 0);
v___x_4408_ = v___x_4405_;
goto v_reusejp_4407_;
}
else
{
lean_object* v_reuseFailAlloc_4409_; 
v_reuseFailAlloc_4409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4409_, 0, v_val_4403_);
v___x_4408_ = v_reuseFailAlloc_4409_;
goto v_reusejp_4407_;
}
v_reusejp_4407_:
{
return v___x_4408_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4411_, lean_object* v___y_4412_, lean_object* v___y_4413_, lean_object* v___y_4414_, lean_object* v___y_4415_, lean_object* v___y_4416_){
_start:
{
lean_object* v_res_4417_; 
v_res_4417_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4411_, v___y_4412_, v___y_4413_, v___y_4414_, v___y_4415_);
lean_dec(v___y_4415_);
lean_dec_ref(v___y_4414_);
lean_dec(v___y_4413_);
lean_dec_ref(v___y_4412_);
return v_res_4417_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4418_, lean_object* v_a_4419_){
_start:
{
if (lean_obj_tag(v_a_4418_) == 0)
{
lean_object* v___x_4420_; 
v___x_4420_ = l_List_reverse___redArg(v_a_4419_);
return v___x_4420_;
}
else
{
lean_object* v_head_4421_; lean_object* v_tail_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4431_; 
v_head_4421_ = lean_ctor_get(v_a_4418_, 0);
v_tail_4422_ = lean_ctor_get(v_a_4418_, 1);
v_isSharedCheck_4431_ = !lean_is_exclusive(v_a_4418_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4424_ = v_a_4418_;
v_isShared_4425_ = v_isSharedCheck_4431_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_tail_4422_);
lean_inc(v_head_4421_);
lean_dec(v_a_4418_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4431_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4426_; lean_object* v___x_4428_; 
v___x_4426_ = l_Lean_mkLevelParam(v_head_4421_);
if (v_isShared_4425_ == 0)
{
lean_ctor_set(v___x_4424_, 1, v_a_4419_);
lean_ctor_set(v___x_4424_, 0, v___x_4426_);
v___x_4428_ = v___x_4424_;
goto v_reusejp_4427_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v___x_4426_);
lean_ctor_set(v_reuseFailAlloc_4430_, 1, v_a_4419_);
v___x_4428_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4427_;
}
v_reusejp_4427_:
{
v_a_4418_ = v_tail_4422_;
v_a_4419_ = v___x_4428_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4432_, lean_object* v___y_4433_, lean_object* v___y_4434_, lean_object* v___y_4435_, lean_object* v___y_4436_){
_start:
{
lean_object* v___x_4438_; 
lean_inc(v_constName_4432_);
v___x_4438_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4432_, v___y_4433_, v___y_4434_, v___y_4435_, v___y_4436_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v_a_4439_; lean_object* v___x_4441_; uint8_t v_isShared_4442_; uint8_t v_isSharedCheck_4450_; 
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4450_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4450_ == 0)
{
v___x_4441_ = v___x_4438_;
v_isShared_4442_ = v_isSharedCheck_4450_;
goto v_resetjp_4440_;
}
else
{
lean_inc(v_a_4439_);
lean_dec(v___x_4438_);
v___x_4441_ = lean_box(0);
v_isShared_4442_ = v_isSharedCheck_4450_;
goto v_resetjp_4440_;
}
v_resetjp_4440_:
{
lean_object* v_levelParams_4443_; lean_object* v___x_4444_; lean_object* v___x_4445_; lean_object* v___x_4446_; lean_object* v___x_4448_; 
v_levelParams_4443_ = lean_ctor_get(v_a_4439_, 1);
lean_inc(v_levelParams_4443_);
lean_dec(v_a_4439_);
v___x_4444_ = lean_box(0);
v___x_4445_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4443_, v___x_4444_);
v___x_4446_ = l_Lean_mkConst(v_constName_4432_, v___x_4445_);
if (v_isShared_4442_ == 0)
{
lean_ctor_set(v___x_4441_, 0, v___x_4446_);
v___x_4448_ = v___x_4441_;
goto v_reusejp_4447_;
}
else
{
lean_object* v_reuseFailAlloc_4449_; 
v_reuseFailAlloc_4449_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4449_, 0, v___x_4446_);
v___x_4448_ = v_reuseFailAlloc_4449_;
goto v_reusejp_4447_;
}
v_reusejp_4447_:
{
return v___x_4448_;
}
}
}
else
{
lean_object* v_a_4451_; lean_object* v___x_4453_; uint8_t v_isShared_4454_; uint8_t v_isSharedCheck_4458_; 
lean_dec(v_constName_4432_);
v_a_4451_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4458_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4458_ == 0)
{
v___x_4453_ = v___x_4438_;
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
else
{
lean_inc(v_a_4451_);
lean_dec(v___x_4438_);
v___x_4453_ = lean_box(0);
v_isShared_4454_ = v_isSharedCheck_4458_;
goto v_resetjp_4452_;
}
v_resetjp_4452_:
{
lean_object* v___x_4456_; 
if (v_isShared_4454_ == 0)
{
v___x_4456_ = v___x_4453_;
goto v_reusejp_4455_;
}
else
{
lean_object* v_reuseFailAlloc_4457_; 
v_reuseFailAlloc_4457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4457_, 0, v_a_4451_);
v___x_4456_ = v_reuseFailAlloc_4457_;
goto v_reusejp_4455_;
}
v_reusejp_4455_:
{
return v___x_4456_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4459_, lean_object* v___y_4460_, lean_object* v___y_4461_, lean_object* v___y_4462_, lean_object* v___y_4463_, lean_object* v___y_4464_){
_start:
{
lean_object* v_res_4465_; 
v_res_4465_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4459_, v___y_4460_, v___y_4461_, v___y_4462_, v___y_4463_);
lean_dec(v___y_4463_);
lean_dec_ref(v___y_4462_);
lean_dec(v___y_4461_);
lean_dec_ref(v___y_4460_);
return v_res_4465_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4467_; lean_object* v___x_4468_; 
v___x_4467_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4468_ = l_Lean_stringToMessageData(v___x_4467_);
return v___x_4468_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4470_; lean_object* v___x_4471_; 
v___x_4470_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4471_ = l_Lean_stringToMessageData(v___x_4470_);
return v___x_4471_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_4473_; lean_object* v___x_4474_; 
v___x_4473_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_4474_ = l_Lean_stringToMessageData(v___x_4473_);
return v___x_4474_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__7(void){
_start:
{
lean_object* v___x_4476_; lean_object* v___x_4477_; 
v___x_4476_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__6));
v___x_4477_ = l_Lean_stringToMessageData(v___x_4476_);
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4478_, uint8_t v_attrKind_4479_, lean_object* v_prio_4480_, lean_object* v_a_4481_, lean_object* v_a_4482_, lean_object* v_a_4483_, lean_object* v_a_4484_){
_start:
{
lean_object* v___x_4486_; 
lean_inc(v_declName_4478_);
v___x_4486_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4478_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; lean_object* v___y_4489_; lean_object* v___y_4490_; lean_object* v___y_4491_; lean_object* v___y_4492_; lean_object* v___y_4493_; lean_object* v___y_4517_; lean_object* v___y_4518_; lean_object* v___y_4519_; lean_object* v___y_4520_; lean_object* v___x_4565_; 
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4486_, 1);
lean_inc(v_declName_4478_);
v___x_4565_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4478_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_);
if (lean_obj_tag(v___x_4565_) == 0)
{
lean_object* v_a_4566_; lean_object* v___x_4567_; uint8_t v___x_4568_; 
v_a_4566_ = lean_ctor_get(v___x_4565_, 0);
lean_inc(v_a_4566_);
lean_dec_ref_known(v___x_4565_, 1);
v___x_4567_ = l_Lean_ConstantInfo_type(v_a_4566_);
v___x_4568_ = l_Lean_Expr_hasSorry(v___x_4567_);
lean_dec_ref(v___x_4567_);
if (v___x_4568_ == 0)
{
lean_object* v___x_4569_; 
lean_inc(v_a_4487_);
v___x_4569_ = l_Lean_Meta_checkNonClassInstance(v_a_4487_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_);
if (lean_obj_tag(v___x_4569_) == 0)
{
lean_object* v___x_4570_; 
lean_dec_ref_known(v___x_4569_, 1);
v___x_4570_ = l_Lean_Meta_checkImpossibleInstance(v_a_4566_, v_a_4481_, v_a_4482_, v_a_4483_, v_a_4484_);
lean_dec(v_a_4566_);
if (lean_obj_tag(v___x_4570_) == 0)
{
lean_dec_ref_known(v___x_4570_, 1);
v___y_4517_ = v_a_4481_;
v___y_4518_ = v_a_4482_;
v___y_4519_ = v_a_4483_;
v___y_4520_ = v_a_4484_;
goto v___jp_4516_;
}
else
{
lean_dec(v_a_4487_);
lean_dec(v_prio_4480_);
lean_dec(v_declName_4478_);
return v___x_4570_;
}
}
else
{
lean_dec(v_a_4566_);
lean_dec(v_a_4487_);
lean_dec(v_prio_4480_);
lean_dec(v_declName_4478_);
return v___x_4569_;
}
}
else
{
lean_dec(v_a_4566_);
v___y_4517_ = v_a_4481_;
v___y_4518_ = v_a_4482_;
v___y_4519_ = v_a_4483_;
v___y_4520_ = v_a_4484_;
goto v___jp_4516_;
}
}
else
{
lean_object* v_a_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4578_; 
lean_dec(v_a_4487_);
lean_dec(v_prio_4480_);
lean_dec(v_declName_4478_);
v_a_4571_ = lean_ctor_get(v___x_4565_, 0);
v_isSharedCheck_4578_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4578_ == 0)
{
v___x_4573_ = v___x_4565_;
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_a_4571_);
lean_dec(v___x_4565_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4578_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
lean_object* v___x_4576_; 
if (v_isShared_4574_ == 0)
{
v___x_4576_ = v___x_4573_;
goto v_reusejp_4575_;
}
else
{
lean_object* v_reuseFailAlloc_4577_; 
v_reuseFailAlloc_4577_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4577_, 0, v_a_4571_);
v___x_4576_ = v_reuseFailAlloc_4577_;
goto v_reusejp_4575_;
}
v_reusejp_4575_:
{
return v___x_4576_;
}
}
}
v___jp_4488_:
{
lean_object* v___x_4494_; lean_object* v_a_4495_; lean_object* v___x_4497_; uint8_t v_isShared_4498_; uint8_t v_isSharedCheck_4515_; 
lean_inc(v_declName_4478_);
v___x_4494_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4478_, v___y_4493_);
v_a_4495_ = lean_ctor_get(v___x_4494_, 0);
v_isSharedCheck_4515_ = !lean_is_exclusive(v___x_4494_);
if (v_isSharedCheck_4515_ == 0)
{
v___x_4497_ = v___x_4494_;
v_isShared_4498_ = v_isSharedCheck_4515_;
goto v_resetjp_4496_;
}
else
{
lean_inc(v_a_4495_);
lean_dec(v___x_4494_);
v___x_4497_ = lean_box(0);
v_isShared_4498_ = v_isSharedCheck_4515_;
goto v_resetjp_4496_;
}
v_resetjp_4496_:
{
lean_object* v___x_4499_; 
lean_inc(v_a_4487_);
v___x_4499_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4487_, v_a_4495_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
if (lean_obj_tag(v___x_4499_) == 0)
{
lean_object* v_a_4500_; lean_object* v___x_4501_; lean_object* v___x_4503_; 
v_a_4500_ = lean_ctor_get(v___x_4499_, 0);
lean_inc(v_a_4500_);
lean_dec_ref_known(v___x_4499_, 1);
v___x_4501_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4498_ == 0)
{
lean_ctor_set_tag(v___x_4497_, 1);
lean_ctor_set(v___x_4497_, 0, v_declName_4478_);
v___x_4503_ = v___x_4497_;
goto v_reusejp_4502_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_declName_4478_);
v___x_4503_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4502_;
}
v_reusejp_4502_:
{
lean_object* v___x_4504_; lean_object* v___x_4505_; 
v___x_4504_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4504_, 0, v___y_4489_);
lean_ctor_set(v___x_4504_, 1, v_a_4487_);
lean_ctor_set(v___x_4504_, 2, v_prio_4480_);
lean_ctor_set(v___x_4504_, 3, v___x_4503_);
lean_ctor_set(v___x_4504_, 4, v_a_4500_);
lean_ctor_set_uint8(v___x_4504_, sizeof(void*)*5, v_attrKind_4479_);
v___x_4505_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4501_, v___x_4504_, v_attrKind_4479_, v___y_4491_, v___y_4492_, v___y_4493_);
return v___x_4505_;
}
}
else
{
lean_object* v_a_4507_; lean_object* v___x_4509_; uint8_t v_isShared_4510_; uint8_t v_isSharedCheck_4514_; 
lean_del_object(v___x_4497_);
lean_dec_ref(v___y_4489_);
lean_dec(v_a_4487_);
lean_dec(v_prio_4480_);
lean_dec(v_declName_4478_);
v_a_4507_ = lean_ctor_get(v___x_4499_, 0);
v_isSharedCheck_4514_ = !lean_is_exclusive(v___x_4499_);
if (v_isSharedCheck_4514_ == 0)
{
v___x_4509_ = v___x_4499_;
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
else
{
lean_inc(v_a_4507_);
lean_dec(v___x_4499_);
v___x_4509_ = lean_box(0);
v_isShared_4510_ = v_isSharedCheck_4514_;
goto v_resetjp_4508_;
}
v_resetjp_4508_:
{
lean_object* v___x_4512_; 
if (v_isShared_4510_ == 0)
{
v___x_4512_ = v___x_4509_;
goto v_reusejp_4511_;
}
else
{
lean_object* v_reuseFailAlloc_4513_; 
v_reuseFailAlloc_4513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4513_, 0, v_a_4507_);
v___x_4512_ = v_reuseFailAlloc_4513_;
goto v_reusejp_4511_;
}
v_reusejp_4511_:
{
return v___x_4512_;
}
}
}
}
}
v___jp_4516_:
{
lean_object* v___x_4521_; 
lean_inc(v_a_4487_);
v___x_4521_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4487_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
if (lean_obj_tag(v___x_4521_) == 0)
{
lean_object* v_a_4522_; lean_object* v___x_4523_; lean_object* v_a_4524_; uint8_t v___x_4525_; uint8_t v___x_4526_; uint8_t v___x_4527_; 
v_a_4522_ = lean_ctor_get(v___x_4521_, 0);
lean_inc(v_a_4522_);
lean_dec_ref_known(v___x_4521_, 1);
lean_inc(v_declName_4478_);
v___x_4523_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4478_, v___y_4520_);
v_a_4524_ = lean_ctor_get(v___x_4523_, 0);
lean_inc(v_a_4524_);
lean_dec_ref(v___x_4523_);
v___x_4525_ = 1;
v___x_4526_ = lean_unbox(v_a_4524_);
lean_dec(v_a_4524_);
v___x_4527_ = l_Lean_instBEqReducibilityStatus_beq(v___x_4526_, v___x_4525_);
if (v___x_4527_ == 0)
{
v___y_4489_ = v_a_4522_;
v___y_4490_ = v___y_4517_;
v___y_4491_ = v___y_4518_;
v___y_4492_ = v___y_4519_;
v___y_4493_ = v___y_4520_;
goto v___jp_4488_;
}
else
{
lean_object* v___x_4528_; 
lean_inc(v_declName_4478_);
v___x_4528_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4478_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
if (lean_obj_tag(v___x_4528_) == 0)
{
lean_object* v_a_4529_; uint8_t v___x_4530_; 
v_a_4529_ = lean_ctor_get(v___x_4528_, 0);
lean_inc(v_a_4529_);
lean_dec_ref_known(v___x_4528_, 1);
v___x_4530_ = l_Lean_ConstantInfo_isDefinition(v_a_4529_);
lean_dec(v_a_4529_);
if (v___x_4530_ == 0)
{
lean_object* v___x_4531_; lean_object* v_env_4532_; uint8_t v___x_4533_; 
v___x_4531_ = lean_st_ref_get(v___y_4520_);
v_env_4532_ = lean_ctor_get(v___x_4531_, 0);
lean_inc_ref(v_env_4532_);
lean_dec(v___x_4531_);
lean_inc(v_declName_4478_);
v___x_4533_ = l_Lean_wasOriginallyDefn(v_env_4532_, v_declName_4478_);
if (v___x_4533_ == 0)
{
v___y_4489_ = v_a_4522_;
v___y_4490_ = v___y_4517_;
v___y_4491_ = v___y_4518_;
v___y_4492_ = v___y_4519_;
v___y_4493_ = v___y_4520_;
goto v___jp_4488_;
}
else
{
lean_object* v___x_4534_; lean_object* v___x_4535_; lean_object* v___x_4536_; lean_object* v___x_4537_; lean_object* v___x_4538_; lean_object* v___x_4539_; 
v___x_4534_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4478_);
v___x_4535_ = l_Lean_MessageData_ofName(v_declName_4478_);
v___x_4536_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4536_, 0, v___x_4534_);
lean_ctor_set(v___x_4536_, 1, v___x_4535_);
v___x_4537_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4538_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4538_, 0, v___x_4536_);
lean_ctor_set(v___x_4538_, 1, v___x_4537_);
v___x_4539_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(v___x_4538_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
if (lean_obj_tag(v___x_4539_) == 0)
{
lean_dec_ref_known(v___x_4539_, 1);
v___y_4489_ = v_a_4522_;
v___y_4490_ = v___y_4517_;
v___y_4491_ = v___y_4518_;
v___y_4492_ = v___y_4519_;
v___y_4493_ = v___y_4520_;
goto v___jp_4488_;
}
else
{
lean_dec(v_a_4522_);
lean_dec(v_a_4487_);
lean_dec(v_prio_4480_);
lean_dec(v_declName_4478_);
return v___x_4539_;
}
}
}
else
{
lean_object* v___x_4540_; lean_object* v___x_4541_; uint8_t v___x_4542_; 
v___x_4540_ = l_Lean_Core_instMonadOptionsCoreM_checkedOptions(v___y_4519_);
v___x_4541_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility));
v___x_4542_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v___x_4540_, v___x_4541_);
lean_dec_ref(v___x_4540_);
if (v___x_4542_ == 0)
{
v___y_4489_ = v_a_4522_;
v___y_4490_ = v___y_4517_;
v___y_4491_ = v___y_4518_;
v___y_4492_ = v___y_4519_;
v___y_4493_ = v___y_4520_;
goto v___jp_4488_;
}
else
{
lean_object* v___x_4543_; lean_object* v___x_4544_; lean_object* v___x_4545_; lean_object* v___x_4546_; lean_object* v___x_4547_; lean_object* v___x_4548_; 
v___x_4543_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
lean_inc(v_declName_4478_);
v___x_4544_ = l_Lean_MessageData_ofName(v_declName_4478_);
v___x_4545_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4545_, 0, v___x_4543_);
lean_ctor_set(v___x_4545_, 1, v___x_4544_);
v___x_4546_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__7, &l_Lean_Meta_addInstance___closed__7_once, _init_l_Lean_Meta_addInstance___closed__7);
v___x_4547_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4547_, 0, v___x_4545_);
lean_ctor_set(v___x_4547_, 1, v___x_4546_);
v___x_4548_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(v___x_4547_, v___y_4517_, v___y_4518_, v___y_4519_, v___y_4520_);
if (lean_obj_tag(v___x_4548_) == 0)
{
lean_dec_ref_known(v___x_4548_, 1);
v___y_4489_ = v_a_4522_;
v___y_4490_ = v___y_4517_;
v___y_4491_ = v___y_4518_;
v___y_4492_ = v___y_4519_;
v___y_4493_ = v___y_4520_;
goto v___jp_4488_;
}
else
{
lean_dec(v_a_4522_);
lean_dec(v_a_4487_);
lean_dec(v_prio_4480_);
lean_dec(v_declName_4478_);
return v___x_4548_;
}
}
}
}
else
{
lean_object* v_a_4549_; lean_object* v___x_4551_; uint8_t v_isShared_4552_; uint8_t v_isSharedCheck_4556_; 
lean_dec(v_a_4522_);
lean_dec(v_a_4487_);
lean_dec(v_prio_4480_);
lean_dec(v_declName_4478_);
v_a_4549_ = lean_ctor_get(v___x_4528_, 0);
v_isSharedCheck_4556_ = !lean_is_exclusive(v___x_4528_);
if (v_isSharedCheck_4556_ == 0)
{
v___x_4551_ = v___x_4528_;
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
else
{
lean_inc(v_a_4549_);
lean_dec(v___x_4528_);
v___x_4551_ = lean_box(0);
v_isShared_4552_ = v_isSharedCheck_4556_;
goto v_resetjp_4550_;
}
v_resetjp_4550_:
{
lean_object* v___x_4554_; 
if (v_isShared_4552_ == 0)
{
v___x_4554_ = v___x_4551_;
goto v_reusejp_4553_;
}
else
{
lean_object* v_reuseFailAlloc_4555_; 
v_reuseFailAlloc_4555_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4555_, 0, v_a_4549_);
v___x_4554_ = v_reuseFailAlloc_4555_;
goto v_reusejp_4553_;
}
v_reusejp_4553_:
{
return v___x_4554_;
}
}
}
}
}
else
{
lean_object* v_a_4557_; lean_object* v___x_4559_; uint8_t v_isShared_4560_; uint8_t v_isSharedCheck_4564_; 
lean_dec(v_a_4487_);
lean_dec(v_prio_4480_);
lean_dec(v_declName_4478_);
v_a_4557_ = lean_ctor_get(v___x_4521_, 0);
v_isSharedCheck_4564_ = !lean_is_exclusive(v___x_4521_);
if (v_isSharedCheck_4564_ == 0)
{
v___x_4559_ = v___x_4521_;
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
else
{
lean_inc(v_a_4557_);
lean_dec(v___x_4521_);
v___x_4559_ = lean_box(0);
v_isShared_4560_ = v_isSharedCheck_4564_;
goto v_resetjp_4558_;
}
v_resetjp_4558_:
{
lean_object* v___x_4562_; 
if (v_isShared_4560_ == 0)
{
v___x_4562_ = v___x_4559_;
goto v_reusejp_4561_;
}
else
{
lean_object* v_reuseFailAlloc_4563_; 
v_reuseFailAlloc_4563_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4563_, 0, v_a_4557_);
v___x_4562_ = v_reuseFailAlloc_4563_;
goto v_reusejp_4561_;
}
v_reusejp_4561_:
{
return v___x_4562_;
}
}
}
}
}
else
{
lean_object* v_a_4579_; lean_object* v___x_4581_; uint8_t v_isShared_4582_; uint8_t v_isSharedCheck_4586_; 
lean_dec(v_prio_4480_);
lean_dec(v_declName_4478_);
v_a_4579_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4586_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4586_ == 0)
{
v___x_4581_ = v___x_4486_;
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
else
{
lean_inc(v_a_4579_);
lean_dec(v___x_4486_);
v___x_4581_ = lean_box(0);
v_isShared_4582_ = v_isSharedCheck_4586_;
goto v_resetjp_4580_;
}
v_resetjp_4580_:
{
lean_object* v___x_4584_; 
if (v_isShared_4582_ == 0)
{
v___x_4584_ = v___x_4581_;
goto v_reusejp_4583_;
}
else
{
lean_object* v_reuseFailAlloc_4585_; 
v_reuseFailAlloc_4585_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4585_, 0, v_a_4579_);
v___x_4584_ = v_reuseFailAlloc_4585_;
goto v_reusejp_4583_;
}
v_reusejp_4583_:
{
return v___x_4584_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4587_, lean_object* v_attrKind_4588_, lean_object* v_prio_4589_, lean_object* v_a_4590_, lean_object* v_a_4591_, lean_object* v_a_4592_, lean_object* v_a_4593_, lean_object* v_a_4594_){
_start:
{
uint8_t v_attrKind_boxed_4595_; lean_object* v_res_4596_; 
v_attrKind_boxed_4595_ = lean_unbox(v_attrKind_4588_);
v_res_4596_ = l_Lean_Meta_addInstance(v_declName_4587_, v_attrKind_boxed_4595_, v_prio_4589_, v_a_4590_, v_a_4591_, v_a_4592_, v_a_4593_);
lean_dec(v_a_4593_);
lean_dec_ref(v_a_4592_);
lean_dec(v_a_4591_);
lean_dec_ref(v_a_4590_);
return v_res_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_4597_, lean_object* v_constName_4598_, lean_object* v___y_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_){
_start:
{
lean_object* v___x_4604_; 
v___x_4604_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4598_, v___y_4599_, v___y_4600_, v___y_4601_, v___y_4602_);
return v___x_4604_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4605_, lean_object* v_constName_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_, lean_object* v___y_4610_, lean_object* v___y_4611_){
_start:
{
lean_object* v_res_4612_; 
v_res_4612_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_4605_, v_constName_4606_, v___y_4607_, v___y_4608_, v___y_4609_, v___y_4610_);
lean_dec(v___y_4610_);
lean_dec_ref(v___y_4609_);
lean_dec(v___y_4608_);
lean_dec_ref(v___y_4607_);
return v_res_4612_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_4613_, lean_object* v_ref_4614_, lean_object* v_constName_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_, lean_object* v___y_4618_, lean_object* v___y_4619_){
_start:
{
lean_object* v___x_4621_; 
v___x_4621_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4614_, v_constName_4615_, v___y_4616_, v___y_4617_, v___y_4618_, v___y_4619_);
return v___x_4621_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4622_, lean_object* v_ref_4623_, lean_object* v_constName_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_, lean_object* v___y_4627_, lean_object* v___y_4628_, lean_object* v___y_4629_){
_start:
{
lean_object* v_res_4630_; 
v_res_4630_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_4622_, v_ref_4623_, v_constName_4624_, v___y_4625_, v___y_4626_, v___y_4627_, v___y_4628_);
lean_dec(v___y_4628_);
lean_dec_ref(v___y_4627_);
lean_dec(v___y_4626_);
lean_dec_ref(v___y_4625_);
lean_dec(v_ref_4623_);
return v_res_4630_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b1_4631_, lean_object* v_ref_4632_, lean_object* v_msg_4633_, lean_object* v_declHint_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_, lean_object* v___y_4638_){
_start:
{
lean_object* v___x_4640_; 
v___x_4640_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4632_, v_msg_4633_, v_declHint_4634_, v___y_4635_, v___y_4636_, v___y_4637_, v___y_4638_);
return v___x_4640_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4641_, lean_object* v_ref_4642_, lean_object* v_msg_4643_, lean_object* v_declHint_4644_, lean_object* v___y_4645_, lean_object* v___y_4646_, lean_object* v___y_4647_, lean_object* v___y_4648_, lean_object* v___y_4649_){
_start:
{
lean_object* v_res_4650_; 
v_res_4650_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(v_00_u03b1_4641_, v_ref_4642_, v_msg_4643_, v_declHint_4644_, v___y_4645_, v___y_4646_, v___y_4647_, v___y_4648_);
lean_dec(v___y_4648_);
lean_dec_ref(v___y_4647_);
lean_dec(v___y_4646_);
lean_dec_ref(v___y_4645_);
lean_dec(v_ref_4642_);
return v_res_4650_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_4651_, lean_object* v_declHint_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v___x_4658_; 
v___x_4658_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4651_, v_declHint_4652_, v___y_4656_);
return v___x_4658_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_4659_, lean_object* v_declHint_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_, lean_object* v___y_4663_, lean_object* v___y_4664_, lean_object* v___y_4665_){
_start:
{
lean_object* v_res_4666_; 
v_res_4666_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(v_msg_4659_, v_declHint_4660_, v___y_4661_, v___y_4662_, v___y_4663_, v___y_4664_);
lean_dec(v___y_4664_);
lean_dec_ref(v___y_4663_);
lean_dec(v___y_4662_);
lean_dec_ref(v___y_4661_);
return v_res_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_4667_, lean_object* v_ref_4668_, lean_object* v_msg_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_){
_start:
{
lean_object* v___x_4675_; 
v___x_4675_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4668_, v_msg_4669_, v___y_4670_, v___y_4671_, v___y_4672_, v___y_4673_);
return v___x_4675_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4676_, lean_object* v_ref_4677_, lean_object* v_msg_4678_, lean_object* v___y_4679_, lean_object* v___y_4680_, lean_object* v___y_4681_, lean_object* v___y_4682_, lean_object* v___y_4683_){
_start:
{
lean_object* v_res_4684_; 
v_res_4684_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_4676_, v_ref_4677_, v_msg_4678_, v___y_4679_, v___y_4680_, v___y_4681_, v___y_4682_);
lean_dec(v___y_4682_);
lean_dec_ref(v___y_4681_);
lean_dec(v___y_4680_);
lean_dec_ref(v___y_4679_);
lean_dec(v_ref_4677_);
return v_res_4684_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4685_, uint8_t v_s_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_){
_start:
{
lean_object* v___x_4690_; lean_object* v_env_4691_; lean_object* v_nextMacroScope_4692_; lean_object* v_ngen_4693_; lean_object* v_auxDeclNGen_4694_; lean_object* v_traceState_4695_; lean_object* v_recordedDeps_4696_; lean_object* v_messages_4697_; lean_object* v_infoState_4698_; lean_object* v_snapshotTasks_4699_; lean_object* v___x_4701_; uint8_t v_isShared_4702_; uint8_t v_isSharedCheck_4728_; 
v___x_4690_ = lean_st_ref_take(v___y_4688_);
v_env_4691_ = lean_ctor_get(v___x_4690_, 0);
v_nextMacroScope_4692_ = lean_ctor_get(v___x_4690_, 1);
v_ngen_4693_ = lean_ctor_get(v___x_4690_, 2);
v_auxDeclNGen_4694_ = lean_ctor_get(v___x_4690_, 3);
v_traceState_4695_ = lean_ctor_get(v___x_4690_, 4);
v_recordedDeps_4696_ = lean_ctor_get(v___x_4690_, 6);
v_messages_4697_ = lean_ctor_get(v___x_4690_, 7);
v_infoState_4698_ = lean_ctor_get(v___x_4690_, 8);
v_snapshotTasks_4699_ = lean_ctor_get(v___x_4690_, 9);
v_isSharedCheck_4728_ = !lean_is_exclusive(v___x_4690_);
if (v_isSharedCheck_4728_ == 0)
{
lean_object* v_unused_4729_; 
v_unused_4729_ = lean_ctor_get(v___x_4690_, 5);
lean_dec(v_unused_4729_);
v___x_4701_ = v___x_4690_;
v_isShared_4702_ = v_isSharedCheck_4728_;
goto v_resetjp_4700_;
}
else
{
lean_inc(v_snapshotTasks_4699_);
lean_inc(v_infoState_4698_);
lean_inc(v_messages_4697_);
lean_inc(v_recordedDeps_4696_);
lean_inc(v_traceState_4695_);
lean_inc(v_auxDeclNGen_4694_);
lean_inc(v_ngen_4693_);
lean_inc(v_nextMacroScope_4692_);
lean_inc(v_env_4691_);
lean_dec(v___x_4690_);
v___x_4701_ = lean_box(0);
v_isShared_4702_ = v_isSharedCheck_4728_;
goto v_resetjp_4700_;
}
v_resetjp_4700_:
{
uint8_t v___x_4703_; lean_object* v___x_4704_; lean_object* v___x_4705_; lean_object* v___x_4706_; lean_object* v___x_4708_; 
v___x_4703_ = 0;
v___x_4704_ = lean_box(0);
v___x_4705_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4691_, v_declName_4685_, v_s_4686_, v___x_4703_, v___x_4704_);
v___x_4706_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_4702_ == 0)
{
lean_ctor_set(v___x_4701_, 5, v___x_4706_);
lean_ctor_set(v___x_4701_, 0, v___x_4705_);
v___x_4708_ = v___x_4701_;
goto v_reusejp_4707_;
}
else
{
lean_object* v_reuseFailAlloc_4727_; 
v_reuseFailAlloc_4727_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4727_, 0, v___x_4705_);
lean_ctor_set(v_reuseFailAlloc_4727_, 1, v_nextMacroScope_4692_);
lean_ctor_set(v_reuseFailAlloc_4727_, 2, v_ngen_4693_);
lean_ctor_set(v_reuseFailAlloc_4727_, 3, v_auxDeclNGen_4694_);
lean_ctor_set(v_reuseFailAlloc_4727_, 4, v_traceState_4695_);
lean_ctor_set(v_reuseFailAlloc_4727_, 5, v___x_4706_);
lean_ctor_set(v_reuseFailAlloc_4727_, 6, v_recordedDeps_4696_);
lean_ctor_set(v_reuseFailAlloc_4727_, 7, v_messages_4697_);
lean_ctor_set(v_reuseFailAlloc_4727_, 8, v_infoState_4698_);
lean_ctor_set(v_reuseFailAlloc_4727_, 9, v_snapshotTasks_4699_);
v___x_4708_ = v_reuseFailAlloc_4727_;
goto v_reusejp_4707_;
}
v_reusejp_4707_:
{
lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v_mctx_4711_; lean_object* v_zetaDeltaFVarIds_4712_; lean_object* v_postponed_4713_; lean_object* v_diag_4714_; lean_object* v___x_4716_; uint8_t v_isShared_4717_; uint8_t v_isSharedCheck_4725_; 
v___x_4709_ = lean_st_ref_put(v___y_4688_, v___x_4708_);
v___x_4710_ = lean_st_ref_take(v___y_4687_);
v_mctx_4711_ = lean_ctor_get(v___x_4710_, 0);
v_zetaDeltaFVarIds_4712_ = lean_ctor_get(v___x_4710_, 2);
v_postponed_4713_ = lean_ctor_get(v___x_4710_, 3);
v_diag_4714_ = lean_ctor_get(v___x_4710_, 4);
v_isSharedCheck_4725_ = !lean_is_exclusive(v___x_4710_);
if (v_isSharedCheck_4725_ == 0)
{
lean_object* v_unused_4726_; 
v_unused_4726_ = lean_ctor_get(v___x_4710_, 1);
lean_dec(v_unused_4726_);
v___x_4716_ = v___x_4710_;
v_isShared_4717_ = v_isSharedCheck_4725_;
goto v_resetjp_4715_;
}
else
{
lean_inc(v_diag_4714_);
lean_inc(v_postponed_4713_);
lean_inc(v_zetaDeltaFVarIds_4712_);
lean_inc(v_mctx_4711_);
lean_dec(v___x_4710_);
v___x_4716_ = lean_box(0);
v_isShared_4717_ = v_isSharedCheck_4725_;
goto v_resetjp_4715_;
}
v_resetjp_4715_:
{
lean_object* v___x_4718_; lean_object* v___x_4719_; lean_object* v___x_4721_; 
v___x_4718_ = lean_box(0);
v___x_4719_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4717_ == 0)
{
lean_ctor_set(v___x_4716_, 1, v___x_4719_);
v___x_4721_ = v___x_4716_;
goto v_reusejp_4720_;
}
else
{
lean_object* v_reuseFailAlloc_4724_; 
v_reuseFailAlloc_4724_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4724_, 0, v_mctx_4711_);
lean_ctor_set(v_reuseFailAlloc_4724_, 1, v___x_4719_);
lean_ctor_set(v_reuseFailAlloc_4724_, 2, v_zetaDeltaFVarIds_4712_);
lean_ctor_set(v_reuseFailAlloc_4724_, 3, v_postponed_4713_);
lean_ctor_set(v_reuseFailAlloc_4724_, 4, v_diag_4714_);
v___x_4721_ = v_reuseFailAlloc_4724_;
goto v_reusejp_4720_;
}
v_reusejp_4720_:
{
lean_object* v___x_4722_; lean_object* v___x_4723_; 
v___x_4722_ = lean_st_ref_put(v___y_4687_, v___x_4721_);
v___x_4723_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4723_, 0, v___x_4718_);
return v___x_4723_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4730_, lean_object* v_s_4731_, lean_object* v___y_4732_, lean_object* v___y_4733_, lean_object* v___y_4734_){
_start:
{
uint8_t v_s_boxed_4735_; lean_object* v_res_4736_; 
v_s_boxed_4735_ = lean_unbox(v_s_4731_);
v_res_4736_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4730_, v_s_boxed_4735_, v___y_4732_, v___y_4733_);
lean_dec(v___y_4733_);
lean_dec(v___y_4732_);
return v_res_4736_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4737_, uint8_t v_s_4738_, lean_object* v___y_4739_, lean_object* v___y_4740_, lean_object* v___y_4741_, lean_object* v___y_4742_){
_start:
{
lean_object* v___x_4744_; 
v___x_4744_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4737_, v_s_4738_, v___y_4740_, v___y_4742_);
return v___x_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4745_, lean_object* v_s_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_, lean_object* v___y_4750_, lean_object* v___y_4751_){
_start:
{
uint8_t v_s_boxed_4752_; lean_object* v_res_4753_; 
v_s_boxed_4752_ = lean_unbox(v_s_4746_);
v_res_4753_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4745_, v_s_boxed_4752_, v___y_4747_, v___y_4748_, v___y_4749_, v___y_4750_);
lean_dec(v___y_4750_);
lean_dec_ref(v___y_4749_);
lean_dec(v___y_4748_);
lean_dec_ref(v___y_4747_);
return v_res_4753_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4754_, uint8_t v_attrKind_4755_, lean_object* v_prio_4756_, lean_object* v_a_4757_, lean_object* v_a_4758_, lean_object* v_a_4759_, lean_object* v_a_4760_){
_start:
{
uint8_t v___x_4762_; lean_object* v___x_4763_; lean_object* v___x_4764_; 
v___x_4762_ = 4;
lean_inc(v_declName_4754_);
v___x_4763_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4754_, v___x_4762_, v_a_4758_, v_a_4760_);
lean_dec_ref(v___x_4763_);
v___x_4764_ = l_Lean_Meta_addInstance(v_declName_4754_, v_attrKind_4755_, v_prio_4756_, v_a_4757_, v_a_4758_, v_a_4759_, v_a_4760_);
return v___x_4764_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4765_, lean_object* v_attrKind_4766_, lean_object* v_prio_4767_, lean_object* v_a_4768_, lean_object* v_a_4769_, lean_object* v_a_4770_, lean_object* v_a_4771_, lean_object* v_a_4772_){
_start:
{
uint8_t v_attrKind_boxed_4773_; lean_object* v_res_4774_; 
v_attrKind_boxed_4773_ = lean_unbox(v_attrKind_4766_);
v_res_4774_ = l_Lean_Meta_registerInstance(v_declName_4765_, v_attrKind_boxed_4773_, v_prio_4767_, v_a_4768_, v_a_4769_, v_a_4770_, v_a_4771_);
lean_dec(v_a_4771_);
lean_dec_ref(v_a_4770_);
lean_dec(v_a_4769_);
lean_dec_ref(v_a_4768_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4775_, lean_object* v_x_4776_){
_start:
{
lean_inc_ref(v_a_4775_);
return v_a_4775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4777_, lean_object* v_x_4778_){
_start:
{
lean_object* v_res_4779_; 
v_res_4779_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4777_, v_x_4778_);
lean_dec_ref(v_x_4778_);
lean_dec_ref(v_a_4777_);
return v_res_4779_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4780_, lean_object* v___y_4781_, lean_object* v___y_4782_){
_start:
{
lean_object* v___x_4784_; lean_object* v_toCold_4785_; lean_object* v_env_4786_; lean_object* v_options_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v___x_4790_; lean_object* v___x_4791_; lean_object* v___x_4792_; lean_object* v___x_4793_; lean_object* v___x_4794_; 
v___x_4784_ = lean_st_ref_get(v___y_4782_);
v_toCold_4785_ = lean_ctor_get(v___y_4781_, 0);
v_env_4786_ = lean_ctor_get(v___x_4784_, 0);
lean_inc_ref(v_env_4786_);
lean_dec(v___x_4784_);
v_options_4787_ = lean_ctor_get(v_toCold_4785_, 2);
v___x_4788_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4789_ = lean_unsigned_to_nat(32u);
v___x_4790_ = lean_mk_empty_array_with_capacity(v___x_4789_);
lean_dec_ref(v___x_4790_);
v___x_4791_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
lean_inc_ref(v_options_4787_);
v___x_4792_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4792_, 0, v_env_4786_);
lean_ctor_set(v___x_4792_, 1, v___x_4788_);
lean_ctor_set(v___x_4792_, 2, v___x_4791_);
lean_ctor_set(v___x_4792_, 3, v_options_4787_);
v___x_4793_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4793_, 0, v___x_4792_);
lean_ctor_set(v___x_4793_, 1, v_msgData_4780_);
v___x_4794_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4794_, 0, v___x_4793_);
return v___x_4794_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4795_, lean_object* v___y_4796_, lean_object* v___y_4797_, lean_object* v___y_4798_){
_start:
{
lean_object* v_res_4799_; 
v_res_4799_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4795_, v___y_4796_, v___y_4797_);
lean_dec(v___y_4797_);
lean_dec_ref(v___y_4796_);
return v_res_4799_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_){
_start:
{
lean_object* v_ref_4804_; lean_object* v___x_4805_; lean_object* v_a_4806_; lean_object* v___x_4808_; uint8_t v_isShared_4809_; uint8_t v_isSharedCheck_4814_; 
v_ref_4804_ = lean_ctor_get(v___y_4801_, 2);
v___x_4805_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4800_, v___y_4801_, v___y_4802_);
v_a_4806_ = lean_ctor_get(v___x_4805_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4805_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4808_ = v___x_4805_;
v_isShared_4809_ = v_isSharedCheck_4814_;
goto v_resetjp_4807_;
}
else
{
lean_inc(v_a_4806_);
lean_dec(v___x_4805_);
v___x_4808_ = lean_box(0);
v_isShared_4809_ = v_isSharedCheck_4814_;
goto v_resetjp_4807_;
}
v_resetjp_4807_:
{
lean_object* v___x_4810_; lean_object* v___x_4812_; 
lean_inc(v_ref_4804_);
v___x_4810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4810_, 0, v_ref_4804_);
lean_ctor_set(v___x_4810_, 1, v_a_4806_);
if (v_isShared_4809_ == 0)
{
lean_ctor_set_tag(v___x_4808_, 1);
lean_ctor_set(v___x_4808_, 0, v___x_4810_);
v___x_4812_ = v___x_4808_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4810_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4815_, lean_object* v___y_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_){
_start:
{
lean_object* v_res_4819_; 
v_res_4819_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4815_, v___y_4816_, v___y_4817_);
lean_dec(v___y_4817_);
lean_dec_ref(v___y_4816_);
return v_res_4819_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4820_, lean_object* v_i_4821_, lean_object* v_k_4822_){
_start:
{
lean_object* v___x_4823_; uint8_t v___x_4824_; 
v___x_4823_ = lean_array_get_size(v_keys_4820_);
v___x_4824_ = lean_nat_dec_lt(v_i_4821_, v___x_4823_);
if (v___x_4824_ == 0)
{
lean_dec(v_i_4821_);
return v___x_4824_;
}
else
{
lean_object* v_k_x27_4825_; uint8_t v___x_4826_; 
v_k_x27_4825_ = lean_array_fget_borrowed(v_keys_4820_, v_i_4821_);
v___x_4826_ = lean_name_eq(v_k_4822_, v_k_x27_4825_);
if (v___x_4826_ == 0)
{
lean_object* v___x_4827_; lean_object* v___x_4828_; 
v___x_4827_ = lean_unsigned_to_nat(1u);
v___x_4828_ = lean_nat_add(v_i_4821_, v___x_4827_);
lean_dec(v_i_4821_);
v_i_4821_ = v___x_4828_;
goto _start;
}
else
{
lean_dec(v_i_4821_);
return v___x_4824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4830_, lean_object* v_i_4831_, lean_object* v_k_4832_){
_start:
{
uint8_t v_res_4833_; lean_object* v_r_4834_; 
v_res_4833_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4830_, v_i_4831_, v_k_4832_);
lean_dec(v_k_4832_);
lean_dec_ref(v_keys_4830_);
v_r_4834_ = lean_box(v_res_4833_);
return v_r_4834_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4835_, size_t v_x_4836_, lean_object* v_x_4837_){
_start:
{
if (lean_obj_tag(v_x_4835_) == 0)
{
lean_object* v_es_4838_; lean_object* v___x_4839_; size_t v___x_4840_; size_t v___x_4841_; lean_object* v_j_4842_; lean_object* v___x_4843_; 
v_es_4838_ = lean_ctor_get(v_x_4835_, 0);
v___x_4839_ = lean_box(2);
v___x_4840_ = ((size_t)31ULL);
v___x_4841_ = lean_usize_land(v_x_4836_, v___x_4840_);
v_j_4842_ = lean_usize_to_nat(v___x_4841_);
v___x_4843_ = lean_array_get_borrowed(v___x_4839_, v_es_4838_, v_j_4842_);
lean_dec(v_j_4842_);
switch(lean_obj_tag(v___x_4843_))
{
case 0:
{
lean_object* v_key_4844_; uint8_t v___x_4845_; 
v_key_4844_ = lean_ctor_get(v___x_4843_, 0);
v___x_4845_ = lean_name_eq(v_x_4837_, v_key_4844_);
return v___x_4845_;
}
case 1:
{
lean_object* v_node_4846_; size_t v___x_4847_; size_t v___x_4848_; 
v_node_4846_ = lean_ctor_get(v___x_4843_, 0);
v___x_4847_ = ((size_t)5ULL);
v___x_4848_ = lean_usize_shift_right(v_x_4836_, v___x_4847_);
v_x_4835_ = v_node_4846_;
v_x_4836_ = v___x_4848_;
goto _start;
}
default: 
{
uint8_t v___x_4850_; 
v___x_4850_ = 0;
return v___x_4850_;
}
}
}
else
{
lean_object* v_ks_4851_; lean_object* v___x_4852_; uint8_t v___x_4853_; 
v_ks_4851_ = lean_ctor_get(v_x_4835_, 0);
v___x_4852_ = lean_unsigned_to_nat(0u);
v___x_4853_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4851_, v___x_4852_, v_x_4837_);
return v___x_4853_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4854_, lean_object* v_x_4855_, lean_object* v_x_4856_){
_start:
{
size_t v_x_2410__boxed_4857_; uint8_t v_res_4858_; lean_object* v_r_4859_; 
v_x_2410__boxed_4857_ = lean_unbox_usize(v_x_4855_);
lean_dec(v_x_4855_);
v_res_4858_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4854_, v_x_2410__boxed_4857_, v_x_4856_);
lean_dec(v_x_4856_);
lean_dec_ref(v_x_4854_);
v_r_4859_ = lean_box(v_res_4858_);
return v_r_4859_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4860_, lean_object* v_x_4861_){
_start:
{
uint64_t v___y_4863_; 
if (lean_obj_tag(v_x_4861_) == 0)
{
uint64_t v___x_4866_; 
v___x_4866_ = 1723ULL;
v___y_4863_ = v___x_4866_;
goto v___jp_4862_;
}
else
{
uint64_t v_hash_4867_; 
v_hash_4867_ = lean_ctor_get_uint64(v_x_4861_, sizeof(void*)*2);
v___y_4863_ = v_hash_4867_;
goto v___jp_4862_;
}
v___jp_4862_:
{
size_t v___x_4864_; uint8_t v___x_4865_; 
v___x_4864_ = lean_uint64_to_usize(v___y_4863_);
v___x_4865_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4860_, v___x_4864_, v_x_4861_);
return v___x_4865_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4868_, lean_object* v_x_4869_){
_start:
{
uint8_t v_res_4870_; lean_object* v_r_4871_; 
v_res_4870_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4868_, v_x_4869_);
lean_dec(v_x_4869_);
lean_dec_ref(v_x_4868_);
v_r_4871_ = lean_box(v_res_4870_);
return v_r_4871_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4872_, lean_object* v_declName_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_){
_start:
{
lean_object* v_instanceNames_4880_; uint8_t v___x_4881_; 
v_instanceNames_4880_ = lean_ctor_get(v_d_4872_, 1);
v___x_4881_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4880_, v_declName_4873_);
if (v___x_4881_ == 0)
{
lean_object* v___x_4882_; lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v_a_4888_; lean_object* v___x_4890_; uint8_t v_isShared_4891_; uint8_t v_isSharedCheck_4895_; 
lean_dec_ref(v_d_4872_);
v___x_4882_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4883_ = l_Lean_MessageData_ofConstName(v_declName_4873_, v___x_4881_);
v___x_4884_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4884_, 0, v___x_4882_);
lean_ctor_set(v___x_4884_, 1, v___x_4883_);
v___x_4885_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4886_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4886_, 0, v___x_4884_);
lean_ctor_set(v___x_4886_, 1, v___x_4885_);
v___x_4887_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4886_, v___y_4874_, v___y_4875_);
v_a_4888_ = lean_ctor_get(v___x_4887_, 0);
v_isSharedCheck_4895_ = !lean_is_exclusive(v___x_4887_);
if (v_isSharedCheck_4895_ == 0)
{
v___x_4890_ = v___x_4887_;
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
else
{
lean_inc(v_a_4888_);
lean_dec(v___x_4887_);
v___x_4890_ = lean_box(0);
v_isShared_4891_ = v_isSharedCheck_4895_;
goto v_resetjp_4889_;
}
v_resetjp_4889_:
{
lean_object* v___x_4893_; 
if (v_isShared_4891_ == 0)
{
v___x_4893_ = v___x_4890_;
goto v_reusejp_4892_;
}
else
{
lean_object* v_reuseFailAlloc_4894_; 
v_reuseFailAlloc_4894_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4894_, 0, v_a_4888_);
v___x_4893_ = v_reuseFailAlloc_4894_;
goto v_reusejp_4892_;
}
v_reusejp_4892_:
{
return v___x_4893_;
}
}
}
else
{
goto v___jp_4877_;
}
v___jp_4877_:
{
lean_object* v___x_4878_; lean_object* v___x_4879_; 
v___x_4878_ = l_Lean_Meta_Instances_eraseCore(v_d_4872_, v_declName_4873_);
v___x_4879_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4878_);
return v___x_4879_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4896_, lean_object* v_declName_4897_, lean_object* v___y_4898_, lean_object* v___y_4899_, lean_object* v___y_4900_){
_start:
{
lean_object* v_res_4901_; 
v_res_4901_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4896_, v_declName_4897_, v___y_4898_, v___y_4899_);
lean_dec(v___y_4899_);
lean_dec_ref(v___y_4898_);
return v_res_4901_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4902_, lean_object* v_declName_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
lean_object* v___x_4907_; lean_object* v_env_4908_; lean_object* v___x_4909_; lean_object* v_ext_4910_; lean_object* v_toEnvExtension_4911_; lean_object* v_asyncMode_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; 
v___x_4907_ = lean_st_ref_get(v___y_4905_);
v_env_4908_ = lean_ctor_get(v___x_4907_, 0);
lean_inc_ref(v_env_4908_);
lean_dec(v___x_4907_);
v___x_4909_ = l_Lean_Meta_instanceExtension;
v_ext_4910_ = lean_ctor_get(v___x_4909_, 1);
v_toEnvExtension_4911_ = lean_ctor_get(v_ext_4910_, 0);
v_asyncMode_4912_ = lean_ctor_get(v_toEnvExtension_4911_, 2);
v___x_4913_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4902_, v___x_4909_, v_env_4908_, v_asyncMode_4912_);
v___x_4914_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4913_, v_declName_4903_, v___y_4904_, v___y_4905_);
if (lean_obj_tag(v___x_4914_) == 0)
{
lean_object* v_a_4915_; lean_object* v___x_4917_; uint8_t v_isShared_4918_; uint8_t v_isSharedCheck_4945_; 
v_a_4915_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4917_ = v___x_4914_;
v_isShared_4918_ = v_isSharedCheck_4945_;
goto v_resetjp_4916_;
}
else
{
lean_inc(v_a_4915_);
lean_dec(v___x_4914_);
v___x_4917_ = lean_box(0);
v_isShared_4918_ = v_isSharedCheck_4945_;
goto v_resetjp_4916_;
}
v_resetjp_4916_:
{
lean_object* v___f_4919_; lean_object* v___x_4920_; lean_object* v_env_4921_; lean_object* v_nextMacroScope_4922_; lean_object* v_ngen_4923_; lean_object* v_auxDeclNGen_4924_; lean_object* v_traceState_4925_; lean_object* v_recordedDeps_4926_; lean_object* v_messages_4927_; lean_object* v_infoState_4928_; lean_object* v_snapshotTasks_4929_; lean_object* v___x_4931_; uint8_t v_isShared_4932_; uint8_t v_isSharedCheck_4943_; 
v___f_4919_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4919_, 0, v_a_4915_);
v___x_4920_ = lean_st_ref_take(v___y_4905_);
v_env_4921_ = lean_ctor_get(v___x_4920_, 0);
v_nextMacroScope_4922_ = lean_ctor_get(v___x_4920_, 1);
v_ngen_4923_ = lean_ctor_get(v___x_4920_, 2);
v_auxDeclNGen_4924_ = lean_ctor_get(v___x_4920_, 3);
v_traceState_4925_ = lean_ctor_get(v___x_4920_, 4);
v_recordedDeps_4926_ = lean_ctor_get(v___x_4920_, 6);
v_messages_4927_ = lean_ctor_get(v___x_4920_, 7);
v_infoState_4928_ = lean_ctor_get(v___x_4920_, 8);
v_snapshotTasks_4929_ = lean_ctor_get(v___x_4920_, 9);
v_isSharedCheck_4943_ = !lean_is_exclusive(v___x_4920_);
if (v_isSharedCheck_4943_ == 0)
{
lean_object* v_unused_4944_; 
v_unused_4944_ = lean_ctor_get(v___x_4920_, 5);
lean_dec(v_unused_4944_);
v___x_4931_ = v___x_4920_;
v_isShared_4932_ = v_isSharedCheck_4943_;
goto v_resetjp_4930_;
}
else
{
lean_inc(v_snapshotTasks_4929_);
lean_inc(v_infoState_4928_);
lean_inc(v_messages_4927_);
lean_inc(v_recordedDeps_4926_);
lean_inc(v_traceState_4925_);
lean_inc(v_auxDeclNGen_4924_);
lean_inc(v_ngen_4923_);
lean_inc(v_nextMacroScope_4922_);
lean_inc(v_env_4921_);
lean_dec(v___x_4920_);
v___x_4931_ = lean_box(0);
v_isShared_4932_ = v_isSharedCheck_4943_;
goto v_resetjp_4930_;
}
v_resetjp_4930_:
{
lean_object* v___x_4933_; lean_object* v___x_4934_; lean_object* v___x_4935_; lean_object* v___x_4937_; 
v___x_4933_ = lean_box(0);
v___x_4934_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4909_, v_env_4921_, v___f_4919_);
v___x_4935_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_4932_ == 0)
{
lean_ctor_set(v___x_4931_, 5, v___x_4935_);
lean_ctor_set(v___x_4931_, 0, v___x_4934_);
v___x_4937_ = v___x_4931_;
goto v_reusejp_4936_;
}
else
{
lean_object* v_reuseFailAlloc_4942_; 
v_reuseFailAlloc_4942_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_4942_, 0, v___x_4934_);
lean_ctor_set(v_reuseFailAlloc_4942_, 1, v_nextMacroScope_4922_);
lean_ctor_set(v_reuseFailAlloc_4942_, 2, v_ngen_4923_);
lean_ctor_set(v_reuseFailAlloc_4942_, 3, v_auxDeclNGen_4924_);
lean_ctor_set(v_reuseFailAlloc_4942_, 4, v_traceState_4925_);
lean_ctor_set(v_reuseFailAlloc_4942_, 5, v___x_4935_);
lean_ctor_set(v_reuseFailAlloc_4942_, 6, v_recordedDeps_4926_);
lean_ctor_set(v_reuseFailAlloc_4942_, 7, v_messages_4927_);
lean_ctor_set(v_reuseFailAlloc_4942_, 8, v_infoState_4928_);
lean_ctor_set(v_reuseFailAlloc_4942_, 9, v_snapshotTasks_4929_);
v___x_4937_ = v_reuseFailAlloc_4942_;
goto v_reusejp_4936_;
}
v_reusejp_4936_:
{
lean_object* v___x_4938_; lean_object* v___x_4940_; 
v___x_4938_ = lean_st_ref_put(v___y_4905_, v___x_4937_);
if (v_isShared_4918_ == 0)
{
lean_ctor_set(v___x_4917_, 0, v___x_4933_);
v___x_4940_ = v___x_4917_;
goto v_reusejp_4939_;
}
else
{
lean_object* v_reuseFailAlloc_4941_; 
v_reuseFailAlloc_4941_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4941_, 0, v___x_4933_);
v___x_4940_ = v_reuseFailAlloc_4941_;
goto v_reusejp_4939_;
}
v_reusejp_4939_:
{
return v___x_4940_;
}
}
}
}
}
else
{
lean_object* v_a_4946_; lean_object* v___x_4948_; uint8_t v_isShared_4949_; uint8_t v_isSharedCheck_4953_; 
v_a_4946_ = lean_ctor_get(v___x_4914_, 0);
v_isSharedCheck_4953_ = !lean_is_exclusive(v___x_4914_);
if (v_isSharedCheck_4953_ == 0)
{
v___x_4948_ = v___x_4914_;
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
else
{
lean_inc(v_a_4946_);
lean_dec(v___x_4914_);
v___x_4948_ = lean_box(0);
v_isShared_4949_ = v_isSharedCheck_4953_;
goto v_resetjp_4947_;
}
v_resetjp_4947_:
{
lean_object* v___x_4951_; 
if (v_isShared_4949_ == 0)
{
v___x_4951_ = v___x_4948_;
goto v_reusejp_4950_;
}
else
{
lean_object* v_reuseFailAlloc_4952_; 
v_reuseFailAlloc_4952_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4952_, 0, v_a_4946_);
v___x_4951_ = v_reuseFailAlloc_4952_;
goto v_reusejp_4950_;
}
v_reusejp_4950_:
{
return v___x_4951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4954_, lean_object* v_declName_4955_, lean_object* v___y_4956_, lean_object* v___y_4957_, lean_object* v___y_4958_){
_start:
{
lean_object* v_res_4959_; 
v_res_4959_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4954_, v_declName_4955_, v___y_4956_, v___y_4957_);
lean_dec(v___y_4957_);
lean_dec_ref(v___y_4956_);
lean_dec_ref(v___x_4954_);
return v_res_4959_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4966_; uint64_t v___x_4967_; 
v___x_4966_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4967_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4966_);
return v___x_4967_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4968_; lean_object* v___x_4969_; lean_object* v___x_4970_; 
v___x_4968_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4969_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4970_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4970_, 0, v___x_4969_);
lean_ctor_set_uint64(v___x_4970_, sizeof(void*)*1, v___x_4968_);
return v___x_4970_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4971_; lean_object* v___x_4972_; 
v___x_4971_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___redArg___closed__0);
v___x_4972_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4972_, 0, v___x_4971_);
return v___x_4972_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4973_; lean_object* v___x_4974_; 
v___x_4973_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4974_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4974_, 0, v___x_4973_);
lean_ctor_set(v___x_4974_, 1, v___x_4973_);
lean_ctor_set(v___x_4974_, 2, v___x_4973_);
lean_ctor_set(v___x_4974_, 3, v___x_4973_);
lean_ctor_set(v___x_4974_, 4, v___x_4973_);
lean_ctor_set(v___x_4974_, 5, v___x_4973_);
return v___x_4974_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4975_; lean_object* v___x_4976_; 
v___x_4975_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4976_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4976_, 0, v___x_4975_);
lean_ctor_set(v___x_4976_, 1, v___x_4975_);
lean_ctor_set(v___x_4976_, 2, v___x_4975_);
lean_ctor_set(v___x_4976_, 3, v___x_4975_);
lean_ctor_set(v___x_4976_, 4, v___x_4975_);
return v___x_4976_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4977_, lean_object* v___x_4978_, lean_object* v_declName_4979_, lean_object* v_stx_4980_, uint8_t v_attrKind_4981_, lean_object* v___y_4982_, lean_object* v___y_4983_){
_start:
{
lean_object* v___x_4985_; lean_object* v___x_4986_; lean_object* v___x_4987_; 
v___x_4985_ = lean_unsigned_to_nat(1u);
v___x_4986_ = l_Lean_Syntax_getArg(v_stx_4980_, v___x_4985_);
v___x_4987_ = l_Lean_getAttrParamOptPrio(v___x_4986_, v___y_4982_, v___y_4983_);
if (lean_obj_tag(v___x_4987_) == 0)
{
lean_object* v_a_4988_; uint8_t v___x_4989_; uint8_t v___x_4990_; lean_object* v___x_4991_; lean_object* v___x_4992_; lean_object* v___x_4993_; lean_object* v___x_4994_; lean_object* v___x_4995_; size_t v___x_4996_; lean_object* v___x_4997_; lean_object* v___x_4998_; lean_object* v___x_4999_; lean_object* v___x_5000_; lean_object* v___x_5001_; lean_object* v___x_5002_; lean_object* v___x_5003_; lean_object* v___x_5004_; lean_object* v___x_5005_; lean_object* v___x_5006_; lean_object* v___x_5007_; lean_object* v___x_5008_; lean_object* v___x_5009_; 
v_a_4988_ = lean_ctor_get(v___x_4987_, 0);
lean_inc(v_a_4988_);
lean_dec_ref_known(v___x_4987_, 1);
v___x_4989_ = 0;
v___x_4990_ = 1;
v___x_4991_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4992_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4993_ = lean_unsigned_to_nat(32u);
v___x_4994_ = lean_mk_empty_array_with_capacity(v___x_4993_);
v___x_4995_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4996_ = ((size_t)5ULL);
lean_inc_n(v___x_4977_, 6);
v___x_4997_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4997_, 0, v___x_4995_);
lean_ctor_set(v___x_4997_, 1, v___x_4994_);
lean_ctor_set(v___x_4997_, 2, v___x_4977_);
lean_ctor_set(v___x_4997_, 3, v___x_4977_);
lean_ctor_set_usize(v___x_4997_, 4, v___x_4996_);
v___x_4998_ = lean_box(1);
lean_inc_ref(v___x_4997_);
v___x_4999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4999_, 0, v___x_4992_);
lean_ctor_set(v___x_4999_, 1, v___x_4997_);
lean_ctor_set(v___x_4999_, 2, v___x_4998_);
v___x_5000_ = lean_mk_empty_array_with_capacity(v___x_4977_);
v___x_5001_ = lean_box(0);
lean_inc(v___x_4978_);
v___x_5002_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_5002_, 0, v___x_4991_);
lean_ctor_set(v___x_5002_, 1, v___x_4978_);
lean_ctor_set(v___x_5002_, 2, v___x_4999_);
lean_ctor_set(v___x_5002_, 3, v___x_5000_);
lean_ctor_set(v___x_5002_, 4, v___x_5001_);
lean_ctor_set(v___x_5002_, 5, v___x_4977_);
lean_ctor_set(v___x_5002_, 6, v___x_5001_);
lean_ctor_set_uint8(v___x_5002_, sizeof(void*)*7, v___x_4989_);
lean_ctor_set_uint8(v___x_5002_, sizeof(void*)*7 + 1, v___x_4989_);
lean_ctor_set_uint8(v___x_5002_, sizeof(void*)*7 + 2, v___x_4989_);
lean_ctor_set_uint8(v___x_5002_, sizeof(void*)*7 + 3, v___x_4990_);
v___x_5003_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_5003_, 0, v___x_4977_);
lean_ctor_set(v___x_5003_, 1, v___x_4977_);
lean_ctor_set(v___x_5003_, 2, v___x_4977_);
lean_ctor_set(v___x_5003_, 3, v___x_4977_);
lean_ctor_set(v___x_5003_, 4, v___x_4992_);
lean_ctor_set(v___x_5003_, 5, v___x_4992_);
lean_ctor_set(v___x_5003_, 6, v___x_4992_);
lean_ctor_set(v___x_5003_, 7, v___x_4992_);
lean_ctor_set(v___x_5003_, 8, v___x_4992_);
lean_ctor_set(v___x_5003_, 9, v___x_4992_);
lean_ctor_set(v___x_5003_, 10, v___x_4992_);
v___x_5004_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5005_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5006_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5006_, 0, v___x_5003_);
lean_ctor_set(v___x_5006_, 1, v___x_5004_);
lean_ctor_set(v___x_5006_, 2, v___x_4978_);
lean_ctor_set(v___x_5006_, 3, v___x_4997_);
lean_ctor_set(v___x_5006_, 4, v___x_5005_);
v___x_5007_ = lean_box(0);
v___x_5008_ = lean_st_mk_ref(v___x_5006_);
v___x_5009_ = l_Lean_Meta_addInstance(v_declName_4979_, v_attrKind_4981_, v_a_4988_, v___x_5002_, v___x_5008_, v___y_4982_, v___y_4983_);
lean_dec_ref_known(v___x_5002_, 7);
if (lean_obj_tag(v___x_5009_) == 0)
{
lean_object* v___x_5011_; uint8_t v_isShared_5012_; uint8_t v_isSharedCheck_5017_; 
v_isSharedCheck_5017_ = !lean_is_exclusive(v___x_5009_);
if (v_isSharedCheck_5017_ == 0)
{
lean_object* v_unused_5018_; 
v_unused_5018_ = lean_ctor_get(v___x_5009_, 0);
lean_dec(v_unused_5018_);
v___x_5011_ = v___x_5009_;
v_isShared_5012_ = v_isSharedCheck_5017_;
goto v_resetjp_5010_;
}
else
{
lean_dec(v___x_5009_);
v___x_5011_ = lean_box(0);
v_isShared_5012_ = v_isSharedCheck_5017_;
goto v_resetjp_5010_;
}
v_resetjp_5010_:
{
lean_object* v___x_5013_; lean_object* v___x_5015_; 
v___x_5013_ = lean_st_ref_get(v___x_5008_);
lean_dec(v___x_5008_);
lean_dec(v___x_5013_);
if (v_isShared_5012_ == 0)
{
lean_ctor_set(v___x_5011_, 0, v___x_5007_);
v___x_5015_ = v___x_5011_;
goto v_reusejp_5014_;
}
else
{
lean_object* v_reuseFailAlloc_5016_; 
v_reuseFailAlloc_5016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5016_, 0, v___x_5007_);
v___x_5015_ = v_reuseFailAlloc_5016_;
goto v_reusejp_5014_;
}
v_reusejp_5014_:
{
return v___x_5015_;
}
}
}
else
{
lean_dec(v___x_5008_);
return v___x_5009_;
}
}
else
{
lean_object* v_a_5019_; lean_object* v___x_5021_; uint8_t v_isShared_5022_; uint8_t v_isSharedCheck_5026_; 
lean_dec(v_declName_4979_);
lean_dec(v___x_4978_);
lean_dec(v___x_4977_);
v_a_5019_ = lean_ctor_get(v___x_4987_, 0);
v_isSharedCheck_5026_ = !lean_is_exclusive(v___x_4987_);
if (v_isSharedCheck_5026_ == 0)
{
v___x_5021_ = v___x_4987_;
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
else
{
lean_inc(v_a_5019_);
lean_dec(v___x_4987_);
v___x_5021_ = lean_box(0);
v_isShared_5022_ = v_isSharedCheck_5026_;
goto v_resetjp_5020_;
}
v_resetjp_5020_:
{
lean_object* v___x_5024_; 
if (v_isShared_5022_ == 0)
{
v___x_5024_ = v___x_5021_;
goto v_reusejp_5023_;
}
else
{
lean_object* v_reuseFailAlloc_5025_; 
v_reuseFailAlloc_5025_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5025_, 0, v_a_5019_);
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
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_5027_, lean_object* v___x_5028_, lean_object* v_declName_5029_, lean_object* v_stx_5030_, lean_object* v_attrKind_5031_, lean_object* v___y_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_){
_start:
{
uint8_t v_attrKind_boxed_5035_; lean_object* v_res_5036_; 
v_attrKind_boxed_5035_ = lean_unbox(v_attrKind_5031_);
v_res_5036_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_5027_, v___x_5028_, v_declName_5029_, v_stx_5030_, v_attrKind_boxed_5035_, v___y_5032_, v___y_5033_);
lean_dec(v___y_5033_);
lean_dec_ref(v___y_5032_);
lean_dec(v_stx_5030_);
return v_res_5036_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_5037_; lean_object* v___f_5038_; 
v___x_5037_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_5038_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_5038_, 0, v___x_5037_);
return v___f_5038_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_5105_; lean_object* v___f_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___f_5105_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_5106_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5107_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5108_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5108_, 0, v___x_5107_);
lean_ctor_set(v___x_5108_, 1, v___f_5106_);
lean_ctor_set(v___x_5108_, 2, v___f_5105_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5110_; lean_object* v___x_5111_; 
v___x_5110_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5111_ = l_Lean_registerBuiltinAttribute(v___x_5110_);
return v___x_5111_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5113_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_5114_, lean_object* v_x_5115_, lean_object* v_x_5116_){
_start:
{
uint8_t v___x_5117_; 
v___x_5117_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_5115_, v_x_5116_);
return v___x_5117_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_5118_, lean_object* v_x_5119_, lean_object* v_x_5120_){
_start:
{
uint8_t v_res_5121_; lean_object* v_r_5122_; 
v_res_5121_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_5118_, v_x_5119_, v_x_5120_);
lean_dec(v_x_5120_);
lean_dec_ref(v_x_5119_);
v_r_5122_ = lean_box(v_res_5121_);
return v_r_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_5123_, lean_object* v_msg_5124_, lean_object* v___y_5125_, lean_object* v___y_5126_){
_start:
{
lean_object* v___x_5128_; 
v___x_5128_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_5124_, v___y_5125_, v___y_5126_);
return v___x_5128_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_5129_, lean_object* v_msg_5130_, lean_object* v___y_5131_, lean_object* v___y_5132_, lean_object* v___y_5133_){
_start:
{
lean_object* v_res_5134_; 
v_res_5134_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_5129_, v_msg_5130_, v___y_5131_, v___y_5132_);
lean_dec(v___y_5132_);
lean_dec_ref(v___y_5131_);
return v_res_5134_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5135_, lean_object* v_x_5136_, size_t v_x_5137_, lean_object* v_x_5138_){
_start:
{
uint8_t v___x_5139_; 
v___x_5139_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5136_, v_x_5137_, v_x_5138_);
return v___x_5139_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5140_, lean_object* v_x_5141_, lean_object* v_x_5142_, lean_object* v_x_5143_){
_start:
{
size_t v_x_3057__boxed_5144_; uint8_t v_res_5145_; lean_object* v_r_5146_; 
v_x_3057__boxed_5144_ = lean_unbox_usize(v_x_5142_);
lean_dec(v_x_5142_);
v_res_5145_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_5140_, v_x_5141_, v_x_3057__boxed_5144_, v_x_5143_);
lean_dec(v_x_5143_);
lean_dec_ref(v_x_5141_);
v_r_5146_ = lean_box(v_res_5145_);
return v_r_5146_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5147_, lean_object* v_keys_5148_, lean_object* v_vals_5149_, lean_object* v_heq_5150_, lean_object* v_i_5151_, lean_object* v_k_5152_){
_start:
{
uint8_t v___x_5153_; 
v___x_5153_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_5148_, v_i_5151_, v_k_5152_);
return v___x_5153_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5154_, lean_object* v_keys_5155_, lean_object* v_vals_5156_, lean_object* v_heq_5157_, lean_object* v_i_5158_, lean_object* v_k_5159_){
_start:
{
uint8_t v_res_5160_; lean_object* v_r_5161_; 
v_res_5160_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_5154_, v_keys_5155_, v_vals_5156_, v_heq_5157_, v_i_5158_, v_k_5159_);
lean_dec(v_k_5159_);
lean_dec_ref(v_vals_5156_);
lean_dec_ref(v_keys_5155_);
v_r_5161_ = lean_box(v_res_5160_);
return v_r_5161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_5164_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5165_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5166_ = l_Lean_addBuiltinDocString(v___x_5164_, v___x_5165_);
return v___x_5166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5167_){
_start:
{
lean_object* v_res_5168_; 
v_res_5168_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_5169_){
_start:
{
lean_object* v___x_5171_; lean_object* v___x_5172_; lean_object* v_env_5173_; lean_object* v___x_5174_; lean_object* v_ext_5175_; lean_object* v_toEnvExtension_5176_; lean_object* v_asyncMode_5177_; lean_object* v___x_5178_; lean_object* v_discrTree_5179_; lean_object* v___x_5180_; 
v___x_5171_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5172_ = lean_st_ref_get(v_a_5169_);
v_env_5173_ = lean_ctor_get(v___x_5172_, 0);
lean_inc_ref(v_env_5173_);
lean_dec(v___x_5172_);
v___x_5174_ = l_Lean_Meta_instanceExtension;
v_ext_5175_ = lean_ctor_get(v___x_5174_, 1);
v_toEnvExtension_5176_ = lean_ctor_get(v_ext_5175_, 0);
v_asyncMode_5177_ = lean_ctor_get(v_toEnvExtension_5176_, 2);
v___x_5178_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5171_, v___x_5174_, v_env_5173_, v_asyncMode_5177_);
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
lean_object* v___x_5194_; lean_object* v___x_5195_; lean_object* v_env_5196_; lean_object* v___x_5197_; lean_object* v_ext_5198_; lean_object* v_toEnvExtension_5199_; lean_object* v_asyncMode_5200_; lean_object* v___x_5201_; lean_object* v_erased_5202_; lean_object* v___x_5203_; 
v___x_5194_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5195_ = lean_st_ref_get(v_a_5192_);
v_env_5196_ = lean_ctor_get(v___x_5195_, 0);
lean_inc_ref(v_env_5196_);
lean_dec(v___x_5195_);
v___x_5197_ = l_Lean_Meta_instanceExtension;
v_ext_5198_ = lean_ctor_get(v___x_5197_, 1);
v_toEnvExtension_5199_ = lean_ctor_get(v_ext_5198_, 0);
v_asyncMode_5200_ = lean_ctor_get(v_toEnvExtension_5199_, 2);
v___x_5201_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5194_, v___x_5197_, v_env_5196_, v_asyncMode_5200_);
v_erased_5202_ = lean_ctor_get(v___x_5201_, 2);
lean_inc_ref(v_erased_5202_);
lean_dec(v___x_5201_);
v___x_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5203_, 0, v_erased_5202_);
return v___x_5203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_5204_, lean_object* v_a_5205_){
_start:
{
lean_object* v_res_5206_; 
v_res_5206_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5204_);
lean_dec(v_a_5204_);
return v_res_5206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_5207_, lean_object* v_a_5208_){
_start:
{
lean_object* v___x_5210_; 
v___x_5210_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5208_);
return v___x_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_){
_start:
{
lean_object* v_res_5214_; 
v_res_5214_ = l_Lean_Meta_getErasedInstances(v_a_5211_, v_a_5212_);
lean_dec(v_a_5212_);
lean_dec_ref(v_a_5211_);
return v_res_5214_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_5215_, lean_object* v_declName_5216_){
_start:
{
lean_object* v___x_5217_; lean_object* v_ext_5218_; lean_object* v_toEnvExtension_5219_; lean_object* v_asyncMode_5220_; lean_object* v___x_5221_; lean_object* v___x_5222_; lean_object* v_instanceNames_5223_; uint8_t v___x_5224_; 
v___x_5217_ = l_Lean_Meta_instanceExtension;
v_ext_5218_ = lean_ctor_get(v___x_5217_, 1);
v_toEnvExtension_5219_ = lean_ctor_get(v_ext_5218_, 0);
v_asyncMode_5220_ = lean_ctor_get(v_toEnvExtension_5219_, 2);
v___x_5221_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5222_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5221_, v___x_5217_, v_env_5215_, v_asyncMode_5220_);
v_instanceNames_5223_ = lean_ctor_get(v___x_5222_, 1);
lean_inc_ref(v_instanceNames_5223_);
lean_dec(v___x_5222_);
v___x_5224_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_5223_, v_declName_5216_);
lean_dec_ref(v_instanceNames_5223_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_5225_, lean_object* v_declName_5226_){
_start:
{
uint8_t v_res_5227_; lean_object* v_r_5228_; 
v_res_5227_ = l_Lean_Meta_isInstanceCore(v_env_5225_, v_declName_5226_);
lean_dec(v_declName_5226_);
v_r_5228_ = lean_box(v_res_5227_);
return v_r_5228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_5229_, lean_object* v_a_5230_){
_start:
{
lean_object* v___x_5232_; lean_object* v_env_5233_; uint8_t v___x_5234_; lean_object* v___x_5235_; lean_object* v___x_5236_; 
v___x_5232_ = lean_st_ref_get(v_a_5230_);
v_env_5233_ = lean_ctor_get(v___x_5232_, 0);
lean_inc_ref(v_env_5233_);
lean_dec(v___x_5232_);
v___x_5234_ = l_Lean_Meta_isInstanceCore(v_env_5233_, v_declName_5229_);
v___x_5235_ = lean_box(v___x_5234_);
v___x_5236_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5236_, 0, v___x_5235_);
return v___x_5236_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_5237_, lean_object* v_a_5238_, lean_object* v_a_5239_){
_start:
{
lean_object* v_res_5240_; 
v_res_5240_ = l_Lean_Meta_isInstance___redArg(v_declName_5237_, v_a_5238_);
lean_dec(v_a_5238_);
lean_dec(v_declName_5237_);
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_5241_, lean_object* v_a_5242_, lean_object* v_a_5243_){
_start:
{
lean_object* v___x_5245_; 
v___x_5245_ = l_Lean_Meta_isInstance___redArg(v_declName_5241_, v_a_5243_);
return v___x_5245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_, lean_object* v_a_5249_){
_start:
{
lean_object* v_res_5250_; 
v_res_5250_ = l_Lean_Meta_isInstance(v_declName_5246_, v_a_5247_, v_a_5248_);
lean_dec(v_a_5248_);
lean_dec_ref(v_a_5247_);
lean_dec(v_declName_5246_);
return v_res_5250_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5251_, lean_object* v_vals_5252_, lean_object* v_i_5253_, lean_object* v_k_5254_){
_start:
{
lean_object* v___x_5255_; uint8_t v___x_5256_; 
v___x_5255_ = lean_array_get_size(v_keys_5251_);
v___x_5256_ = lean_nat_dec_lt(v_i_5253_, v___x_5255_);
if (v___x_5256_ == 0)
{
lean_object* v___x_5257_; 
lean_dec(v_i_5253_);
v___x_5257_ = lean_box(0);
return v___x_5257_;
}
else
{
lean_object* v_k_x27_5258_; uint8_t v___x_5259_; 
v_k_x27_5258_ = lean_array_fget_borrowed(v_keys_5251_, v_i_5253_);
v___x_5259_ = lean_name_eq(v_k_5254_, v_k_x27_5258_);
if (v___x_5259_ == 0)
{
lean_object* v___x_5260_; lean_object* v___x_5261_; 
v___x_5260_ = lean_unsigned_to_nat(1u);
v___x_5261_ = lean_nat_add(v_i_5253_, v___x_5260_);
lean_dec(v_i_5253_);
v_i_5253_ = v___x_5261_;
goto _start;
}
else
{
lean_object* v___x_5263_; lean_object* v___x_5264_; 
v___x_5263_ = lean_array_fget_borrowed(v_vals_5252_, v_i_5253_);
lean_dec(v_i_5253_);
lean_inc(v___x_5263_);
v___x_5264_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5264_, 0, v___x_5263_);
return v___x_5264_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5265_, lean_object* v_vals_5266_, lean_object* v_i_5267_, lean_object* v_k_5268_){
_start:
{
lean_object* v_res_5269_; 
v_res_5269_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5265_, v_vals_5266_, v_i_5267_, v_k_5268_);
lean_dec(v_k_5268_);
lean_dec_ref(v_vals_5266_);
lean_dec_ref(v_keys_5265_);
return v_res_5269_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_5270_, size_t v_x_5271_, lean_object* v_x_5272_){
_start:
{
if (lean_obj_tag(v_x_5270_) == 0)
{
lean_object* v_es_5273_; lean_object* v___x_5274_; size_t v___x_5275_; size_t v___x_5276_; lean_object* v_j_5277_; lean_object* v___x_5278_; 
v_es_5273_ = lean_ctor_get(v_x_5270_, 0);
v___x_5274_ = lean_box(2);
v___x_5275_ = ((size_t)31ULL);
v___x_5276_ = lean_usize_land(v_x_5271_, v___x_5275_);
v_j_5277_ = lean_usize_to_nat(v___x_5276_);
v___x_5278_ = lean_array_get_borrowed(v___x_5274_, v_es_5273_, v_j_5277_);
lean_dec(v_j_5277_);
switch(lean_obj_tag(v___x_5278_))
{
case 0:
{
lean_object* v_key_5279_; lean_object* v_val_5280_; uint8_t v___x_5281_; 
v_key_5279_ = lean_ctor_get(v___x_5278_, 0);
v_val_5280_ = lean_ctor_get(v___x_5278_, 1);
v___x_5281_ = lean_name_eq(v_x_5272_, v_key_5279_);
if (v___x_5281_ == 0)
{
lean_object* v___x_5282_; 
v___x_5282_ = lean_box(0);
return v___x_5282_;
}
else
{
lean_object* v___x_5283_; 
lean_inc(v_val_5280_);
v___x_5283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5283_, 0, v_val_5280_);
return v___x_5283_;
}
}
case 1:
{
lean_object* v_node_5284_; size_t v___x_5285_; size_t v___x_5286_; 
v_node_5284_ = lean_ctor_get(v___x_5278_, 0);
v___x_5285_ = ((size_t)5ULL);
v___x_5286_ = lean_usize_shift_right(v_x_5271_, v___x_5285_);
v_x_5270_ = v_node_5284_;
v_x_5271_ = v___x_5286_;
goto _start;
}
default: 
{
lean_object* v___x_5288_; 
v___x_5288_ = lean_box(0);
return v___x_5288_;
}
}
}
else
{
lean_object* v_ks_5289_; lean_object* v_vs_5290_; lean_object* v___x_5291_; lean_object* v___x_5292_; 
v_ks_5289_ = lean_ctor_get(v_x_5270_, 0);
v_vs_5290_ = lean_ctor_get(v_x_5270_, 1);
v___x_5291_ = lean_unsigned_to_nat(0u);
v___x_5292_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5289_, v_vs_5290_, v___x_5291_, v_x_5272_);
return v___x_5292_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5293_, lean_object* v_x_5294_, lean_object* v_x_5295_){
_start:
{
size_t v_x_479__boxed_5296_; lean_object* v_res_5297_; 
v_x_479__boxed_5296_ = lean_unbox_usize(v_x_5294_);
lean_dec(v_x_5294_);
v_res_5297_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5293_, v_x_479__boxed_5296_, v_x_5295_);
lean_dec(v_x_5295_);
lean_dec_ref(v_x_5293_);
return v_res_5297_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_5298_, lean_object* v_x_5299_){
_start:
{
uint64_t v___y_5301_; 
if (lean_obj_tag(v_x_5299_) == 0)
{
uint64_t v___x_5304_; 
v___x_5304_ = 1723ULL;
v___y_5301_ = v___x_5304_;
goto v___jp_5300_;
}
else
{
uint64_t v_hash_5305_; 
v_hash_5305_ = lean_ctor_get_uint64(v_x_5299_, sizeof(void*)*2);
v___y_5301_ = v_hash_5305_;
goto v___jp_5300_;
}
v___jp_5300_:
{
size_t v___x_5302_; lean_object* v___x_5303_; 
v___x_5302_ = lean_uint64_to_usize(v___y_5301_);
v___x_5303_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5298_, v___x_5302_, v_x_5299_);
return v___x_5303_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_5306_, lean_object* v_x_5307_){
_start:
{
lean_object* v_res_5308_; 
v_res_5308_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5306_, v_x_5307_);
lean_dec(v_x_5307_);
lean_dec_ref(v_x_5306_);
return v_res_5308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_5309_, lean_object* v_a_5310_){
_start:
{
lean_object* v___x_5312_; lean_object* v___x_5313_; lean_object* v_env_5314_; lean_object* v___x_5315_; lean_object* v_ext_5316_; lean_object* v_toEnvExtension_5317_; lean_object* v_asyncMode_5318_; lean_object* v___x_5319_; lean_object* v_instanceNames_5320_; lean_object* v___x_5321_; 
v___x_5312_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5313_ = lean_st_ref_get(v_a_5310_);
v_env_5314_ = lean_ctor_get(v___x_5313_, 0);
lean_inc_ref(v_env_5314_);
lean_dec(v___x_5313_);
v___x_5315_ = l_Lean_Meta_instanceExtension;
v_ext_5316_ = lean_ctor_get(v___x_5315_, 1);
v_toEnvExtension_5317_ = lean_ctor_get(v_ext_5316_, 0);
v_asyncMode_5318_ = lean_ctor_get(v_toEnvExtension_5317_, 2);
v___x_5319_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5312_, v___x_5315_, v_env_5314_, v_asyncMode_5318_);
v_instanceNames_5320_ = lean_ctor_get(v___x_5319_, 1);
lean_inc_ref(v_instanceNames_5320_);
lean_dec(v___x_5319_);
v___x_5321_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5320_, v_declName_5309_);
lean_dec_ref(v_instanceNames_5320_);
if (lean_obj_tag(v___x_5321_) == 1)
{
lean_object* v_val_5322_; lean_object* v___x_5324_; uint8_t v_isShared_5325_; uint8_t v_isSharedCheck_5331_; 
v_val_5322_ = lean_ctor_get(v___x_5321_, 0);
v_isSharedCheck_5331_ = !lean_is_exclusive(v___x_5321_);
if (v_isSharedCheck_5331_ == 0)
{
v___x_5324_ = v___x_5321_;
v_isShared_5325_ = v_isSharedCheck_5331_;
goto v_resetjp_5323_;
}
else
{
lean_inc(v_val_5322_);
lean_dec(v___x_5321_);
v___x_5324_ = lean_box(0);
v_isShared_5325_ = v_isSharedCheck_5331_;
goto v_resetjp_5323_;
}
v_resetjp_5323_:
{
lean_object* v_priority_5326_; lean_object* v___x_5328_; 
v_priority_5326_ = lean_ctor_get(v_val_5322_, 2);
lean_inc(v_priority_5326_);
lean_dec(v_val_5322_);
if (v_isShared_5325_ == 0)
{
lean_ctor_set(v___x_5324_, 0, v_priority_5326_);
v___x_5328_ = v___x_5324_;
goto v_reusejp_5327_;
}
else
{
lean_object* v_reuseFailAlloc_5330_; 
v_reuseFailAlloc_5330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5330_, 0, v_priority_5326_);
v___x_5328_ = v_reuseFailAlloc_5330_;
goto v_reusejp_5327_;
}
v_reusejp_5327_:
{
lean_object* v___x_5329_; 
v___x_5329_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5329_, 0, v___x_5328_);
return v___x_5329_;
}
}
}
else
{
lean_object* v___x_5332_; lean_object* v___x_5333_; 
lean_dec(v___x_5321_);
v___x_5332_ = lean_box(0);
v___x_5333_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5333_, 0, v___x_5332_);
return v___x_5333_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_5334_, lean_object* v_a_5335_, lean_object* v_a_5336_){
_start:
{
lean_object* v_res_5337_; 
v_res_5337_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5334_, v_a_5335_);
lean_dec(v_a_5335_);
lean_dec(v_declName_5334_);
return v_res_5337_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_5338_, lean_object* v_a_5339_, lean_object* v_a_5340_){
_start:
{
lean_object* v___x_5342_; 
v___x_5342_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5338_, v_a_5340_);
return v___x_5342_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_5343_, lean_object* v_a_5344_, lean_object* v_a_5345_, lean_object* v_a_5346_){
_start:
{
lean_object* v_res_5347_; 
v_res_5347_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_5343_, v_a_5344_, v_a_5345_);
lean_dec(v_a_5345_);
lean_dec_ref(v_a_5344_);
lean_dec(v_declName_5343_);
return v_res_5347_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_5348_, lean_object* v_x_5349_, lean_object* v_x_5350_){
_start:
{
lean_object* v___x_5351_; 
v___x_5351_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5349_, v_x_5350_);
return v___x_5351_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_5352_, lean_object* v_x_5353_, lean_object* v_x_5354_){
_start:
{
lean_object* v_res_5355_; 
v_res_5355_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_5352_, v_x_5353_, v_x_5354_);
lean_dec(v_x_5354_);
lean_dec_ref(v_x_5353_);
return v_res_5355_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5356_, lean_object* v_x_5357_, size_t v_x_5358_, lean_object* v_x_5359_){
_start:
{
lean_object* v___x_5360_; 
v___x_5360_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5357_, v_x_5358_, v_x_5359_);
return v___x_5360_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5361_, lean_object* v_x_5362_, lean_object* v_x_5363_, lean_object* v_x_5364_){
_start:
{
size_t v_x_590__boxed_5365_; lean_object* v_res_5366_; 
v_x_590__boxed_5365_ = lean_unbox_usize(v_x_5363_);
lean_dec(v_x_5363_);
v_res_5366_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_5361_, v_x_5362_, v_x_590__boxed_5365_, v_x_5364_);
lean_dec(v_x_5364_);
lean_dec_ref(v_x_5362_);
return v_res_5366_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5367_, lean_object* v_keys_5368_, lean_object* v_vals_5369_, lean_object* v_heq_5370_, lean_object* v_i_5371_, lean_object* v_k_5372_){
_start:
{
lean_object* v___x_5373_; 
v___x_5373_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5368_, v_vals_5369_, v_i_5371_, v_k_5372_);
return v___x_5373_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5374_, lean_object* v_keys_5375_, lean_object* v_vals_5376_, lean_object* v_heq_5377_, lean_object* v_i_5378_, lean_object* v_k_5379_){
_start:
{
lean_object* v_res_5380_; 
v_res_5380_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5374_, v_keys_5375_, v_vals_5376_, v_heq_5377_, v_i_5378_, v_k_5379_);
lean_dec(v_k_5379_);
lean_dec_ref(v_vals_5376_);
lean_dec_ref(v_keys_5375_);
return v_res_5380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_5381_, lean_object* v_a_5382_){
_start:
{
lean_object* v___x_5384_; lean_object* v___x_5385_; lean_object* v_env_5386_; lean_object* v___x_5387_; lean_object* v_ext_5388_; lean_object* v_toEnvExtension_5389_; lean_object* v_asyncMode_5390_; lean_object* v___x_5391_; lean_object* v_instanceNames_5392_; lean_object* v___x_5393_; 
v___x_5384_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5385_ = lean_st_ref_get(v_a_5382_);
v_env_5386_ = lean_ctor_get(v___x_5385_, 0);
lean_inc_ref(v_env_5386_);
lean_dec(v___x_5385_);
v___x_5387_ = l_Lean_Meta_instanceExtension;
v_ext_5388_ = lean_ctor_get(v___x_5387_, 1);
v_toEnvExtension_5389_ = lean_ctor_get(v_ext_5388_, 0);
v_asyncMode_5390_ = lean_ctor_get(v_toEnvExtension_5389_, 2);
v___x_5391_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5384_, v___x_5387_, v_env_5386_, v_asyncMode_5390_);
v_instanceNames_5392_ = lean_ctor_get(v___x_5391_, 1);
lean_inc_ref(v_instanceNames_5392_);
lean_dec(v___x_5391_);
v___x_5393_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5392_, v_declName_5381_);
lean_dec_ref(v_instanceNames_5392_);
if (lean_obj_tag(v___x_5393_) == 1)
{
lean_object* v_val_5394_; lean_object* v___x_5396_; uint8_t v_isShared_5397_; uint8_t v_isSharedCheck_5404_; 
v_val_5394_ = lean_ctor_get(v___x_5393_, 0);
v_isSharedCheck_5404_ = !lean_is_exclusive(v___x_5393_);
if (v_isSharedCheck_5404_ == 0)
{
v___x_5396_ = v___x_5393_;
v_isShared_5397_ = v_isSharedCheck_5404_;
goto v_resetjp_5395_;
}
else
{
lean_inc(v_val_5394_);
lean_dec(v___x_5393_);
v___x_5396_ = lean_box(0);
v_isShared_5397_ = v_isSharedCheck_5404_;
goto v_resetjp_5395_;
}
v_resetjp_5395_:
{
uint8_t v_attrKind_5398_; lean_object* v___x_5399_; lean_object* v___x_5401_; 
v_attrKind_5398_ = lean_ctor_get_uint8(v_val_5394_, sizeof(void*)*5);
lean_dec(v_val_5394_);
v___x_5399_ = lean_box(v_attrKind_5398_);
if (v_isShared_5397_ == 0)
{
lean_ctor_set(v___x_5396_, 0, v___x_5399_);
v___x_5401_ = v___x_5396_;
goto v_reusejp_5400_;
}
else
{
lean_object* v_reuseFailAlloc_5403_; 
v_reuseFailAlloc_5403_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5403_, 0, v___x_5399_);
v___x_5401_ = v_reuseFailAlloc_5403_;
goto v_reusejp_5400_;
}
v_reusejp_5400_:
{
lean_object* v___x_5402_; 
v___x_5402_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5402_, 0, v___x_5401_);
return v___x_5402_;
}
}
}
else
{
lean_object* v___x_5405_; lean_object* v___x_5406_; 
lean_dec(v___x_5393_);
v___x_5405_ = lean_box(0);
v___x_5406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5406_, 0, v___x_5405_);
return v___x_5406_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_5407_, lean_object* v_a_5408_, lean_object* v_a_5409_){
_start:
{
lean_object* v_res_5410_; 
v_res_5410_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5407_, v_a_5408_);
lean_dec(v_a_5408_);
lean_dec(v_declName_5407_);
return v_res_5410_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_5411_, lean_object* v_a_5412_, lean_object* v_a_5413_){
_start:
{
lean_object* v___x_5415_; 
v___x_5415_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5411_, v_a_5413_);
return v___x_5415_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_5416_, lean_object* v_a_5417_, lean_object* v_a_5418_, lean_object* v_a_5419_){
_start:
{
lean_object* v_res_5420_; 
v_res_5420_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_5416_, v_a_5417_, v_a_5418_);
lean_dec(v_a_5418_);
lean_dec_ref(v_a_5417_);
lean_dec(v_declName_5416_);
return v_res_5420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5425_, lean_object* v_v_5426_, lean_object* v_t_5427_){
_start:
{
if (lean_obj_tag(v_t_5427_) == 0)
{
lean_object* v_size_5428_; lean_object* v_k_5429_; lean_object* v_v_5430_; lean_object* v_l_5431_; lean_object* v_r_5432_; lean_object* v___x_5434_; uint8_t v_isShared_5435_; uint8_t v_isSharedCheck_5713_; 
v_size_5428_ = lean_ctor_get(v_t_5427_, 0);
v_k_5429_ = lean_ctor_get(v_t_5427_, 1);
v_v_5430_ = lean_ctor_get(v_t_5427_, 2);
v_l_5431_ = lean_ctor_get(v_t_5427_, 3);
v_r_5432_ = lean_ctor_get(v_t_5427_, 4);
v_isSharedCheck_5713_ = !lean_is_exclusive(v_t_5427_);
if (v_isSharedCheck_5713_ == 0)
{
v___x_5434_ = v_t_5427_;
v_isShared_5435_ = v_isSharedCheck_5713_;
goto v_resetjp_5433_;
}
else
{
lean_inc(v_r_5432_);
lean_inc(v_l_5431_);
lean_inc(v_v_5430_);
lean_inc(v_k_5429_);
lean_inc(v_size_5428_);
lean_dec(v_t_5427_);
v___x_5434_ = lean_box(0);
v_isShared_5435_ = v_isSharedCheck_5713_;
goto v_resetjp_5433_;
}
v_resetjp_5433_:
{
uint8_t v___x_5436_; 
v___x_5436_ = lean_nat_dec_lt(v_k_5429_, v_k_5425_);
if (v___x_5436_ == 0)
{
uint8_t v___x_5437_; 
v___x_5437_ = lean_nat_dec_eq(v_k_5429_, v_k_5425_);
if (v___x_5437_ == 0)
{
lean_object* v_impl_5438_; lean_object* v___x_5439_; 
lean_dec(v_size_5428_);
v_impl_5438_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5425_, v_v_5426_, v_r_5432_);
v___x_5439_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5431_) == 0)
{
lean_object* v_size_5440_; lean_object* v_size_5441_; lean_object* v_k_5442_; lean_object* v_v_5443_; lean_object* v_l_5444_; lean_object* v_r_5445_; lean_object* v___x_5446_; lean_object* v___x_5447_; uint8_t v___x_5448_; 
v_size_5440_ = lean_ctor_get(v_l_5431_, 0);
v_size_5441_ = lean_ctor_get(v_impl_5438_, 0);
v_k_5442_ = lean_ctor_get(v_impl_5438_, 1);
v_v_5443_ = lean_ctor_get(v_impl_5438_, 2);
v_l_5444_ = lean_ctor_get(v_impl_5438_, 3);
lean_inc(v_l_5444_);
v_r_5445_ = lean_ctor_get(v_impl_5438_, 4);
v___x_5446_ = lean_unsigned_to_nat(3u);
v___x_5447_ = lean_nat_mul(v___x_5446_, v_size_5440_);
v___x_5448_ = lean_nat_dec_lt(v___x_5447_, v_size_5441_);
lean_dec(v___x_5447_);
if (v___x_5448_ == 0)
{
lean_object* v___x_5449_; lean_object* v___x_5450_; lean_object* v___x_5452_; 
lean_dec(v_l_5444_);
v___x_5449_ = lean_nat_add(v___x_5439_, v_size_5440_);
v___x_5450_ = lean_nat_add(v___x_5449_, v_size_5441_);
lean_dec(v___x_5449_);
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 4, v_impl_5438_);
lean_ctor_set(v___x_5434_, 0, v___x_5450_);
v___x_5452_ = v___x_5434_;
goto v_reusejp_5451_;
}
else
{
lean_object* v_reuseFailAlloc_5453_; 
v_reuseFailAlloc_5453_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5453_, 0, v___x_5450_);
lean_ctor_set(v_reuseFailAlloc_5453_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5453_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5453_, 3, v_l_5431_);
lean_ctor_set(v_reuseFailAlloc_5453_, 4, v_impl_5438_);
v___x_5452_ = v_reuseFailAlloc_5453_;
goto v_reusejp_5451_;
}
v_reusejp_5451_:
{
return v___x_5452_;
}
}
else
{
lean_object* v___x_5455_; uint8_t v_isShared_5456_; uint8_t v_isSharedCheck_5517_; 
lean_inc(v_r_5445_);
lean_inc(v_v_5443_);
lean_inc(v_k_5442_);
lean_inc(v_size_5441_);
v_isSharedCheck_5517_ = !lean_is_exclusive(v_impl_5438_);
if (v_isSharedCheck_5517_ == 0)
{
lean_object* v_unused_5518_; lean_object* v_unused_5519_; lean_object* v_unused_5520_; lean_object* v_unused_5521_; lean_object* v_unused_5522_; 
v_unused_5518_ = lean_ctor_get(v_impl_5438_, 4);
lean_dec(v_unused_5518_);
v_unused_5519_ = lean_ctor_get(v_impl_5438_, 3);
lean_dec(v_unused_5519_);
v_unused_5520_ = lean_ctor_get(v_impl_5438_, 2);
lean_dec(v_unused_5520_);
v_unused_5521_ = lean_ctor_get(v_impl_5438_, 1);
lean_dec(v_unused_5521_);
v_unused_5522_ = lean_ctor_get(v_impl_5438_, 0);
lean_dec(v_unused_5522_);
v___x_5455_ = v_impl_5438_;
v_isShared_5456_ = v_isSharedCheck_5517_;
goto v_resetjp_5454_;
}
else
{
lean_dec(v_impl_5438_);
v___x_5455_ = lean_box(0);
v_isShared_5456_ = v_isSharedCheck_5517_;
goto v_resetjp_5454_;
}
v_resetjp_5454_:
{
lean_object* v_size_5457_; lean_object* v_k_5458_; lean_object* v_v_5459_; lean_object* v_l_5460_; lean_object* v_r_5461_; lean_object* v_size_5462_; lean_object* v___x_5463_; lean_object* v___x_5464_; uint8_t v___x_5465_; 
v_size_5457_ = lean_ctor_get(v_l_5444_, 0);
v_k_5458_ = lean_ctor_get(v_l_5444_, 1);
v_v_5459_ = lean_ctor_get(v_l_5444_, 2);
v_l_5460_ = lean_ctor_get(v_l_5444_, 3);
v_r_5461_ = lean_ctor_get(v_l_5444_, 4);
v_size_5462_ = lean_ctor_get(v_r_5445_, 0);
v___x_5463_ = lean_unsigned_to_nat(2u);
v___x_5464_ = lean_nat_mul(v___x_5463_, v_size_5462_);
v___x_5465_ = lean_nat_dec_lt(v_size_5457_, v___x_5464_);
lean_dec(v___x_5464_);
if (v___x_5465_ == 0)
{
lean_object* v___x_5467_; uint8_t v_isShared_5468_; uint8_t v_isSharedCheck_5493_; 
lean_inc(v_r_5461_);
lean_inc(v_l_5460_);
lean_inc(v_v_5459_);
lean_inc(v_k_5458_);
v_isSharedCheck_5493_ = !lean_is_exclusive(v_l_5444_);
if (v_isSharedCheck_5493_ == 0)
{
lean_object* v_unused_5494_; lean_object* v_unused_5495_; lean_object* v_unused_5496_; lean_object* v_unused_5497_; lean_object* v_unused_5498_; 
v_unused_5494_ = lean_ctor_get(v_l_5444_, 4);
lean_dec(v_unused_5494_);
v_unused_5495_ = lean_ctor_get(v_l_5444_, 3);
lean_dec(v_unused_5495_);
v_unused_5496_ = lean_ctor_get(v_l_5444_, 2);
lean_dec(v_unused_5496_);
v_unused_5497_ = lean_ctor_get(v_l_5444_, 1);
lean_dec(v_unused_5497_);
v_unused_5498_ = lean_ctor_get(v_l_5444_, 0);
lean_dec(v_unused_5498_);
v___x_5467_ = v_l_5444_;
v_isShared_5468_ = v_isSharedCheck_5493_;
goto v_resetjp_5466_;
}
else
{
lean_dec(v_l_5444_);
v___x_5467_ = lean_box(0);
v_isShared_5468_ = v_isSharedCheck_5493_;
goto v_resetjp_5466_;
}
v_resetjp_5466_:
{
lean_object* v___x_5469_; lean_object* v___x_5470_; lean_object* v___y_5472_; lean_object* v___y_5473_; lean_object* v___y_5474_; lean_object* v___y_5483_; 
v___x_5469_ = lean_nat_add(v___x_5439_, v_size_5440_);
v___x_5470_ = lean_nat_add(v___x_5469_, v_size_5441_);
lean_dec(v_size_5441_);
if (lean_obj_tag(v_l_5460_) == 0)
{
lean_object* v_size_5491_; 
v_size_5491_ = lean_ctor_get(v_l_5460_, 0);
lean_inc(v_size_5491_);
v___y_5483_ = v_size_5491_;
goto v___jp_5482_;
}
else
{
lean_object* v___x_5492_; 
v___x_5492_ = lean_unsigned_to_nat(0u);
v___y_5483_ = v___x_5492_;
goto v___jp_5482_;
}
v___jp_5471_:
{
lean_object* v___x_5475_; lean_object* v___x_5477_; 
v___x_5475_ = lean_nat_add(v___y_5472_, v___y_5474_);
lean_dec(v___y_5474_);
lean_dec(v___y_5472_);
if (v_isShared_5468_ == 0)
{
lean_ctor_set(v___x_5467_, 4, v_r_5445_);
lean_ctor_set(v___x_5467_, 3, v_r_5461_);
lean_ctor_set(v___x_5467_, 2, v_v_5443_);
lean_ctor_set(v___x_5467_, 1, v_k_5442_);
lean_ctor_set(v___x_5467_, 0, v___x_5475_);
v___x_5477_ = v___x_5467_;
goto v_reusejp_5476_;
}
else
{
lean_object* v_reuseFailAlloc_5481_; 
v_reuseFailAlloc_5481_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5481_, 0, v___x_5475_);
lean_ctor_set(v_reuseFailAlloc_5481_, 1, v_k_5442_);
lean_ctor_set(v_reuseFailAlloc_5481_, 2, v_v_5443_);
lean_ctor_set(v_reuseFailAlloc_5481_, 3, v_r_5461_);
lean_ctor_set(v_reuseFailAlloc_5481_, 4, v_r_5445_);
v___x_5477_ = v_reuseFailAlloc_5481_;
goto v_reusejp_5476_;
}
v_reusejp_5476_:
{
lean_object* v___x_5479_; 
if (v_isShared_5456_ == 0)
{
lean_ctor_set(v___x_5455_, 4, v___x_5477_);
lean_ctor_set(v___x_5455_, 3, v___y_5473_);
lean_ctor_set(v___x_5455_, 2, v_v_5459_);
lean_ctor_set(v___x_5455_, 1, v_k_5458_);
lean_ctor_set(v___x_5455_, 0, v___x_5470_);
v___x_5479_ = v___x_5455_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5480_; 
v_reuseFailAlloc_5480_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5480_, 0, v___x_5470_);
lean_ctor_set(v_reuseFailAlloc_5480_, 1, v_k_5458_);
lean_ctor_set(v_reuseFailAlloc_5480_, 2, v_v_5459_);
lean_ctor_set(v_reuseFailAlloc_5480_, 3, v___y_5473_);
lean_ctor_set(v_reuseFailAlloc_5480_, 4, v___x_5477_);
v___x_5479_ = v_reuseFailAlloc_5480_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
return v___x_5479_;
}
}
}
v___jp_5482_:
{
lean_object* v___x_5484_; lean_object* v___x_5486_; 
v___x_5484_ = lean_nat_add(v___x_5469_, v___y_5483_);
lean_dec(v___y_5483_);
lean_dec(v___x_5469_);
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 4, v_l_5460_);
lean_ctor_set(v___x_5434_, 0, v___x_5484_);
v___x_5486_ = v___x_5434_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v___x_5484_);
lean_ctor_set(v_reuseFailAlloc_5490_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5490_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5490_, 3, v_l_5431_);
lean_ctor_set(v_reuseFailAlloc_5490_, 4, v_l_5460_);
v___x_5486_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
lean_object* v___x_5487_; 
v___x_5487_ = lean_nat_add(v___x_5439_, v_size_5462_);
if (lean_obj_tag(v_r_5461_) == 0)
{
lean_object* v_size_5488_; 
v_size_5488_ = lean_ctor_get(v_r_5461_, 0);
lean_inc(v_size_5488_);
v___y_5472_ = v___x_5487_;
v___y_5473_ = v___x_5486_;
v___y_5474_ = v_size_5488_;
goto v___jp_5471_;
}
else
{
lean_object* v___x_5489_; 
v___x_5489_ = lean_unsigned_to_nat(0u);
v___y_5472_ = v___x_5487_;
v___y_5473_ = v___x_5486_;
v___y_5474_ = v___x_5489_;
goto v___jp_5471_;
}
}
}
}
}
else
{
lean_object* v___x_5499_; lean_object* v___x_5500_; lean_object* v___x_5501_; lean_object* v___x_5503_; 
lean_del_object(v___x_5434_);
v___x_5499_ = lean_nat_add(v___x_5439_, v_size_5440_);
v___x_5500_ = lean_nat_add(v___x_5499_, v_size_5441_);
lean_dec(v_size_5441_);
v___x_5501_ = lean_nat_add(v___x_5499_, v_size_5457_);
lean_dec(v___x_5499_);
lean_inc_ref(v_l_5431_);
if (v_isShared_5456_ == 0)
{
lean_ctor_set(v___x_5455_, 4, v_l_5444_);
lean_ctor_set(v___x_5455_, 3, v_l_5431_);
lean_ctor_set(v___x_5455_, 2, v_v_5430_);
lean_ctor_set(v___x_5455_, 1, v_k_5429_);
lean_ctor_set(v___x_5455_, 0, v___x_5501_);
v___x_5503_ = v___x_5455_;
goto v_reusejp_5502_;
}
else
{
lean_object* v_reuseFailAlloc_5516_; 
v_reuseFailAlloc_5516_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5516_, 0, v___x_5501_);
lean_ctor_set(v_reuseFailAlloc_5516_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5516_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5516_, 3, v_l_5431_);
lean_ctor_set(v_reuseFailAlloc_5516_, 4, v_l_5444_);
v___x_5503_ = v_reuseFailAlloc_5516_;
goto v_reusejp_5502_;
}
v_reusejp_5502_:
{
lean_object* v___x_5505_; uint8_t v_isShared_5506_; uint8_t v_isSharedCheck_5510_; 
v_isSharedCheck_5510_ = !lean_is_exclusive(v_l_5431_);
if (v_isSharedCheck_5510_ == 0)
{
lean_object* v_unused_5511_; lean_object* v_unused_5512_; lean_object* v_unused_5513_; lean_object* v_unused_5514_; lean_object* v_unused_5515_; 
v_unused_5511_ = lean_ctor_get(v_l_5431_, 4);
lean_dec(v_unused_5511_);
v_unused_5512_ = lean_ctor_get(v_l_5431_, 3);
lean_dec(v_unused_5512_);
v_unused_5513_ = lean_ctor_get(v_l_5431_, 2);
lean_dec(v_unused_5513_);
v_unused_5514_ = lean_ctor_get(v_l_5431_, 1);
lean_dec(v_unused_5514_);
v_unused_5515_ = lean_ctor_get(v_l_5431_, 0);
lean_dec(v_unused_5515_);
v___x_5505_ = v_l_5431_;
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
else
{
lean_dec(v_l_5431_);
v___x_5505_ = lean_box(0);
v_isShared_5506_ = v_isSharedCheck_5510_;
goto v_resetjp_5504_;
}
v_resetjp_5504_:
{
lean_object* v___x_5508_; 
if (v_isShared_5506_ == 0)
{
lean_ctor_set(v___x_5505_, 4, v_r_5445_);
lean_ctor_set(v___x_5505_, 3, v___x_5503_);
lean_ctor_set(v___x_5505_, 2, v_v_5443_);
lean_ctor_set(v___x_5505_, 1, v_k_5442_);
lean_ctor_set(v___x_5505_, 0, v___x_5500_);
v___x_5508_ = v___x_5505_;
goto v_reusejp_5507_;
}
else
{
lean_object* v_reuseFailAlloc_5509_; 
v_reuseFailAlloc_5509_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5509_, 0, v___x_5500_);
lean_ctor_set(v_reuseFailAlloc_5509_, 1, v_k_5442_);
lean_ctor_set(v_reuseFailAlloc_5509_, 2, v_v_5443_);
lean_ctor_set(v_reuseFailAlloc_5509_, 3, v___x_5503_);
lean_ctor_set(v_reuseFailAlloc_5509_, 4, v_r_5445_);
v___x_5508_ = v_reuseFailAlloc_5509_;
goto v_reusejp_5507_;
}
v_reusejp_5507_:
{
return v___x_5508_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5523_; 
v_l_5523_ = lean_ctor_get(v_impl_5438_, 3);
lean_inc(v_l_5523_);
if (lean_obj_tag(v_l_5523_) == 0)
{
lean_object* v_r_5524_; lean_object* v_k_5525_; lean_object* v_v_5526_; lean_object* v___x_5528_; uint8_t v_isShared_5529_; uint8_t v_isSharedCheck_5549_; 
v_r_5524_ = lean_ctor_get(v_impl_5438_, 4);
v_k_5525_ = lean_ctor_get(v_impl_5438_, 1);
v_v_5526_ = lean_ctor_get(v_impl_5438_, 2);
v_isSharedCheck_5549_ = !lean_is_exclusive(v_impl_5438_);
if (v_isSharedCheck_5549_ == 0)
{
lean_object* v_unused_5550_; lean_object* v_unused_5551_; 
v_unused_5550_ = lean_ctor_get(v_impl_5438_, 3);
lean_dec(v_unused_5550_);
v_unused_5551_ = lean_ctor_get(v_impl_5438_, 0);
lean_dec(v_unused_5551_);
v___x_5528_ = v_impl_5438_;
v_isShared_5529_ = v_isSharedCheck_5549_;
goto v_resetjp_5527_;
}
else
{
lean_inc(v_r_5524_);
lean_inc(v_v_5526_);
lean_inc(v_k_5525_);
lean_dec(v_impl_5438_);
v___x_5528_ = lean_box(0);
v_isShared_5529_ = v_isSharedCheck_5549_;
goto v_resetjp_5527_;
}
v_resetjp_5527_:
{
lean_object* v_k_5530_; lean_object* v_v_5531_; lean_object* v___x_5533_; uint8_t v_isShared_5534_; uint8_t v_isSharedCheck_5545_; 
v_k_5530_ = lean_ctor_get(v_l_5523_, 1);
v_v_5531_ = lean_ctor_get(v_l_5523_, 2);
v_isSharedCheck_5545_ = !lean_is_exclusive(v_l_5523_);
if (v_isSharedCheck_5545_ == 0)
{
lean_object* v_unused_5546_; lean_object* v_unused_5547_; lean_object* v_unused_5548_; 
v_unused_5546_ = lean_ctor_get(v_l_5523_, 4);
lean_dec(v_unused_5546_);
v_unused_5547_ = lean_ctor_get(v_l_5523_, 3);
lean_dec(v_unused_5547_);
v_unused_5548_ = lean_ctor_get(v_l_5523_, 0);
lean_dec(v_unused_5548_);
v___x_5533_ = v_l_5523_;
v_isShared_5534_ = v_isSharedCheck_5545_;
goto v_resetjp_5532_;
}
else
{
lean_inc(v_v_5531_);
lean_inc(v_k_5530_);
lean_dec(v_l_5523_);
v___x_5533_ = lean_box(0);
v_isShared_5534_ = v_isSharedCheck_5545_;
goto v_resetjp_5532_;
}
v_resetjp_5532_:
{
lean_object* v___x_5535_; lean_object* v___x_5537_; 
v___x_5535_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5524_, 2);
if (v_isShared_5534_ == 0)
{
lean_ctor_set(v___x_5533_, 4, v_r_5524_);
lean_ctor_set(v___x_5533_, 3, v_r_5524_);
lean_ctor_set(v___x_5533_, 2, v_v_5430_);
lean_ctor_set(v___x_5533_, 1, v_k_5429_);
lean_ctor_set(v___x_5533_, 0, v___x_5439_);
v___x_5537_ = v___x_5533_;
goto v_reusejp_5536_;
}
else
{
lean_object* v_reuseFailAlloc_5544_; 
v_reuseFailAlloc_5544_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5544_, 0, v___x_5439_);
lean_ctor_set(v_reuseFailAlloc_5544_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5544_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5544_, 3, v_r_5524_);
lean_ctor_set(v_reuseFailAlloc_5544_, 4, v_r_5524_);
v___x_5537_ = v_reuseFailAlloc_5544_;
goto v_reusejp_5536_;
}
v_reusejp_5536_:
{
lean_object* v___x_5539_; 
lean_inc(v_r_5524_);
if (v_isShared_5529_ == 0)
{
lean_ctor_set(v___x_5528_, 3, v_r_5524_);
lean_ctor_set(v___x_5528_, 0, v___x_5439_);
v___x_5539_ = v___x_5528_;
goto v_reusejp_5538_;
}
else
{
lean_object* v_reuseFailAlloc_5543_; 
v_reuseFailAlloc_5543_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5543_, 0, v___x_5439_);
lean_ctor_set(v_reuseFailAlloc_5543_, 1, v_k_5525_);
lean_ctor_set(v_reuseFailAlloc_5543_, 2, v_v_5526_);
lean_ctor_set(v_reuseFailAlloc_5543_, 3, v_r_5524_);
lean_ctor_set(v_reuseFailAlloc_5543_, 4, v_r_5524_);
v___x_5539_ = v_reuseFailAlloc_5543_;
goto v_reusejp_5538_;
}
v_reusejp_5538_:
{
lean_object* v___x_5541_; 
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 4, v___x_5539_);
lean_ctor_set(v___x_5434_, 3, v___x_5537_);
lean_ctor_set(v___x_5434_, 2, v_v_5531_);
lean_ctor_set(v___x_5434_, 1, v_k_5530_);
lean_ctor_set(v___x_5434_, 0, v___x_5535_);
v___x_5541_ = v___x_5434_;
goto v_reusejp_5540_;
}
else
{
lean_object* v_reuseFailAlloc_5542_; 
v_reuseFailAlloc_5542_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5542_, 0, v___x_5535_);
lean_ctor_set(v_reuseFailAlloc_5542_, 1, v_k_5530_);
lean_ctor_set(v_reuseFailAlloc_5542_, 2, v_v_5531_);
lean_ctor_set(v_reuseFailAlloc_5542_, 3, v___x_5537_);
lean_ctor_set(v_reuseFailAlloc_5542_, 4, v___x_5539_);
v___x_5541_ = v_reuseFailAlloc_5542_;
goto v_reusejp_5540_;
}
v_reusejp_5540_:
{
return v___x_5541_;
}
}
}
}
}
}
else
{
lean_object* v_r_5552_; 
v_r_5552_ = lean_ctor_get(v_impl_5438_, 4);
lean_inc(v_r_5552_);
if (lean_obj_tag(v_r_5552_) == 0)
{
lean_object* v_k_5553_; lean_object* v_v_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5565_; 
v_k_5553_ = lean_ctor_get(v_impl_5438_, 1);
v_v_5554_ = lean_ctor_get(v_impl_5438_, 2);
v_isSharedCheck_5565_ = !lean_is_exclusive(v_impl_5438_);
if (v_isSharedCheck_5565_ == 0)
{
lean_object* v_unused_5566_; lean_object* v_unused_5567_; lean_object* v_unused_5568_; 
v_unused_5566_ = lean_ctor_get(v_impl_5438_, 4);
lean_dec(v_unused_5566_);
v_unused_5567_ = lean_ctor_get(v_impl_5438_, 3);
lean_dec(v_unused_5567_);
v_unused_5568_ = lean_ctor_get(v_impl_5438_, 0);
lean_dec(v_unused_5568_);
v___x_5556_ = v_impl_5438_;
v_isShared_5557_ = v_isSharedCheck_5565_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_v_5554_);
lean_inc(v_k_5553_);
lean_dec(v_impl_5438_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5565_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v___x_5558_; lean_object* v___x_5560_; 
v___x_5558_ = lean_unsigned_to_nat(3u);
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 4, v_l_5523_);
lean_ctor_set(v___x_5556_, 2, v_v_5430_);
lean_ctor_set(v___x_5556_, 1, v_k_5429_);
lean_ctor_set(v___x_5556_, 0, v___x_5439_);
v___x_5560_ = v___x_5556_;
goto v_reusejp_5559_;
}
else
{
lean_object* v_reuseFailAlloc_5564_; 
v_reuseFailAlloc_5564_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5564_, 0, v___x_5439_);
lean_ctor_set(v_reuseFailAlloc_5564_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5564_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5564_, 3, v_l_5523_);
lean_ctor_set(v_reuseFailAlloc_5564_, 4, v_l_5523_);
v___x_5560_ = v_reuseFailAlloc_5564_;
goto v_reusejp_5559_;
}
v_reusejp_5559_:
{
lean_object* v___x_5562_; 
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 4, v_r_5552_);
lean_ctor_set(v___x_5434_, 3, v___x_5560_);
lean_ctor_set(v___x_5434_, 2, v_v_5554_);
lean_ctor_set(v___x_5434_, 1, v_k_5553_);
lean_ctor_set(v___x_5434_, 0, v___x_5558_);
v___x_5562_ = v___x_5434_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5563_; 
v_reuseFailAlloc_5563_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5563_, 0, v___x_5558_);
lean_ctor_set(v_reuseFailAlloc_5563_, 1, v_k_5553_);
lean_ctor_set(v_reuseFailAlloc_5563_, 2, v_v_5554_);
lean_ctor_set(v_reuseFailAlloc_5563_, 3, v___x_5560_);
lean_ctor_set(v_reuseFailAlloc_5563_, 4, v_r_5552_);
v___x_5562_ = v_reuseFailAlloc_5563_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
return v___x_5562_;
}
}
}
}
else
{
lean_object* v___x_5569_; lean_object* v___x_5571_; 
v___x_5569_ = lean_unsigned_to_nat(2u);
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 4, v_impl_5438_);
lean_ctor_set(v___x_5434_, 3, v_r_5552_);
lean_ctor_set(v___x_5434_, 0, v___x_5569_);
v___x_5571_ = v___x_5434_;
goto v_reusejp_5570_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v___x_5569_);
lean_ctor_set(v_reuseFailAlloc_5572_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5572_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5572_, 3, v_r_5552_);
lean_ctor_set(v_reuseFailAlloc_5572_, 4, v_impl_5438_);
v___x_5571_ = v_reuseFailAlloc_5572_;
goto v_reusejp_5570_;
}
v_reusejp_5570_:
{
return v___x_5571_;
}
}
}
}
}
else
{
lean_object* v___x_5574_; 
lean_dec(v_v_5430_);
lean_dec(v_k_5429_);
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 2, v_v_5426_);
lean_ctor_set(v___x_5434_, 1, v_k_5425_);
v___x_5574_ = v___x_5434_;
goto v_reusejp_5573_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v_size_5428_);
lean_ctor_set(v_reuseFailAlloc_5575_, 1, v_k_5425_);
lean_ctor_set(v_reuseFailAlloc_5575_, 2, v_v_5426_);
lean_ctor_set(v_reuseFailAlloc_5575_, 3, v_l_5431_);
lean_ctor_set(v_reuseFailAlloc_5575_, 4, v_r_5432_);
v___x_5574_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5573_;
}
v_reusejp_5573_:
{
return v___x_5574_;
}
}
}
else
{
lean_object* v_impl_5576_; lean_object* v___x_5577_; 
lean_dec(v_size_5428_);
v_impl_5576_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5425_, v_v_5426_, v_l_5431_);
v___x_5577_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5432_) == 0)
{
lean_object* v_size_5578_; lean_object* v_size_5579_; lean_object* v_k_5580_; lean_object* v_v_5581_; lean_object* v_l_5582_; lean_object* v_r_5583_; lean_object* v___x_5584_; lean_object* v___x_5585_; uint8_t v___x_5586_; 
v_size_5578_ = lean_ctor_get(v_r_5432_, 0);
v_size_5579_ = lean_ctor_get(v_impl_5576_, 0);
v_k_5580_ = lean_ctor_get(v_impl_5576_, 1);
v_v_5581_ = lean_ctor_get(v_impl_5576_, 2);
v_l_5582_ = lean_ctor_get(v_impl_5576_, 3);
v_r_5583_ = lean_ctor_get(v_impl_5576_, 4);
lean_inc(v_r_5583_);
v___x_5584_ = lean_unsigned_to_nat(3u);
v___x_5585_ = lean_nat_mul(v___x_5584_, v_size_5578_);
v___x_5586_ = lean_nat_dec_lt(v___x_5585_, v_size_5579_);
lean_dec(v___x_5585_);
if (v___x_5586_ == 0)
{
lean_object* v___x_5587_; lean_object* v___x_5588_; lean_object* v___x_5590_; 
lean_dec(v_r_5583_);
v___x_5587_ = lean_nat_add(v___x_5577_, v_size_5579_);
v___x_5588_ = lean_nat_add(v___x_5587_, v_size_5578_);
lean_dec(v___x_5587_);
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 3, v_impl_5576_);
lean_ctor_set(v___x_5434_, 0, v___x_5588_);
v___x_5590_ = v___x_5434_;
goto v_reusejp_5589_;
}
else
{
lean_object* v_reuseFailAlloc_5591_; 
v_reuseFailAlloc_5591_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5591_, 0, v___x_5588_);
lean_ctor_set(v_reuseFailAlloc_5591_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5591_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5591_, 3, v_impl_5576_);
lean_ctor_set(v_reuseFailAlloc_5591_, 4, v_r_5432_);
v___x_5590_ = v_reuseFailAlloc_5591_;
goto v_reusejp_5589_;
}
v_reusejp_5589_:
{
return v___x_5590_;
}
}
else
{
lean_object* v___x_5593_; uint8_t v_isShared_5594_; uint8_t v_isSharedCheck_5657_; 
lean_inc(v_l_5582_);
lean_inc(v_v_5581_);
lean_inc(v_k_5580_);
lean_inc(v_size_5579_);
v_isSharedCheck_5657_ = !lean_is_exclusive(v_impl_5576_);
if (v_isSharedCheck_5657_ == 0)
{
lean_object* v_unused_5658_; lean_object* v_unused_5659_; lean_object* v_unused_5660_; lean_object* v_unused_5661_; lean_object* v_unused_5662_; 
v_unused_5658_ = lean_ctor_get(v_impl_5576_, 4);
lean_dec(v_unused_5658_);
v_unused_5659_ = lean_ctor_get(v_impl_5576_, 3);
lean_dec(v_unused_5659_);
v_unused_5660_ = lean_ctor_get(v_impl_5576_, 2);
lean_dec(v_unused_5660_);
v_unused_5661_ = lean_ctor_get(v_impl_5576_, 1);
lean_dec(v_unused_5661_);
v_unused_5662_ = lean_ctor_get(v_impl_5576_, 0);
lean_dec(v_unused_5662_);
v___x_5593_ = v_impl_5576_;
v_isShared_5594_ = v_isSharedCheck_5657_;
goto v_resetjp_5592_;
}
else
{
lean_dec(v_impl_5576_);
v___x_5593_ = lean_box(0);
v_isShared_5594_ = v_isSharedCheck_5657_;
goto v_resetjp_5592_;
}
v_resetjp_5592_:
{
lean_object* v_size_5595_; lean_object* v_size_5596_; lean_object* v_k_5597_; lean_object* v_v_5598_; lean_object* v_l_5599_; lean_object* v_r_5600_; lean_object* v___x_5601_; lean_object* v___x_5602_; uint8_t v___x_5603_; 
v_size_5595_ = lean_ctor_get(v_l_5582_, 0);
v_size_5596_ = lean_ctor_get(v_r_5583_, 0);
v_k_5597_ = lean_ctor_get(v_r_5583_, 1);
v_v_5598_ = lean_ctor_get(v_r_5583_, 2);
v_l_5599_ = lean_ctor_get(v_r_5583_, 3);
v_r_5600_ = lean_ctor_get(v_r_5583_, 4);
v___x_5601_ = lean_unsigned_to_nat(2u);
v___x_5602_ = lean_nat_mul(v___x_5601_, v_size_5595_);
v___x_5603_ = lean_nat_dec_lt(v_size_5596_, v___x_5602_);
lean_dec(v___x_5602_);
if (v___x_5603_ == 0)
{
lean_object* v___x_5605_; uint8_t v_isShared_5606_; uint8_t v_isSharedCheck_5632_; 
lean_inc(v_r_5600_);
lean_inc(v_l_5599_);
lean_inc(v_v_5598_);
lean_inc(v_k_5597_);
v_isSharedCheck_5632_ = !lean_is_exclusive(v_r_5583_);
if (v_isSharedCheck_5632_ == 0)
{
lean_object* v_unused_5633_; lean_object* v_unused_5634_; lean_object* v_unused_5635_; lean_object* v_unused_5636_; lean_object* v_unused_5637_; 
v_unused_5633_ = lean_ctor_get(v_r_5583_, 4);
lean_dec(v_unused_5633_);
v_unused_5634_ = lean_ctor_get(v_r_5583_, 3);
lean_dec(v_unused_5634_);
v_unused_5635_ = lean_ctor_get(v_r_5583_, 2);
lean_dec(v_unused_5635_);
v_unused_5636_ = lean_ctor_get(v_r_5583_, 1);
lean_dec(v_unused_5636_);
v_unused_5637_ = lean_ctor_get(v_r_5583_, 0);
lean_dec(v_unused_5637_);
v___x_5605_ = v_r_5583_;
v_isShared_5606_ = v_isSharedCheck_5632_;
goto v_resetjp_5604_;
}
else
{
lean_dec(v_r_5583_);
v___x_5605_ = lean_box(0);
v_isShared_5606_ = v_isSharedCheck_5632_;
goto v_resetjp_5604_;
}
v_resetjp_5604_:
{
lean_object* v___x_5607_; lean_object* v___x_5608_; lean_object* v___y_5610_; lean_object* v___y_5611_; lean_object* v___y_5612_; lean_object* v___x_5620_; lean_object* v___y_5622_; 
v___x_5607_ = lean_nat_add(v___x_5577_, v_size_5579_);
lean_dec(v_size_5579_);
v___x_5608_ = lean_nat_add(v___x_5607_, v_size_5578_);
lean_dec(v___x_5607_);
v___x_5620_ = lean_nat_add(v___x_5577_, v_size_5595_);
if (lean_obj_tag(v_l_5599_) == 0)
{
lean_object* v_size_5630_; 
v_size_5630_ = lean_ctor_get(v_l_5599_, 0);
lean_inc(v_size_5630_);
v___y_5622_ = v_size_5630_;
goto v___jp_5621_;
}
else
{
lean_object* v___x_5631_; 
v___x_5631_ = lean_unsigned_to_nat(0u);
v___y_5622_ = v___x_5631_;
goto v___jp_5621_;
}
v___jp_5609_:
{
lean_object* v___x_5613_; lean_object* v___x_5615_; 
v___x_5613_ = lean_nat_add(v___y_5610_, v___y_5612_);
lean_dec(v___y_5612_);
lean_dec(v___y_5610_);
if (v_isShared_5606_ == 0)
{
lean_ctor_set(v___x_5605_, 4, v_r_5432_);
lean_ctor_set(v___x_5605_, 3, v_r_5600_);
lean_ctor_set(v___x_5605_, 2, v_v_5430_);
lean_ctor_set(v___x_5605_, 1, v_k_5429_);
lean_ctor_set(v___x_5605_, 0, v___x_5613_);
v___x_5615_ = v___x_5605_;
goto v_reusejp_5614_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v___x_5613_);
lean_ctor_set(v_reuseFailAlloc_5619_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5619_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5619_, 3, v_r_5600_);
lean_ctor_set(v_reuseFailAlloc_5619_, 4, v_r_5432_);
v___x_5615_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5614_;
}
v_reusejp_5614_:
{
lean_object* v___x_5617_; 
if (v_isShared_5594_ == 0)
{
lean_ctor_set(v___x_5593_, 4, v___x_5615_);
lean_ctor_set(v___x_5593_, 3, v___y_5611_);
lean_ctor_set(v___x_5593_, 2, v_v_5598_);
lean_ctor_set(v___x_5593_, 1, v_k_5597_);
lean_ctor_set(v___x_5593_, 0, v___x_5608_);
v___x_5617_ = v___x_5593_;
goto v_reusejp_5616_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v___x_5608_);
lean_ctor_set(v_reuseFailAlloc_5618_, 1, v_k_5597_);
lean_ctor_set(v_reuseFailAlloc_5618_, 2, v_v_5598_);
lean_ctor_set(v_reuseFailAlloc_5618_, 3, v___y_5611_);
lean_ctor_set(v_reuseFailAlloc_5618_, 4, v___x_5615_);
v___x_5617_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5616_;
}
v_reusejp_5616_:
{
return v___x_5617_;
}
}
}
v___jp_5621_:
{
lean_object* v___x_5623_; lean_object* v___x_5625_; 
v___x_5623_ = lean_nat_add(v___x_5620_, v___y_5622_);
lean_dec(v___y_5622_);
lean_dec(v___x_5620_);
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 4, v_l_5599_);
lean_ctor_set(v___x_5434_, 3, v_l_5582_);
lean_ctor_set(v___x_5434_, 2, v_v_5581_);
lean_ctor_set(v___x_5434_, 1, v_k_5580_);
lean_ctor_set(v___x_5434_, 0, v___x_5623_);
v___x_5625_ = v___x_5434_;
goto v_reusejp_5624_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v___x_5623_);
lean_ctor_set(v_reuseFailAlloc_5629_, 1, v_k_5580_);
lean_ctor_set(v_reuseFailAlloc_5629_, 2, v_v_5581_);
lean_ctor_set(v_reuseFailAlloc_5629_, 3, v_l_5582_);
lean_ctor_set(v_reuseFailAlloc_5629_, 4, v_l_5599_);
v___x_5625_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5624_;
}
v_reusejp_5624_:
{
lean_object* v___x_5626_; 
v___x_5626_ = lean_nat_add(v___x_5577_, v_size_5578_);
if (lean_obj_tag(v_r_5600_) == 0)
{
lean_object* v_size_5627_; 
v_size_5627_ = lean_ctor_get(v_r_5600_, 0);
lean_inc(v_size_5627_);
v___y_5610_ = v___x_5626_;
v___y_5611_ = v___x_5625_;
v___y_5612_ = v_size_5627_;
goto v___jp_5609_;
}
else
{
lean_object* v___x_5628_; 
v___x_5628_ = lean_unsigned_to_nat(0u);
v___y_5610_ = v___x_5626_;
v___y_5611_ = v___x_5625_;
v___y_5612_ = v___x_5628_;
goto v___jp_5609_;
}
}
}
}
}
else
{
lean_object* v___x_5638_; lean_object* v___x_5639_; lean_object* v___x_5640_; lean_object* v___x_5641_; lean_object* v___x_5643_; 
lean_del_object(v___x_5434_);
v___x_5638_ = lean_nat_add(v___x_5577_, v_size_5579_);
lean_dec(v_size_5579_);
v___x_5639_ = lean_nat_add(v___x_5638_, v_size_5578_);
lean_dec(v___x_5638_);
v___x_5640_ = lean_nat_add(v___x_5577_, v_size_5578_);
v___x_5641_ = lean_nat_add(v___x_5640_, v_size_5596_);
lean_dec(v___x_5640_);
lean_inc_ref(v_r_5432_);
if (v_isShared_5594_ == 0)
{
lean_ctor_set(v___x_5593_, 4, v_r_5432_);
lean_ctor_set(v___x_5593_, 3, v_r_5583_);
lean_ctor_set(v___x_5593_, 2, v_v_5430_);
lean_ctor_set(v___x_5593_, 1, v_k_5429_);
lean_ctor_set(v___x_5593_, 0, v___x_5641_);
v___x_5643_ = v___x_5593_;
goto v_reusejp_5642_;
}
else
{
lean_object* v_reuseFailAlloc_5656_; 
v_reuseFailAlloc_5656_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5656_, 0, v___x_5641_);
lean_ctor_set(v_reuseFailAlloc_5656_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5656_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5656_, 3, v_r_5583_);
lean_ctor_set(v_reuseFailAlloc_5656_, 4, v_r_5432_);
v___x_5643_ = v_reuseFailAlloc_5656_;
goto v_reusejp_5642_;
}
v_reusejp_5642_:
{
lean_object* v___x_5645_; uint8_t v_isShared_5646_; uint8_t v_isSharedCheck_5650_; 
v_isSharedCheck_5650_ = !lean_is_exclusive(v_r_5432_);
if (v_isSharedCheck_5650_ == 0)
{
lean_object* v_unused_5651_; lean_object* v_unused_5652_; lean_object* v_unused_5653_; lean_object* v_unused_5654_; lean_object* v_unused_5655_; 
v_unused_5651_ = lean_ctor_get(v_r_5432_, 4);
lean_dec(v_unused_5651_);
v_unused_5652_ = lean_ctor_get(v_r_5432_, 3);
lean_dec(v_unused_5652_);
v_unused_5653_ = lean_ctor_get(v_r_5432_, 2);
lean_dec(v_unused_5653_);
v_unused_5654_ = lean_ctor_get(v_r_5432_, 1);
lean_dec(v_unused_5654_);
v_unused_5655_ = lean_ctor_get(v_r_5432_, 0);
lean_dec(v_unused_5655_);
v___x_5645_ = v_r_5432_;
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
else
{
lean_dec(v_r_5432_);
v___x_5645_ = lean_box(0);
v_isShared_5646_ = v_isSharedCheck_5650_;
goto v_resetjp_5644_;
}
v_resetjp_5644_:
{
lean_object* v___x_5648_; 
if (v_isShared_5646_ == 0)
{
lean_ctor_set(v___x_5645_, 4, v___x_5643_);
lean_ctor_set(v___x_5645_, 3, v_l_5582_);
lean_ctor_set(v___x_5645_, 2, v_v_5581_);
lean_ctor_set(v___x_5645_, 1, v_k_5580_);
lean_ctor_set(v___x_5645_, 0, v___x_5639_);
v___x_5648_ = v___x_5645_;
goto v_reusejp_5647_;
}
else
{
lean_object* v_reuseFailAlloc_5649_; 
v_reuseFailAlloc_5649_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5649_, 0, v___x_5639_);
lean_ctor_set(v_reuseFailAlloc_5649_, 1, v_k_5580_);
lean_ctor_set(v_reuseFailAlloc_5649_, 2, v_v_5581_);
lean_ctor_set(v_reuseFailAlloc_5649_, 3, v_l_5582_);
lean_ctor_set(v_reuseFailAlloc_5649_, 4, v___x_5643_);
v___x_5648_ = v_reuseFailAlloc_5649_;
goto v_reusejp_5647_;
}
v_reusejp_5647_:
{
return v___x_5648_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5663_; 
v_l_5663_ = lean_ctor_get(v_impl_5576_, 3);
if (lean_obj_tag(v_l_5663_) == 0)
{
lean_object* v_r_5664_; lean_object* v_k_5665_; lean_object* v_v_5666_; lean_object* v___x_5668_; uint8_t v_isShared_5669_; uint8_t v_isSharedCheck_5677_; 
lean_inc_ref(v_l_5663_);
v_r_5664_ = lean_ctor_get(v_impl_5576_, 4);
v_k_5665_ = lean_ctor_get(v_impl_5576_, 1);
v_v_5666_ = lean_ctor_get(v_impl_5576_, 2);
v_isSharedCheck_5677_ = !lean_is_exclusive(v_impl_5576_);
if (v_isSharedCheck_5677_ == 0)
{
lean_object* v_unused_5678_; lean_object* v_unused_5679_; 
v_unused_5678_ = lean_ctor_get(v_impl_5576_, 3);
lean_dec(v_unused_5678_);
v_unused_5679_ = lean_ctor_get(v_impl_5576_, 0);
lean_dec(v_unused_5679_);
v___x_5668_ = v_impl_5576_;
v_isShared_5669_ = v_isSharedCheck_5677_;
goto v_resetjp_5667_;
}
else
{
lean_inc(v_r_5664_);
lean_inc(v_v_5666_);
lean_inc(v_k_5665_);
lean_dec(v_impl_5576_);
v___x_5668_ = lean_box(0);
v_isShared_5669_ = v_isSharedCheck_5677_;
goto v_resetjp_5667_;
}
v_resetjp_5667_:
{
lean_object* v___x_5670_; lean_object* v___x_5672_; 
v___x_5670_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5664_);
if (v_isShared_5669_ == 0)
{
lean_ctor_set(v___x_5668_, 3, v_r_5664_);
lean_ctor_set(v___x_5668_, 2, v_v_5430_);
lean_ctor_set(v___x_5668_, 1, v_k_5429_);
lean_ctor_set(v___x_5668_, 0, v___x_5577_);
v___x_5672_ = v___x_5668_;
goto v_reusejp_5671_;
}
else
{
lean_object* v_reuseFailAlloc_5676_; 
v_reuseFailAlloc_5676_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5676_, 0, v___x_5577_);
lean_ctor_set(v_reuseFailAlloc_5676_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5676_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5676_, 3, v_r_5664_);
lean_ctor_set(v_reuseFailAlloc_5676_, 4, v_r_5664_);
v___x_5672_ = v_reuseFailAlloc_5676_;
goto v_reusejp_5671_;
}
v_reusejp_5671_:
{
lean_object* v___x_5674_; 
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 4, v___x_5672_);
lean_ctor_set(v___x_5434_, 3, v_l_5663_);
lean_ctor_set(v___x_5434_, 2, v_v_5666_);
lean_ctor_set(v___x_5434_, 1, v_k_5665_);
lean_ctor_set(v___x_5434_, 0, v___x_5670_);
v___x_5674_ = v___x_5434_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v___x_5670_);
lean_ctor_set(v_reuseFailAlloc_5675_, 1, v_k_5665_);
lean_ctor_set(v_reuseFailAlloc_5675_, 2, v_v_5666_);
lean_ctor_set(v_reuseFailAlloc_5675_, 3, v_l_5663_);
lean_ctor_set(v_reuseFailAlloc_5675_, 4, v___x_5672_);
v___x_5674_ = v_reuseFailAlloc_5675_;
goto v_reusejp_5673_;
}
v_reusejp_5673_:
{
return v___x_5674_;
}
}
}
}
else
{
lean_object* v_r_5680_; 
v_r_5680_ = lean_ctor_get(v_impl_5576_, 4);
lean_inc(v_r_5680_);
if (lean_obj_tag(v_r_5680_) == 0)
{
lean_object* v_k_5681_; lean_object* v_v_5682_; lean_object* v___x_5684_; uint8_t v_isShared_5685_; uint8_t v_isSharedCheck_5705_; 
lean_inc(v_l_5663_);
v_k_5681_ = lean_ctor_get(v_impl_5576_, 1);
v_v_5682_ = lean_ctor_get(v_impl_5576_, 2);
v_isSharedCheck_5705_ = !lean_is_exclusive(v_impl_5576_);
if (v_isSharedCheck_5705_ == 0)
{
lean_object* v_unused_5706_; lean_object* v_unused_5707_; lean_object* v_unused_5708_; 
v_unused_5706_ = lean_ctor_get(v_impl_5576_, 4);
lean_dec(v_unused_5706_);
v_unused_5707_ = lean_ctor_get(v_impl_5576_, 3);
lean_dec(v_unused_5707_);
v_unused_5708_ = lean_ctor_get(v_impl_5576_, 0);
lean_dec(v_unused_5708_);
v___x_5684_ = v_impl_5576_;
v_isShared_5685_ = v_isSharedCheck_5705_;
goto v_resetjp_5683_;
}
else
{
lean_inc(v_v_5682_);
lean_inc(v_k_5681_);
lean_dec(v_impl_5576_);
v___x_5684_ = lean_box(0);
v_isShared_5685_ = v_isSharedCheck_5705_;
goto v_resetjp_5683_;
}
v_resetjp_5683_:
{
lean_object* v_k_5686_; lean_object* v_v_5687_; lean_object* v___x_5689_; uint8_t v_isShared_5690_; uint8_t v_isSharedCheck_5701_; 
v_k_5686_ = lean_ctor_get(v_r_5680_, 1);
v_v_5687_ = lean_ctor_get(v_r_5680_, 2);
v_isSharedCheck_5701_ = !lean_is_exclusive(v_r_5680_);
if (v_isSharedCheck_5701_ == 0)
{
lean_object* v_unused_5702_; lean_object* v_unused_5703_; lean_object* v_unused_5704_; 
v_unused_5702_ = lean_ctor_get(v_r_5680_, 4);
lean_dec(v_unused_5702_);
v_unused_5703_ = lean_ctor_get(v_r_5680_, 3);
lean_dec(v_unused_5703_);
v_unused_5704_ = lean_ctor_get(v_r_5680_, 0);
lean_dec(v_unused_5704_);
v___x_5689_ = v_r_5680_;
v_isShared_5690_ = v_isSharedCheck_5701_;
goto v_resetjp_5688_;
}
else
{
lean_inc(v_v_5687_);
lean_inc(v_k_5686_);
lean_dec(v_r_5680_);
v___x_5689_ = lean_box(0);
v_isShared_5690_ = v_isSharedCheck_5701_;
goto v_resetjp_5688_;
}
v_resetjp_5688_:
{
lean_object* v___x_5691_; lean_object* v___x_5693_; 
v___x_5691_ = lean_unsigned_to_nat(3u);
if (v_isShared_5690_ == 0)
{
lean_ctor_set(v___x_5689_, 4, v_l_5663_);
lean_ctor_set(v___x_5689_, 3, v_l_5663_);
lean_ctor_set(v___x_5689_, 2, v_v_5682_);
lean_ctor_set(v___x_5689_, 1, v_k_5681_);
lean_ctor_set(v___x_5689_, 0, v___x_5577_);
v___x_5693_ = v___x_5689_;
goto v_reusejp_5692_;
}
else
{
lean_object* v_reuseFailAlloc_5700_; 
v_reuseFailAlloc_5700_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5700_, 0, v___x_5577_);
lean_ctor_set(v_reuseFailAlloc_5700_, 1, v_k_5681_);
lean_ctor_set(v_reuseFailAlloc_5700_, 2, v_v_5682_);
lean_ctor_set(v_reuseFailAlloc_5700_, 3, v_l_5663_);
lean_ctor_set(v_reuseFailAlloc_5700_, 4, v_l_5663_);
v___x_5693_ = v_reuseFailAlloc_5700_;
goto v_reusejp_5692_;
}
v_reusejp_5692_:
{
lean_object* v___x_5695_; 
if (v_isShared_5685_ == 0)
{
lean_ctor_set(v___x_5684_, 4, v_l_5663_);
lean_ctor_set(v___x_5684_, 2, v_v_5430_);
lean_ctor_set(v___x_5684_, 1, v_k_5429_);
lean_ctor_set(v___x_5684_, 0, v___x_5577_);
v___x_5695_ = v___x_5684_;
goto v_reusejp_5694_;
}
else
{
lean_object* v_reuseFailAlloc_5699_; 
v_reuseFailAlloc_5699_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5699_, 0, v___x_5577_);
lean_ctor_set(v_reuseFailAlloc_5699_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5699_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5699_, 3, v_l_5663_);
lean_ctor_set(v_reuseFailAlloc_5699_, 4, v_l_5663_);
v___x_5695_ = v_reuseFailAlloc_5699_;
goto v_reusejp_5694_;
}
v_reusejp_5694_:
{
lean_object* v___x_5697_; 
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 4, v___x_5695_);
lean_ctor_set(v___x_5434_, 3, v___x_5693_);
lean_ctor_set(v___x_5434_, 2, v_v_5687_);
lean_ctor_set(v___x_5434_, 1, v_k_5686_);
lean_ctor_set(v___x_5434_, 0, v___x_5691_);
v___x_5697_ = v___x_5434_;
goto v_reusejp_5696_;
}
else
{
lean_object* v_reuseFailAlloc_5698_; 
v_reuseFailAlloc_5698_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5698_, 0, v___x_5691_);
lean_ctor_set(v_reuseFailAlloc_5698_, 1, v_k_5686_);
lean_ctor_set(v_reuseFailAlloc_5698_, 2, v_v_5687_);
lean_ctor_set(v_reuseFailAlloc_5698_, 3, v___x_5693_);
lean_ctor_set(v_reuseFailAlloc_5698_, 4, v___x_5695_);
v___x_5697_ = v_reuseFailAlloc_5698_;
goto v_reusejp_5696_;
}
v_reusejp_5696_:
{
return v___x_5697_;
}
}
}
}
}
}
else
{
lean_object* v___x_5709_; lean_object* v___x_5711_; 
v___x_5709_ = lean_unsigned_to_nat(2u);
if (v_isShared_5435_ == 0)
{
lean_ctor_set(v___x_5434_, 4, v_r_5680_);
lean_ctor_set(v___x_5434_, 3, v_impl_5576_);
lean_ctor_set(v___x_5434_, 0, v___x_5709_);
v___x_5711_ = v___x_5434_;
goto v_reusejp_5710_;
}
else
{
lean_object* v_reuseFailAlloc_5712_; 
v_reuseFailAlloc_5712_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5712_, 0, v___x_5709_);
lean_ctor_set(v_reuseFailAlloc_5712_, 1, v_k_5429_);
lean_ctor_set(v_reuseFailAlloc_5712_, 2, v_v_5430_);
lean_ctor_set(v_reuseFailAlloc_5712_, 3, v_impl_5576_);
lean_ctor_set(v_reuseFailAlloc_5712_, 4, v_r_5680_);
v___x_5711_ = v_reuseFailAlloc_5712_;
goto v_reusejp_5710_;
}
v_reusejp_5710_:
{
return v___x_5711_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5714_; lean_object* v___x_5715_; 
v___x_5714_ = lean_unsigned_to_nat(1u);
v___x_5715_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5714_);
lean_ctor_set(v___x_5715_, 1, v_k_5425_);
lean_ctor_set(v___x_5715_, 2, v_v_5426_);
lean_ctor_set(v___x_5715_, 3, v_t_5427_);
lean_ctor_set(v___x_5715_, 4, v_t_5427_);
return v___x_5715_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5716_, lean_object* v_t_5717_){
_start:
{
if (lean_obj_tag(v_t_5717_) == 0)
{
lean_object* v_k_5718_; lean_object* v_l_5719_; lean_object* v_r_5720_; uint8_t v___x_5721_; 
v_k_5718_ = lean_ctor_get(v_t_5717_, 1);
v_l_5719_ = lean_ctor_get(v_t_5717_, 3);
v_r_5720_ = lean_ctor_get(v_t_5717_, 4);
v___x_5721_ = lean_nat_dec_lt(v_k_5718_, v_k_5716_);
if (v___x_5721_ == 0)
{
uint8_t v___x_5722_; 
v___x_5722_ = lean_nat_dec_eq(v_k_5718_, v_k_5716_);
if (v___x_5722_ == 0)
{
v_t_5717_ = v_r_5720_;
goto _start;
}
else
{
return v___x_5722_;
}
}
else
{
v_t_5717_ = v_l_5719_;
goto _start;
}
}
else
{
uint8_t v___x_5725_; 
v___x_5725_ = 0;
return v___x_5725_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5726_, lean_object* v_t_5727_){
_start:
{
uint8_t v_res_5728_; lean_object* v_r_5729_; 
v_res_5728_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5726_, v_t_5727_);
lean_dec(v_t_5727_);
lean_dec(v_k_5726_);
v_r_5729_ = lean_box(v_res_5728_);
return v_r_5729_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5730_, lean_object* v_e_5731_){
_start:
{
lean_object* v_defaultInstances_5732_; lean_object* v_priorities_5733_; lean_object* v___x_5735_; uint8_t v_isShared_5736_; uint8_t v_isSharedCheck_5760_; 
v_defaultInstances_5732_ = lean_ctor_get(v_d_5730_, 0);
v_priorities_5733_ = lean_ctor_get(v_d_5730_, 1);
v_isSharedCheck_5760_ = !lean_is_exclusive(v_d_5730_);
if (v_isSharedCheck_5760_ == 0)
{
v___x_5735_ = v_d_5730_;
v_isShared_5736_ = v_isSharedCheck_5760_;
goto v_resetjp_5734_;
}
else
{
lean_inc(v_priorities_5733_);
lean_inc(v_defaultInstances_5732_);
lean_dec(v_d_5730_);
v___x_5735_ = lean_box(0);
v_isShared_5736_ = v_isSharedCheck_5760_;
goto v_resetjp_5734_;
}
v_resetjp_5734_:
{
lean_object* v_className_5737_; lean_object* v_instanceName_5738_; lean_object* v_priority_5739_; lean_object* v___y_5741_; uint8_t v___x_5757_; 
v_className_5737_ = lean_ctor_get(v_e_5731_, 0);
lean_inc(v_className_5737_);
v_instanceName_5738_ = lean_ctor_get(v_e_5731_, 1);
lean_inc(v_instanceName_5738_);
v_priority_5739_ = lean_ctor_get(v_e_5731_, 2);
lean_inc(v_priority_5739_);
lean_dec_ref(v_e_5731_);
v___x_5757_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5739_, v_priorities_5733_);
if (v___x_5757_ == 0)
{
lean_object* v___x_5758_; lean_object* v___x_5759_; 
v___x_5758_ = lean_box(0);
lean_inc(v_priority_5739_);
v___x_5759_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5739_, v___x_5758_, v_priorities_5733_);
v___y_5741_ = v___x_5759_;
goto v___jp_5740_;
}
else
{
v___y_5741_ = v_priorities_5733_;
goto v___jp_5740_;
}
v___jp_5740_:
{
lean_object* v___x_5742_; 
v___x_5742_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5732_, v_className_5737_);
if (lean_obj_tag(v___x_5742_) == 0)
{
lean_object* v___x_5743_; lean_object* v___x_5744_; lean_object* v___x_5745_; lean_object* v___x_5746_; lean_object* v___x_5748_; 
v___x_5743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5743_, 0, v_instanceName_5738_);
lean_ctor_set(v___x_5743_, 1, v_priority_5739_);
v___x_5744_ = lean_box(0);
v___x_5745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5745_, 0, v___x_5743_);
lean_ctor_set(v___x_5745_, 1, v___x_5744_);
v___x_5746_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5737_, v___x_5745_, v_defaultInstances_5732_);
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 1, v___y_5741_);
lean_ctor_set(v___x_5735_, 0, v___x_5746_);
v___x_5748_ = v___x_5735_;
goto v_reusejp_5747_;
}
else
{
lean_object* v_reuseFailAlloc_5749_; 
v_reuseFailAlloc_5749_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5749_, 0, v___x_5746_);
lean_ctor_set(v_reuseFailAlloc_5749_, 1, v___y_5741_);
v___x_5748_ = v_reuseFailAlloc_5749_;
goto v_reusejp_5747_;
}
v_reusejp_5747_:
{
return v___x_5748_;
}
}
else
{
lean_object* v_val_5750_; lean_object* v___x_5751_; lean_object* v___x_5752_; lean_object* v___x_5753_; lean_object* v___x_5755_; 
v_val_5750_ = lean_ctor_get(v___x_5742_, 0);
lean_inc(v_val_5750_);
lean_dec_ref_known(v___x_5742_, 1);
v___x_5751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5751_, 0, v_instanceName_5738_);
lean_ctor_set(v___x_5751_, 1, v_priority_5739_);
v___x_5752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5752_, 0, v___x_5751_);
lean_ctor_set(v___x_5752_, 1, v_val_5750_);
v___x_5753_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5737_, v___x_5752_, v_defaultInstances_5732_);
if (v_isShared_5736_ == 0)
{
lean_ctor_set(v___x_5735_, 1, v___y_5741_);
lean_ctor_set(v___x_5735_, 0, v___x_5753_);
v___x_5755_ = v___x_5735_;
goto v_reusejp_5754_;
}
else
{
lean_object* v_reuseFailAlloc_5756_; 
v_reuseFailAlloc_5756_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5756_, 0, v___x_5753_);
lean_ctor_set(v_reuseFailAlloc_5756_, 1, v___y_5741_);
v___x_5755_ = v_reuseFailAlloc_5756_;
goto v_reusejp_5754_;
}
v_reusejp_5754_:
{
return v___x_5755_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5761_, lean_object* v_k_5762_, lean_object* v_t_5763_){
_start:
{
uint8_t v___x_5764_; 
v___x_5764_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5762_, v_t_5763_);
return v___x_5764_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5765_, lean_object* v_k_5766_, lean_object* v_t_5767_){
_start:
{
uint8_t v_res_5768_; lean_object* v_r_5769_; 
v_res_5768_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5765_, v_k_5766_, v_t_5767_);
lean_dec(v_t_5767_);
lean_dec(v_k_5766_);
v_r_5769_ = lean_box(v_res_5768_);
return v_r_5769_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5770_, lean_object* v_k_5771_, lean_object* v_v_5772_, lean_object* v_t_5773_, lean_object* v_hl_5774_){
_start:
{
lean_object* v___x_5775_; 
v___x_5775_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5771_, v_v_5772_, v_t_5773_);
return v___x_5775_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object* v_env_5776_, lean_object* v_as_5777_, size_t v_i_5778_, size_t v_stop_5779_, lean_object* v_b_5780_){
_start:
{
lean_object* v___y_5782_; uint8_t v___x_5786_; 
v___x_5786_ = lean_usize_dec_eq(v_i_5778_, v_stop_5779_);
if (v___x_5786_ == 0)
{
lean_object* v___x_5787_; lean_object* v_instanceName_5788_; uint8_t v___x_5789_; lean_object* v___x_5790_; uint8_t v___x_5791_; 
v___x_5787_ = lean_array_uget_borrowed(v_as_5777_, v_i_5778_);
v_instanceName_5788_ = lean_ctor_get(v___x_5787_, 1);
v___x_5789_ = 1;
lean_inc_ref(v_env_5776_);
v___x_5790_ = l_Lean_Environment_setExporting(v_env_5776_, v___x_5789_);
lean_inc(v_instanceName_5788_);
v___x_5791_ = l_Lean_Environment_contains(v___x_5790_, v_instanceName_5788_, v___x_5786_);
if (v___x_5791_ == 0)
{
v___y_5782_ = v_b_5780_;
goto v___jp_5781_;
}
else
{
lean_object* v___x_5792_; 
lean_inc(v___x_5787_);
v___x_5792_ = lean_array_push(v_b_5780_, v___x_5787_);
v___y_5782_ = v___x_5792_;
goto v___jp_5781_;
}
}
else
{
lean_dec_ref(v_env_5776_);
return v_b_5780_;
}
v___jp_5781_:
{
size_t v___x_5783_; size_t v___x_5784_; 
v___x_5783_ = ((size_t)1ULL);
v___x_5784_ = lean_usize_add(v_i_5778_, v___x_5783_);
v_i_5778_ = v___x_5784_;
v_b_5780_ = v___y_5782_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_5793_, lean_object* v_as_5794_, lean_object* v_i_5795_, lean_object* v_stop_5796_, lean_object* v_b_5797_){
_start:
{
size_t v_i_boxed_5798_; size_t v_stop_boxed_5799_; lean_object* v_res_5800_; 
v_i_boxed_5798_ = lean_unbox_usize(v_i_5795_);
lean_dec(v_i_5795_);
v_stop_boxed_5799_ = lean_unbox_usize(v_stop_5796_);
lean_dec(v_stop_5796_);
v_res_5800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5793_, v_as_5794_, v_i_boxed_5798_, v_stop_boxed_5799_, v_b_5797_);
lean_dec_ref(v_as_5794_);
return v_res_5800_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_env_5803_, lean_object* v_x_5804_, lean_object* v_entries_5805_){
_start:
{
lean_object* v_all_5806_; lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v___x_5809_; uint8_t v___x_5810_; 
v_all_5806_ = lean_array_mk(v_entries_5805_);
v___x_5807_ = lean_unsigned_to_nat(0u);
v___x_5808_ = lean_array_get_size(v_all_5806_);
v___x_5809_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5810_ = lean_nat_dec_lt(v___x_5807_, v___x_5808_);
if (v___x_5810_ == 0)
{
lean_object* v___x_5811_; 
lean_dec_ref(v_env_5803_);
v___x_5811_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5811_, 0, v___x_5809_);
lean_ctor_set(v___x_5811_, 1, v___x_5809_);
lean_ctor_set(v___x_5811_, 2, v_all_5806_);
return v___x_5811_;
}
else
{
uint8_t v___x_5812_; 
v___x_5812_ = lean_nat_dec_le(v___x_5808_, v___x_5808_);
if (v___x_5812_ == 0)
{
if (v___x_5810_ == 0)
{
lean_object* v___x_5813_; 
lean_dec_ref(v_env_5803_);
v___x_5813_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5813_, 0, v___x_5809_);
lean_ctor_set(v___x_5813_, 1, v___x_5809_);
lean_ctor_set(v___x_5813_, 2, v_all_5806_);
return v___x_5813_;
}
else
{
size_t v___x_5814_; size_t v___x_5815_; lean_object* v___x_5816_; lean_object* v___x_5817_; 
v___x_5814_ = ((size_t)0ULL);
v___x_5815_ = lean_usize_of_nat(v___x_5808_);
v___x_5816_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5803_, v_all_5806_, v___x_5814_, v___x_5815_, v___x_5809_);
lean_inc_ref(v___x_5816_);
v___x_5817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5817_, 0, v___x_5816_);
lean_ctor_set(v___x_5817_, 1, v___x_5816_);
lean_ctor_set(v___x_5817_, 2, v_all_5806_);
return v___x_5817_;
}
}
else
{
size_t v___x_5818_; size_t v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5818_ = ((size_t)0ULL);
v___x_5819_ = lean_usize_of_nat(v___x_5808_);
v___x_5820_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5803_, v_all_5806_, v___x_5818_, v___x_5819_, v___x_5809_);
lean_inc_ref(v___x_5820_);
v___x_5821_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5821_, 0, v___x_5820_);
lean_ctor_set(v___x_5821_, 1, v___x_5820_);
lean_ctor_set(v___x_5821_, 2, v_all_5806_);
return v___x_5821_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5822_, lean_object* v_x_5823_, lean_object* v_entries_5824_){
_start:
{
lean_object* v_res_5825_; 
v_res_5825_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5822_, v_x_5823_, v_entries_5824_);
lean_dec_ref(v_x_5823_);
return v_res_5825_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5826_){
_start:
{
lean_object* v___x_5827_; 
v___x_5827_ = lean_array_mk(v_es_5826_);
return v___x_5827_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5828_, size_t v_i_5829_, size_t v_stop_5830_, lean_object* v_b_5831_){
_start:
{
uint8_t v___x_5832_; 
v___x_5832_ = lean_usize_dec_eq(v_i_5829_, v_stop_5830_);
if (v___x_5832_ == 0)
{
lean_object* v___x_5833_; lean_object* v___x_5834_; size_t v___x_5835_; size_t v___x_5836_; 
v___x_5833_ = lean_array_uget_borrowed(v_as_5828_, v_i_5829_);
lean_inc(v___x_5833_);
v___x_5834_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5831_, v___x_5833_);
v___x_5835_ = ((size_t)1ULL);
v___x_5836_ = lean_usize_add(v_i_5829_, v___x_5835_);
v_i_5829_ = v___x_5836_;
v_b_5831_ = v___x_5834_;
goto _start;
}
else
{
return v_b_5831_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5838_, lean_object* v_i_5839_, lean_object* v_stop_5840_, lean_object* v_b_5841_){
_start:
{
size_t v_i_boxed_5842_; size_t v_stop_boxed_5843_; lean_object* v_res_5844_; 
v_i_boxed_5842_ = lean_unbox_usize(v_i_5839_);
lean_dec(v_i_5839_);
v_stop_boxed_5843_ = lean_unbox_usize(v_stop_5840_);
lean_dec(v_stop_5840_);
v_res_5844_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5838_, v_i_boxed_5842_, v_stop_boxed_5843_, v_b_5841_);
lean_dec_ref(v_as_5838_);
return v_res_5844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5845_, size_t v_i_5846_, size_t v_stop_5847_, lean_object* v_b_5848_){
_start:
{
lean_object* v___y_5850_; uint8_t v___x_5854_; 
v___x_5854_ = lean_usize_dec_eq(v_i_5846_, v_stop_5847_);
if (v___x_5854_ == 0)
{
lean_object* v___x_5855_; lean_object* v___x_5856_; lean_object* v___x_5857_; uint8_t v___x_5858_; 
v___x_5855_ = lean_array_uget_borrowed(v_as_5845_, v_i_5846_);
v___x_5856_ = lean_unsigned_to_nat(0u);
v___x_5857_ = lean_array_get_size(v___x_5855_);
v___x_5858_ = lean_nat_dec_lt(v___x_5856_, v___x_5857_);
if (v___x_5858_ == 0)
{
v___y_5850_ = v_b_5848_;
goto v___jp_5849_;
}
else
{
size_t v___x_5859_; size_t v___x_5860_; lean_object* v___x_5861_; 
v___x_5859_ = ((size_t)0ULL);
v___x_5860_ = lean_usize_of_nat(v___x_5857_);
v___x_5861_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5855_, v___x_5859_, v___x_5860_, v_b_5848_);
v___y_5850_ = v___x_5861_;
goto v___jp_5849_;
}
}
else
{
return v_b_5848_;
}
v___jp_5849_:
{
size_t v___x_5851_; size_t v___x_5852_; 
v___x_5851_ = ((size_t)1ULL);
v___x_5852_ = lean_usize_add(v_i_5846_, v___x_5851_);
v_i_5846_ = v___x_5852_;
v_b_5848_ = v___y_5850_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5862_, lean_object* v_i_5863_, lean_object* v_stop_5864_, lean_object* v_b_5865_){
_start:
{
size_t v_i_boxed_5866_; size_t v_stop_boxed_5867_; lean_object* v_res_5868_; 
v_i_boxed_5866_ = lean_unbox_usize(v_i_5863_);
lean_dec(v_i_5863_);
v_stop_boxed_5867_ = lean_unbox_usize(v_stop_5864_);
lean_dec(v_stop_5864_);
v_res_5868_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5862_, v_i_boxed_5866_, v_stop_boxed_5867_, v_b_5865_);
lean_dec_ref(v_as_5862_);
return v_res_5868_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_5869_, lean_object* v_as_5870_){
_start:
{
lean_object* v___x_5871_; lean_object* v___x_5872_; uint8_t v___x_5873_; 
v___x_5871_ = lean_unsigned_to_nat(0u);
v___x_5872_ = lean_array_get_size(v_as_5870_);
v___x_5873_ = lean_nat_dec_lt(v___x_5871_, v___x_5872_);
if (v___x_5873_ == 0)
{
return v_initState_5869_;
}
else
{
size_t v___x_5874_; size_t v___x_5875_; lean_object* v___x_5876_; 
v___x_5874_ = ((size_t)0ULL);
v___x_5875_ = lean_usize_of_nat(v___x_5872_);
v___x_5876_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5870_, v___x_5874_, v___x_5875_, v_initState_5869_);
return v___x_5876_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_5877_, lean_object* v_as_5878_){
_start:
{
lean_object* v_res_5879_; 
v_res_5879_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_5877_, v_as_5878_);
lean_dec_ref(v_as_5878_);
return v_res_5879_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5880_){
_start:
{
lean_object* v___x_5881_; lean_object* v___x_5882_; 
v___x_5881_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5882_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_5881_, v_es_5880_);
return v___x_5882_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_5883_){
_start:
{
lean_object* v_res_5884_; 
v_res_5884_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_5883_);
lean_dec_ref(v_es_5883_);
return v_res_5884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; 
v___x_5905_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5906_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5905_);
return v___x_5906_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_5907_){
_start:
{
lean_object* v_res_5908_; 
v_res_5908_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_5908_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5909_, lean_object* v___y_5910_, lean_object* v___y_5911_){
_start:
{
lean_object* v___x_5913_; lean_object* v_nextMacroScope_5914_; lean_object* v_ngen_5915_; lean_object* v_auxDeclNGen_5916_; lean_object* v_traceState_5917_; lean_object* v_recordedDeps_5918_; lean_object* v_messages_5919_; lean_object* v_infoState_5920_; lean_object* v_snapshotTasks_5921_; lean_object* v___x_5923_; uint8_t v_isShared_5924_; uint8_t v_isSharedCheck_5947_; 
v___x_5913_ = lean_st_ref_take(v___y_5911_);
v_nextMacroScope_5914_ = lean_ctor_get(v___x_5913_, 1);
v_ngen_5915_ = lean_ctor_get(v___x_5913_, 2);
v_auxDeclNGen_5916_ = lean_ctor_get(v___x_5913_, 3);
v_traceState_5917_ = lean_ctor_get(v___x_5913_, 4);
v_recordedDeps_5918_ = lean_ctor_get(v___x_5913_, 6);
v_messages_5919_ = lean_ctor_get(v___x_5913_, 7);
v_infoState_5920_ = lean_ctor_get(v___x_5913_, 8);
v_snapshotTasks_5921_ = lean_ctor_get(v___x_5913_, 9);
v_isSharedCheck_5947_ = !lean_is_exclusive(v___x_5913_);
if (v_isSharedCheck_5947_ == 0)
{
lean_object* v_unused_5948_; lean_object* v_unused_5949_; 
v_unused_5948_ = lean_ctor_get(v___x_5913_, 5);
lean_dec(v_unused_5948_);
v_unused_5949_ = lean_ctor_get(v___x_5913_, 0);
lean_dec(v_unused_5949_);
v___x_5923_ = v___x_5913_;
v_isShared_5924_ = v_isSharedCheck_5947_;
goto v_resetjp_5922_;
}
else
{
lean_inc(v_snapshotTasks_5921_);
lean_inc(v_infoState_5920_);
lean_inc(v_messages_5919_);
lean_inc(v_recordedDeps_5918_);
lean_inc(v_traceState_5917_);
lean_inc(v_auxDeclNGen_5916_);
lean_inc(v_ngen_5915_);
lean_inc(v_nextMacroScope_5914_);
lean_dec(v___x_5913_);
v___x_5923_ = lean_box(0);
v_isShared_5924_ = v_isSharedCheck_5947_;
goto v_resetjp_5922_;
}
v_resetjp_5922_:
{
lean_object* v___x_5925_; lean_object* v___x_5927_; 
v___x_5925_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
if (v_isShared_5924_ == 0)
{
lean_ctor_set(v___x_5923_, 5, v___x_5925_);
lean_ctor_set(v___x_5923_, 0, v_env_5909_);
v___x_5927_ = v___x_5923_;
goto v_reusejp_5926_;
}
else
{
lean_object* v_reuseFailAlloc_5946_; 
v_reuseFailAlloc_5946_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_5946_, 0, v_env_5909_);
lean_ctor_set(v_reuseFailAlloc_5946_, 1, v_nextMacroScope_5914_);
lean_ctor_set(v_reuseFailAlloc_5946_, 2, v_ngen_5915_);
lean_ctor_set(v_reuseFailAlloc_5946_, 3, v_auxDeclNGen_5916_);
lean_ctor_set(v_reuseFailAlloc_5946_, 4, v_traceState_5917_);
lean_ctor_set(v_reuseFailAlloc_5946_, 5, v___x_5925_);
lean_ctor_set(v_reuseFailAlloc_5946_, 6, v_recordedDeps_5918_);
lean_ctor_set(v_reuseFailAlloc_5946_, 7, v_messages_5919_);
lean_ctor_set(v_reuseFailAlloc_5946_, 8, v_infoState_5920_);
lean_ctor_set(v_reuseFailAlloc_5946_, 9, v_snapshotTasks_5921_);
v___x_5927_ = v_reuseFailAlloc_5946_;
goto v_reusejp_5926_;
}
v_reusejp_5926_:
{
lean_object* v___x_5928_; lean_object* v___x_5929_; lean_object* v_mctx_5930_; lean_object* v_zetaDeltaFVarIds_5931_; lean_object* v_postponed_5932_; lean_object* v_diag_5933_; lean_object* v___x_5935_; uint8_t v_isShared_5936_; uint8_t v_isSharedCheck_5944_; 
v___x_5928_ = lean_st_ref_put(v___y_5911_, v___x_5927_);
v___x_5929_ = lean_st_ref_take(v___y_5910_);
v_mctx_5930_ = lean_ctor_get(v___x_5929_, 0);
v_zetaDeltaFVarIds_5931_ = lean_ctor_get(v___x_5929_, 2);
v_postponed_5932_ = lean_ctor_get(v___x_5929_, 3);
v_diag_5933_ = lean_ctor_get(v___x_5929_, 4);
v_isSharedCheck_5944_ = !lean_is_exclusive(v___x_5929_);
if (v_isSharedCheck_5944_ == 0)
{
lean_object* v_unused_5945_; 
v_unused_5945_ = lean_ctor_get(v___x_5929_, 1);
lean_dec(v_unused_5945_);
v___x_5935_ = v___x_5929_;
v_isShared_5936_ = v_isSharedCheck_5944_;
goto v_resetjp_5934_;
}
else
{
lean_inc(v_diag_5933_);
lean_inc(v_postponed_5932_);
lean_inc(v_zetaDeltaFVarIds_5931_);
lean_inc(v_mctx_5930_);
lean_dec(v___x_5929_);
v___x_5935_ = lean_box(0);
v_isShared_5936_ = v_isSharedCheck_5944_;
goto v_resetjp_5934_;
}
v_resetjp_5934_:
{
lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5940_; 
v___x_5937_ = lean_box(0);
v___x_5938_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5936_ == 0)
{
lean_ctor_set(v___x_5935_, 1, v___x_5938_);
v___x_5940_ = v___x_5935_;
goto v_reusejp_5939_;
}
else
{
lean_object* v_reuseFailAlloc_5943_; 
v_reuseFailAlloc_5943_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5943_, 0, v_mctx_5930_);
lean_ctor_set(v_reuseFailAlloc_5943_, 1, v___x_5938_);
lean_ctor_set(v_reuseFailAlloc_5943_, 2, v_zetaDeltaFVarIds_5931_);
lean_ctor_set(v_reuseFailAlloc_5943_, 3, v_postponed_5932_);
lean_ctor_set(v_reuseFailAlloc_5943_, 4, v_diag_5933_);
v___x_5940_ = v_reuseFailAlloc_5943_;
goto v_reusejp_5939_;
}
v_reusejp_5939_:
{
lean_object* v___x_5941_; lean_object* v___x_5942_; 
v___x_5941_ = lean_st_ref_put(v___y_5910_, v___x_5940_);
v___x_5942_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5937_);
return v___x_5942_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5950_, lean_object* v___y_5951_, lean_object* v___y_5952_, lean_object* v___y_5953_){
_start:
{
lean_object* v_res_5954_; 
v_res_5954_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5950_, v___y_5951_, v___y_5952_);
lean_dec(v___y_5952_);
lean_dec(v___y_5951_);
return v_res_5954_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5955_, lean_object* v___y_5956_, lean_object* v___y_5957_, lean_object* v___y_5958_, lean_object* v___y_5959_){
_start:
{
lean_object* v___x_5961_; 
v___x_5961_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5955_, v___y_5957_, v___y_5959_);
return v___x_5961_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_){
_start:
{
lean_object* v_res_5968_; 
v_res_5968_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_);
lean_dec(v___y_5966_);
lean_dec_ref(v___y_5965_);
lean_dec(v___y_5964_);
lean_dec_ref(v___y_5963_);
return v_res_5968_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5970_; lean_object* v___x_5971_; 
v___x_5970_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5971_ = l_Lean_stringToMessageData(v___x_5970_);
return v___x_5971_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5973_; lean_object* v___x_5974_; 
v___x_5973_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5974_ = l_Lean_stringToMessageData(v___x_5973_);
return v___x_5974_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5976_; lean_object* v___x_5977_; 
v___x_5976_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5977_ = l_Lean_stringToMessageData(v___x_5976_);
return v___x_5977_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5979_; lean_object* v___x_5980_; 
v___x_5979_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5980_ = l_Lean_stringToMessageData(v___x_5979_);
return v___x_5980_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5982_; lean_object* v___x_5983_; 
v___x_5982_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5983_ = l_Lean_stringToMessageData(v___x_5982_);
return v___x_5983_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5984_, lean_object* v_prio_5985_, lean_object* v_x_5986_, lean_object* v_type_5987_, lean_object* v___y_5988_, lean_object* v___y_5989_, lean_object* v___y_5990_, lean_object* v___y_5991_){
_start:
{
lean_object* v___x_5993_; 
v___x_5993_ = l_Lean_Expr_getAppFn(v_type_5987_);
if (lean_obj_tag(v___x_5993_) == 4)
{
lean_object* v_declName_5994_; lean_object* v___y_5996_; lean_object* v___y_5997_; lean_object* v___y_5998_; lean_object* v___y_5999_; lean_object* v___x_6009_; lean_object* v_env_6010_; uint8_t v___x_6011_; 
v_declName_5994_ = lean_ctor_get(v___x_5993_, 0);
lean_inc(v_declName_5994_);
lean_dec_ref_known(v___x_5993_, 2);
v___x_6009_ = lean_st_ref_get(v___y_5991_);
v_env_6010_ = lean_ctor_get(v___x_6009_, 0);
lean_inc_ref(v_env_6010_);
lean_dec(v___x_6009_);
v___x_6011_ = l_Lean_isClass(v_env_6010_, v_declName_5994_);
if (v___x_6011_ == 0)
{
lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; 
lean_dec(v_prio_5985_);
v___x_6012_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_6013_ = l_Lean_MessageData_ofConstName(v_declName_5984_, v___x_6011_);
v___x_6014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6012_);
lean_ctor_set(v___x_6014_, 1, v___x_6013_);
v___x_6015_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_6016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6014_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
lean_inc(v_declName_5994_);
v___x_6017_ = l_Lean_MessageData_ofName(v_declName_5994_);
v___x_6018_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6018_, 0, v___x_6016_);
lean_ctor_set(v___x_6018_, 1, v___x_6017_);
v___x_6019_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_6020_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6018_);
lean_ctor_set(v___x_6020_, 1, v___x_6019_);
v___x_6021_ = l_Lean_MessageData_ofConstName(v_declName_5994_, v___x_6011_);
v___x_6022_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6020_);
lean_ctor_set(v___x_6022_, 1, v___x_6021_);
v___x_6023_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_6024_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6024_, 0, v___x_6022_);
lean_ctor_set(v___x_6024_, 1, v___x_6023_);
v___x_6025_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6024_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_);
return v___x_6025_;
}
else
{
v___y_5996_ = v___y_5988_;
v___y_5997_ = v___y_5989_;
v___y_5998_ = v___y_5990_;
v___y_5999_ = v___y_5991_;
goto v___jp_5995_;
}
v___jp_5995_:
{
lean_object* v___x_6000_; lean_object* v_env_6001_; lean_object* v___x_6002_; lean_object* v_toEnvExtension_6003_; lean_object* v_asyncMode_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; 
v___x_6000_ = lean_st_ref_get(v___y_5999_);
v_env_6001_ = lean_ctor_get(v___x_6000_, 0);
lean_inc_ref(v_env_6001_);
lean_dec(v___x_6000_);
v___x_6002_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6003_ = lean_ctor_get(v___x_6002_, 0);
v_asyncMode_6004_ = lean_ctor_get(v_toEnvExtension_6003_, 2);
v___x_6005_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6005_, 0, v_declName_5994_);
lean_ctor_set(v___x_6005_, 1, v_declName_5984_);
lean_ctor_set(v___x_6005_, 2, v_prio_5985_);
v___x_6006_ = lean_box(0);
v___x_6007_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_6002_, v_env_6001_, v___x_6005_, v_asyncMode_6004_, v___x_6006_);
v___x_6008_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_6007_, v___y_5997_, v___y_5999_);
return v___x_6008_;
}
}
else
{
lean_object* v___x_6026_; uint8_t v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; 
lean_dec_ref(v___x_5993_);
lean_dec(v_prio_5985_);
v___x_6026_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_6027_ = 0;
v___x_6028_ = l_Lean_MessageData_ofConstName(v_declName_5984_, v___x_6027_);
v___x_6029_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6029_, 0, v___x_6026_);
lean_ctor_set(v___x_6029_, 1, v___x_6028_);
v___x_6030_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_6031_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6031_, 0, v___x_6029_);
lean_ctor_set(v___x_6031_, 1, v___x_6030_);
v___x_6032_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6031_, v___y_5988_, v___y_5989_, v___y_5990_, v___y_5991_);
return v___x_6032_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_6033_, lean_object* v_prio_6034_, lean_object* v_x_6035_, lean_object* v_type_6036_, lean_object* v___y_6037_, lean_object* v___y_6038_, lean_object* v___y_6039_, lean_object* v___y_6040_, lean_object* v___y_6041_){
_start:
{
lean_object* v_res_6042_; 
v_res_6042_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_6033_, v_prio_6034_, v_x_6035_, v_type_6036_, v___y_6037_, v___y_6038_, v___y_6039_, v___y_6040_);
lean_dec(v___y_6040_);
lean_dec_ref(v___y_6039_);
lean_dec(v___y_6038_);
lean_dec_ref(v___y_6037_);
lean_dec_ref(v_type_6036_);
lean_dec_ref(v_x_6035_);
return v_res_6042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_6043_, lean_object* v_prio_6044_, lean_object* v_a_6045_, lean_object* v_a_6046_, lean_object* v_a_6047_, lean_object* v_a_6048_){
_start:
{
lean_object* v___f_6050_; lean_object* v___x_6051_; lean_object* v_env_6052_; uint8_t v___x_6053_; lean_object* v___x_6054_; 
lean_inc_n(v_declName_6043_, 2);
v___f_6050_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_6050_, 0, v_declName_6043_);
lean_closure_set(v___f_6050_, 1, v_prio_6044_);
v___x_6051_ = lean_st_ref_get(v_a_6048_);
v_env_6052_ = lean_ctor_get(v___x_6051_, 0);
lean_inc_ref(v_env_6052_);
lean_dec(v___x_6051_);
v___x_6053_ = 0;
v___x_6054_ = l_Lean_Environment_find_x3f(v_env_6052_, v_declName_6043_, v___x_6053_);
if (lean_obj_tag(v___x_6054_) == 0)
{
lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; lean_object* v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; 
lean_dec_ref(v___f_6050_);
v___x_6055_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_6056_ = l_Lean_MessageData_ofConstName(v_declName_6043_, v___x_6053_);
v___x_6057_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6057_, 0, v___x_6055_);
lean_ctor_set(v___x_6057_, 1, v___x_6056_);
v___x_6058_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_6059_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6059_, 0, v___x_6057_);
lean_ctor_set(v___x_6059_, 1, v___x_6058_);
v___x_6060_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_6059_, v_a_6045_, v_a_6046_, v_a_6047_, v_a_6048_);
return v___x_6060_;
}
else
{
lean_object* v_val_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; 
lean_dec(v_declName_6043_);
v_val_6061_ = lean_ctor_get(v___x_6054_, 0);
lean_inc(v_val_6061_);
lean_dec_ref_known(v___x_6054_, 1);
v___x_6062_ = l_Lean_ConstantInfo_type(v_val_6061_);
lean_dec(v_val_6061_);
v___x_6063_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_6062_, v___f_6050_, v___x_6053_, v___x_6053_, v_a_6045_, v_a_6046_, v_a_6047_, v_a_6048_);
return v___x_6063_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_6064_, lean_object* v_prio_6065_, lean_object* v_a_6066_, lean_object* v_a_6067_, lean_object* v_a_6068_, lean_object* v_a_6069_, lean_object* v_a_6070_){
_start:
{
lean_object* v_res_6071_; 
v_res_6071_ = l_Lean_Meta_addDefaultInstance(v_declName_6064_, v_prio_6065_, v_a_6066_, v_a_6067_, v_a_6068_, v_a_6069_);
lean_dec(v_a_6069_);
lean_dec_ref(v_a_6068_);
lean_dec(v_a_6067_);
lean_dec_ref(v_a_6066_);
return v_res_6071_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_6073_; lean_object* v___x_6074_; 
v___x_6073_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_6074_ = l_Lean_stringToMessageData(v___x_6073_);
return v___x_6074_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_6076_; lean_object* v___x_6077_; 
v___x_6076_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_6077_ = l_Lean_stringToMessageData(v___x_6076_);
return v___x_6077_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_6081_, uint8_t v_kind_6082_, lean_object* v___y_6083_, lean_object* v___y_6084_){
_start:
{
lean_object* v___x_6086_; lean_object* v___x_6087_; lean_object* v___x_6088_; lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___y_6092_; 
v___x_6086_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_6087_ = l_Lean_MessageData_ofName(v_name_6081_);
v___x_6088_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6088_, 0, v___x_6086_);
lean_ctor_set(v___x_6088_, 1, v___x_6087_);
v___x_6089_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_6090_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6090_, 0, v___x_6088_);
lean_ctor_set(v___x_6090_, 1, v___x_6089_);
switch(v_kind_6082_)
{
case 0:
{
lean_object* v___x_6099_; 
v___x_6099_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_6092_ = v___x_6099_;
goto v___jp_6091_;
}
case 1:
{
lean_object* v___x_6100_; 
v___x_6100_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_6092_ = v___x_6100_;
goto v___jp_6091_;
}
default: 
{
lean_object* v___x_6101_; 
v___x_6101_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_6092_ = v___x_6101_;
goto v___jp_6091_;
}
}
v___jp_6091_:
{
lean_object* v___x_6093_; lean_object* v___x_6094_; lean_object* v___x_6095_; lean_object* v___x_6096_; lean_object* v___x_6097_; lean_object* v___x_6098_; 
lean_inc_ref(v___y_6092_);
v___x_6093_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6093_, 0, v___y_6092_);
v___x_6094_ = l_Lean_MessageData_ofFormat(v___x_6093_);
v___x_6095_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6095_, 0, v___x_6090_);
lean_ctor_set(v___x_6095_, 1, v___x_6094_);
v___x_6096_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_6097_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6097_, 0, v___x_6095_);
lean_ctor_set(v___x_6097_, 1, v___x_6096_);
v___x_6098_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6097_, v___y_6083_, v___y_6084_);
return v___x_6098_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_6102_, lean_object* v_kind_6103_, lean_object* v___y_6104_, lean_object* v___y_6105_, lean_object* v___y_6106_){
_start:
{
uint8_t v_kind_boxed_6107_; lean_object* v_res_6108_; 
v_kind_boxed_6107_ = lean_unbox(v_kind_6103_);
v_res_6108_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6102_, v_kind_boxed_6107_, v___y_6104_, v___y_6105_);
lean_dec(v___y_6105_);
lean_dec_ref(v___y_6104_);
return v_res_6108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6109_, lean_object* v___x_6110_, lean_object* v___x_6111_, lean_object* v_declName_6112_, lean_object* v_stx_6113_, uint8_t v_kind_6114_, lean_object* v___y_6115_, lean_object* v___y_6116_){
_start:
{
lean_object* v___x_6118_; lean_object* v___x_6119_; lean_object* v___x_6120_; 
v___x_6118_ = lean_unsigned_to_nat(1u);
v___x_6119_ = l_Lean_Syntax_getArg(v_stx_6113_, v___x_6118_);
v___x_6120_ = l_Lean_getAttrParamOptPrio(v___x_6119_, v___y_6115_, v___y_6116_);
if (lean_obj_tag(v___x_6120_) == 0)
{
lean_object* v_a_6121_; lean_object* v___y_6123_; lean_object* v___y_6124_; uint8_t v___x_6155_; uint8_t v___x_6156_; 
v_a_6121_ = lean_ctor_get(v___x_6120_, 0);
lean_inc(v_a_6121_);
lean_dec_ref_known(v___x_6120_, 1);
v___x_6155_ = 0;
v___x_6156_ = l_Lean_instBEqAttributeKind_beq(v_kind_6114_, v___x_6155_);
if (v___x_6156_ == 0)
{
lean_object* v___x_6157_; 
lean_dec(v_a_6121_);
lean_dec(v_declName_6112_);
lean_dec(v___x_6110_);
lean_dec(v___x_6109_);
v___x_6157_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_6111_, v_kind_6114_, v___y_6115_, v___y_6116_);
return v___x_6157_;
}
else
{
lean_dec(v___x_6111_);
v___y_6123_ = v___y_6115_;
v___y_6124_ = v___y_6116_;
goto v___jp_6122_;
}
v___jp_6122_:
{
uint8_t v___x_6125_; uint8_t v___x_6126_; lean_object* v___x_6127_; lean_object* v___x_6128_; lean_object* v___x_6129_; lean_object* v___x_6130_; lean_object* v___x_6131_; size_t v___x_6132_; lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; lean_object* v___x_6136_; lean_object* v___x_6137_; lean_object* v___x_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v___x_6144_; lean_object* v___x_6145_; 
v___x_6125_ = 0;
v___x_6126_ = 1;
v___x_6127_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6128_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6129_ = lean_unsigned_to_nat(32u);
v___x_6130_ = lean_mk_empty_array_with_capacity(v___x_6129_);
v___x_6131_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_6132_ = ((size_t)5ULL);
lean_inc_n(v___x_6109_, 6);
v___x_6133_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6133_, 0, v___x_6131_);
lean_ctor_set(v___x_6133_, 1, v___x_6130_);
lean_ctor_set(v___x_6133_, 2, v___x_6109_);
lean_ctor_set(v___x_6133_, 3, v___x_6109_);
lean_ctor_set_usize(v___x_6133_, 4, v___x_6132_);
v___x_6134_ = lean_box(1);
lean_inc_ref(v___x_6133_);
v___x_6135_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6135_, 0, v___x_6128_);
lean_ctor_set(v___x_6135_, 1, v___x_6133_);
lean_ctor_set(v___x_6135_, 2, v___x_6134_);
v___x_6136_ = lean_mk_empty_array_with_capacity(v___x_6109_);
v___x_6137_ = lean_box(0);
lean_inc(v___x_6110_);
v___x_6138_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6138_, 0, v___x_6127_);
lean_ctor_set(v___x_6138_, 1, v___x_6110_);
lean_ctor_set(v___x_6138_, 2, v___x_6135_);
lean_ctor_set(v___x_6138_, 3, v___x_6136_);
lean_ctor_set(v___x_6138_, 4, v___x_6137_);
lean_ctor_set(v___x_6138_, 5, v___x_6109_);
lean_ctor_set(v___x_6138_, 6, v___x_6137_);
lean_ctor_set_uint8(v___x_6138_, sizeof(void*)*7, v___x_6125_);
lean_ctor_set_uint8(v___x_6138_, sizeof(void*)*7 + 1, v___x_6125_);
lean_ctor_set_uint8(v___x_6138_, sizeof(void*)*7 + 2, v___x_6125_);
lean_ctor_set_uint8(v___x_6138_, sizeof(void*)*7 + 3, v___x_6126_);
v___x_6139_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6139_, 0, v___x_6109_);
lean_ctor_set(v___x_6139_, 1, v___x_6109_);
lean_ctor_set(v___x_6139_, 2, v___x_6109_);
lean_ctor_set(v___x_6139_, 3, v___x_6109_);
lean_ctor_set(v___x_6139_, 4, v___x_6128_);
lean_ctor_set(v___x_6139_, 5, v___x_6128_);
lean_ctor_set(v___x_6139_, 6, v___x_6128_);
lean_ctor_set(v___x_6139_, 7, v___x_6128_);
lean_ctor_set(v___x_6139_, 8, v___x_6128_);
lean_ctor_set(v___x_6139_, 9, v___x_6128_);
lean_ctor_set(v___x_6139_, 10, v___x_6128_);
v___x_6140_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6141_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6142_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6142_, 0, v___x_6139_);
lean_ctor_set(v___x_6142_, 1, v___x_6140_);
lean_ctor_set(v___x_6142_, 2, v___x_6110_);
lean_ctor_set(v___x_6142_, 3, v___x_6133_);
lean_ctor_set(v___x_6142_, 4, v___x_6141_);
v___x_6143_ = lean_box(0);
v___x_6144_ = lean_st_mk_ref(v___x_6142_);
v___x_6145_ = l_Lean_Meta_addDefaultInstance(v_declName_6112_, v_a_6121_, v___x_6138_, v___x_6144_, v___y_6123_, v___y_6124_);
lean_dec_ref_known(v___x_6138_, 7);
if (lean_obj_tag(v___x_6145_) == 0)
{
lean_object* v___x_6147_; uint8_t v_isShared_6148_; uint8_t v_isSharedCheck_6153_; 
v_isSharedCheck_6153_ = !lean_is_exclusive(v___x_6145_);
if (v_isSharedCheck_6153_ == 0)
{
lean_object* v_unused_6154_; 
v_unused_6154_ = lean_ctor_get(v___x_6145_, 0);
lean_dec(v_unused_6154_);
v___x_6147_ = v___x_6145_;
v_isShared_6148_ = v_isSharedCheck_6153_;
goto v_resetjp_6146_;
}
else
{
lean_dec(v___x_6145_);
v___x_6147_ = lean_box(0);
v_isShared_6148_ = v_isSharedCheck_6153_;
goto v_resetjp_6146_;
}
v_resetjp_6146_:
{
lean_object* v___x_6149_; lean_object* v___x_6151_; 
v___x_6149_ = lean_st_ref_get(v___x_6144_);
lean_dec(v___x_6144_);
lean_dec(v___x_6149_);
if (v_isShared_6148_ == 0)
{
lean_ctor_set(v___x_6147_, 0, v___x_6143_);
v___x_6151_ = v___x_6147_;
goto v_reusejp_6150_;
}
else
{
lean_object* v_reuseFailAlloc_6152_; 
v_reuseFailAlloc_6152_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6152_, 0, v___x_6143_);
v___x_6151_ = v_reuseFailAlloc_6152_;
goto v_reusejp_6150_;
}
v_reusejp_6150_:
{
return v___x_6151_;
}
}
}
else
{
lean_dec(v___x_6144_);
return v___x_6145_;
}
}
}
else
{
lean_object* v_a_6158_; lean_object* v___x_6160_; uint8_t v_isShared_6161_; uint8_t v_isSharedCheck_6165_; 
lean_dec(v_declName_6112_);
lean_dec(v___x_6111_);
lean_dec(v___x_6110_);
lean_dec(v___x_6109_);
v_a_6158_ = lean_ctor_get(v___x_6120_, 0);
v_isSharedCheck_6165_ = !lean_is_exclusive(v___x_6120_);
if (v_isSharedCheck_6165_ == 0)
{
v___x_6160_ = v___x_6120_;
v_isShared_6161_ = v_isSharedCheck_6165_;
goto v_resetjp_6159_;
}
else
{
lean_inc(v_a_6158_);
lean_dec(v___x_6120_);
v___x_6160_ = lean_box(0);
v_isShared_6161_ = v_isSharedCheck_6165_;
goto v_resetjp_6159_;
}
v_resetjp_6159_:
{
lean_object* v___x_6163_; 
if (v_isShared_6161_ == 0)
{
v___x_6163_ = v___x_6160_;
goto v_reusejp_6162_;
}
else
{
lean_object* v_reuseFailAlloc_6164_; 
v_reuseFailAlloc_6164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6164_, 0, v_a_6158_);
v___x_6163_ = v_reuseFailAlloc_6164_;
goto v_reusejp_6162_;
}
v_reusejp_6162_:
{
return v___x_6163_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6166_, lean_object* v___x_6167_, lean_object* v___x_6168_, lean_object* v_declName_6169_, lean_object* v_stx_6170_, lean_object* v_kind_6171_, lean_object* v___y_6172_, lean_object* v___y_6173_, lean_object* v___y_6174_){
_start:
{
uint8_t v_kind_boxed_6175_; lean_object* v_res_6176_; 
v_kind_boxed_6175_ = lean_unbox(v_kind_6171_);
v_res_6176_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6166_, v___x_6167_, v___x_6168_, v_declName_6169_, v_stx_6170_, v_kind_boxed_6175_, v___y_6172_, v___y_6173_);
lean_dec(v___y_6173_);
lean_dec_ref(v___y_6172_);
lean_dec(v_stx_6170_);
return v_res_6176_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6178_; lean_object* v___x_6179_; 
v___x_6178_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6179_ = l_Lean_stringToMessageData(v___x_6178_);
return v___x_6179_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6181_; lean_object* v___x_6182_; 
v___x_6181_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6182_ = l_Lean_stringToMessageData(v___x_6181_);
return v___x_6182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6183_, lean_object* v_decl_6184_, lean_object* v___y_6185_, lean_object* v___y_6186_){
_start:
{
lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v___x_6190_; lean_object* v___x_6191_; lean_object* v___x_6192_; lean_object* v___x_6193_; 
v___x_6188_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6189_ = l_Lean_MessageData_ofName(v___x_6183_);
v___x_6190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6190_, 0, v___x_6188_);
lean_ctor_set(v___x_6190_, 1, v___x_6189_);
v___x_6191_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6192_, 0, v___x_6190_);
lean_ctor_set(v___x_6192_, 1, v___x_6191_);
v___x_6193_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6192_, v___y_6185_, v___y_6186_);
return v___x_6193_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6194_, lean_object* v_decl_6195_, lean_object* v___y_6196_, lean_object* v___y_6197_, lean_object* v___y_6198_){
_start:
{
lean_object* v_res_6199_; 
v_res_6199_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6194_, v_decl_6195_, v___y_6196_, v___y_6197_);
lean_dec(v___y_6197_);
lean_dec_ref(v___y_6196_);
lean_dec(v_decl_6195_);
return v_res_6199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; 
v___x_6232_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6233_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6234_ = l_Lean_registerBuiltinAttribute(v___x_6233_);
if (lean_obj_tag(v___x_6234_) == 0)
{
lean_object* v___x_6235_; uint8_t v___x_6236_; lean_object* v___x_6237_; 
lean_dec_ref_known(v___x_6234_, 1);
v___x_6235_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_6236_ = 0;
v___x_6237_ = l_Lean_registerTraceClass(v___x_6235_, v___x_6236_, v___x_6232_);
return v___x_6237_;
}
else
{
return v___x_6234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_6238_){
_start:
{
lean_object* v_res_6239_; 
v_res_6239_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_6239_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_6240_, lean_object* v_name_6241_, uint8_t v_kind_6242_, lean_object* v___y_6243_, lean_object* v___y_6244_){
_start:
{
lean_object* v___x_6246_; 
v___x_6246_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6241_, v_kind_6242_, v___y_6243_, v___y_6244_);
return v___x_6246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_6247_, lean_object* v_name_6248_, lean_object* v_kind_6249_, lean_object* v___y_6250_, lean_object* v___y_6251_, lean_object* v___y_6252_){
_start:
{
uint8_t v_kind_boxed_6253_; lean_object* v_res_6254_; 
v_kind_boxed_6253_ = lean_unbox(v_kind_6249_);
v_res_6254_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_6247_, v_name_6248_, v_kind_boxed_6253_, v___y_6250_, v___y_6251_);
lean_dec(v___y_6251_);
lean_dec_ref(v___y_6250_);
return v_res_6254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_6255_, lean_object* v_toPure_6256_, lean_object* v_____do__lift_6257_){
_start:
{
lean_object* v___x_6258_; lean_object* v_toEnvExtension_6259_; lean_object* v_asyncMode_6260_; lean_object* v___x_6261_; lean_object* v___x_6262_; lean_object* v_priorities_6263_; lean_object* v___x_6264_; 
v___x_6258_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6259_ = lean_ctor_get(v___x_6258_, 0);
v_asyncMode_6260_ = lean_ctor_get(v_toEnvExtension_6259_, 2);
v___x_6261_ = lean_box(0);
v___x_6262_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6255_, v___x_6258_, v_____do__lift_6257_, v_asyncMode_6260_, v___x_6261_);
v_priorities_6263_ = lean_ctor_get(v___x_6262_, 1);
lean_inc(v_priorities_6263_);
lean_dec(v___x_6262_);
v___x_6264_ = lean_apply_2(v_toPure_6256_, lean_box(0), v_priorities_6263_);
return v___x_6264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_6265_, lean_object* v_inst_6266_){
_start:
{
lean_object* v_toApplicative_6267_; lean_object* v_toBind_6268_; lean_object* v_getEnv_6269_; lean_object* v_toPure_6270_; lean_object* v___x_6271_; lean_object* v___f_6272_; lean_object* v___x_6273_; 
v_toApplicative_6267_ = lean_ctor_get(v_inst_6265_, 0);
lean_inc_ref(v_toApplicative_6267_);
v_toBind_6268_ = lean_ctor_get(v_inst_6265_, 1);
lean_inc(v_toBind_6268_);
lean_dec_ref(v_inst_6265_);
v_getEnv_6269_ = lean_ctor_get(v_inst_6266_, 0);
lean_inc(v_getEnv_6269_);
lean_dec_ref(v_inst_6266_);
v_toPure_6270_ = lean_ctor_get(v_toApplicative_6267_, 1);
lean_inc(v_toPure_6270_);
lean_dec_ref(v_toApplicative_6267_);
v___x_6271_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6272_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6272_, 0, v___x_6271_);
lean_closure_set(v___f_6272_, 1, v_toPure_6270_);
v___x_6273_ = lean_apply_4(v_toBind_6268_, lean_box(0), lean_box(0), v_getEnv_6269_, v___f_6272_);
return v___x_6273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_6274_, lean_object* v_inst_6275_, lean_object* v_inst_6276_){
_start:
{
lean_object* v___x_6277_; 
v___x_6277_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_6275_, v_inst_6276_);
return v___x_6277_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_6278_, uint8_t v_isExporting_6279_, lean_object* v_x_6280_){
_start:
{
lean_object* v_fst_6281_; uint8_t v___x_6282_; 
v_fst_6281_ = lean_ctor_get(v_x_6280_, 0);
lean_inc(v_fst_6281_);
lean_dec_ref(v_x_6280_);
v___x_6282_ = l_Lean_Environment_contains(v_env_6278_, v_fst_6281_, v_isExporting_6279_);
return v___x_6282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_6283_, lean_object* v_isExporting_6284_, lean_object* v_x_6285_){
_start:
{
uint8_t v_isExporting_boxed_6286_; uint8_t v_res_6287_; lean_object* v_r_6288_; 
v_isExporting_boxed_6286_ = lean_unbox(v_isExporting_6284_);
v_res_6287_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_6283_, v_isExporting_boxed_6286_, v_x_6285_);
v_r_6288_ = lean_box(v_res_6287_);
return v_r_6288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_6289_, lean_object* v_toPure_6290_, lean_object* v_className_6291_, lean_object* v_env_6292_){
_start:
{
lean_object* v___y_6294_; lean_object* v___x_6302_; lean_object* v_toEnvExtension_6303_; lean_object* v_asyncMode_6304_; lean_object* v___x_6305_; lean_object* v___x_6306_; lean_object* v_defaultInstances_6307_; lean_object* v___x_6308_; 
v___x_6302_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6303_ = lean_ctor_get(v___x_6302_, 0);
v_asyncMode_6304_ = lean_ctor_get(v_toEnvExtension_6303_, 2);
v___x_6305_ = lean_box(0);
lean_inc_ref(v_env_6292_);
v___x_6306_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6289_, v___x_6302_, v_env_6292_, v_asyncMode_6304_, v___x_6305_);
v_defaultInstances_6307_ = lean_ctor_get(v___x_6306_, 0);
lean_inc(v_defaultInstances_6307_);
lean_dec(v___x_6306_);
v___x_6308_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_6307_, v_className_6291_);
lean_dec(v_defaultInstances_6307_);
if (lean_obj_tag(v___x_6308_) == 0)
{
lean_object* v___x_6309_; 
v___x_6309_ = lean_box(0);
v___y_6294_ = v___x_6309_;
goto v___jp_6293_;
}
else
{
lean_object* v_val_6310_; 
v_val_6310_ = lean_ctor_get(v___x_6308_, 0);
lean_inc(v_val_6310_);
lean_dec_ref_known(v___x_6308_, 1);
v___y_6294_ = v_val_6310_;
goto v___jp_6293_;
}
v___jp_6293_:
{
uint8_t v_isExporting_6295_; 
v_isExporting_6295_ = lean_ctor_get_uint8(v_env_6292_, sizeof(void*)*8);
if (v_isExporting_6295_ == 0)
{
lean_object* v___x_6296_; 
lean_dec_ref(v_env_6292_);
v___x_6296_ = lean_apply_2(v_toPure_6290_, lean_box(0), v___y_6294_);
return v___x_6296_;
}
else
{
lean_object* v___x_6297_; lean_object* v___f_6298_; lean_object* v___x_6299_; lean_object* v___x_6300_; lean_object* v___x_6301_; 
v___x_6297_ = lean_box(v_isExporting_6295_);
v___f_6298_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6298_, 0, v_env_6292_);
lean_closure_set(v___f_6298_, 1, v___x_6297_);
v___x_6299_ = lean_box(0);
v___x_6300_ = l_List_filterTR_loop___redArg(v___f_6298_, v___y_6294_, v___x_6299_);
v___x_6301_ = lean_apply_2(v_toPure_6290_, lean_box(0), v___x_6300_);
return v___x_6301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_6311_, lean_object* v_toPure_6312_, lean_object* v_className_6313_, lean_object* v_env_6314_){
_start:
{
lean_object* v_res_6315_; 
v_res_6315_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_6311_, v_toPure_6312_, v_className_6313_, v_env_6314_);
lean_dec(v_className_6313_);
return v_res_6315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_6316_, lean_object* v_inst_6317_, lean_object* v_className_6318_){
_start:
{
lean_object* v_toApplicative_6319_; lean_object* v_toBind_6320_; lean_object* v_getEnv_6321_; lean_object* v_toPure_6322_; lean_object* v___x_6323_; lean_object* v___f_6324_; lean_object* v___x_6325_; 
v_toApplicative_6319_ = lean_ctor_get(v_inst_6316_, 0);
lean_inc_ref(v_toApplicative_6319_);
v_toBind_6320_ = lean_ctor_get(v_inst_6316_, 1);
lean_inc(v_toBind_6320_);
lean_dec_ref(v_inst_6316_);
v_getEnv_6321_ = lean_ctor_get(v_inst_6317_, 0);
lean_inc(v_getEnv_6321_);
lean_dec_ref(v_inst_6317_);
v_toPure_6322_ = lean_ctor_get(v_toApplicative_6319_, 1);
lean_inc(v_toPure_6322_);
lean_dec_ref(v_toApplicative_6319_);
v___x_6323_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6324_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_6324_, 0, v___x_6323_);
lean_closure_set(v___f_6324_, 1, v_toPure_6322_);
lean_closure_set(v___f_6324_, 2, v_className_6318_);
v___x_6325_ = lean_apply_4(v_toBind_6320_, lean_box(0), lean_box(0), v_getEnv_6321_, v___f_6324_);
return v___x_6325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6326_, lean_object* v_inst_6327_, lean_object* v_inst_6328_, lean_object* v_className_6329_){
_start:
{
lean_object* v___x_6330_; 
v___x_6330_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6327_, v_inst_6328_, v_className_6329_);
return v___x_6330_;
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
