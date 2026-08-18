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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_instBEqKey_beq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
extern lean_object* l_Lean_instInhabitedExpr;
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
lean_object* lean_st_ref_take(lean_object*);
uint64_t l_Lean_instHashableMVarId_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* lean_st_ref_put(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Lean_isPrivateName(lean_object*);
lean_object* l_Lean_Meta_DiscrTree_empty(lean_object*);
uint64_t l_Lean_Meta_DiscrTree_Key_hash(lean_object*);
lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_expr_eqv(lean_object*, lean_object*);
uint8_t l_Lean_Meta_DiscrTree_Key_lt(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_shiftr(lean_object*, lean_object*);
lean_object* l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_isUnaryNode___redArg(lean_object*);
lean_object* l_Array_eraseIdx___redArg(lean_object*, lean_object*);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Meta_DiscrTree_instInhabited(lean_object*);
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
uint8_t l_Lean_Expr_hasMVar(lean_object*);
lean_object* l_Lean_instantiateMVarsCore(lean_object*, lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Expr_hasExprMVar(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Expr_setPPExplicit(lean_object*, uint8_t);
lean_object* l_Lean_indentExpr(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofExpr(lean_object*);
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
lean_object* l_Lean_Syntax_getPos_x3f(lean_object*, uint8_t);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
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
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0;
static lean_once_cell_t l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0(lean_object*);
static lean_once_cell_t l_Lean_Meta_instInhabitedInstances_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedInstances_default___closed__0;
static lean_once_cell_t l_Lean_Meta_instInhabitedInstances_default___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedInstances_default___closed__1;
static lean_once_cell_t l_Lean_Meta_instInhabitedInstances_default___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedInstances_default___closed__2;
static lean_once_cell_t l_Lean_Meta_instInhabitedInstances_default___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedInstances_default___closed__3;
static lean_once_cell_t l_Lean_Meta_instInhabitedInstances_default___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_instInhabitedInstances_default___closed__4;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedInstances_default;
LEAN_EXPORT lean_object* l_Lean_Meta_instInhabitedInstances;
static lean_once_cell_t l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0;
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__0 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__0_value;
static const lean_ctor_object l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__0_value),((lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__0_value)}};
static const lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__1 = (const lean_object*)&l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13(lean_object*, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "instanceExtension"};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__6_00___x40_Lean_Meta_Instances_3022255136____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(194, 50, 106, 158, 41, 60, 103, 214)}};
static const lean_ctor_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__2_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(75, 253, 187, 89, 234, 162, 232, 19)}};
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_addInstanceEntry, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(uint8_t, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed(lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6;
static const lean_array_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8;
static const lean_ctor_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_value;
static const lean_ctor_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_value),((lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_value)}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10_value;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "This instance has "};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " argument"};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__15 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__15_value;
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3;
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
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "A private declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 79, .m_capacity = 79, .m_length = 78, .m_data = "` (from the current module) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "A public declaration `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 68, .m_capacity = 68, .m_length = 67, .m_data = "` exists but is imported privately; consider adding `public import "};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "` (from `"};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17;
static const lean_string_object l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 54, .m_capacity = 54, .m_length = 53, .m_data = "`) exists but would need to be public to access here."};
static const lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18 = (const lean_object*)&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18_value;
static lean_once_cell_t l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19;
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
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_;
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
static const lean_string_object l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 428, .m_capacity = 428, .m_length = 427, .m_data = "Registers type class instances.\n\nThe `instance` command, which expands to `@[instance] def`, is usually preferred over using this\nattribute directly. However it might sometimes still be necessary to use this attribute directly,\nin particular for `opaque` instances.\n\nTo assign priorities to instances, `@[instance prio]` can be used (where `prio` is a priority).\nThis corresponds to the `instance (priority := prio)` notation.\n"};
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
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0(void){
_start:
{
lean_object* v___x_104_; 
v___x_104_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_104_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__1(void){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_105_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__0);
v___x_106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_106_, 0, v___x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0(lean_object* v_00_u03b2_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_once(&l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__1, &l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__1_once, _init_l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0___closed__1);
return v___x_108_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__0(void){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_Lean_Meta_DiscrTree_empty(lean_box(0));
return v___x_109_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__1(void){
_start:
{
lean_object* v___x_110_; 
v___x_110_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_110_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__2(void){
_start:
{
lean_object* v___x_111_; lean_object* v___x_112_; 
v___x_111_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__1, &l_Lean_Meta_instInhabitedInstances_default___closed__1_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__1);
v___x_112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_112_, 0, v___x_111_);
return v___x_112_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__3(void){
_start:
{
lean_object* v___x_113_; 
v___x_113_ = l_Lean_PersistentHashMap_empty___at___00Lean_Meta_instInhabitedInstances_default_spec__0(lean_box(0));
return v___x_113_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default___closed__4(void){
_start:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_114_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__3, &l_Lean_Meta_instInhabitedInstances_default___closed__3_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__3);
v___x_115_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__2, &l_Lean_Meta_instInhabitedInstances_default___closed__2_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__2);
v___x_116_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__0, &l_Lean_Meta_instInhabitedInstances_default___closed__0_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__0);
v___x_117_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_117_, 0, v___x_116_);
lean_ctor_set(v___x_117_, 1, v___x_115_);
lean_ctor_set(v___x_117_, 2, v___x_114_);
return v___x_117_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances_default(void){
_start:
{
lean_object* v___x_118_; 
v___x_118_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__4, &l_Lean_Meta_instInhabitedInstances_default___closed__4_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__4);
return v___x_118_;
}
}
static lean_object* _init_l_Lean_Meta_instInhabitedInstances(void){
_start:
{
lean_object* v___x_119_; 
v___x_119_ = l_Lean_Meta_instInhabitedInstances_default;
return v___x_119_;
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_120_; 
v___x_120_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(lean_object* v_msg_121_){
_start:
{
lean_object* v___x_122_; lean_object* v___x_123_; 
v___x_122_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0);
v___x_123_ = lean_panic_fn_borrowed(v___x_122_, v_msg_121_);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(lean_object* v_xs_124_, lean_object* v_v_125_, lean_object* v_i_126_){
_start:
{
lean_object* v___x_127_; uint8_t v___x_128_; 
v___x_127_ = lean_array_get_size(v_xs_124_);
v___x_128_ = lean_nat_dec_lt(v_i_126_, v___x_127_);
if (v___x_128_ == 0)
{
lean_object* v___x_129_; 
lean_dec(v_i_126_);
v___x_129_ = lean_box(0);
return v___x_129_;
}
else
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = lean_array_fget_borrowed(v_xs_124_, v_i_126_);
v___x_131_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_130_, v_v_125_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
v___x_132_ = lean_unsigned_to_nat(1u);
v___x_133_ = lean_nat_add(v_i_126_, v___x_132_);
lean_dec(v_i_126_);
v_i_126_ = v___x_133_;
goto _start;
}
else
{
lean_object* v___x_135_; 
v___x_135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_135_, 0, v_i_126_);
return v___x_135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_xs_136_, lean_object* v_v_137_, lean_object* v_i_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(v_xs_136_, v_v_137_, v_i_138_);
lean_dec(v_v_137_);
lean_dec_ref(v_xs_136_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(lean_object* v_xs_140_, lean_object* v_v_141_){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = lean_unsigned_to_nat(0u);
v___x_143_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(v_xs_140_, v_v_141_, v___x_142_);
return v___x_143_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4___boxed(lean_object* v_xs_144_, lean_object* v_v_145_){
_start:
{
lean_object* v_res_146_; 
v_res_146_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(v_xs_144_, v_v_145_);
lean_dec(v_v_145_);
lean_dec_ref(v_xs_144_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(lean_object* v_x_147_, lean_object* v_x_148_, lean_object* v_x_149_, lean_object* v_x_150_){
_start:
{
lean_object* v_ks_151_; lean_object* v_vs_152_; lean_object* v___x_154_; uint8_t v_isShared_155_; uint8_t v_isSharedCheck_176_; 
v_ks_151_ = lean_ctor_get(v_x_147_, 0);
v_vs_152_ = lean_ctor_get(v_x_147_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_x_147_);
if (v_isSharedCheck_176_ == 0)
{
v___x_154_ = v_x_147_;
v_isShared_155_ = v_isSharedCheck_176_;
goto v_resetjp_153_;
}
else
{
lean_inc(v_vs_152_);
lean_inc(v_ks_151_);
lean_dec(v_x_147_);
v___x_154_ = lean_box(0);
v_isShared_155_ = v_isSharedCheck_176_;
goto v_resetjp_153_;
}
v_resetjp_153_:
{
lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_156_ = lean_array_get_size(v_ks_151_);
v___x_157_ = lean_nat_dec_lt(v_x_148_, v___x_156_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_161_; 
lean_dec(v_x_148_);
v___x_158_ = lean_array_push(v_ks_151_, v_x_149_);
v___x_159_ = lean_array_push(v_vs_152_, v_x_150_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v___x_159_);
lean_ctor_set(v___x_154_, 0, v___x_158_);
v___x_161_ = v___x_154_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_162_; 
v_reuseFailAlloc_162_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_162_, 0, v___x_158_);
lean_ctor_set(v_reuseFailAlloc_162_, 1, v___x_159_);
v___x_161_ = v_reuseFailAlloc_162_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
return v___x_161_;
}
}
else
{
lean_object* v_k_x27_163_; uint8_t v___x_164_; 
v_k_x27_163_ = lean_array_fget_borrowed(v_ks_151_, v_x_148_);
v___x_164_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_149_, v_k_x27_163_);
if (v___x_164_ == 0)
{
lean_object* v___x_166_; 
if (v_isShared_155_ == 0)
{
v___x_166_ = v___x_154_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_170_; 
v_reuseFailAlloc_170_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_170_, 0, v_ks_151_);
lean_ctor_set(v_reuseFailAlloc_170_, 1, v_vs_152_);
v___x_166_ = v_reuseFailAlloc_170_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = lean_unsigned_to_nat(1u);
v___x_168_ = lean_nat_add(v_x_148_, v___x_167_);
lean_dec(v_x_148_);
v_x_147_ = v___x_166_;
v_x_148_ = v___x_168_;
goto _start;
}
}
else
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_174_; 
v___x_171_ = lean_array_fset(v_ks_151_, v_x_148_, v_x_149_);
v___x_172_ = lean_array_fset(v_vs_152_, v_x_148_, v_x_150_);
lean_dec(v_x_148_);
if (v_isShared_155_ == 0)
{
lean_ctor_set(v___x_154_, 1, v___x_172_);
lean_ctor_set(v___x_154_, 0, v___x_171_);
v___x_174_ = v___x_154_;
goto v_reusejp_173_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v___x_172_);
v___x_174_ = v_reuseFailAlloc_175_;
goto v_reusejp_173_;
}
v_reusejp_173_:
{
return v___x_174_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(lean_object* v_n_177_, lean_object* v_k_178_, lean_object* v_v_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(v_n_177_, v___x_180_, v_k_178_, v_v_179_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_182_; 
v___x_182_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_x_183_, size_t v_x_184_, size_t v_x_185_, lean_object* v_x_186_, lean_object* v_x_187_){
_start:
{
if (lean_obj_tag(v_x_183_) == 0)
{
lean_object* v_es_188_; size_t v___x_189_; size_t v___x_190_; lean_object* v_j_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v_es_188_ = lean_ctor_get(v_x_183_, 0);
v___x_189_ = ((size_t)31ULL);
v___x_190_ = lean_usize_land(v_x_184_, v___x_189_);
v_j_191_ = lean_usize_to_nat(v___x_190_);
v___x_192_ = lean_array_get_size(v_es_188_);
v___x_193_ = lean_nat_dec_lt(v_j_191_, v___x_192_);
if (v___x_193_ == 0)
{
lean_dec(v_j_191_);
lean_dec(v_x_187_);
lean_dec(v_x_186_);
return v_x_183_;
}
else
{
lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_232_; 
lean_inc_ref(v_es_188_);
v_isSharedCheck_232_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_232_ == 0)
{
lean_object* v_unused_233_; 
v_unused_233_ = lean_ctor_get(v_x_183_, 0);
lean_dec(v_unused_233_);
v___x_195_ = v_x_183_;
v_isShared_196_ = v_isSharedCheck_232_;
goto v_resetjp_194_;
}
else
{
lean_dec(v_x_183_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_232_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
lean_object* v_v_197_; lean_object* v___x_198_; lean_object* v_xs_x27_199_; lean_object* v___y_201_; 
v_v_197_ = lean_array_fget(v_es_188_, v_j_191_);
v___x_198_ = lean_box(0);
v_xs_x27_199_ = lean_array_fset(v_es_188_, v_j_191_, v___x_198_);
switch(lean_obj_tag(v_v_197_))
{
case 0:
{
lean_object* v_key_206_; lean_object* v_val_207_; lean_object* v___x_209_; uint8_t v_isShared_210_; uint8_t v_isSharedCheck_217_; 
v_key_206_ = lean_ctor_get(v_v_197_, 0);
v_val_207_ = lean_ctor_get(v_v_197_, 1);
v_isSharedCheck_217_ = !lean_is_exclusive(v_v_197_);
if (v_isSharedCheck_217_ == 0)
{
v___x_209_ = v_v_197_;
v_isShared_210_ = v_isSharedCheck_217_;
goto v_resetjp_208_;
}
else
{
lean_inc(v_val_207_);
lean_inc(v_key_206_);
lean_dec(v_v_197_);
v___x_209_ = lean_box(0);
v_isShared_210_ = v_isSharedCheck_217_;
goto v_resetjp_208_;
}
v_resetjp_208_:
{
uint8_t v___x_211_; 
v___x_211_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_186_, v_key_206_);
if (v___x_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; 
lean_del_object(v___x_209_);
v___x_212_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_206_, v_val_207_, v_x_186_, v_x_187_);
v___x_213_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
v___y_201_ = v___x_213_;
goto v___jp_200_;
}
else
{
lean_object* v___x_215_; 
lean_dec(v_val_207_);
lean_dec(v_key_206_);
if (v_isShared_210_ == 0)
{
lean_ctor_set(v___x_209_, 1, v_x_187_);
lean_ctor_set(v___x_209_, 0, v_x_186_);
v___x_215_ = v___x_209_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_216_; 
v_reuseFailAlloc_216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_216_, 0, v_x_186_);
lean_ctor_set(v_reuseFailAlloc_216_, 1, v_x_187_);
v___x_215_ = v_reuseFailAlloc_216_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
v___y_201_ = v___x_215_;
goto v___jp_200_;
}
}
}
}
case 1:
{
lean_object* v_node_218_; lean_object* v___x_220_; uint8_t v_isShared_221_; uint8_t v_isSharedCheck_230_; 
v_node_218_ = lean_ctor_get(v_v_197_, 0);
v_isSharedCheck_230_ = !lean_is_exclusive(v_v_197_);
if (v_isSharedCheck_230_ == 0)
{
v___x_220_ = v_v_197_;
v_isShared_221_ = v_isSharedCheck_230_;
goto v_resetjp_219_;
}
else
{
lean_inc(v_node_218_);
lean_dec(v_v_197_);
v___x_220_ = lean_box(0);
v_isShared_221_ = v_isSharedCheck_230_;
goto v_resetjp_219_;
}
v_resetjp_219_:
{
size_t v___x_222_; size_t v___x_223_; size_t v___x_224_; size_t v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_222_ = ((size_t)5ULL);
v___x_223_ = lean_usize_shift_right(v_x_184_, v___x_222_);
v___x_224_ = ((size_t)1ULL);
v___x_225_ = lean_usize_add(v_x_185_, v___x_224_);
v___x_226_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_node_218_, v___x_223_, v___x_225_, v_x_186_, v_x_187_);
if (v_isShared_221_ == 0)
{
lean_ctor_set(v___x_220_, 0, v___x_226_);
v___x_228_ = v___x_220_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
v___y_201_ = v___x_228_;
goto v___jp_200_;
}
}
}
default: 
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_231_, 0, v_x_186_);
lean_ctor_set(v___x_231_, 1, v_x_187_);
v___y_201_ = v___x_231_;
goto v___jp_200_;
}
}
v___jp_200_:
{
lean_object* v___x_202_; lean_object* v___x_204_; 
v___x_202_ = lean_array_fset(v_xs_x27_199_, v_j_191_, v___y_201_);
lean_dec(v_j_191_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_202_);
v___x_204_ = v___x_195_;
goto v_reusejp_203_;
}
else
{
lean_object* v_reuseFailAlloc_205_; 
v_reuseFailAlloc_205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_205_, 0, v___x_202_);
v___x_204_ = v_reuseFailAlloc_205_;
goto v_reusejp_203_;
}
v_reusejp_203_:
{
return v___x_204_;
}
}
}
}
}
else
{
lean_object* v_ks_234_; lean_object* v_vs_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_255_; 
v_ks_234_ = lean_ctor_get(v_x_183_, 0);
v_vs_235_ = lean_ctor_get(v_x_183_, 1);
v_isSharedCheck_255_ = !lean_is_exclusive(v_x_183_);
if (v_isSharedCheck_255_ == 0)
{
v___x_237_ = v_x_183_;
v_isShared_238_ = v_isSharedCheck_255_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_vs_235_);
lean_inc(v_ks_234_);
lean_dec(v_x_183_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_255_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v___x_240_; 
if (v_isShared_238_ == 0)
{
v___x_240_ = v___x_237_;
goto v_reusejp_239_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_ks_234_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_vs_235_);
v___x_240_ = v_reuseFailAlloc_254_;
goto v_reusejp_239_;
}
v_reusejp_239_:
{
lean_object* v_newNode_241_; uint8_t v___y_243_; size_t v___x_249_; uint8_t v___x_250_; 
v_newNode_241_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(v___x_240_, v_x_186_, v_x_187_);
v___x_249_ = ((size_t)7ULL);
v___x_250_ = lean_usize_dec_le(v___x_249_, v_x_185_);
if (v___x_250_ == 0)
{
lean_object* v___x_251_; lean_object* v___x_252_; uint8_t v___x_253_; 
v___x_251_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_241_);
v___x_252_ = lean_unsigned_to_nat(4u);
v___x_253_ = lean_nat_dec_lt(v___x_251_, v___x_252_);
lean_dec(v___x_251_);
v___y_243_ = v___x_253_;
goto v___jp_242_;
}
else
{
v___y_243_ = v___x_250_;
goto v___jp_242_;
}
v___jp_242_:
{
if (v___y_243_ == 0)
{
lean_object* v_ks_244_; lean_object* v_vs_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_ks_244_ = lean_ctor_get(v_newNode_241_, 0);
lean_inc_ref(v_ks_244_);
v_vs_245_ = lean_ctor_get(v_newNode_241_, 1);
lean_inc_ref(v_vs_245_);
lean_dec_ref(v_newNode_241_);
v___x_246_ = lean_unsigned_to_nat(0u);
v___x_247_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0);
v___x_248_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(v_x_185_, v_ks_244_, v_vs_245_, v___x_246_, v___x_247_);
lean_dec_ref(v_vs_245_);
lean_dec_ref(v_ks_244_);
return v___x_248_;
}
else
{
return v_newNode_241_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(size_t v_depth_256_, lean_object* v_keys_257_, lean_object* v_vals_258_, lean_object* v_i_259_, lean_object* v_entries_260_){
_start:
{
lean_object* v___x_261_; uint8_t v___x_262_; 
v___x_261_ = lean_array_get_size(v_keys_257_);
v___x_262_ = lean_nat_dec_lt(v_i_259_, v___x_261_);
if (v___x_262_ == 0)
{
lean_dec(v_i_259_);
return v_entries_260_;
}
else
{
lean_object* v_k_263_; lean_object* v_v_264_; uint64_t v___x_265_; size_t v_h_266_; size_t v___x_267_; lean_object* v___x_268_; size_t v___x_269_; size_t v___x_270_; size_t v___x_271_; size_t v_h_272_; lean_object* v___x_273_; lean_object* v___x_274_; 
v_k_263_ = lean_array_fget_borrowed(v_keys_257_, v_i_259_);
v_v_264_ = lean_array_fget_borrowed(v_vals_258_, v_i_259_);
v___x_265_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_263_);
v_h_266_ = lean_uint64_to_usize(v___x_265_);
v___x_267_ = ((size_t)5ULL);
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = ((size_t)1ULL);
v___x_270_ = lean_usize_sub(v_depth_256_, v___x_269_);
v___x_271_ = lean_usize_mul(v___x_267_, v___x_270_);
v_h_272_ = lean_usize_shift_right(v_h_266_, v___x_271_);
v___x_273_ = lean_nat_add(v_i_259_, v___x_268_);
lean_dec(v_i_259_);
lean_inc(v_v_264_);
lean_inc(v_k_263_);
v___x_274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_entries_260_, v_h_272_, v_depth_256_, v_k_263_, v_v_264_);
v_i_259_ = v___x_273_;
v_entries_260_ = v___x_274_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg___boxed(lean_object* v_depth_276_, lean_object* v_keys_277_, lean_object* v_vals_278_, lean_object* v_i_279_, lean_object* v_entries_280_){
_start:
{
size_t v_depth_boxed_281_; lean_object* v_res_282_; 
v_depth_boxed_281_ = lean_unbox_usize(v_depth_276_);
lean_dec(v_depth_276_);
v_res_282_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(v_depth_boxed_281_, v_keys_277_, v_vals_278_, v_i_279_, v_entries_280_);
lean_dec_ref(v_vals_278_);
lean_dec_ref(v_keys_277_);
return v_res_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_, lean_object* v_x_286_, lean_object* v_x_287_){
_start:
{
size_t v_x_2121__boxed_288_; size_t v_x_2122__boxed_289_; lean_object* v_res_290_; 
v_x_2121__boxed_288_ = lean_unbox_usize(v_x_284_);
lean_dec(v_x_284_);
v_x_2122__boxed_289_ = lean_unbox_usize(v_x_285_);
lean_dec(v_x_285_);
v_res_290_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_x_283_, v_x_2121__boxed_288_, v_x_2122__boxed_289_, v_x_286_, v_x_287_);
return v_res_290_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(lean_object* v_x_291_, lean_object* v_keys_292_, lean_object* v_v_293_, lean_object* v_k_294_, lean_object* v_x_295_){
_start:
{
lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v_c_298_; lean_object* v___x_299_; 
v___x_296_ = lean_unsigned_to_nat(1u);
v___x_297_ = lean_nat_add(v_x_291_, v___x_296_);
v_c_298_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_292_, v_v_293_, v___x_297_);
lean_dec(v___x_297_);
v___x_299_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_299_, 0, v_k_294_);
lean_ctor_set(v___x_299_, 1, v_c_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* v_x_300_, lean_object* v_keys_301_, lean_object* v_v_302_, lean_object* v_k_303_, lean_object* v_x_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_300_, v_keys_301_, v_v_302_, v_k_303_, v_x_304_);
lean_dec_ref(v_keys_301_);
lean_dec(v_x_300_);
return v_res_305_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(lean_object* v_a_306_, lean_object* v_b_307_){
_start:
{
lean_object* v_fst_308_; lean_object* v_fst_309_; uint8_t v___x_310_; 
v_fst_308_ = lean_ctor_get(v_a_306_, 0);
v_fst_309_ = lean_ctor_get(v_b_307_, 0);
v___x_310_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_308_, v_fst_309_);
return v___x_310_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1___boxed(lean_object* v_a_311_, lean_object* v_b_312_){
_start:
{
uint8_t v_res_313_; lean_object* v_r_314_; 
v_res_313_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_a_311_, v_b_312_);
lean_dec_ref(v_b_312_);
lean_dec_ref(v_a_311_);
v_r_314_ = lean_box(v_res_313_);
return v_r_314_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(lean_object* v_vs_315_, lean_object* v_v_316_, lean_object* v_i_317_){
_start:
{
lean_object* v___x_318_; uint8_t v___x_319_; 
v___x_318_ = lean_array_get_size(v_vs_315_);
v___x_319_ = lean_nat_dec_lt(v_i_317_, v___x_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_320_; 
lean_dec(v_i_317_);
v___x_320_ = lean_array_push(v_vs_315_, v_v_316_);
return v___x_320_;
}
else
{
lean_object* v_val_321_; lean_object* v___x_322_; lean_object* v_val_323_; uint8_t v___x_324_; 
v_val_321_ = lean_ctor_get(v_v_316_, 1);
v___x_322_ = lean_array_fget_borrowed(v_vs_315_, v_i_317_);
v_val_323_ = lean_ctor_get(v___x_322_, 1);
v___x_324_ = lean_expr_eqv(v_val_321_, v_val_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
v___x_325_ = lean_unsigned_to_nat(1u);
v___x_326_ = lean_nat_add(v_i_317_, v___x_325_);
lean_dec(v_i_317_);
v_i_317_ = v___x_326_;
goto _start;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = lean_array_fset(v_vs_315_, v_i_317_, v_v_316_);
lean_dec(v_i_317_);
return v___x_328_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(lean_object* v_vs_329_, lean_object* v_v_330_){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = lean_unsigned_to_nat(0u);
v___x_332_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(v_vs_329_, v_v_330_, v___x_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_x_337_, lean_object* v_keys_338_, lean_object* v_v_339_, lean_object* v_k_340_, lean_object* v_as_341_, lean_object* v_k_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v_mid_347_; lean_object* v_midVal_348_; uint8_t v___x_349_; 
v___x_345_ = lean_nat_add(v_x_343_, v_x_344_);
v___x_346_ = lean_unsigned_to_nat(1u);
v_mid_347_ = lean_nat_shiftr(v___x_345_, v___x_346_);
lean_dec(v___x_345_);
v_midVal_348_ = lean_array_fget(v_as_341_, v_mid_347_);
v___x_349_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_midVal_348_, v_k_342_);
if (v___x_349_ == 0)
{
uint8_t v___x_350_; 
lean_dec(v_x_344_);
v___x_350_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_342_, v_midVal_348_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; uint8_t v___x_352_; 
lean_dec(v_x_343_);
v___x_351_ = lean_array_get_size(v_as_341_);
v___x_352_ = lean_nat_dec_lt(v_mid_347_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec(v_midVal_348_);
lean_dec(v_mid_347_);
lean_dec(v_k_340_);
lean_dec_ref(v_v_339_);
return v_as_341_;
}
else
{
lean_object* v_snd_353_; lean_object* v___x_355_; uint8_t v_isShared_356_; uint8_t v_isSharedCheck_365_; 
v_snd_353_ = lean_ctor_get(v_midVal_348_, 1);
v_isSharedCheck_365_ = !lean_is_exclusive(v_midVal_348_);
if (v_isSharedCheck_365_ == 0)
{
lean_object* v_unused_366_; 
v_unused_366_ = lean_ctor_get(v_midVal_348_, 0);
lean_dec(v_unused_366_);
v___x_355_ = v_midVal_348_;
v_isShared_356_ = v_isSharedCheck_365_;
goto v_resetjp_354_;
}
else
{
lean_inc(v_snd_353_);
lean_dec(v_midVal_348_);
v___x_355_ = lean_box(0);
v_isShared_356_ = v_isSharedCheck_365_;
goto v_resetjp_354_;
}
v_resetjp_354_:
{
lean_object* v___x_357_; lean_object* v_xs_x27_358_; lean_object* v___x_359_; lean_object* v_c_360_; lean_object* v___x_362_; 
v___x_357_ = lean_box(0);
v_xs_x27_358_ = lean_array_fset(v_as_341_, v_mid_347_, v___x_357_);
v___x_359_ = lean_nat_add(v_x_337_, v___x_346_);
v_c_360_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_338_, v_v_339_, v___x_359_, v_snd_353_);
lean_dec(v___x_359_);
if (v_isShared_356_ == 0)
{
lean_ctor_set(v___x_355_, 1, v_c_360_);
lean_ctor_set(v___x_355_, 0, v_k_340_);
v___x_362_ = v___x_355_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v_k_340_);
lean_ctor_set(v_reuseFailAlloc_364_, 1, v_c_360_);
v___x_362_ = v_reuseFailAlloc_364_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
lean_object* v___x_363_; 
v___x_363_ = lean_array_fset(v_xs_x27_358_, v_mid_347_, v___x_362_);
lean_dec(v_mid_347_);
return v___x_363_;
}
}
}
}
else
{
lean_dec(v_midVal_348_);
v_x_344_ = v_mid_347_;
goto _start;
}
}
else
{
uint8_t v___x_368_; 
lean_dec(v_midVal_348_);
v___x_368_ = lean_nat_dec_eq(v_mid_347_, v_x_343_);
if (v___x_368_ == 0)
{
lean_dec(v_x_343_);
v_x_343_ = v_mid_347_;
goto _start;
}
else
{
lean_object* v___x_370_; lean_object* v_c_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v_j_374_; lean_object* v_as_375_; lean_object* v___x_376_; 
lean_dec(v_mid_347_);
lean_dec(v_x_344_);
v___x_370_ = lean_nat_add(v_x_337_, v___x_346_);
v_c_371_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_338_, v_v_339_, v___x_370_);
lean_dec(v___x_370_);
v___x_372_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_372_, 0, v_k_340_);
lean_ctor_set(v___x_372_, 1, v_c_371_);
v___x_373_ = lean_nat_add(v_x_343_, v___x_346_);
lean_dec(v_x_343_);
v_j_374_ = lean_array_get_size(v_as_341_);
v_as_375_ = lean_array_push(v_as_341_, v___x_372_);
v___x_376_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_373_, v_as_375_, v_j_374_);
lean_dec(v___x_373_);
return v___x_376_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(lean_object* v_x_377_, lean_object* v_keys_378_, lean_object* v_v_379_, lean_object* v_k_380_, lean_object* v_as_381_, lean_object* v_k_382_){
_start:
{
lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; 
v___x_383_ = lean_array_get_size(v_as_381_);
v___x_384_ = lean_unsigned_to_nat(0u);
v___x_385_ = lean_nat_dec_eq(v___x_383_, v___x_384_);
if (v___x_385_ == 0)
{
lean_object* v___x_386_; uint8_t v___x_387_; 
v___x_386_ = lean_array_fget_borrowed(v_as_381_, v___x_384_);
v___x_387_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_382_, v___x_386_);
if (v___x_387_ == 0)
{
uint8_t v___x_388_; 
v___x_388_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v___x_386_, v_k_382_);
if (v___x_388_ == 0)
{
uint8_t v___x_389_; 
v___x_389_ = lean_nat_dec_lt(v___x_384_, v___x_383_);
if (v___x_389_ == 0)
{
lean_dec(v_k_380_);
lean_dec_ref(v_v_379_);
return v_as_381_;
}
else
{
lean_object* v___x_390_; lean_object* v_xs_x27_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
lean_inc(v___x_386_);
v___x_390_ = lean_box(0);
v_xs_x27_391_ = lean_array_fset(v_as_381_, v___x_384_, v___x_390_);
v___x_392_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_377_, v_keys_378_, v_v_379_, v_k_380_, v___x_386_);
v___x_393_ = lean_array_fset(v_xs_x27_391_, v___x_384_, v___x_392_);
return v___x_393_;
}
}
else
{
lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; uint8_t v___x_397_; 
v___x_394_ = lean_unsigned_to_nat(1u);
v___x_395_ = lean_nat_sub(v___x_383_, v___x_394_);
v___x_396_ = lean_array_fget_borrowed(v_as_381_, v___x_395_);
v___x_397_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v___x_396_, v_k_382_);
if (v___x_397_ == 0)
{
uint8_t v___x_398_; 
v___x_398_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_382_, v___x_396_);
if (v___x_398_ == 0)
{
uint8_t v___x_399_; 
v___x_399_ = lean_nat_dec_lt(v___x_395_, v___x_383_);
if (v___x_399_ == 0)
{
lean_dec(v___x_395_);
lean_dec(v_k_380_);
lean_dec_ref(v_v_379_);
return v_as_381_;
}
else
{
lean_object* v___x_400_; lean_object* v_xs_x27_401_; lean_object* v___x_402_; lean_object* v___x_403_; 
lean_inc(v___x_396_);
v___x_400_ = lean_box(0);
v_xs_x27_401_ = lean_array_fset(v_as_381_, v___x_395_, v___x_400_);
v___x_402_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_377_, v_keys_378_, v_v_379_, v_k_380_, v___x_396_);
v___x_403_ = lean_array_fset(v_xs_x27_401_, v___x_395_, v___x_402_);
lean_dec(v___x_395_);
return v___x_403_;
}
}
else
{
lean_object* v___x_404_; 
v___x_404_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_377_, v_keys_378_, v_v_379_, v_k_380_, v_as_381_, v_k_382_, v___x_384_, v___x_395_);
return v___x_404_;
}
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec(v___x_395_);
v___x_405_ = lean_box(0);
v___x_406_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_377_, v_keys_378_, v_v_379_, v_k_380_, v___x_405_);
v___x_407_ = lean_array_push(v_as_381_, v___x_406_);
return v___x_407_;
}
}
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v_as_410_; lean_object* v___x_411_; 
v___x_408_ = lean_box(0);
v___x_409_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_377_, v_keys_378_, v_v_379_, v_k_380_, v___x_408_);
v_as_410_ = lean_array_push(v_as_381_, v___x_409_);
v___x_411_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_384_, v_as_410_, v___x_383_);
return v___x_411_;
}
}
else
{
lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_412_ = lean_box(0);
v___x_413_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_377_, v_keys_378_, v_v_379_, v_k_380_, v___x_412_);
v___x_414_ = lean_array_push(v_as_381_, v___x_413_);
return v___x_414_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object* v_keys_415_, lean_object* v_v_416_, lean_object* v_x_417_, lean_object* v_x_418_){
_start:
{
lean_object* v_vs_419_; lean_object* v_children_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_437_; 
v_vs_419_ = lean_ctor_get(v_x_418_, 0);
v_children_420_ = lean_ctor_get(v_x_418_, 1);
v_isSharedCheck_437_ = !lean_is_exclusive(v_x_418_);
if (v_isSharedCheck_437_ == 0)
{
v___x_422_ = v_x_418_;
v_isShared_423_ = v_isSharedCheck_437_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_children_420_);
lean_inc(v_vs_419_);
lean_dec(v_x_418_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_437_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; uint8_t v___x_425_; 
v___x_424_ = lean_array_get_size(v_keys_415_);
v___x_425_ = lean_nat_dec_lt(v_x_417_, v___x_424_);
if (v___x_425_ == 0)
{
lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_426_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(v_vs_419_, v_v_416_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 0, v___x_426_);
v___x_428_ = v___x_422_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v_children_420_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
else
{
lean_object* v_k_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v_c_433_; lean_object* v___x_435_; 
v_k_430_ = lean_array_fget_borrowed(v_keys_415_, v_x_417_);
v___x_431_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__1));
lean_inc_n(v_k_430_, 2);
v___x_432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_432_, 0, v_k_430_);
lean_ctor_set(v___x_432_, 1, v___x_431_);
v_c_433_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(v_x_417_, v_keys_415_, v_v_416_, v_k_430_, v_children_420_, v___x_432_);
lean_dec_ref_known(v___x_432_, 2);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 1, v_c_433_);
v___x_435_ = v___x_422_;
goto v_reusejp_434_;
}
else
{
lean_object* v_reuseFailAlloc_436_; 
v_reuseFailAlloc_436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_436_, 0, v_vs_419_);
lean_ctor_set(v_reuseFailAlloc_436_, 1, v_c_433_);
v___x_435_ = v_reuseFailAlloc_436_;
goto v_reusejp_434_;
}
v_reusejp_434_:
{
return v___x_435_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(lean_object* v_x_438_, lean_object* v_keys_439_, lean_object* v_v_440_, lean_object* v_k_441_, lean_object* v_x_442_){
_start:
{
lean_object* v_snd_443_; lean_object* v___x_445_; uint8_t v_isShared_446_; uint8_t v_isSharedCheck_453_; 
v_snd_443_ = lean_ctor_get(v_x_442_, 1);
v_isSharedCheck_453_ = !lean_is_exclusive(v_x_442_);
if (v_isSharedCheck_453_ == 0)
{
lean_object* v_unused_454_; 
v_unused_454_ = lean_ctor_get(v_x_442_, 0);
lean_dec(v_unused_454_);
v___x_445_ = v_x_442_;
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
else
{
lean_inc(v_snd_443_);
lean_dec(v_x_442_);
v___x_445_ = lean_box(0);
v_isShared_446_ = v_isSharedCheck_453_;
goto v_resetjp_444_;
}
v_resetjp_444_:
{
lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v_c_449_; lean_object* v___x_451_; 
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_add(v_x_438_, v___x_447_);
v_c_449_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_439_, v_v_440_, v___x_448_, v_snd_443_);
lean_dec(v___x_448_);
if (v_isShared_446_ == 0)
{
lean_ctor_set(v___x_445_, 1, v_c_449_);
lean_ctor_set(v___x_445_, 0, v_k_441_);
v___x_451_ = v___x_445_;
goto v_reusejp_450_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_k_441_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v_c_449_);
v___x_451_ = v_reuseFailAlloc_452_;
goto v_reusejp_450_;
}
v_reusejp_450_:
{
return v___x_451_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* v_x_455_, lean_object* v_keys_456_, lean_object* v_v_457_, lean_object* v_k_458_, lean_object* v_x_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_455_, v_keys_456_, v_v_457_, v_k_458_, v_x_459_);
lean_dec_ref(v_keys_456_);
lean_dec(v_x_455_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object* v_keys_461_, lean_object* v_v_462_, lean_object* v_x_463_, lean_object* v_x_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_461_, v_v_462_, v_x_463_, v_x_464_);
lean_dec(v_x_463_);
lean_dec_ref(v_keys_461_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_x_466_, lean_object* v_keys_467_, lean_object* v_v_468_, lean_object* v_k_469_, lean_object* v_as_470_, lean_object* v_k_471_, lean_object* v_x_472_, lean_object* v_x_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_466_, v_keys_467_, v_v_468_, v_k_469_, v_as_470_, v_k_471_, v_x_472_, v_x_473_);
lean_dec_ref(v_k_471_);
lean_dec_ref(v_keys_467_);
lean_dec(v_x_466_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_x_475_, lean_object* v_keys_476_, lean_object* v_v_477_, lean_object* v_k_478_, lean_object* v_as_479_, lean_object* v_k_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(v_x_475_, v_keys_476_, v_v_477_, v_k_478_, v_as_479_, v_k_480_);
lean_dec_ref(v_k_480_);
lean_dec_ref(v_keys_476_);
lean_dec(v_x_475_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(lean_object* v_keys_482_, lean_object* v_v_483_, lean_object* v_x_484_){
_start:
{
if (lean_obj_tag(v_x_484_) == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_485_ = lean_unsigned_to_nat(1u);
v___x_486_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_482_, v_v_483_, v___x_485_);
v___x_487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_487_, 0, v___x_486_);
return v___x_487_;
}
else
{
lean_object* v_val_488_; lean_object* v___x_490_; uint8_t v_isShared_491_; uint8_t v_isSharedCheck_497_; 
v_val_488_ = lean_ctor_get(v_x_484_, 0);
v_isSharedCheck_497_ = !lean_is_exclusive(v_x_484_);
if (v_isSharedCheck_497_ == 0)
{
v___x_490_ = v_x_484_;
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
else
{
lean_inc(v_val_488_);
lean_dec(v_x_484_);
v___x_490_ = lean_box(0);
v_isShared_491_ = v_isSharedCheck_497_;
goto v_resetjp_489_;
}
v_resetjp_489_:
{
lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_495_; 
v___x_492_ = lean_unsigned_to_nat(1u);
v___x_493_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_482_, v_v_483_, v___x_492_, v_val_488_);
if (v_isShared_491_ == 0)
{
lean_ctor_set(v___x_490_, 0, v___x_493_);
v___x_495_ = v___x_490_;
goto v_reusejp_494_;
}
else
{
lean_object* v_reuseFailAlloc_496_; 
v_reuseFailAlloc_496_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_496_, 0, v___x_493_);
v___x_495_ = v_reuseFailAlloc_496_;
goto v_reusejp_494_;
}
v_reusejp_494_:
{
return v___x_495_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0___boxed(lean_object* v_keys_498_, lean_object* v_v_499_, lean_object* v_x_500_){
_start:
{
lean_object* v_res_501_; 
v_res_501_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_498_, v_v_499_, v_x_500_);
lean_dec_ref(v_keys_498_);
return v_res_501_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(lean_object* v_keys_502_, lean_object* v_v_503_, lean_object* v_x_504_, size_t v_x_505_, size_t v_x_506_, lean_object* v_x_507_){
_start:
{
if (lean_obj_tag(v_x_504_) == 0)
{
lean_object* v_es_508_; size_t v___x_509_; size_t v___x_510_; lean_object* v_j_511_; lean_object* v___x_512_; uint8_t v___x_513_; 
v_es_508_ = lean_ctor_get(v_x_504_, 0);
v___x_509_ = ((size_t)31ULL);
v___x_510_ = lean_usize_land(v_x_505_, v___x_509_);
v_j_511_ = lean_usize_to_nat(v___x_510_);
v___x_512_ = lean_array_get_size(v_es_508_);
v___x_513_ = lean_nat_dec_lt(v_j_511_, v___x_512_);
if (v___x_513_ == 0)
{
lean_dec(v_j_511_);
lean_dec(v_x_507_);
lean_dec_ref(v_v_503_);
return v_x_504_;
}
else
{
lean_object* v___x_515_; uint8_t v_isShared_516_; uint8_t v_isSharedCheck_581_; 
lean_inc_ref(v_es_508_);
v_isSharedCheck_581_ = !lean_is_exclusive(v_x_504_);
if (v_isSharedCheck_581_ == 0)
{
lean_object* v_unused_582_; 
v_unused_582_ = lean_ctor_get(v_x_504_, 0);
lean_dec(v_unused_582_);
v___x_515_ = v_x_504_;
v_isShared_516_ = v_isSharedCheck_581_;
goto v_resetjp_514_;
}
else
{
lean_dec(v_x_504_);
v___x_515_ = lean_box(0);
v_isShared_516_ = v_isSharedCheck_581_;
goto v_resetjp_514_;
}
v_resetjp_514_:
{
lean_object* v_v_517_; lean_object* v___x_518_; lean_object* v_xs_x27_519_; lean_object* v___y_521_; 
v_v_517_ = lean_array_fget(v_es_508_, v_j_511_);
v___x_518_ = lean_box(0);
v_xs_x27_519_ = lean_array_fset(v_es_508_, v_j_511_, v___x_518_);
switch(lean_obj_tag(v_v_517_))
{
case 0:
{
lean_object* v_key_526_; lean_object* v_val_527_; uint8_t v___x_528_; 
v_key_526_ = lean_ctor_get(v_v_517_, 0);
v_val_527_ = lean_ctor_get(v_v_517_, 1);
v___x_528_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_507_, v_key_526_);
if (v___x_528_ == 0)
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_box(0);
v___x_530_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_502_, v_v_503_, v___x_529_);
if (lean_obj_tag(v___x_530_) == 0)
{
lean_dec(v_x_507_);
v___y_521_ = v_v_517_;
goto v___jp_520_;
}
else
{
lean_object* v_val_531_; lean_object* v___x_533_; uint8_t v_isShared_534_; uint8_t v_isSharedCheck_539_; 
lean_inc(v_val_527_);
lean_inc(v_key_526_);
lean_dec_ref_known(v_v_517_, 2);
v_val_531_ = lean_ctor_get(v___x_530_, 0);
v_isSharedCheck_539_ = !lean_is_exclusive(v___x_530_);
if (v_isSharedCheck_539_ == 0)
{
v___x_533_ = v___x_530_;
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
else
{
lean_inc(v_val_531_);
lean_dec(v___x_530_);
v___x_533_ = lean_box(0);
v_isShared_534_ = v_isSharedCheck_539_;
goto v_resetjp_532_;
}
v_resetjp_532_:
{
lean_object* v___x_535_; lean_object* v___x_537_; 
v___x_535_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_526_, v_val_527_, v_x_507_, v_val_531_);
if (v_isShared_534_ == 0)
{
lean_ctor_set(v___x_533_, 0, v___x_535_);
v___x_537_ = v___x_533_;
goto v_reusejp_536_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_535_);
v___x_537_ = v_reuseFailAlloc_538_;
goto v_reusejp_536_;
}
v_reusejp_536_:
{
v___y_521_ = v___x_537_;
goto v___jp_520_;
}
}
}
}
else
{
lean_object* v___x_541_; uint8_t v_isShared_542_; uint8_t v_isSharedCheck_550_; 
lean_inc(v_val_527_);
v_isSharedCheck_550_ = !lean_is_exclusive(v_v_517_);
if (v_isSharedCheck_550_ == 0)
{
lean_object* v_unused_551_; lean_object* v_unused_552_; 
v_unused_551_ = lean_ctor_get(v_v_517_, 1);
lean_dec(v_unused_551_);
v_unused_552_ = lean_ctor_get(v_v_517_, 0);
lean_dec(v_unused_552_);
v___x_541_ = v_v_517_;
v_isShared_542_ = v_isSharedCheck_550_;
goto v_resetjp_540_;
}
else
{
lean_dec(v_v_517_);
v___x_541_ = lean_box(0);
v_isShared_542_ = v_isSharedCheck_550_;
goto v_resetjp_540_;
}
v_resetjp_540_:
{
lean_object* v___x_543_; lean_object* v___x_544_; 
v___x_543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_543_, 0, v_val_527_);
v___x_544_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_502_, v_v_503_, v___x_543_);
if (lean_obj_tag(v___x_544_) == 0)
{
lean_object* v___x_545_; 
lean_del_object(v___x_541_);
lean_dec(v_x_507_);
v___x_545_ = lean_box(2);
v___y_521_ = v___x_545_;
goto v___jp_520_;
}
else
{
lean_object* v_val_546_; lean_object* v___x_548_; 
v_val_546_ = lean_ctor_get(v___x_544_, 0);
lean_inc(v_val_546_);
lean_dec_ref_known(v___x_544_, 1);
if (v_isShared_542_ == 0)
{
lean_ctor_set(v___x_541_, 1, v_val_546_);
lean_ctor_set(v___x_541_, 0, v_x_507_);
v___x_548_ = v___x_541_;
goto v_reusejp_547_;
}
else
{
lean_object* v_reuseFailAlloc_549_; 
v_reuseFailAlloc_549_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_549_, 0, v_x_507_);
lean_ctor_set(v_reuseFailAlloc_549_, 1, v_val_546_);
v___x_548_ = v_reuseFailAlloc_549_;
goto v_reusejp_547_;
}
v_reusejp_547_:
{
v___y_521_ = v___x_548_;
goto v___jp_520_;
}
}
}
}
}
case 1:
{
lean_object* v_node_553_; lean_object* v___x_555_; uint8_t v_isShared_556_; uint8_t v_isSharedCheck_576_; 
v_node_553_ = lean_ctor_get(v_v_517_, 0);
v_isSharedCheck_576_ = !lean_is_exclusive(v_v_517_);
if (v_isSharedCheck_576_ == 0)
{
v___x_555_ = v_v_517_;
v_isShared_556_ = v_isSharedCheck_576_;
goto v_resetjp_554_;
}
else
{
lean_inc(v_node_553_);
lean_dec(v_v_517_);
v___x_555_ = lean_box(0);
v_isShared_556_ = v_isSharedCheck_576_;
goto v_resetjp_554_;
}
v_resetjp_554_:
{
size_t v___x_557_; size_t v___x_558_; size_t v___x_559_; size_t v___x_560_; lean_object* v_newNode_561_; lean_object* v___x_562_; 
v___x_557_ = ((size_t)5ULL);
v___x_558_ = lean_usize_shift_right(v_x_505_, v___x_557_);
v___x_559_ = ((size_t)1ULL);
v___x_560_ = lean_usize_add(v_x_506_, v___x_559_);
v_newNode_561_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_502_, v_v_503_, v_node_553_, v___x_558_, v___x_560_, v_x_507_);
lean_inc_ref(v_newNode_561_);
v___x_562_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_561_);
if (lean_obj_tag(v___x_562_) == 0)
{
lean_object* v___x_564_; 
if (v_isShared_556_ == 0)
{
lean_ctor_set(v___x_555_, 0, v_newNode_561_);
v___x_564_ = v___x_555_;
goto v_reusejp_563_;
}
else
{
lean_object* v_reuseFailAlloc_565_; 
v_reuseFailAlloc_565_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_565_, 0, v_newNode_561_);
v___x_564_ = v_reuseFailAlloc_565_;
goto v_reusejp_563_;
}
v_reusejp_563_:
{
v___y_521_ = v___x_564_;
goto v___jp_520_;
}
}
else
{
lean_object* v_val_566_; lean_object* v_fst_567_; lean_object* v_snd_568_; lean_object* v___x_570_; uint8_t v_isShared_571_; uint8_t v_isSharedCheck_575_; 
lean_dec_ref(v_newNode_561_);
lean_del_object(v___x_555_);
v_val_566_ = lean_ctor_get(v___x_562_, 0);
lean_inc(v_val_566_);
lean_dec_ref_known(v___x_562_, 1);
v_fst_567_ = lean_ctor_get(v_val_566_, 0);
v_snd_568_ = lean_ctor_get(v_val_566_, 1);
v_isSharedCheck_575_ = !lean_is_exclusive(v_val_566_);
if (v_isSharedCheck_575_ == 0)
{
v___x_570_ = v_val_566_;
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
else
{
lean_inc(v_snd_568_);
lean_inc(v_fst_567_);
lean_dec(v_val_566_);
v___x_570_ = lean_box(0);
v_isShared_571_ = v_isSharedCheck_575_;
goto v_resetjp_569_;
}
v_resetjp_569_:
{
lean_object* v___x_573_; 
if (v_isShared_571_ == 0)
{
v___x_573_ = v___x_570_;
goto v_reusejp_572_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_fst_567_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_snd_568_);
v___x_573_ = v_reuseFailAlloc_574_;
goto v_reusejp_572_;
}
v_reusejp_572_:
{
v___y_521_ = v___x_573_;
goto v___jp_520_;
}
}
}
}
}
default: 
{
lean_object* v___x_577_; lean_object* v___x_578_; 
v___x_577_ = lean_box(0);
v___x_578_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_502_, v_v_503_, v___x_577_);
if (lean_obj_tag(v___x_578_) == 0)
{
lean_dec(v_x_507_);
v___y_521_ = v_v_517_;
goto v___jp_520_;
}
else
{
lean_object* v_val_579_; lean_object* v___x_580_; 
v_val_579_ = lean_ctor_get(v___x_578_, 0);
lean_inc(v_val_579_);
lean_dec_ref_known(v___x_578_, 1);
v___x_580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_580_, 0, v_x_507_);
lean_ctor_set(v___x_580_, 1, v_val_579_);
v___y_521_ = v___x_580_;
goto v___jp_520_;
}
}
}
v___jp_520_:
{
lean_object* v___x_522_; lean_object* v___x_524_; 
v___x_522_ = lean_array_fset(v_xs_x27_519_, v_j_511_, v___y_521_);
lean_dec(v_j_511_);
if (v_isShared_516_ == 0)
{
lean_ctor_set(v___x_515_, 0, v___x_522_);
v___x_524_ = v___x_515_;
goto v_reusejp_523_;
}
else
{
lean_object* v_reuseFailAlloc_525_; 
v_reuseFailAlloc_525_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_525_, 0, v___x_522_);
v___x_524_ = v_reuseFailAlloc_525_;
goto v_reusejp_523_;
}
v_reusejp_523_:
{
return v___x_524_;
}
}
}
}
}
else
{
lean_object* v_ks_583_; lean_object* v_vs_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_617_; 
v_ks_583_ = lean_ctor_get(v_x_504_, 0);
v_vs_584_ = lean_ctor_get(v_x_504_, 1);
v_isSharedCheck_617_ = !lean_is_exclusive(v_x_504_);
if (v_isSharedCheck_617_ == 0)
{
v___x_586_ = v_x_504_;
v_isShared_587_ = v_isSharedCheck_617_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_vs_584_);
lean_inc(v_ks_583_);
lean_dec(v_x_504_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_617_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; 
v___x_588_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(v_ks_583_, v_x_507_);
if (lean_obj_tag(v___x_588_) == 0)
{
lean_object* v___x_590_; 
if (v_isShared_587_ == 0)
{
v___x_590_ = v___x_586_;
goto v_reusejp_589_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_ks_583_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_vs_584_);
v___x_590_ = v_reuseFailAlloc_595_;
goto v_reusejp_589_;
}
v_reusejp_589_:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = lean_box(0);
v___x_592_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_502_, v_v_503_, v___x_591_);
if (lean_obj_tag(v___x_592_) == 0)
{
lean_dec(v_x_507_);
return v___x_590_;
}
else
{
lean_object* v_val_593_; lean_object* v___x_594_; 
v_val_593_ = lean_ctor_get(v___x_592_, 0);
lean_inc(v_val_593_);
lean_dec_ref_known(v___x_592_, 1);
v___x_594_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v___x_590_, v_x_505_, v_x_506_, v_x_507_, v_val_593_);
return v___x_594_;
}
}
}
else
{
lean_object* v_val_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_616_; 
v_val_596_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_616_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_616_ == 0)
{
v___x_598_ = v___x_588_;
v_isShared_599_ = v_isSharedCheck_616_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_val_596_);
lean_dec(v___x_588_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_616_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_v_x27_600_; lean_object* v_keys_601_; lean_object* v_vals_602_; lean_object* v___x_604_; 
v_v_x27_600_ = lean_array_fget(v_vs_584_, v_val_596_);
lean_inc(v_val_596_);
v_keys_601_ = l_Array_eraseIdx___redArg(v_ks_583_, v_val_596_);
v_vals_602_ = l_Array_eraseIdx___redArg(v_vs_584_, v_val_596_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 0, v_v_x27_600_);
v___x_604_ = v___x_598_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_615_; 
v_reuseFailAlloc_615_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_615_, 0, v_v_x27_600_);
v___x_604_ = v_reuseFailAlloc_615_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_605_; 
v___x_605_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_502_, v_v_503_, v___x_604_);
if (lean_obj_tag(v___x_605_) == 0)
{
lean_object* v___x_607_; 
lean_dec(v_x_507_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_vals_602_);
lean_ctor_set(v___x_586_, 0, v_keys_601_);
v___x_607_ = v___x_586_;
goto v_reusejp_606_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_keys_601_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_vals_602_);
v___x_607_ = v_reuseFailAlloc_608_;
goto v_reusejp_606_;
}
v_reusejp_606_:
{
return v___x_607_;
}
}
else
{
lean_object* v_val_609_; lean_object* v_keys_610_; lean_object* v_vals_611_; lean_object* v___x_613_; 
v_val_609_ = lean_ctor_get(v___x_605_, 0);
lean_inc(v_val_609_);
lean_dec_ref_known(v___x_605_, 1);
v_keys_610_ = lean_array_push(v_keys_601_, v_x_507_);
v_vals_611_ = lean_array_push(v_vals_602_, v_val_609_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_vals_611_);
lean_ctor_set(v___x_586_, 0, v_keys_610_);
v___x_613_ = v___x_586_;
goto v_reusejp_612_;
}
else
{
lean_object* v_reuseFailAlloc_614_; 
v_reuseFailAlloc_614_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_614_, 0, v_keys_610_);
lean_ctor_set(v_reuseFailAlloc_614_, 1, v_vals_611_);
v___x_613_ = v_reuseFailAlloc_614_;
goto v_reusejp_612_;
}
v_reusejp_612_:
{
return v___x_613_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___boxed(lean_object* v_keys_618_, lean_object* v_v_619_, lean_object* v_x_620_, lean_object* v_x_621_, lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
size_t v_x_2546__boxed_624_; size_t v_x_2547__boxed_625_; lean_object* v_res_626_; 
v_x_2546__boxed_624_ = lean_unbox_usize(v_x_621_);
lean_dec(v_x_621_);
v_x_2547__boxed_625_ = lean_unbox_usize(v_x_622_);
lean_dec(v_x_622_);
v_res_626_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_618_, v_v_619_, v_x_620_, v_x_2546__boxed_624_, v_x_2547__boxed_625_, v_x_623_);
lean_dec_ref(v_keys_618_);
return v_res_626_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; 
v___x_630_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2));
v___x_631_ = lean_unsigned_to_nat(23u);
v___x_632_ = lean_unsigned_to_nat(166u);
v___x_633_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1));
v___x_634_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0));
v___x_635_ = l_mkPanicMessageWithDecl(v___x_634_, v___x_633_, v___x_632_, v___x_631_, v___x_630_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(lean_object* v_d_636_, lean_object* v_keys_637_, lean_object* v_v_638_){
_start:
{
lean_object* v___x_639_; lean_object* v___x_640_; uint8_t v___x_641_; 
v___x_639_ = lean_array_get_size(v_keys_637_);
v___x_640_ = lean_unsigned_to_nat(0u);
v___x_641_ = lean_nat_dec_eq(v___x_639_, v___x_640_);
if (v___x_641_ == 0)
{
lean_object* v___x_642_; lean_object* v_k_643_; uint64_t v___x_644_; size_t v_h_645_; size_t v___x_646_; lean_object* v___x_647_; 
v___x_642_ = lean_box(0);
v_k_643_ = lean_array_get_borrowed(v___x_642_, v_keys_637_, v___x_640_);
v___x_644_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_643_);
v_h_645_ = lean_uint64_to_usize(v___x_644_);
v___x_646_ = ((size_t)1ULL);
lean_inc(v_k_643_);
v___x_647_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_637_, v_v_638_, v_d_636_, v_h_645_, v___x_646_, v_k_643_);
return v___x_647_;
}
else
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec_ref(v_v_638_);
lean_dec_ref(v_d_636_);
v___x_648_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3);
v___x_649_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v___x_648_);
return v___x_649_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___boxed(lean_object* v_d_650_, lean_object* v_keys_651_, lean_object* v_v_652_){
_start:
{
lean_object* v_res_653_; 
v_res_653_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_d_650_, v_keys_651_, v_v_652_);
lean_dec_ref(v_keys_651_);
return v_res_653_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16___redArg(lean_object* v_x_654_, lean_object* v_x_655_, lean_object* v_x_656_, lean_object* v_x_657_){
_start:
{
lean_object* v_ks_658_; lean_object* v_vs_659_; lean_object* v___x_661_; uint8_t v_isShared_662_; uint8_t v_isSharedCheck_683_; 
v_ks_658_ = lean_ctor_get(v_x_654_, 0);
v_vs_659_ = lean_ctor_get(v_x_654_, 1);
v_isSharedCheck_683_ = !lean_is_exclusive(v_x_654_);
if (v_isSharedCheck_683_ == 0)
{
v___x_661_ = v_x_654_;
v_isShared_662_ = v_isSharedCheck_683_;
goto v_resetjp_660_;
}
else
{
lean_inc(v_vs_659_);
lean_inc(v_ks_658_);
lean_dec(v_x_654_);
v___x_661_ = lean_box(0);
v_isShared_662_ = v_isSharedCheck_683_;
goto v_resetjp_660_;
}
v_resetjp_660_:
{
lean_object* v___x_663_; uint8_t v___x_664_; 
v___x_663_ = lean_array_get_size(v_ks_658_);
v___x_664_ = lean_nat_dec_lt(v_x_655_, v___x_663_);
if (v___x_664_ == 0)
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_668_; 
lean_dec(v_x_655_);
v___x_665_ = lean_array_push(v_ks_658_, v_x_656_);
v___x_666_ = lean_array_push(v_vs_659_, v_x_657_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_666_);
lean_ctor_set(v___x_661_, 0, v___x_665_);
v___x_668_ = v___x_661_;
goto v_reusejp_667_;
}
else
{
lean_object* v_reuseFailAlloc_669_; 
v_reuseFailAlloc_669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_669_, 0, v___x_665_);
lean_ctor_set(v_reuseFailAlloc_669_, 1, v___x_666_);
v___x_668_ = v_reuseFailAlloc_669_;
goto v_reusejp_667_;
}
v_reusejp_667_:
{
return v___x_668_;
}
}
else
{
lean_object* v_k_x27_670_; uint8_t v___x_671_; 
v_k_x27_670_ = lean_array_fget_borrowed(v_ks_658_, v_x_655_);
v___x_671_ = lean_name_eq(v_x_656_, v_k_x27_670_);
if (v___x_671_ == 0)
{
lean_object* v___x_673_; 
if (v_isShared_662_ == 0)
{
v___x_673_ = v___x_661_;
goto v_reusejp_672_;
}
else
{
lean_object* v_reuseFailAlloc_677_; 
v_reuseFailAlloc_677_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_677_, 0, v_ks_658_);
lean_ctor_set(v_reuseFailAlloc_677_, 1, v_vs_659_);
v___x_673_ = v_reuseFailAlloc_677_;
goto v_reusejp_672_;
}
v_reusejp_672_:
{
lean_object* v___x_674_; lean_object* v___x_675_; 
v___x_674_ = lean_unsigned_to_nat(1u);
v___x_675_ = lean_nat_add(v_x_655_, v___x_674_);
lean_dec(v_x_655_);
v_x_654_ = v___x_673_;
v_x_655_ = v___x_675_;
goto _start;
}
}
else
{
lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_678_ = lean_array_fset(v_ks_658_, v_x_655_, v_x_656_);
v___x_679_ = lean_array_fset(v_vs_659_, v_x_655_, v_x_657_);
lean_dec(v_x_655_);
if (v_isShared_662_ == 0)
{
lean_ctor_set(v___x_661_, 1, v___x_679_);
lean_ctor_set(v___x_661_, 0, v___x_678_);
v___x_681_ = v___x_661_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_678_);
lean_ctor_set(v_reuseFailAlloc_682_, 1, v___x_679_);
v___x_681_ = v_reuseFailAlloc_682_;
goto v_reusejp_680_;
}
v_reusejp_680_:
{
return v___x_681_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9___redArg(lean_object* v_n_684_, lean_object* v_k_685_, lean_object* v_v_686_){
_start:
{
lean_object* v___x_687_; lean_object* v___x_688_; 
v___x_687_ = lean_unsigned_to_nat(0u);
v___x_688_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16___redArg(v_n_684_, v___x_687_, v_k_685_, v_v_686_);
return v___x_688_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(lean_object* v_x_690_, size_t v_x_691_, size_t v_x_692_, lean_object* v_x_693_, lean_object* v_x_694_){
_start:
{
if (lean_obj_tag(v_x_690_) == 0)
{
lean_object* v_es_695_; size_t v___x_696_; size_t v___x_697_; lean_object* v_j_698_; lean_object* v___x_699_; uint8_t v___x_700_; 
v_es_695_ = lean_ctor_get(v_x_690_, 0);
v___x_696_ = ((size_t)31ULL);
v___x_697_ = lean_usize_land(v_x_691_, v___x_696_);
v_j_698_ = lean_usize_to_nat(v___x_697_);
v___x_699_ = lean_array_get_size(v_es_695_);
v___x_700_ = lean_nat_dec_lt(v_j_698_, v___x_699_);
if (v___x_700_ == 0)
{
lean_dec(v_j_698_);
lean_dec(v_x_694_);
lean_dec(v_x_693_);
return v_x_690_;
}
else
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_739_; 
lean_inc_ref(v_es_695_);
v_isSharedCheck_739_ = !lean_is_exclusive(v_x_690_);
if (v_isSharedCheck_739_ == 0)
{
lean_object* v_unused_740_; 
v_unused_740_ = lean_ctor_get(v_x_690_, 0);
lean_dec(v_unused_740_);
v___x_702_ = v_x_690_;
v_isShared_703_ = v_isSharedCheck_739_;
goto v_resetjp_701_;
}
else
{
lean_dec(v_x_690_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_739_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v_v_704_; lean_object* v___x_705_; lean_object* v_xs_x27_706_; lean_object* v___y_708_; 
v_v_704_ = lean_array_fget(v_es_695_, v_j_698_);
v___x_705_ = lean_box(0);
v_xs_x27_706_ = lean_array_fset(v_es_695_, v_j_698_, v___x_705_);
switch(lean_obj_tag(v_v_704_))
{
case 0:
{
lean_object* v_key_713_; lean_object* v_val_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_724_; 
v_key_713_ = lean_ctor_get(v_v_704_, 0);
v_val_714_ = lean_ctor_get(v_v_704_, 1);
v_isSharedCheck_724_ = !lean_is_exclusive(v_v_704_);
if (v_isSharedCheck_724_ == 0)
{
v___x_716_ = v_v_704_;
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_val_714_);
lean_inc(v_key_713_);
lean_dec(v_v_704_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_724_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
uint8_t v___x_718_; 
v___x_718_ = lean_name_eq(v_x_693_, v_key_713_);
if (v___x_718_ == 0)
{
lean_object* v___x_719_; lean_object* v___x_720_; 
lean_del_object(v___x_716_);
v___x_719_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_713_, v_val_714_, v_x_693_, v_x_694_);
v___x_720_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_720_, 0, v___x_719_);
v___y_708_ = v___x_720_;
goto v___jp_707_;
}
else
{
lean_object* v___x_722_; 
lean_dec(v_val_714_);
lean_dec(v_key_713_);
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 1, v_x_694_);
lean_ctor_set(v___x_716_, 0, v_x_693_);
v___x_722_ = v___x_716_;
goto v_reusejp_721_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v_x_693_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_x_694_);
v___x_722_ = v_reuseFailAlloc_723_;
goto v_reusejp_721_;
}
v_reusejp_721_:
{
v___y_708_ = v___x_722_;
goto v___jp_707_;
}
}
}
}
case 1:
{
lean_object* v_node_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_737_; 
v_node_725_ = lean_ctor_get(v_v_704_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v_v_704_);
if (v_isSharedCheck_737_ == 0)
{
v___x_727_ = v_v_704_;
v_isShared_728_ = v_isSharedCheck_737_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_node_725_);
lean_dec(v_v_704_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_737_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
size_t v___x_729_; size_t v___x_730_; size_t v___x_731_; size_t v___x_732_; lean_object* v___x_733_; lean_object* v___x_735_; 
v___x_729_ = ((size_t)5ULL);
v___x_730_ = lean_usize_shift_right(v_x_691_, v___x_729_);
v___x_731_ = ((size_t)1ULL);
v___x_732_ = lean_usize_add(v_x_692_, v___x_731_);
v___x_733_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_node_725_, v___x_730_, v___x_732_, v_x_693_, v_x_694_);
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 0, v___x_733_);
v___x_735_ = v___x_727_;
goto v_reusejp_734_;
}
else
{
lean_object* v_reuseFailAlloc_736_; 
v_reuseFailAlloc_736_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_736_, 0, v___x_733_);
v___x_735_ = v_reuseFailAlloc_736_;
goto v_reusejp_734_;
}
v_reusejp_734_:
{
v___y_708_ = v___x_735_;
goto v___jp_707_;
}
}
}
default: 
{
lean_object* v___x_738_; 
v___x_738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_738_, 0, v_x_693_);
lean_ctor_set(v___x_738_, 1, v_x_694_);
v___y_708_ = v___x_738_;
goto v___jp_707_;
}
}
v___jp_707_:
{
lean_object* v___x_709_; lean_object* v___x_711_; 
v___x_709_ = lean_array_fset(v_xs_x27_706_, v_j_698_, v___y_708_);
lean_dec(v_j_698_);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 0, v___x_709_);
v___x_711_ = v___x_702_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v___x_709_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
}
}
else
{
lean_object* v_ks_741_; lean_object* v_vs_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_762_; 
v_ks_741_ = lean_ctor_get(v_x_690_, 0);
v_vs_742_ = lean_ctor_get(v_x_690_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v_x_690_);
if (v_isSharedCheck_762_ == 0)
{
v___x_744_ = v_x_690_;
v_isShared_745_ = v_isSharedCheck_762_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_vs_742_);
lean_inc(v_ks_741_);
lean_dec(v_x_690_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_762_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_747_; 
if (v_isShared_745_ == 0)
{
v___x_747_ = v___x_744_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_ks_741_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_vs_742_);
v___x_747_ = v_reuseFailAlloc_761_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v_newNode_748_; uint8_t v___y_750_; size_t v___x_756_; uint8_t v___x_757_; 
v_newNode_748_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9___redArg(v___x_747_, v_x_693_, v_x_694_);
v___x_756_ = ((size_t)7ULL);
v___x_757_ = lean_usize_dec_le(v___x_756_, v_x_692_);
if (v___x_757_ == 0)
{
lean_object* v___x_758_; lean_object* v___x_759_; uint8_t v___x_760_; 
v___x_758_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_748_);
v___x_759_ = lean_unsigned_to_nat(4u);
v___x_760_ = lean_nat_dec_lt(v___x_758_, v___x_759_);
lean_dec(v___x_758_);
v___y_750_ = v___x_760_;
goto v___jp_749_;
}
else
{
v___y_750_ = v___x_757_;
goto v___jp_749_;
}
v___jp_749_:
{
if (v___y_750_ == 0)
{
lean_object* v_ks_751_; lean_object* v_vs_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; 
v_ks_751_ = lean_ctor_get(v_newNode_748_, 0);
lean_inc_ref(v_ks_751_);
v_vs_752_ = lean_ctor_get(v_newNode_748_, 1);
lean_inc_ref(v_vs_752_);
lean_dec_ref(v_newNode_748_);
v___x_753_ = lean_unsigned_to_nat(0u);
v___x_754_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0);
v___x_755_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_x_692_, v_ks_751_, v_vs_752_, v___x_753_, v___x_754_);
lean_dec_ref(v_vs_752_);
lean_dec_ref(v_ks_751_);
return v___x_755_;
}
else
{
return v_newNode_748_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(size_t v_depth_763_, lean_object* v_keys_764_, lean_object* v_vals_765_, lean_object* v_i_766_, lean_object* v_entries_767_){
_start:
{
lean_object* v___x_768_; uint8_t v___x_769_; 
v___x_768_ = lean_array_get_size(v_keys_764_);
v___x_769_ = lean_nat_dec_lt(v_i_766_, v___x_768_);
if (v___x_769_ == 0)
{
lean_dec(v_i_766_);
return v_entries_767_;
}
else
{
lean_object* v_k_770_; lean_object* v_v_771_; uint64_t v___y_773_; 
v_k_770_ = lean_array_fget_borrowed(v_keys_764_, v_i_766_);
v_v_771_ = lean_array_fget_borrowed(v_vals_765_, v_i_766_);
if (lean_obj_tag(v_k_770_) == 0)
{
uint64_t v___x_784_; 
v___x_784_ = 1723ULL;
v___y_773_ = v___x_784_;
goto v___jp_772_;
}
else
{
uint64_t v_hash_785_; 
v_hash_785_ = lean_ctor_get_uint64(v_k_770_, sizeof(void*)*2);
v___y_773_ = v_hash_785_;
goto v___jp_772_;
}
v___jp_772_:
{
size_t v_h_774_; size_t v___x_775_; lean_object* v___x_776_; size_t v___x_777_; size_t v___x_778_; size_t v___x_779_; size_t v_h_780_; lean_object* v___x_781_; lean_object* v___x_782_; 
v_h_774_ = lean_uint64_to_usize(v___y_773_);
v___x_775_ = ((size_t)5ULL);
v___x_776_ = lean_unsigned_to_nat(1u);
v___x_777_ = ((size_t)1ULL);
v___x_778_ = lean_usize_sub(v_depth_763_, v___x_777_);
v___x_779_ = lean_usize_mul(v___x_775_, v___x_778_);
v_h_780_ = lean_usize_shift_right(v_h_774_, v___x_779_);
v___x_781_ = lean_nat_add(v_i_766_, v___x_776_);
lean_dec(v_i_766_);
lean_inc(v_v_771_);
lean_inc(v_k_770_);
v___x_782_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_entries_767_, v_h_780_, v_depth_763_, v_k_770_, v_v_771_);
v_i_766_ = v___x_781_;
v_entries_767_ = v___x_782_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_depth_786_, lean_object* v_keys_787_, lean_object* v_vals_788_, lean_object* v_i_789_, lean_object* v_entries_790_){
_start:
{
size_t v_depth_boxed_791_; lean_object* v_res_792_; 
v_depth_boxed_791_ = lean_unbox_usize(v_depth_786_);
lean_dec(v_depth_786_);
v_res_792_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_depth_boxed_791_, v_keys_787_, v_vals_788_, v_i_789_, v_entries_790_);
lean_dec_ref(v_vals_788_);
lean_dec_ref(v_keys_787_);
return v_res_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___boxed(lean_object* v_x_793_, lean_object* v_x_794_, lean_object* v_x_795_, lean_object* v_x_796_, lean_object* v_x_797_){
_start:
{
size_t v_x_2883__boxed_798_; size_t v_x_2884__boxed_799_; lean_object* v_res_800_; 
v_x_2883__boxed_798_ = lean_unbox_usize(v_x_794_);
lean_dec(v_x_794_);
v_x_2884__boxed_799_ = lean_unbox_usize(v_x_795_);
lean_dec(v_x_795_);
v_res_800_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_793_, v_x_2883__boxed_798_, v_x_2884__boxed_799_, v_x_796_, v_x_797_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(lean_object* v_x_801_, lean_object* v_x_802_, lean_object* v_x_803_){
_start:
{
uint64_t v___y_805_; 
if (lean_obj_tag(v_x_802_) == 0)
{
uint64_t v___x_809_; 
v___x_809_ = 1723ULL;
v___y_805_ = v___x_809_;
goto v___jp_804_;
}
else
{
uint64_t v_hash_810_; 
v_hash_810_ = lean_ctor_get_uint64(v_x_802_, sizeof(void*)*2);
v___y_805_ = v_hash_810_;
goto v___jp_804_;
}
v___jp_804_:
{
size_t v___x_806_; size_t v___x_807_; lean_object* v___x_808_; 
v___x_806_ = lean_uint64_to_usize(v___y_805_);
v___x_807_ = ((size_t)1ULL);
v___x_808_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_801_, v___x_806_, v___x_807_, v_x_802_, v_x_803_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(lean_object* v_xs_811_, lean_object* v_v_812_, lean_object* v_i_813_){
_start:
{
lean_object* v___x_814_; uint8_t v___x_815_; 
v___x_814_ = lean_array_get_size(v_xs_811_);
v___x_815_ = lean_nat_dec_lt(v_i_813_, v___x_814_);
if (v___x_815_ == 0)
{
lean_object* v___x_816_; 
lean_dec(v_i_813_);
v___x_816_ = lean_box(0);
return v___x_816_;
}
else
{
lean_object* v___x_817_; uint8_t v___x_818_; 
v___x_817_ = lean_array_fget_borrowed(v_xs_811_, v_i_813_);
v___x_818_ = lean_name_eq(v___x_817_, v_v_812_);
if (v___x_818_ == 0)
{
lean_object* v___x_819_; lean_object* v___x_820_; 
v___x_819_ = lean_unsigned_to_nat(1u);
v___x_820_ = lean_nat_add(v_i_813_, v___x_819_);
lean_dec(v_i_813_);
v_i_813_ = v___x_820_;
goto _start;
}
else
{
lean_object* v___x_822_; 
v___x_822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_822_, 0, v_i_813_);
return v___x_822_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20___boxed(lean_object* v_xs_823_, lean_object* v_v_824_, lean_object* v_i_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(v_xs_823_, v_v_824_, v_i_825_);
lean_dec(v_v_824_);
lean_dec_ref(v_xs_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(lean_object* v_xs_827_, lean_object* v_v_828_){
_start:
{
lean_object* v___x_829_; lean_object* v___x_830_; 
v___x_829_ = lean_unsigned_to_nat(0u);
v___x_830_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(v_xs_827_, v_v_828_, v___x_829_);
return v___x_830_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13___boxed(lean_object* v_xs_831_, lean_object* v_v_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(v_xs_831_, v_v_832_);
lean_dec(v_v_832_);
lean_dec_ref(v_xs_831_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(lean_object* v_x_834_, size_t v_x_835_, lean_object* v_x_836_){
_start:
{
if (lean_obj_tag(v_x_834_) == 0)
{
lean_object* v_es_837_; lean_object* v___x_838_; size_t v___x_839_; size_t v___x_840_; lean_object* v_j_841_; lean_object* v_entry_842_; 
v_es_837_ = lean_ctor_get(v_x_834_, 0);
v___x_838_ = lean_box(2);
v___x_839_ = ((size_t)31ULL);
v___x_840_ = lean_usize_land(v_x_835_, v___x_839_);
v_j_841_ = lean_usize_to_nat(v___x_840_);
v_entry_842_ = lean_array_get(v___x_838_, v_es_837_, v_j_841_);
switch(lean_obj_tag(v_entry_842_))
{
case 0:
{
lean_object* v_key_843_; uint8_t v___x_844_; 
v_key_843_ = lean_ctor_get(v_entry_842_, 0);
lean_inc(v_key_843_);
lean_dec_ref_known(v_entry_842_, 2);
v___x_844_ = lean_name_eq(v_x_836_, v_key_843_);
lean_dec(v_key_843_);
if (v___x_844_ == 0)
{
lean_dec(v_j_841_);
return v_x_834_;
}
else
{
lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_852_; 
lean_inc_ref(v_es_837_);
v_isSharedCheck_852_ = !lean_is_exclusive(v_x_834_);
if (v_isSharedCheck_852_ == 0)
{
lean_object* v_unused_853_; 
v_unused_853_ = lean_ctor_get(v_x_834_, 0);
lean_dec(v_unused_853_);
v___x_846_ = v_x_834_;
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
else
{
lean_dec(v_x_834_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_852_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; lean_object* v___x_850_; 
v___x_848_ = lean_array_set(v_es_837_, v_j_841_, v___x_838_);
lean_dec(v_j_841_);
if (v_isShared_847_ == 0)
{
lean_ctor_set(v___x_846_, 0, v___x_848_);
v___x_850_ = v___x_846_;
goto v_reusejp_849_;
}
else
{
lean_object* v_reuseFailAlloc_851_; 
v_reuseFailAlloc_851_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_851_, 0, v___x_848_);
v___x_850_ = v_reuseFailAlloc_851_;
goto v_reusejp_849_;
}
v_reusejp_849_:
{
return v___x_850_;
}
}
}
}
case 1:
{
lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_888_; 
lean_inc_ref(v_es_837_);
v_isSharedCheck_888_ = !lean_is_exclusive(v_x_834_);
if (v_isSharedCheck_888_ == 0)
{
lean_object* v_unused_889_; 
v_unused_889_ = lean_ctor_get(v_x_834_, 0);
lean_dec(v_unused_889_);
v___x_855_ = v_x_834_;
v_isShared_856_ = v_isSharedCheck_888_;
goto v_resetjp_854_;
}
else
{
lean_dec(v_x_834_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_888_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
lean_object* v_node_857_; lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_887_; 
v_node_857_ = lean_ctor_get(v_entry_842_, 0);
v_isSharedCheck_887_ = !lean_is_exclusive(v_entry_842_);
if (v_isSharedCheck_887_ == 0)
{
v___x_859_ = v_entry_842_;
v_isShared_860_ = v_isSharedCheck_887_;
goto v_resetjp_858_;
}
else
{
lean_inc(v_node_857_);
lean_dec(v_entry_842_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_887_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
size_t v___x_861_; lean_object* v_entries_862_; size_t v___x_863_; lean_object* v_newNode_864_; lean_object* v___x_865_; 
v___x_861_ = ((size_t)5ULL);
v_entries_862_ = lean_array_set(v_es_837_, v_j_841_, v___x_838_);
v___x_863_ = lean_usize_shift_right(v_x_835_, v___x_861_);
v_newNode_864_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_node_857_, v___x_863_, v_x_836_);
lean_inc_ref(v_newNode_864_);
v___x_865_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_864_);
if (lean_obj_tag(v___x_865_) == 0)
{
lean_object* v___x_867_; 
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v_newNode_864_);
v___x_867_ = v___x_859_;
goto v_reusejp_866_;
}
else
{
lean_object* v_reuseFailAlloc_872_; 
v_reuseFailAlloc_872_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_872_, 0, v_newNode_864_);
v___x_867_ = v_reuseFailAlloc_872_;
goto v_reusejp_866_;
}
v_reusejp_866_:
{
lean_object* v___x_868_; lean_object* v___x_870_; 
v___x_868_ = lean_array_set(v_entries_862_, v_j_841_, v___x_867_);
lean_dec(v_j_841_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_868_);
v___x_870_ = v___x_855_;
goto v_reusejp_869_;
}
else
{
lean_object* v_reuseFailAlloc_871_; 
v_reuseFailAlloc_871_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_871_, 0, v___x_868_);
v___x_870_ = v_reuseFailAlloc_871_;
goto v_reusejp_869_;
}
v_reusejp_869_:
{
return v___x_870_;
}
}
}
else
{
lean_object* v_val_873_; lean_object* v_fst_874_; lean_object* v_snd_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_886_; 
lean_dec_ref(v_newNode_864_);
lean_del_object(v___x_859_);
v_val_873_ = lean_ctor_get(v___x_865_, 0);
lean_inc(v_val_873_);
lean_dec_ref_known(v___x_865_, 1);
v_fst_874_ = lean_ctor_get(v_val_873_, 0);
v_snd_875_ = lean_ctor_get(v_val_873_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_val_873_);
if (v_isSharedCheck_886_ == 0)
{
v___x_877_ = v_val_873_;
v_isShared_878_ = v_isSharedCheck_886_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_snd_875_);
lean_inc(v_fst_874_);
lean_dec(v_val_873_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_886_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v___x_880_; 
if (v_isShared_878_ == 0)
{
v___x_880_ = v___x_877_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_885_; 
v_reuseFailAlloc_885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_885_, 0, v_fst_874_);
lean_ctor_set(v_reuseFailAlloc_885_, 1, v_snd_875_);
v___x_880_ = v_reuseFailAlloc_885_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_883_; 
v___x_881_ = lean_array_set(v_entries_862_, v_j_841_, v___x_880_);
lean_dec(v_j_841_);
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v___x_881_);
v___x_883_ = v___x_855_;
goto v_reusejp_882_;
}
else
{
lean_object* v_reuseFailAlloc_884_; 
v_reuseFailAlloc_884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_884_, 0, v___x_881_);
v___x_883_ = v_reuseFailAlloc_884_;
goto v_reusejp_882_;
}
v_reusejp_882_:
{
return v___x_883_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_841_);
return v_x_834_;
}
}
}
else
{
lean_object* v_ks_890_; lean_object* v_vs_891_; lean_object* v___x_893_; uint8_t v_isShared_894_; uint8_t v_isSharedCheck_905_; 
v_ks_890_ = lean_ctor_get(v_x_834_, 0);
v_vs_891_ = lean_ctor_get(v_x_834_, 1);
v_isSharedCheck_905_ = !lean_is_exclusive(v_x_834_);
if (v_isSharedCheck_905_ == 0)
{
v___x_893_ = v_x_834_;
v_isShared_894_ = v_isSharedCheck_905_;
goto v_resetjp_892_;
}
else
{
lean_inc(v_vs_891_);
lean_inc(v_ks_890_);
lean_dec(v_x_834_);
v___x_893_ = lean_box(0);
v_isShared_894_ = v_isSharedCheck_905_;
goto v_resetjp_892_;
}
v_resetjp_892_:
{
lean_object* v___x_895_; 
v___x_895_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(v_ks_890_, v_x_836_);
if (lean_obj_tag(v___x_895_) == 0)
{
lean_object* v___x_897_; 
if (v_isShared_894_ == 0)
{
v___x_897_ = v___x_893_;
goto v_reusejp_896_;
}
else
{
lean_object* v_reuseFailAlloc_898_; 
v_reuseFailAlloc_898_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_898_, 0, v_ks_890_);
lean_ctor_set(v_reuseFailAlloc_898_, 1, v_vs_891_);
v___x_897_ = v_reuseFailAlloc_898_;
goto v_reusejp_896_;
}
v_reusejp_896_:
{
return v___x_897_;
}
}
else
{
lean_object* v_val_899_; lean_object* v_keys_x27_900_; lean_object* v_vals_x27_901_; lean_object* v___x_903_; 
v_val_899_ = lean_ctor_get(v___x_895_, 0);
lean_inc_n(v_val_899_, 2);
lean_dec_ref_known(v___x_895_, 1);
v_keys_x27_900_ = l_Array_eraseIdx___redArg(v_ks_890_, v_val_899_);
v_vals_x27_901_ = l_Array_eraseIdx___redArg(v_vs_891_, v_val_899_);
if (v_isShared_894_ == 0)
{
lean_ctor_set(v___x_893_, 1, v_vals_x27_901_);
lean_ctor_set(v___x_893_, 0, v_keys_x27_900_);
v___x_903_ = v___x_893_;
goto v_reusejp_902_;
}
else
{
lean_object* v_reuseFailAlloc_904_; 
v_reuseFailAlloc_904_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_904_, 0, v_keys_x27_900_);
lean_ctor_set(v_reuseFailAlloc_904_, 1, v_vals_x27_901_);
v___x_903_ = v_reuseFailAlloc_904_;
goto v_reusejp_902_;
}
v_reusejp_902_:
{
return v___x_903_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg___boxed(lean_object* v_x_906_, lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
size_t v_x_3081__boxed_909_; lean_object* v_res_910_; 
v_x_3081__boxed_909_ = lean_unbox_usize(v_x_907_);
lean_dec(v_x_907_);
v_res_910_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_906_, v_x_3081__boxed_909_, v_x_908_);
lean_dec(v_x_908_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
uint64_t v___y_914_; 
if (lean_obj_tag(v_x_912_) == 0)
{
uint64_t v___x_917_; 
v___x_917_ = 1723ULL;
v___y_914_ = v___x_917_;
goto v___jp_913_;
}
else
{
uint64_t v_hash_918_; 
v_hash_918_ = lean_ctor_get_uint64(v_x_912_, sizeof(void*)*2);
v___y_914_ = v_hash_918_;
goto v___jp_913_;
}
v___jp_913_:
{
size_t v_h_915_; lean_object* v___x_916_; 
v_h_915_ = lean_uint64_to_usize(v___y_914_);
v___x_916_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_911_, v_h_915_, v_x_912_);
return v___x_916_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg___boxed(lean_object* v_x_919_, lean_object* v_x_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_919_, v_x_920_);
lean_dec(v_x_920_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object* v_d_922_, lean_object* v_e_923_){
_start:
{
lean_object* v_globalName_x3f_924_; 
v_globalName_x3f_924_ = lean_ctor_get(v_e_923_, 3);
if (lean_obj_tag(v_globalName_x3f_924_) == 0)
{
lean_object* v_keys_925_; lean_object* v_discrTree_926_; lean_object* v_instanceNames_927_; lean_object* v_erased_928_; lean_object* v___x_930_; uint8_t v_isShared_931_; uint8_t v_isSharedCheck_936_; 
v_keys_925_ = lean_ctor_get(v_e_923_, 0);
lean_inc_ref(v_keys_925_);
v_discrTree_926_ = lean_ctor_get(v_d_922_, 0);
v_instanceNames_927_ = lean_ctor_get(v_d_922_, 1);
v_erased_928_ = lean_ctor_get(v_d_922_, 2);
v_isSharedCheck_936_ = !lean_is_exclusive(v_d_922_);
if (v_isSharedCheck_936_ == 0)
{
v___x_930_ = v_d_922_;
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
else
{
lean_inc(v_erased_928_);
lean_inc(v_instanceNames_927_);
lean_inc(v_discrTree_926_);
lean_dec(v_d_922_);
v___x_930_ = lean_box(0);
v_isShared_931_ = v_isSharedCheck_936_;
goto v_resetjp_929_;
}
v_resetjp_929_:
{
lean_object* v___x_932_; lean_object* v___x_934_; 
v___x_932_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_926_, v_keys_925_, v_e_923_);
lean_dec_ref(v_keys_925_);
if (v_isShared_931_ == 0)
{
lean_ctor_set(v___x_930_, 0, v___x_932_);
v___x_934_ = v___x_930_;
goto v_reusejp_933_;
}
else
{
lean_object* v_reuseFailAlloc_935_; 
v_reuseFailAlloc_935_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_935_, 0, v___x_932_);
lean_ctor_set(v_reuseFailAlloc_935_, 1, v_instanceNames_927_);
lean_ctor_set(v_reuseFailAlloc_935_, 2, v_erased_928_);
v___x_934_ = v_reuseFailAlloc_935_;
goto v_reusejp_933_;
}
v_reusejp_933_:
{
return v___x_934_;
}
}
}
else
{
lean_object* v_keys_937_; lean_object* v_val_938_; lean_object* v_discrTree_939_; lean_object* v_instanceNames_940_; lean_object* v_erased_941_; lean_object* v___x_943_; uint8_t v_isShared_944_; uint8_t v_isSharedCheck_951_; 
v_keys_937_ = lean_ctor_get(v_e_923_, 0);
v_val_938_ = lean_ctor_get(v_globalName_x3f_924_, 0);
lean_inc(v_val_938_);
v_discrTree_939_ = lean_ctor_get(v_d_922_, 0);
v_instanceNames_940_ = lean_ctor_get(v_d_922_, 1);
v_erased_941_ = lean_ctor_get(v_d_922_, 2);
v_isSharedCheck_951_ = !lean_is_exclusive(v_d_922_);
if (v_isSharedCheck_951_ == 0)
{
v___x_943_ = v_d_922_;
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
else
{
lean_inc(v_erased_941_);
lean_inc(v_instanceNames_940_);
lean_inc(v_discrTree_939_);
lean_dec(v_d_922_);
v___x_943_ = lean_box(0);
v_isShared_944_ = v_isSharedCheck_951_;
goto v_resetjp_942_;
}
v_resetjp_942_:
{
lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_949_; 
lean_inc_ref(v_e_923_);
v___x_945_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_939_, v_keys_937_, v_e_923_);
lean_inc(v_val_938_);
v___x_946_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_instanceNames_940_, v_val_938_, v_e_923_);
v___x_947_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_erased_941_, v_val_938_);
lean_dec(v_val_938_);
if (v_isShared_944_ == 0)
{
lean_ctor_set(v___x_943_, 2, v___x_947_);
lean_ctor_set(v___x_943_, 1, v___x_946_);
lean_ctor_set(v___x_943_, 0, v___x_945_);
v___x_949_ = v___x_943_;
goto v_reusejp_948_;
}
else
{
lean_object* v_reuseFailAlloc_950_; 
v_reuseFailAlloc_950_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_950_, 0, v___x_945_);
lean_ctor_set(v_reuseFailAlloc_950_, 1, v___x_946_);
lean_ctor_set(v_reuseFailAlloc_950_, 2, v___x_947_);
v___x_949_ = v_reuseFailAlloc_950_;
goto v_reusejp_948_;
}
v_reusejp_948_:
{
return v___x_949_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1(lean_object* v_00_u03b2_952_, lean_object* v_x_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_x_953_, v_x_954_, v_x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(lean_object* v_00_u03b2_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_958_, v_x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___boxed(lean_object* v_00_u03b2_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
lean_object* v_res_964_; 
v_res_964_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(v_00_u03b2_961_, v_x_962_, v_x_963_);
lean_dec(v_x_963_);
return v_res_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4(lean_object* v_00_u03b2_965_, lean_object* v_x_966_, size_t v_x_967_, size_t v_x_968_, lean_object* v_x_969_, lean_object* v_x_970_){
_start:
{
lean_object* v___x_971_; 
v___x_971_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_966_, v_x_967_, v_x_968_, v_x_969_, v_x_970_);
return v___x_971_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___boxed(lean_object* v_00_u03b2_972_, lean_object* v_x_973_, lean_object* v_x_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_){
_start:
{
size_t v_x_3285__boxed_978_; size_t v_x_3286__boxed_979_; lean_object* v_res_980_; 
v_x_3285__boxed_978_ = lean_unbox_usize(v_x_974_);
lean_dec(v_x_974_);
v_x_3286__boxed_979_ = lean_unbox_usize(v_x_975_);
lean_dec(v_x_975_);
v_res_980_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4(v_00_u03b2_972_, v_x_973_, v_x_3285__boxed_978_, v_x_3286__boxed_979_, v_x_976_, v_x_977_);
return v_res_980_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6(lean_object* v_00_u03b2_981_, lean_object* v_x_982_, size_t v_x_983_, lean_object* v_x_984_){
_start:
{
lean_object* v___x_985_; 
v___x_985_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_982_, v_x_983_, v_x_984_);
return v___x_985_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___boxed(lean_object* v_00_u03b2_986_, lean_object* v_x_987_, lean_object* v_x_988_, lean_object* v_x_989_){
_start:
{
size_t v_x_3302__boxed_990_; lean_object* v_res_991_; 
v_x_3302__boxed_990_ = lean_unbox_usize(v_x_988_);
lean_dec(v_x_988_);
v_res_991_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6(v_00_u03b2_986_, v_x_987_, v_x_3302__boxed_990_, v_x_989_);
lean_dec(v_x_989_);
return v_res_991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_992_, lean_object* v_x_993_, size_t v_x_994_, size_t v_x_995_, lean_object* v_x_996_, lean_object* v_x_997_){
_start:
{
lean_object* v___x_998_; 
v___x_998_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_x_993_, v_x_994_, v_x_995_, v_x_996_, v_x_997_);
return v___x_998_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_999_, lean_object* v_x_1000_, lean_object* v_x_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_){
_start:
{
size_t v_x_3313__boxed_1005_; size_t v_x_3314__boxed_1006_; lean_object* v_res_1007_; 
v_x_3313__boxed_1005_ = lean_unbox_usize(v_x_1001_);
lean_dec(v_x_1001_);
v_x_3314__boxed_1006_ = lean_unbox_usize(v_x_1002_);
lean_dec(v_x_1002_);
v_res_1007_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(v_00_u03b2_999_, v_x_1000_, v_x_3313__boxed_1005_, v_x_3314__boxed_1006_, v_x_1003_, v_x_1004_);
return v_res_1007_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_1008_, lean_object* v_n_1009_, lean_object* v_k_1010_, lean_object* v_v_1011_){
_start:
{
lean_object* v___x_1012_; 
v___x_1012_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9___redArg(v_n_1009_, v_k_1010_, v_v_1011_);
return v___x_1012_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_1013_, size_t v_depth_1014_, lean_object* v_keys_1015_, lean_object* v_vals_1016_, lean_object* v_heq_1017_, lean_object* v_i_1018_, lean_object* v_entries_1019_){
_start:
{
lean_object* v___x_1020_; 
v___x_1020_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_depth_1014_, v_keys_1015_, v_vals_1016_, v_i_1018_, v_entries_1019_);
return v___x_1020_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___boxed(lean_object* v_00_u03b2_1021_, lean_object* v_depth_1022_, lean_object* v_keys_1023_, lean_object* v_vals_1024_, lean_object* v_heq_1025_, lean_object* v_i_1026_, lean_object* v_entries_1027_){
_start:
{
size_t v_depth_boxed_1028_; lean_object* v_res_1029_; 
v_depth_boxed_1028_ = lean_unbox_usize(v_depth_1022_);
lean_dec(v_depth_1022_);
v_res_1029_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10(v_00_u03b2_1021_, v_depth_boxed_1028_, v_keys_1023_, v_vals_1024_, v_heq_1025_, v_i_1026_, v_entries_1027_);
lean_dec_ref(v_vals_1024_);
lean_dec_ref(v_keys_1023_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7(lean_object* v_x_1030_, lean_object* v_keys_1031_, lean_object* v_v_1032_, lean_object* v_k_1033_, lean_object* v_as_1034_, lean_object* v_k_1035_, lean_object* v_x_1036_, lean_object* v_x_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_){
_start:
{
lean_object* v___x_1040_; 
v___x_1040_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_1030_, v_keys_1031_, v_v_1032_, v_k_1033_, v_as_1034_, v_k_1035_, v_x_1036_, v_x_1037_);
return v___x_1040_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_x_1041_, lean_object* v_keys_1042_, lean_object* v_v_1043_, lean_object* v_k_1044_, lean_object* v_as_1045_, lean_object* v_k_1046_, lean_object* v_x_1047_, lean_object* v_x_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_){
_start:
{
lean_object* v_res_1051_; 
v_res_1051_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7(v_x_1041_, v_keys_1042_, v_v_1043_, v_k_1044_, v_as_1045_, v_k_1046_, v_x_1047_, v_x_1048_, v_x_1049_, v_x_1050_);
lean_dec_ref(v_k_1046_);
lean_dec_ref(v_keys_1042_);
lean_dec(v_x_1041_);
return v_res_1051_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12(lean_object* v_00_u03b2_1052_, lean_object* v_n_1053_, lean_object* v_k_1054_, lean_object* v_v_1055_){
_start:
{
lean_object* v___x_1056_; 
v___x_1056_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(v_n_1053_, v_k_1054_, v_v_1055_);
return v___x_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13(lean_object* v_00_u03b2_1057_, size_t v_depth_1058_, lean_object* v_keys_1059_, lean_object* v_vals_1060_, lean_object* v_heq_1061_, lean_object* v_i_1062_, lean_object* v_entries_1063_){
_start:
{
lean_object* v___x_1064_; 
v___x_1064_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(v_depth_1058_, v_keys_1059_, v_vals_1060_, v_i_1062_, v_entries_1063_);
return v___x_1064_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___boxed(lean_object* v_00_u03b2_1065_, lean_object* v_depth_1066_, lean_object* v_keys_1067_, lean_object* v_vals_1068_, lean_object* v_heq_1069_, lean_object* v_i_1070_, lean_object* v_entries_1071_){
_start:
{
size_t v_depth_boxed_1072_; lean_object* v_res_1073_; 
v_depth_boxed_1072_ = lean_unbox_usize(v_depth_1066_);
lean_dec(v_depth_1066_);
v_res_1073_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13(v_00_u03b2_1065_, v_depth_boxed_1072_, v_keys_1067_, v_vals_1068_, v_heq_1069_, v_i_1070_, v_entries_1071_);
lean_dec_ref(v_vals_1068_);
lean_dec_ref(v_keys_1067_);
return v_res_1073_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16(lean_object* v_00_u03b2_1074_, lean_object* v_x_1075_, lean_object* v_x_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_){
_start:
{
lean_object* v___x_1079_; 
v___x_1079_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16___redArg(v_x_1075_, v_x_1076_, v_x_1077_, v_x_1078_);
return v___x_1079_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_){
_start:
{
lean_object* v___x_1085_; 
v___x_1085_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(v_x_1081_, v_x_1082_, v_x_1083_, v_x_1084_);
return v___x_1085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_eraseCore(lean_object* v_d_1086_, lean_object* v_declName_1087_){
_start:
{
lean_object* v_discrTree_1088_; lean_object* v_instanceNames_1089_; lean_object* v_erased_1090_; lean_object* v___x_1092_; uint8_t v_isShared_1093_; uint8_t v_isSharedCheck_1100_; 
v_discrTree_1088_ = lean_ctor_get(v_d_1086_, 0);
v_instanceNames_1089_ = lean_ctor_get(v_d_1086_, 1);
v_erased_1090_ = lean_ctor_get(v_d_1086_, 2);
v_isSharedCheck_1100_ = !lean_is_exclusive(v_d_1086_);
if (v_isSharedCheck_1100_ == 0)
{
v___x_1092_ = v_d_1086_;
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
else
{
lean_inc(v_erased_1090_);
lean_inc(v_instanceNames_1089_);
lean_inc(v_discrTree_1088_);
lean_dec(v_d_1086_);
v___x_1092_ = lean_box(0);
v_isShared_1093_ = v_isSharedCheck_1100_;
goto v_resetjp_1091_;
}
v_resetjp_1091_:
{
lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1098_; 
v___x_1094_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_instanceNames_1089_, v_declName_1087_);
v___x_1095_ = lean_box(0);
v___x_1096_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_erased_1090_, v_declName_1087_, v___x_1095_);
if (v_isShared_1093_ == 0)
{
lean_ctor_set(v___x_1092_, 2, v___x_1096_);
lean_ctor_set(v___x_1092_, 1, v___x_1094_);
v___x_1098_ = v___x_1092_;
goto v_reusejp_1097_;
}
else
{
lean_object* v_reuseFailAlloc_1099_; 
v_reuseFailAlloc_1099_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1099_, 0, v_discrTree_1088_);
lean_ctor_set(v_reuseFailAlloc_1099_, 1, v___x_1094_);
lean_ctor_set(v_reuseFailAlloc_1099_, 2, v___x_1096_);
v___x_1098_ = v_reuseFailAlloc_1099_;
goto v_reusejp_1097_;
}
v_reusejp_1097_:
{
return v___x_1098_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__0(lean_object* v_d_1101_, lean_object* v_declName_1102_, lean_object* v_toPure_1103_, lean_object* v_____r_1104_){
_start:
{
lean_object* v___x_1105_; lean_object* v___x_1106_; 
v___x_1105_ = l_Lean_Meta_Instances_eraseCore(v_d_1101_, v_declName_1102_);
v___x_1106_ = lean_apply_2(v_toPure_1103_, lean_box(0), v___x_1105_);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__1(lean_object* v___f_1107_, lean_object* v_____r_1108_){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_apply_1(v___f_1107_, v_____r_1108_);
return v___x_1109_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
v___x_1113_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__2));
v___x_1114_ = l_Lean_stringToMessageData(v___x_1113_);
return v___x_1114_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__5(void){
_start:
{
lean_object* v___x_1116_; lean_object* v___x_1117_; 
v___x_1116_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__4));
v___x_1117_ = l_Lean_stringToMessageData(v___x_1116_);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg(lean_object* v_inst_1118_, lean_object* v_inst_1119_, lean_object* v_d_1120_, lean_object* v_declName_1121_){
_start:
{
lean_object* v_toApplicative_1122_; lean_object* v_toBind_1123_; lean_object* v_toPure_1124_; lean_object* v_instanceNames_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___f_1128_; uint8_t v___x_1129_; 
v_toApplicative_1122_ = lean_ctor_get(v_inst_1118_, 0);
v_toBind_1123_ = lean_ctor_get(v_inst_1118_, 1);
lean_inc(v_toBind_1123_);
v_toPure_1124_ = lean_ctor_get(v_toApplicative_1122_, 1);
v_instanceNames_1125_ = lean_ctor_get(v_d_1120_, 1);
v___x_1126_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__0));
v___x_1127_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__1));
lean_inc(v_toPure_1124_);
lean_inc_n(v_declName_1121_, 2);
lean_inc_ref(v_d_1120_);
v___f_1128_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1128_, 0, v_d_1120_);
lean_closure_set(v___f_1128_, 1, v_declName_1121_);
lean_closure_set(v___f_1128_, 2, v_toPure_1124_);
lean_inc_ref(v_instanceNames_1125_);
v___x_1129_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1126_, v___x_1127_, v_instanceNames_1125_, v_declName_1121_);
if (v___x_1129_ == 0)
{
lean_object* v___f_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; 
lean_dec_ref(v_d_1120_);
v___f_1130_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1130_, 0, v___f_1128_);
v___x_1131_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_1132_ = l_Lean_MessageData_ofConstName(v_declName_1121_, v___x_1129_);
v___x_1133_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1133_, 0, v___x_1131_);
lean_ctor_set(v___x_1133_, 1, v___x_1132_);
v___x_1134_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = l_Lean_throwError___redArg(v_inst_1118_, v_inst_1119_, v___x_1135_);
v___x_1137_ = lean_apply_4(v_toBind_1123_, lean_box(0), lean_box(0), v___x_1136_, v___f_1130_);
return v___x_1137_;
}
else
{
lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_inc(v_toPure_1124_);
lean_dec_ref(v___f_1128_);
lean_dec(v_toBind_1123_);
lean_dec_ref(v_inst_1119_);
lean_dec_ref(v_inst_1118_);
v___x_1138_ = lean_box(0);
v___x_1139_ = l_Lean_Meta_Instances_erase___redArg___lam__0(v_d_1120_, v_declName_1121_, v_toPure_1124_, v___x_1138_);
return v___x_1139_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase(lean_object* v_m_1140_, lean_object* v_inst_1141_, lean_object* v_inst_1142_, lean_object* v_d_1143_, lean_object* v_declName_1144_){
_start:
{
lean_object* v___x_1145_; 
v___x_1145_ = l_Lean_Meta_Instances_erase___redArg(v_inst_1141_, v_inst_1142_, v_d_1143_, v_declName_1144_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(lean_object* v_x_1146_, lean_object* v_e_1147_){
_start:
{
lean_object* v_globalName_x3f_1152_; 
v_globalName_x3f_1152_ = lean_ctor_get(v_e_1147_, 3);
lean_inc(v_globalName_x3f_1152_);
if (lean_obj_tag(v_globalName_x3f_1152_) == 0)
{
goto v___jp_1148_;
}
else
{
lean_object* v_val_1153_; lean_object* v___x_1155_; uint8_t v_isShared_1156_; uint8_t v_isSharedCheck_1162_; 
v_val_1153_ = lean_ctor_get(v_globalName_x3f_1152_, 0);
v_isSharedCheck_1162_ = !lean_is_exclusive(v_globalName_x3f_1152_);
if (v_isSharedCheck_1162_ == 0)
{
v___x_1155_ = v_globalName_x3f_1152_;
v_isShared_1156_ = v_isSharedCheck_1162_;
goto v_resetjp_1154_;
}
else
{
lean_inc(v_val_1153_);
lean_dec(v_globalName_x3f_1152_);
v___x_1155_ = lean_box(0);
v_isShared_1156_ = v_isSharedCheck_1162_;
goto v_resetjp_1154_;
}
v_resetjp_1154_:
{
uint8_t v___x_1157_; 
v___x_1157_ = l_Lean_isPrivateName(v_val_1153_);
lean_dec(v_val_1153_);
if (v___x_1157_ == 0)
{
lean_object* v___x_1159_; 
if (v_isShared_1156_ == 0)
{
lean_ctor_set(v___x_1155_, 0, v_e_1147_);
v___x_1159_ = v___x_1155_;
goto v_reusejp_1158_;
}
else
{
lean_object* v_reuseFailAlloc_1161_; 
v_reuseFailAlloc_1161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1161_, 0, v_e_1147_);
v___x_1159_ = v_reuseFailAlloc_1161_;
goto v_reusejp_1158_;
}
v_reusejp_1158_:
{
lean_object* v___x_1160_; 
lean_inc_ref_n(v___x_1159_, 2);
v___x_1160_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1160_, 0, v___x_1159_);
lean_ctor_set(v___x_1160_, 1, v___x_1159_);
lean_ctor_set(v___x_1160_, 2, v___x_1159_);
return v___x_1160_;
}
}
else
{
lean_del_object(v___x_1155_);
goto v___jp_1148_;
}
}
}
v___jp_1148_:
{
lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; 
v___x_1149_ = lean_box(0);
v___x_1150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1150_, 0, v_e_1147_);
v___x_1151_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1151_, 0, v___x_1149_);
lean_ctor_set(v___x_1151_, 1, v___x_1149_);
lean_ctor_set(v___x_1151_, 2, v___x_1150_);
return v___x_1151_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v_x_1163_, lean_object* v_e_1164_){
_start:
{
lean_object* v_res_1165_; 
v_res_1165_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(v_x_1163_, v_e_1164_);
lean_dec_ref(v_x_1163_);
return v_res_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(lean_object* v___y_1166_){
_start:
{
lean_inc_ref(v___y_1166_);
return v___y_1166_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v___y_1167_){
_start:
{
lean_object* v_res_1168_; 
v_res_1168_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(v___y_1167_);
lean_dec_ref(v___y_1167_);
return v_res_1168_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1177_; lean_object* v___f_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; 
v___f_1177_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___f_1178_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1179_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__4, &l_Lean_Meta_instInhabitedInstances_default___closed__4_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__4);
v___x_1180_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1181_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1182_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1182_, 0, v___x_1181_);
lean_ctor_set(v___x_1182_, 1, v___x_1180_);
lean_ctor_set(v___x_1182_, 2, v___x_1179_);
lean_ctor_set(v___x_1182_, 3, v___f_1178_);
lean_ctor_set(v___x_1182_, 4, v___f_1177_);
return v___x_1182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1184_; lean_object* v___x_1185_; 
v___x_1184_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_);
v___x_1185_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1184_);
return v___x_1185_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v_a_1186_){
_start:
{
lean_object* v_res_1187_; 
v_res_1187_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_();
return v_res_1187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object* v_k_1188_, uint8_t v_allowLevelAssignments_1189_, lean_object* v___y_1190_, lean_object* v___y_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_){
_start:
{
lean_object* v___x_1195_; 
v___x_1195_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1189_, v_k_1188_, v___y_1190_, v___y_1191_, v___y_1192_, v___y_1193_);
if (lean_obj_tag(v___x_1195_) == 0)
{
lean_object* v_a_1196_; lean_object* v___x_1198_; uint8_t v_isShared_1199_; uint8_t v_isSharedCheck_1203_; 
v_a_1196_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1203_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1198_ = v___x_1195_;
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
else
{
lean_inc(v_a_1196_);
lean_dec(v___x_1195_);
v___x_1198_ = lean_box(0);
v_isShared_1199_ = v_isSharedCheck_1203_;
goto v_resetjp_1197_;
}
v_resetjp_1197_:
{
lean_object* v___x_1201_; 
if (v_isShared_1199_ == 0)
{
v___x_1201_ = v___x_1198_;
goto v_reusejp_1200_;
}
else
{
lean_object* v_reuseFailAlloc_1202_; 
v_reuseFailAlloc_1202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1202_, 0, v_a_1196_);
v___x_1201_ = v_reuseFailAlloc_1202_;
goto v_reusejp_1200_;
}
v_reusejp_1200_:
{
return v___x_1201_;
}
}
}
else
{
lean_object* v_a_1204_; lean_object* v___x_1206_; uint8_t v_isShared_1207_; uint8_t v_isSharedCheck_1211_; 
v_a_1204_ = lean_ctor_get(v___x_1195_, 0);
v_isSharedCheck_1211_ = !lean_is_exclusive(v___x_1195_);
if (v_isSharedCheck_1211_ == 0)
{
v___x_1206_ = v___x_1195_;
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
else
{
lean_inc(v_a_1204_);
lean_dec(v___x_1195_);
v___x_1206_ = lean_box(0);
v_isShared_1207_ = v_isSharedCheck_1211_;
goto v_resetjp_1205_;
}
v_resetjp_1205_:
{
lean_object* v___x_1209_; 
if (v_isShared_1207_ == 0)
{
v___x_1209_ = v___x_1206_;
goto v_reusejp_1208_;
}
else
{
lean_object* v_reuseFailAlloc_1210_; 
v_reuseFailAlloc_1210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1210_, 0, v_a_1204_);
v___x_1209_ = v_reuseFailAlloc_1210_;
goto v_reusejp_1208_;
}
v_reusejp_1208_:
{
return v___x_1209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object* v_k_1212_, lean_object* v_allowLevelAssignments_1213_, lean_object* v___y_1214_, lean_object* v___y_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1219_; lean_object* v_res_1220_; 
v_allowLevelAssignments_boxed_1219_ = lean_unbox(v_allowLevelAssignments_1213_);
v_res_1220_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1212_, v_allowLevelAssignments_boxed_1219_, v___y_1214_, v___y_1215_, v___y_1216_, v___y_1217_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
lean_dec(v___y_1215_);
lean_dec_ref(v___y_1214_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object* v_00_u03b1_1221_, lean_object* v_k_1222_, uint8_t v_allowLevelAssignments_1223_, lean_object* v___y_1224_, lean_object* v___y_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_){
_start:
{
lean_object* v___x_1229_; 
v___x_1229_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1222_, v_allowLevelAssignments_1223_, v___y_1224_, v___y_1225_, v___y_1226_, v___y_1227_);
return v___x_1229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object* v_00_u03b1_1230_, lean_object* v_k_1231_, lean_object* v_allowLevelAssignments_1232_, lean_object* v___y_1233_, lean_object* v___y_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1238_; lean_object* v_res_1239_; 
v_allowLevelAssignments_boxed_1238_ = lean_unbox(v_allowLevelAssignments_1232_);
v_res_1239_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(v_00_u03b1_1230_, v_k_1231_, v_allowLevelAssignments_boxed_1238_, v___y_1233_, v___y_1234_, v___y_1235_, v___y_1236_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
lean_dec(v___y_1234_);
lean_dec_ref(v___y_1233_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1240_, lean_object* v___x_1241_, uint8_t v___x_1242_, lean_object* v___y_1243_, lean_object* v___y_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_){
_start:
{
lean_object* v___x_1248_; 
v___x_1248_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1240_, v___x_1241_, v___x_1242_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
if (lean_obj_tag(v___x_1248_) == 0)
{
lean_object* v_a_1249_; lean_object* v_snd_1250_; lean_object* v_snd_1251_; uint8_t v___x_1252_; lean_object* v___x_1253_; 
v_a_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc(v_a_1249_);
lean_dec_ref_known(v___x_1248_, 1);
v_snd_1250_ = lean_ctor_get(v_a_1249_, 1);
lean_inc(v_snd_1250_);
lean_dec(v_a_1249_);
v_snd_1251_ = lean_ctor_get(v_snd_1250_, 1);
lean_inc(v_snd_1251_);
lean_dec(v_snd_1250_);
v___x_1252_ = 0;
v___x_1253_ = l_Lean_Meta_DiscrTree_mkPath(v_snd_1251_, v___x_1252_, v___y_1243_, v___y_1244_, v___y_1245_, v___y_1246_);
return v___x_1253_;
}
else
{
lean_object* v_a_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1261_; 
v_a_1254_ = lean_ctor_get(v___x_1248_, 0);
v_isSharedCheck_1261_ = !lean_is_exclusive(v___x_1248_);
if (v_isSharedCheck_1261_ == 0)
{
v___x_1256_ = v___x_1248_;
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_a_1254_);
lean_dec(v___x_1248_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1261_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v___x_1259_; 
if (v_isShared_1257_ == 0)
{
v___x_1259_ = v___x_1256_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1260_; 
v_reuseFailAlloc_1260_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1260_, 0, v_a_1254_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object* v_a_1262_, lean_object* v___x_1263_, lean_object* v___x_1264_, lean_object* v___y_1265_, lean_object* v___y_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_){
_start:
{
uint8_t v___x_497__boxed_1270_; lean_object* v_res_1271_; 
v___x_497__boxed_1270_ = lean_unbox(v___x_1264_);
v_res_1271_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1262_, v___x_1263_, v___x_497__boxed_1270_, v___y_1265_, v___y_1266_, v___y_1267_, v___y_1268_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
lean_dec(v___y_1266_);
lean_dec_ref(v___y_1265_);
return v_res_1271_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object* v_e_1272_, lean_object* v_a_1273_, lean_object* v_a_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_){
_start:
{
lean_object* v___x_1278_; 
lean_inc(v_a_1276_);
lean_inc_ref(v_a_1275_);
lean_inc(v_a_1274_);
lean_inc_ref(v_a_1273_);
v___x_1278_ = lean_infer_type(v_e_1272_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
if (lean_obj_tag(v___x_1278_) == 0)
{
lean_object* v_a_1279_; lean_object* v___x_1280_; uint8_t v___x_1281_; lean_object* v___x_1282_; lean_object* v___f_1283_; uint8_t v___x_1284_; lean_object* v___x_1285_; 
v_a_1279_ = lean_ctor_get(v___x_1278_, 0);
lean_inc(v_a_1279_);
lean_dec_ref_known(v___x_1278_, 1);
v___x_1280_ = lean_box(0);
v___x_1281_ = 0;
v___x_1282_ = lean_box(v___x_1281_);
v___f_1283_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1283_, 0, v_a_1279_);
lean_closure_set(v___f_1283_, 1, v___x_1280_);
lean_closure_set(v___f_1283_, 2, v___x_1282_);
v___x_1284_ = 0;
v___x_1285_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v___f_1283_, v___x_1284_, v_a_1273_, v_a_1274_, v_a_1275_, v_a_1276_);
return v___x_1285_;
}
else
{
lean_object* v_a_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1293_; 
v_a_1286_ = lean_ctor_get(v___x_1278_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1278_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1288_ = v___x_1278_;
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_a_1286_);
lean_dec(v___x_1278_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1293_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1291_; 
if (v_isShared_1289_ == 0)
{
v___x_1291_ = v___x_1288_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v_a_1286_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object* v_e_1294_, lean_object* v_a_1295_, lean_object* v_a_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_){
_start:
{
lean_object* v_res_1300_; 
v_res_1300_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_e_1294_, v_a_1295_, v_a_1296_, v_a_1297_, v_a_1298_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
lean_dec(v_a_1296_);
lean_dec_ref(v_a_1295_);
return v_res_1300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1301_, lean_object* v_b_1302_, lean_object* v_c_1303_, lean_object* v___y_1304_, lean_object* v___y_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_){
_start:
{
lean_object* v___x_1309_; 
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
lean_inc(v___y_1305_);
lean_inc_ref(v___y_1304_);
v___x_1309_ = lean_apply_7(v_k_1301_, v_b_1302_, v_c_1303_, v___y_1304_, v___y_1305_, v___y_1306_, v___y_1307_, lean_box(0));
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1310_, lean_object* v_b_1311_, lean_object* v_c_1312_, lean_object* v___y_1313_, lean_object* v___y_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_){
_start:
{
lean_object* v_res_1318_; 
v_res_1318_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1310_, v_b_1311_, v_c_1312_, v___y_1313_, v___y_1314_, v___y_1315_, v___y_1316_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
lean_dec(v___y_1314_);
lean_dec_ref(v___y_1313_);
return v_res_1318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object* v_type_1319_, lean_object* v_k_1320_, uint8_t v_cleanupAnnotations_1321_, uint8_t v_whnfType_1322_, lean_object* v___y_1323_, lean_object* v___y_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_){
_start:
{
lean_object* v___f_1328_; lean_object* v___x_1329_; 
v___f_1328_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1328_, 0, v_k_1320_);
v___x_1329_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1319_, v___f_1328_, v_cleanupAnnotations_1321_, v_whnfType_1322_, v___y_1323_, v___y_1324_, v___y_1325_, v___y_1326_);
if (lean_obj_tag(v___x_1329_) == 0)
{
lean_object* v_a_1330_; lean_object* v___x_1332_; uint8_t v_isShared_1333_; uint8_t v_isSharedCheck_1337_; 
v_a_1330_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1337_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1337_ == 0)
{
v___x_1332_ = v___x_1329_;
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
else
{
lean_inc(v_a_1330_);
lean_dec(v___x_1329_);
v___x_1332_ = lean_box(0);
v_isShared_1333_ = v_isSharedCheck_1337_;
goto v_resetjp_1331_;
}
v_resetjp_1331_:
{
lean_object* v___x_1335_; 
if (v_isShared_1333_ == 0)
{
v___x_1335_ = v___x_1332_;
goto v_reusejp_1334_;
}
else
{
lean_object* v_reuseFailAlloc_1336_; 
v_reuseFailAlloc_1336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1336_, 0, v_a_1330_);
v___x_1335_ = v_reuseFailAlloc_1336_;
goto v_reusejp_1334_;
}
v_reusejp_1334_:
{
return v___x_1335_;
}
}
}
else
{
lean_object* v_a_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1345_; 
v_a_1338_ = lean_ctor_get(v___x_1329_, 0);
v_isSharedCheck_1345_ = !lean_is_exclusive(v___x_1329_);
if (v_isSharedCheck_1345_ == 0)
{
v___x_1340_ = v___x_1329_;
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_a_1338_);
lean_dec(v___x_1329_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1345_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v___x_1343_; 
if (v_isShared_1341_ == 0)
{
v___x_1343_ = v___x_1340_;
goto v_reusejp_1342_;
}
else
{
lean_object* v_reuseFailAlloc_1344_; 
v_reuseFailAlloc_1344_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1344_, 0, v_a_1338_);
v___x_1343_ = v_reuseFailAlloc_1344_;
goto v_reusejp_1342_;
}
v_reusejp_1342_:
{
return v___x_1343_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object* v_type_1346_, lean_object* v_k_1347_, lean_object* v_cleanupAnnotations_1348_, lean_object* v_whnfType_1349_, lean_object* v___y_1350_, lean_object* v___y_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1355_; uint8_t v_whnfType_boxed_1356_; lean_object* v_res_1357_; 
v_cleanupAnnotations_boxed_1355_ = lean_unbox(v_cleanupAnnotations_1348_);
v_whnfType_boxed_1356_ = lean_unbox(v_whnfType_1349_);
v_res_1357_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1346_, v_k_1347_, v_cleanupAnnotations_boxed_1355_, v_whnfType_boxed_1356_, v___y_1350_, v___y_1351_, v___y_1352_, v___y_1353_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
lean_dec(v___y_1351_);
lean_dec_ref(v___y_1350_);
return v_res_1357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object* v_00_u03b1_1358_, lean_object* v_type_1359_, lean_object* v_k_1360_, uint8_t v_cleanupAnnotations_1361_, uint8_t v_whnfType_1362_, lean_object* v___y_1363_, lean_object* v___y_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1359_, v_k_1360_, v_cleanupAnnotations_1361_, v_whnfType_1362_, v___y_1363_, v___y_1364_, v___y_1365_, v___y_1366_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object* v_00_u03b1_1369_, lean_object* v_type_1370_, lean_object* v_k_1371_, lean_object* v_cleanupAnnotations_1372_, lean_object* v_whnfType_1373_, lean_object* v___y_1374_, lean_object* v___y_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1379_; uint8_t v_whnfType_boxed_1380_; lean_object* v_res_1381_; 
v_cleanupAnnotations_boxed_1379_ = lean_unbox(v_cleanupAnnotations_1372_);
v_whnfType_boxed_1380_ = lean_unbox(v_whnfType_1373_);
v_res_1381_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(v_00_u03b1_1369_, v_type_1370_, v_k_1371_, v_cleanupAnnotations_boxed_1379_, v_whnfType_boxed_1380_, v___y_1374_, v___y_1375_, v___y_1376_, v___y_1377_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
lean_dec(v___y_1375_);
lean_dec_ref(v___y_1374_);
return v_res_1381_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object* v_as_1385_, size_t v_sz_1386_, size_t v_i_1387_, lean_object* v_b_1388_, lean_object* v___y_1389_, lean_object* v___y_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_){
_start:
{
uint8_t v___x_1394_; 
v___x_1394_ = lean_usize_dec_lt(v_i_1387_, v_sz_1386_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; 
v___x_1395_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1395_, 0, v_b_1388_);
return v___x_1395_;
}
else
{
lean_object* v_fst_1396_; lean_object* v_snd_1397_; lean_object* v___x_1399_; uint8_t v_isShared_1400_; uint8_t v_isSharedCheck_1449_; 
v_fst_1396_ = lean_ctor_get(v_b_1388_, 0);
v_snd_1397_ = lean_ctor_get(v_b_1388_, 1);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_b_1388_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1399_ = v_b_1388_;
v_isShared_1400_ = v_isSharedCheck_1449_;
goto v_resetjp_1398_;
}
else
{
lean_inc(v_snd_1397_);
lean_inc(v_fst_1396_);
lean_dec(v_b_1388_);
v___x_1399_ = lean_box(0);
v_isShared_1400_ = v_isSharedCheck_1449_;
goto v_resetjp_1398_;
}
v_resetjp_1398_:
{
lean_object* v_next_1406_; 
v_next_1406_ = lean_ctor_get(v_snd_1397_, 0);
lean_inc(v_next_1406_);
if (lean_obj_tag(v_next_1406_) == 0)
{
goto v___jp_1401_;
}
else
{
lean_object* v_upperBound_1407_; lean_object* v_val_1408_; lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1448_; 
v_upperBound_1407_ = lean_ctor_get(v_snd_1397_, 1);
v_val_1408_ = lean_ctor_get(v_next_1406_, 0);
v_isSharedCheck_1448_ = !lean_is_exclusive(v_next_1406_);
if (v_isSharedCheck_1448_ == 0)
{
v___x_1410_ = v_next_1406_;
v_isShared_1411_ = v_isSharedCheck_1448_;
goto v_resetjp_1409_;
}
else
{
lean_inc(v_val_1408_);
lean_dec(v_next_1406_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1448_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
uint8_t v___x_1412_; 
v___x_1412_ = lean_nat_dec_lt(v_val_1408_, v_upperBound_1407_);
if (v___x_1412_ == 0)
{
lean_del_object(v___x_1410_);
lean_dec(v_val_1408_);
goto v___jp_1401_;
}
else
{
lean_object* v___x_1414_; uint8_t v_isShared_1415_; uint8_t v_isSharedCheck_1445_; 
lean_inc(v_upperBound_1407_);
lean_del_object(v___x_1399_);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_snd_1397_);
if (v_isSharedCheck_1445_ == 0)
{
lean_object* v_unused_1446_; lean_object* v_unused_1447_; 
v_unused_1446_ = lean_ctor_get(v_snd_1397_, 1);
lean_dec(v_unused_1446_);
v_unused_1447_ = lean_ctor_get(v_snd_1397_, 0);
lean_dec(v_unused_1447_);
v___x_1414_ = v_snd_1397_;
v_isShared_1415_ = v_isSharedCheck_1445_;
goto v_resetjp_1413_;
}
else
{
lean_dec(v_snd_1397_);
v___x_1414_ = lean_box(0);
v_isShared_1415_ = v_isSharedCheck_1445_;
goto v_resetjp_1413_;
}
v_resetjp_1413_:
{
lean_object* v_a_1416_; lean_object* v___x_1417_; 
v_a_1416_ = lean_array_uget_borrowed(v_as_1385_, v_i_1387_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v___y_1390_);
lean_inc_ref(v___y_1389_);
lean_inc(v_a_1416_);
v___x_1417_ = lean_infer_type(v_a_1416_, v___y_1389_, v___y_1390_, v___y_1391_, v___y_1392_);
if (lean_obj_tag(v___x_1417_) == 0)
{
lean_object* v_a_1418_; lean_object* v_a_1420_; lean_object* v___x_1424_; lean_object* v___x_1425_; lean_object* v___x_1427_; 
v_a_1418_ = lean_ctor_get(v___x_1417_, 0);
lean_inc(v_a_1418_);
lean_dec_ref_known(v___x_1417_, 1);
v___x_1424_ = lean_unsigned_to_nat(1u);
v___x_1425_ = lean_nat_add(v_val_1408_, v___x_1424_);
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1425_);
v___x_1427_ = v___x_1410_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1436_; 
v_reuseFailAlloc_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1436_, 0, v___x_1425_);
v___x_1427_ = v_reuseFailAlloc_1436_;
goto v_reusejp_1426_;
}
v___jp_1419_:
{
size_t v___x_1421_; size_t v___x_1422_; 
v___x_1421_ = ((size_t)1ULL);
v___x_1422_ = lean_usize_add(v_i_1387_, v___x_1421_);
v_i_1387_ = v___x_1422_;
v_b_1388_ = v_a_1420_;
goto _start;
}
v_reusejp_1426_:
{
lean_object* v___x_1429_; 
if (v_isShared_1415_ == 0)
{
lean_ctor_set(v___x_1414_, 0, v___x_1427_);
v___x_1429_ = v___x_1414_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1435_; 
v_reuseFailAlloc_1435_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1435_, 0, v___x_1427_);
lean_ctor_set(v_reuseFailAlloc_1435_, 1, v_upperBound_1407_);
v___x_1429_ = v_reuseFailAlloc_1435_;
goto v_reusejp_1428_;
}
v_reusejp_1428_:
{
lean_object* v___x_1430_; uint8_t v___x_1431_; 
v___x_1430_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1));
v___x_1431_ = l_Lean_Expr_isAppOf(v_a_1418_, v___x_1430_);
lean_dec(v_a_1418_);
if (v___x_1431_ == 0)
{
lean_object* v___x_1432_; 
lean_dec(v_val_1408_);
v___x_1432_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1432_, 0, v_fst_1396_);
lean_ctor_set(v___x_1432_, 1, v___x_1429_);
v_a_1420_ = v___x_1432_;
goto v___jp_1419_;
}
else
{
lean_object* v___x_1433_; lean_object* v___x_1434_; 
v___x_1433_ = lean_array_push(v_fst_1396_, v_val_1408_);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v___x_1433_);
lean_ctor_set(v___x_1434_, 1, v___x_1429_);
v_a_1420_ = v___x_1434_;
goto v___jp_1419_;
}
}
}
}
else
{
lean_object* v_a_1437_; lean_object* v___x_1439_; uint8_t v_isShared_1440_; uint8_t v_isSharedCheck_1444_; 
lean_del_object(v___x_1414_);
lean_del_object(v___x_1410_);
lean_dec(v_val_1408_);
lean_dec(v_upperBound_1407_);
lean_dec(v_fst_1396_);
v_a_1437_ = lean_ctor_get(v___x_1417_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v___x_1417_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1439_ = v___x_1417_;
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
else
{
lean_inc(v_a_1437_);
lean_dec(v___x_1417_);
v___x_1439_ = lean_box(0);
v_isShared_1440_ = v_isSharedCheck_1444_;
goto v_resetjp_1438_;
}
v_resetjp_1438_:
{
lean_object* v___x_1442_; 
if (v_isShared_1440_ == 0)
{
v___x_1442_ = v___x_1439_;
goto v_reusejp_1441_;
}
else
{
lean_object* v_reuseFailAlloc_1443_; 
v_reuseFailAlloc_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1443_, 0, v_a_1437_);
v___x_1442_ = v_reuseFailAlloc_1443_;
goto v_reusejp_1441_;
}
v_reusejp_1441_:
{
return v___x_1442_;
}
}
}
}
}
}
}
v___jp_1401_:
{
lean_object* v___x_1403_; 
if (v_isShared_1400_ == 0)
{
v___x_1403_ = v___x_1399_;
goto v_reusejp_1402_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_fst_1396_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_snd_1397_);
v___x_1403_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1402_;
}
v_reusejp_1402_:
{
lean_object* v___x_1404_; 
v___x_1404_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1404_, 0, v___x_1403_);
return v___x_1404_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object* v_as_1450_, lean_object* v_sz_1451_, lean_object* v_i_1452_, lean_object* v_b_1453_, lean_object* v___y_1454_, lean_object* v___y_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_){
_start:
{
size_t v_sz_boxed_1459_; size_t v_i_boxed_1460_; lean_object* v_res_1461_; 
v_sz_boxed_1459_ = lean_unbox_usize(v_sz_1451_);
lean_dec(v_sz_1451_);
v_i_boxed_1460_ = lean_unbox_usize(v_i_1452_);
lean_dec(v_i_1452_);
v_res_1461_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_as_1450_, v_sz_boxed_1459_, v_i_boxed_1460_, v_b_1453_, v___y_1454_, v___y_1455_, v___y_1456_, v___y_1457_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec(v___y_1455_);
lean_dec_ref(v___y_1454_);
lean_dec_ref(v_as_1450_);
return v_res_1461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object* v_declName_1466_, lean_object* v_args_1467_, lean_object* v_x_1468_, lean_object* v___y_1469_, lean_object* v___y_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_){
_start:
{
lean_object* v___x_1474_; lean_object* v___y_1476_; lean_object* v_env_1501_; lean_object* v___x_1502_; 
v___x_1474_ = lean_st_ref_get(v___y_1472_);
v_env_1501_ = lean_ctor_get(v___x_1474_, 0);
lean_inc_ref(v_env_1501_);
lean_dec(v___x_1474_);
v___x_1502_ = l_Lean_getOutParamPositions_x3f(v_env_1501_, v_declName_1466_);
if (lean_obj_tag(v___x_1502_) == 0)
{
lean_object* v___x_1503_; 
v___x_1503_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___y_1476_ = v___x_1503_;
goto v___jp_1475_;
}
else
{
lean_object* v_val_1504_; 
v_val_1504_ = lean_ctor_get(v___x_1502_, 0);
lean_inc(v_val_1504_);
lean_dec_ref_known(v___x_1502_, 1);
v___y_1476_ = v_val_1504_;
goto v___jp_1475_;
}
v___jp_1475_:
{
lean_object* v___x_1477_; lean_object* v___x_1478_; lean_object* v___x_1479_; lean_object* v___x_1480_; size_t v_sz_1481_; size_t v___x_1482_; lean_object* v___x_1483_; 
v___x_1477_ = lean_array_get_size(v_args_1467_);
v___x_1478_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_1479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1479_, 0, v___x_1478_);
lean_ctor_set(v___x_1479_, 1, v___x_1477_);
v___x_1480_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1480_, 0, v___y_1476_);
lean_ctor_set(v___x_1480_, 1, v___x_1479_);
v_sz_1481_ = lean_array_size(v_args_1467_);
v___x_1482_ = ((size_t)0ULL);
v___x_1483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_args_1467_, v_sz_1481_, v___x_1482_, v___x_1480_, v___y_1469_, v___y_1470_, v___y_1471_, v___y_1472_);
if (lean_obj_tag(v___x_1483_) == 0)
{
lean_object* v_a_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1492_; 
v_a_1484_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1492_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1492_ == 0)
{
v___x_1486_ = v___x_1483_;
v_isShared_1487_ = v_isSharedCheck_1492_;
goto v_resetjp_1485_;
}
else
{
lean_inc(v_a_1484_);
lean_dec(v___x_1483_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1492_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v_fst_1488_; lean_object* v___x_1490_; 
v_fst_1488_ = lean_ctor_get(v_a_1484_, 0);
lean_inc(v_fst_1488_);
lean_dec(v_a_1484_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 0, v_fst_1488_);
v___x_1490_ = v___x_1486_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_fst_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
else
{
lean_object* v_a_1493_; lean_object* v___x_1495_; uint8_t v_isShared_1496_; uint8_t v_isSharedCheck_1500_; 
v_a_1493_ = lean_ctor_get(v___x_1483_, 0);
v_isSharedCheck_1500_ = !lean_is_exclusive(v___x_1483_);
if (v_isSharedCheck_1500_ == 0)
{
v___x_1495_ = v___x_1483_;
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
else
{
lean_inc(v_a_1493_);
lean_dec(v___x_1483_);
v___x_1495_ = lean_box(0);
v_isShared_1496_ = v_isSharedCheck_1500_;
goto v_resetjp_1494_;
}
v_resetjp_1494_:
{
lean_object* v___x_1498_; 
if (v_isShared_1496_ == 0)
{
v___x_1498_ = v___x_1495_;
goto v_reusejp_1497_;
}
else
{
lean_object* v_reuseFailAlloc_1499_; 
v_reuseFailAlloc_1499_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1499_, 0, v_a_1493_);
v___x_1498_ = v_reuseFailAlloc_1499_;
goto v_reusejp_1497_;
}
v_reusejp_1497_:
{
return v___x_1498_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object* v_declName_1505_, lean_object* v_args_1506_, lean_object* v_x_1507_, lean_object* v___y_1508_, lean_object* v___y_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(v_declName_1505_, v_args_1506_, v_x_1507_, v___y_1508_, v___y_1509_, v___y_1510_, v___y_1511_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec(v___y_1509_);
lean_dec_ref(v___y_1508_);
lean_dec_ref(v_x_1507_);
lean_dec_ref(v_args_1506_);
lean_dec(v_declName_1505_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object* v_classTy_1514_, lean_object* v_a_1515_, lean_object* v_a_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_){
_start:
{
lean_object* v___x_1520_; 
v___x_1520_ = l_Lean_Expr_getAppFn(v_classTy_1514_);
if (lean_obj_tag(v___x_1520_) == 4)
{
lean_object* v_declName_1521_; lean_object* v___x_1522_; 
v_declName_1521_ = lean_ctor_get(v___x_1520_, 0);
lean_inc(v_declName_1521_);
lean_inc(v_a_1518_);
lean_inc_ref(v_a_1517_);
lean_inc(v_a_1516_);
lean_inc_ref(v_a_1515_);
v___x_1522_ = lean_infer_type(v___x_1520_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
if (lean_obj_tag(v___x_1522_) == 0)
{
lean_object* v_a_1523_; lean_object* v___f_1524_; uint8_t v___x_1525_; lean_object* v___x_1526_; 
v_a_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_a_1523_);
lean_dec_ref_known(v___x_1522_, 1);
v___f_1524_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1524_, 0, v_declName_1521_);
v___x_1525_ = 0;
v___x_1526_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_1523_, v___f_1524_, v___x_1525_, v___x_1525_, v_a_1515_, v_a_1516_, v_a_1517_, v_a_1518_);
return v___x_1526_;
}
else
{
lean_object* v_a_1527_; lean_object* v___x_1529_; uint8_t v_isShared_1530_; uint8_t v_isSharedCheck_1534_; 
lean_dec(v_declName_1521_);
v_a_1527_ = lean_ctor_get(v___x_1522_, 0);
v_isSharedCheck_1534_ = !lean_is_exclusive(v___x_1522_);
if (v_isSharedCheck_1534_ == 0)
{
v___x_1529_ = v___x_1522_;
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
else
{
lean_inc(v_a_1527_);
lean_dec(v___x_1522_);
v___x_1529_ = lean_box(0);
v_isShared_1530_ = v_isSharedCheck_1534_;
goto v_resetjp_1528_;
}
v_resetjp_1528_:
{
lean_object* v___x_1532_; 
if (v_isShared_1530_ == 0)
{
v___x_1532_ = v___x_1529_;
goto v_reusejp_1531_;
}
else
{
lean_object* v_reuseFailAlloc_1533_; 
v_reuseFailAlloc_1533_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1533_, 0, v_a_1527_);
v___x_1532_ = v_reuseFailAlloc_1533_;
goto v_reusejp_1531_;
}
v_reusejp_1531_:
{
return v___x_1532_;
}
}
}
}
else
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec_ref(v___x_1520_);
v___x_1535_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_1536_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1536_, 0, v___x_1535_);
return v___x_1536_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object* v_classTy_1537_, lean_object* v_a_1538_, lean_object* v_a_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_){
_start:
{
lean_object* v_res_1543_; 
v_res_1543_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_classTy_1537_, v_a_1538_, v_a_1539_, v_a_1540_, v_a_1541_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec(v_a_1539_);
lean_dec_ref(v_a_1538_);
lean_dec_ref(v_classTy_1537_);
return v_res_1543_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_a_1544_, lean_object* v_as_1545_, lean_object* v_j_1546_){
_start:
{
lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1547_ = lean_array_get_size(v_as_1545_);
v___x_1548_ = lean_nat_dec_lt(v_j_1546_, v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; 
lean_dec(v_j_1546_);
v___x_1549_ = lean_box(0);
return v___x_1549_;
}
else
{
lean_object* v___x_1550_; lean_object* v___x_1551_; uint8_t v___x_1552_; 
v___x_1550_ = lean_array_fget_borrowed(v_as_1545_, v_j_1546_);
v___x_1551_ = l_Lean_Expr_mvarId_x21(v___x_1550_);
v___x_1552_ = l_Lean_instBEqMVarId_beq(v___x_1551_, v_a_1544_);
lean_dec(v___x_1551_);
if (v___x_1552_ == 0)
{
lean_object* v___x_1553_; lean_object* v___x_1554_; 
v___x_1553_ = lean_unsigned_to_nat(1u);
v___x_1554_ = lean_nat_add(v_j_1546_, v___x_1553_);
lean_dec(v_j_1546_);
v_j_1546_ = v___x_1554_;
goto _start;
}
else
{
lean_object* v___x_1556_; 
v___x_1556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1556_, 0, v_j_1546_);
return v___x_1556_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_a_1557_, lean_object* v_as_1558_, lean_object* v_j_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1557_, v_as_1558_, v_j_1559_);
lean_dec_ref(v_as_1558_);
lean_dec(v_a_1557_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1561_, lean_object* v_x_1562_, lean_object* v_x_1563_, lean_object* v_x_1564_){
_start:
{
lean_object* v_ks_1565_; lean_object* v_vs_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1590_; 
v_ks_1565_ = lean_ctor_get(v_x_1561_, 0);
v_vs_1566_ = lean_ctor_get(v_x_1561_, 1);
v_isSharedCheck_1590_ = !lean_is_exclusive(v_x_1561_);
if (v_isSharedCheck_1590_ == 0)
{
v___x_1568_ = v_x_1561_;
v_isShared_1569_ = v_isSharedCheck_1590_;
goto v_resetjp_1567_;
}
else
{
lean_inc(v_vs_1566_);
lean_inc(v_ks_1565_);
lean_dec(v_x_1561_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1590_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; uint8_t v___x_1571_; 
v___x_1570_ = lean_array_get_size(v_ks_1565_);
v___x_1571_ = lean_nat_dec_lt(v_x_1562_, v___x_1570_);
if (v___x_1571_ == 0)
{
lean_object* v___x_1572_; lean_object* v___x_1573_; lean_object* v___x_1575_; 
lean_dec(v_x_1562_);
v___x_1572_ = lean_array_push(v_ks_1565_, v_x_1563_);
v___x_1573_ = lean_array_push(v_vs_1566_, v_x_1564_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v___x_1573_);
lean_ctor_set(v___x_1568_, 0, v___x_1572_);
v___x_1575_ = v___x_1568_;
goto v_reusejp_1574_;
}
else
{
lean_object* v_reuseFailAlloc_1576_; 
v_reuseFailAlloc_1576_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1576_, 0, v___x_1572_);
lean_ctor_set(v_reuseFailAlloc_1576_, 1, v___x_1573_);
v___x_1575_ = v_reuseFailAlloc_1576_;
goto v_reusejp_1574_;
}
v_reusejp_1574_:
{
return v___x_1575_;
}
}
else
{
lean_object* v_k_x27_1577_; uint8_t v___x_1578_; 
v_k_x27_1577_ = lean_array_fget_borrowed(v_ks_1565_, v_x_1562_);
v___x_1578_ = l_Lean_instBEqMVarId_beq(v_x_1563_, v_k_x27_1577_);
if (v___x_1578_ == 0)
{
lean_object* v___x_1580_; 
if (v_isShared_1569_ == 0)
{
v___x_1580_ = v___x_1568_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1584_; 
v_reuseFailAlloc_1584_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1584_, 0, v_ks_1565_);
lean_ctor_set(v_reuseFailAlloc_1584_, 1, v_vs_1566_);
v___x_1580_ = v_reuseFailAlloc_1584_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
lean_object* v___x_1581_; lean_object* v___x_1582_; 
v___x_1581_ = lean_unsigned_to_nat(1u);
v___x_1582_ = lean_nat_add(v_x_1562_, v___x_1581_);
lean_dec(v_x_1562_);
v_x_1561_ = v___x_1580_;
v_x_1562_ = v___x_1582_;
goto _start;
}
}
else
{
lean_object* v___x_1585_; lean_object* v___x_1586_; lean_object* v___x_1588_; 
v___x_1585_ = lean_array_fset(v_ks_1565_, v_x_1562_, v_x_1563_);
v___x_1586_ = lean_array_fset(v_vs_1566_, v_x_1562_, v_x_1564_);
lean_dec(v_x_1562_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 1, v___x_1586_);
lean_ctor_set(v___x_1568_, 0, v___x_1585_);
v___x_1588_ = v___x_1568_;
goto v_reusejp_1587_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v___x_1586_);
v___x_1588_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1587_;
}
v_reusejp_1587_:
{
return v___x_1588_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1591_, lean_object* v_k_1592_, lean_object* v_v_1593_){
_start:
{
lean_object* v___x_1594_; lean_object* v___x_1595_; 
v___x_1594_ = lean_unsigned_to_nat(0u);
v___x_1595_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1591_, v___x_1594_, v_k_1592_, v_v_1593_);
return v___x_1595_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1596_, size_t v_x_1597_, size_t v_x_1598_, lean_object* v_x_1599_, lean_object* v_x_1600_){
_start:
{
if (lean_obj_tag(v_x_1596_) == 0)
{
lean_object* v_es_1601_; size_t v___x_1602_; size_t v___x_1603_; lean_object* v_j_1604_; lean_object* v___x_1605_; uint8_t v___x_1606_; 
v_es_1601_ = lean_ctor_get(v_x_1596_, 0);
v___x_1602_ = ((size_t)31ULL);
v___x_1603_ = lean_usize_land(v_x_1597_, v___x_1602_);
v_j_1604_ = lean_usize_to_nat(v___x_1603_);
v___x_1605_ = lean_array_get_size(v_es_1601_);
v___x_1606_ = lean_nat_dec_lt(v_j_1604_, v___x_1605_);
if (v___x_1606_ == 0)
{
lean_dec(v_j_1604_);
lean_dec(v_x_1600_);
lean_dec(v_x_1599_);
return v_x_1596_;
}
else
{
lean_object* v___x_1608_; uint8_t v_isShared_1609_; uint8_t v_isSharedCheck_1645_; 
lean_inc_ref(v_es_1601_);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_x_1596_);
if (v_isSharedCheck_1645_ == 0)
{
lean_object* v_unused_1646_; 
v_unused_1646_ = lean_ctor_get(v_x_1596_, 0);
lean_dec(v_unused_1646_);
v___x_1608_ = v_x_1596_;
v_isShared_1609_ = v_isSharedCheck_1645_;
goto v_resetjp_1607_;
}
else
{
lean_dec(v_x_1596_);
v___x_1608_ = lean_box(0);
v_isShared_1609_ = v_isSharedCheck_1645_;
goto v_resetjp_1607_;
}
v_resetjp_1607_:
{
lean_object* v_v_1610_; lean_object* v___x_1611_; lean_object* v_xs_x27_1612_; lean_object* v___y_1614_; 
v_v_1610_ = lean_array_fget(v_es_1601_, v_j_1604_);
v___x_1611_ = lean_box(0);
v_xs_x27_1612_ = lean_array_fset(v_es_1601_, v_j_1604_, v___x_1611_);
switch(lean_obj_tag(v_v_1610_))
{
case 0:
{
lean_object* v_key_1619_; lean_object* v_val_1620_; lean_object* v___x_1622_; uint8_t v_isShared_1623_; uint8_t v_isSharedCheck_1630_; 
v_key_1619_ = lean_ctor_get(v_v_1610_, 0);
v_val_1620_ = lean_ctor_get(v_v_1610_, 1);
v_isSharedCheck_1630_ = !lean_is_exclusive(v_v_1610_);
if (v_isSharedCheck_1630_ == 0)
{
v___x_1622_ = v_v_1610_;
v_isShared_1623_ = v_isSharedCheck_1630_;
goto v_resetjp_1621_;
}
else
{
lean_inc(v_val_1620_);
lean_inc(v_key_1619_);
lean_dec(v_v_1610_);
v___x_1622_ = lean_box(0);
v_isShared_1623_ = v_isSharedCheck_1630_;
goto v_resetjp_1621_;
}
v_resetjp_1621_:
{
uint8_t v___x_1624_; 
v___x_1624_ = l_Lean_instBEqMVarId_beq(v_x_1599_, v_key_1619_);
if (v___x_1624_ == 0)
{
lean_object* v___x_1625_; lean_object* v___x_1626_; 
lean_del_object(v___x_1622_);
v___x_1625_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1619_, v_val_1620_, v_x_1599_, v_x_1600_);
v___x_1626_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1626_, 0, v___x_1625_);
v___y_1614_ = v___x_1626_;
goto v___jp_1613_;
}
else
{
lean_object* v___x_1628_; 
lean_dec(v_val_1620_);
lean_dec(v_key_1619_);
if (v_isShared_1623_ == 0)
{
lean_ctor_set(v___x_1622_, 1, v_x_1600_);
lean_ctor_set(v___x_1622_, 0, v_x_1599_);
v___x_1628_ = v___x_1622_;
goto v_reusejp_1627_;
}
else
{
lean_object* v_reuseFailAlloc_1629_; 
v_reuseFailAlloc_1629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1629_, 0, v_x_1599_);
lean_ctor_set(v_reuseFailAlloc_1629_, 1, v_x_1600_);
v___x_1628_ = v_reuseFailAlloc_1629_;
goto v_reusejp_1627_;
}
v_reusejp_1627_:
{
v___y_1614_ = v___x_1628_;
goto v___jp_1613_;
}
}
}
}
case 1:
{
lean_object* v_node_1631_; lean_object* v___x_1633_; uint8_t v_isShared_1634_; uint8_t v_isSharedCheck_1643_; 
v_node_1631_ = lean_ctor_get(v_v_1610_, 0);
v_isSharedCheck_1643_ = !lean_is_exclusive(v_v_1610_);
if (v_isSharedCheck_1643_ == 0)
{
v___x_1633_ = v_v_1610_;
v_isShared_1634_ = v_isSharedCheck_1643_;
goto v_resetjp_1632_;
}
else
{
lean_inc(v_node_1631_);
lean_dec(v_v_1610_);
v___x_1633_ = lean_box(0);
v_isShared_1634_ = v_isSharedCheck_1643_;
goto v_resetjp_1632_;
}
v_resetjp_1632_:
{
size_t v___x_1635_; size_t v___x_1636_; size_t v___x_1637_; size_t v___x_1638_; lean_object* v___x_1639_; lean_object* v___x_1641_; 
v___x_1635_ = ((size_t)5ULL);
v___x_1636_ = lean_usize_shift_right(v_x_1597_, v___x_1635_);
v___x_1637_ = ((size_t)1ULL);
v___x_1638_ = lean_usize_add(v_x_1598_, v___x_1637_);
v___x_1639_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_node_1631_, v___x_1636_, v___x_1638_, v_x_1599_, v_x_1600_);
if (v_isShared_1634_ == 0)
{
lean_ctor_set(v___x_1633_, 0, v___x_1639_);
v___x_1641_ = v___x_1633_;
goto v_reusejp_1640_;
}
else
{
lean_object* v_reuseFailAlloc_1642_; 
v_reuseFailAlloc_1642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1642_, 0, v___x_1639_);
v___x_1641_ = v_reuseFailAlloc_1642_;
goto v_reusejp_1640_;
}
v_reusejp_1640_:
{
v___y_1614_ = v___x_1641_;
goto v___jp_1613_;
}
}
}
default: 
{
lean_object* v___x_1644_; 
v___x_1644_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1644_, 0, v_x_1599_);
lean_ctor_set(v___x_1644_, 1, v_x_1600_);
v___y_1614_ = v___x_1644_;
goto v___jp_1613_;
}
}
v___jp_1613_:
{
lean_object* v___x_1615_; lean_object* v___x_1617_; 
v___x_1615_ = lean_array_fset(v_xs_x27_1612_, v_j_1604_, v___y_1614_);
lean_dec(v_j_1604_);
if (v_isShared_1609_ == 0)
{
lean_ctor_set(v___x_1608_, 0, v___x_1615_);
v___x_1617_ = v___x_1608_;
goto v_reusejp_1616_;
}
else
{
lean_object* v_reuseFailAlloc_1618_; 
v_reuseFailAlloc_1618_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1618_, 0, v___x_1615_);
v___x_1617_ = v_reuseFailAlloc_1618_;
goto v_reusejp_1616_;
}
v_reusejp_1616_:
{
return v___x_1617_;
}
}
}
}
}
else
{
lean_object* v_ks_1647_; lean_object* v_vs_1648_; lean_object* v___x_1650_; uint8_t v_isShared_1651_; uint8_t v_isSharedCheck_1668_; 
v_ks_1647_ = lean_ctor_get(v_x_1596_, 0);
v_vs_1648_ = lean_ctor_get(v_x_1596_, 1);
v_isSharedCheck_1668_ = !lean_is_exclusive(v_x_1596_);
if (v_isSharedCheck_1668_ == 0)
{
v___x_1650_ = v_x_1596_;
v_isShared_1651_ = v_isSharedCheck_1668_;
goto v_resetjp_1649_;
}
else
{
lean_inc(v_vs_1648_);
lean_inc(v_ks_1647_);
lean_dec(v_x_1596_);
v___x_1650_ = lean_box(0);
v_isShared_1651_ = v_isSharedCheck_1668_;
goto v_resetjp_1649_;
}
v_resetjp_1649_:
{
lean_object* v___x_1653_; 
if (v_isShared_1651_ == 0)
{
v___x_1653_ = v___x_1650_;
goto v_reusejp_1652_;
}
else
{
lean_object* v_reuseFailAlloc_1667_; 
v_reuseFailAlloc_1667_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1667_, 0, v_ks_1647_);
lean_ctor_set(v_reuseFailAlloc_1667_, 1, v_vs_1648_);
v___x_1653_ = v_reuseFailAlloc_1667_;
goto v_reusejp_1652_;
}
v_reusejp_1652_:
{
lean_object* v_newNode_1654_; uint8_t v___y_1656_; size_t v___x_1662_; uint8_t v___x_1663_; 
v_newNode_1654_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v___x_1653_, v_x_1599_, v_x_1600_);
v___x_1662_ = ((size_t)7ULL);
v___x_1663_ = lean_usize_dec_le(v___x_1662_, v_x_1598_);
if (v___x_1663_ == 0)
{
lean_object* v___x_1664_; lean_object* v___x_1665_; uint8_t v___x_1666_; 
v___x_1664_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1654_);
v___x_1665_ = lean_unsigned_to_nat(4u);
v___x_1666_ = lean_nat_dec_lt(v___x_1664_, v___x_1665_);
lean_dec(v___x_1664_);
v___y_1656_ = v___x_1666_;
goto v___jp_1655_;
}
else
{
v___y_1656_ = v___x_1663_;
goto v___jp_1655_;
}
v___jp_1655_:
{
if (v___y_1656_ == 0)
{
lean_object* v_ks_1657_; lean_object* v_vs_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; 
v_ks_1657_ = lean_ctor_get(v_newNode_1654_, 0);
lean_inc_ref(v_ks_1657_);
v_vs_1658_ = lean_ctor_get(v_newNode_1654_, 1);
lean_inc_ref(v_vs_1658_);
lean_dec_ref(v_newNode_1654_);
v___x_1659_ = lean_unsigned_to_nat(0u);
v___x_1660_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0);
v___x_1661_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_x_1598_, v_ks_1657_, v_vs_1658_, v___x_1659_, v___x_1660_);
lean_dec_ref(v_vs_1658_);
lean_dec_ref(v_ks_1657_);
return v___x_1661_;
}
else
{
return v_newNode_1654_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(size_t v_depth_1669_, lean_object* v_keys_1670_, lean_object* v_vals_1671_, lean_object* v_i_1672_, lean_object* v_entries_1673_){
_start:
{
lean_object* v___x_1674_; uint8_t v___x_1675_; 
v___x_1674_ = lean_array_get_size(v_keys_1670_);
v___x_1675_ = lean_nat_dec_lt(v_i_1672_, v___x_1674_);
if (v___x_1675_ == 0)
{
lean_dec(v_i_1672_);
return v_entries_1673_;
}
else
{
lean_object* v_k_1676_; lean_object* v_v_1677_; uint64_t v___x_1678_; size_t v_h_1679_; size_t v___x_1680_; lean_object* v___x_1681_; size_t v___x_1682_; size_t v___x_1683_; size_t v___x_1684_; size_t v_h_1685_; lean_object* v___x_1686_; lean_object* v___x_1687_; 
v_k_1676_ = lean_array_fget_borrowed(v_keys_1670_, v_i_1672_);
v_v_1677_ = lean_array_fget_borrowed(v_vals_1671_, v_i_1672_);
v___x_1678_ = l_Lean_instHashableMVarId_hash(v_k_1676_);
v_h_1679_ = lean_uint64_to_usize(v___x_1678_);
v___x_1680_ = ((size_t)5ULL);
v___x_1681_ = lean_unsigned_to_nat(1u);
v___x_1682_ = ((size_t)1ULL);
v___x_1683_ = lean_usize_sub(v_depth_1669_, v___x_1682_);
v___x_1684_ = lean_usize_mul(v___x_1680_, v___x_1683_);
v_h_1685_ = lean_usize_shift_right(v_h_1679_, v___x_1684_);
v___x_1686_ = lean_nat_add(v_i_1672_, v___x_1681_);
lean_dec(v_i_1672_);
lean_inc(v_v_1677_);
lean_inc(v_k_1676_);
v___x_1687_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_entries_1673_, v_h_1685_, v_depth_1669_, v_k_1676_, v_v_1677_);
v_i_1672_ = v___x_1686_;
v_entries_1673_ = v___x_1687_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1689_, lean_object* v_keys_1690_, lean_object* v_vals_1691_, lean_object* v_i_1692_, lean_object* v_entries_1693_){
_start:
{
size_t v_depth_boxed_1694_; lean_object* v_res_1695_; 
v_depth_boxed_1694_ = lean_unbox_usize(v_depth_1689_);
lean_dec(v_depth_1689_);
v_res_1695_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1694_, v_keys_1690_, v_vals_1691_, v_i_1692_, v_entries_1693_);
lean_dec_ref(v_vals_1691_);
lean_dec_ref(v_keys_1690_);
return v_res_1695_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1696_, lean_object* v_x_1697_, lean_object* v_x_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_){
_start:
{
size_t v_x_1624__boxed_1701_; size_t v_x_1625__boxed_1702_; lean_object* v_res_1703_; 
v_x_1624__boxed_1701_ = lean_unbox_usize(v_x_1697_);
lean_dec(v_x_1697_);
v_x_1625__boxed_1702_ = lean_unbox_usize(v_x_1698_);
lean_dec(v_x_1698_);
v_res_1703_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1696_, v_x_1624__boxed_1701_, v_x_1625__boxed_1702_, v_x_1699_, v_x_1700_);
return v_res_1703_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(lean_object* v_x_1704_, lean_object* v_x_1705_, lean_object* v_x_1706_){
_start:
{
uint64_t v___x_1707_; size_t v___x_1708_; size_t v___x_1709_; lean_object* v___x_1710_; 
v___x_1707_ = l_Lean_instHashableMVarId_hash(v_x_1705_);
v___x_1708_ = lean_uint64_to_usize(v___x_1707_);
v___x_1709_ = ((size_t)1ULL);
v___x_1710_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1704_, v___x_1708_, v___x_1709_, v_x_1705_, v_x_1706_);
return v___x_1710_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(lean_object* v_mvarId_1711_, lean_object* v_val_1712_, lean_object* v___y_1713_){
_start:
{
lean_object* v___x_1715_; lean_object* v_mctx_1716_; lean_object* v_cache_1717_; lean_object* v_zetaDeltaFVarIds_1718_; lean_object* v_postponed_1719_; lean_object* v_diag_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1749_; 
v___x_1715_ = lean_st_ref_take(v___y_1713_);
v_mctx_1716_ = lean_ctor_get(v___x_1715_, 0);
v_cache_1717_ = lean_ctor_get(v___x_1715_, 1);
v_zetaDeltaFVarIds_1718_ = lean_ctor_get(v___x_1715_, 2);
v_postponed_1719_ = lean_ctor_get(v___x_1715_, 3);
v_diag_1720_ = lean_ctor_get(v___x_1715_, 4);
v_isSharedCheck_1749_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1722_ = v___x_1715_;
v_isShared_1723_ = v_isSharedCheck_1749_;
goto v_resetjp_1721_;
}
else
{
lean_inc(v_diag_1720_);
lean_inc(v_postponed_1719_);
lean_inc(v_zetaDeltaFVarIds_1718_);
lean_inc(v_cache_1717_);
lean_inc(v_mctx_1716_);
lean_dec(v___x_1715_);
v___x_1722_ = lean_box(0);
v_isShared_1723_ = v_isSharedCheck_1749_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v_depth_1724_; lean_object* v_levelAssignDepth_1725_; lean_object* v_lmvarCounter_1726_; lean_object* v_mvarCounter_1727_; lean_object* v_lDecls_1728_; lean_object* v_decls_1729_; lean_object* v_userNames_1730_; lean_object* v_lAssignment_1731_; lean_object* v_eAssignment_1732_; lean_object* v_dAssignment_1733_; lean_object* v_instanceTypedMVars_1734_; lean_object* v___x_1736_; uint8_t v_isShared_1737_; uint8_t v_isSharedCheck_1748_; 
v_depth_1724_ = lean_ctor_get(v_mctx_1716_, 0);
v_levelAssignDepth_1725_ = lean_ctor_get(v_mctx_1716_, 1);
v_lmvarCounter_1726_ = lean_ctor_get(v_mctx_1716_, 2);
v_mvarCounter_1727_ = lean_ctor_get(v_mctx_1716_, 3);
v_lDecls_1728_ = lean_ctor_get(v_mctx_1716_, 4);
v_decls_1729_ = lean_ctor_get(v_mctx_1716_, 5);
v_userNames_1730_ = lean_ctor_get(v_mctx_1716_, 6);
v_lAssignment_1731_ = lean_ctor_get(v_mctx_1716_, 7);
v_eAssignment_1732_ = lean_ctor_get(v_mctx_1716_, 8);
v_dAssignment_1733_ = lean_ctor_get(v_mctx_1716_, 9);
v_instanceTypedMVars_1734_ = lean_ctor_get(v_mctx_1716_, 10);
v_isSharedCheck_1748_ = !lean_is_exclusive(v_mctx_1716_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1736_ = v_mctx_1716_;
v_isShared_1737_ = v_isSharedCheck_1748_;
goto v_resetjp_1735_;
}
else
{
lean_inc(v_instanceTypedMVars_1734_);
lean_inc(v_dAssignment_1733_);
lean_inc(v_eAssignment_1732_);
lean_inc(v_lAssignment_1731_);
lean_inc(v_userNames_1730_);
lean_inc(v_decls_1729_);
lean_inc(v_lDecls_1728_);
lean_inc(v_mvarCounter_1727_);
lean_inc(v_lmvarCounter_1726_);
lean_inc(v_levelAssignDepth_1725_);
lean_inc(v_depth_1724_);
lean_dec(v_mctx_1716_);
v___x_1736_ = lean_box(0);
v_isShared_1737_ = v_isSharedCheck_1748_;
goto v_resetjp_1735_;
}
v_resetjp_1735_:
{
lean_object* v___x_1738_; lean_object* v___x_1740_; 
v___x_1738_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_eAssignment_1732_, v_mvarId_1711_, v_val_1712_);
if (v_isShared_1737_ == 0)
{
lean_ctor_set(v___x_1736_, 8, v___x_1738_);
v___x_1740_ = v___x_1736_;
goto v_reusejp_1739_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v_depth_1724_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_levelAssignDepth_1725_);
lean_ctor_set(v_reuseFailAlloc_1747_, 2, v_lmvarCounter_1726_);
lean_ctor_set(v_reuseFailAlloc_1747_, 3, v_mvarCounter_1727_);
lean_ctor_set(v_reuseFailAlloc_1747_, 4, v_lDecls_1728_);
lean_ctor_set(v_reuseFailAlloc_1747_, 5, v_decls_1729_);
lean_ctor_set(v_reuseFailAlloc_1747_, 6, v_userNames_1730_);
lean_ctor_set(v_reuseFailAlloc_1747_, 7, v_lAssignment_1731_);
lean_ctor_set(v_reuseFailAlloc_1747_, 8, v___x_1738_);
lean_ctor_set(v_reuseFailAlloc_1747_, 9, v_dAssignment_1733_);
lean_ctor_set(v_reuseFailAlloc_1747_, 10, v_instanceTypedMVars_1734_);
v___x_1740_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1739_;
}
v_reusejp_1739_:
{
lean_object* v___x_1742_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1740_);
v___x_1742_ = v___x_1722_;
goto v_reusejp_1741_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v___x_1740_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_cache_1717_);
lean_ctor_set(v_reuseFailAlloc_1746_, 2, v_zetaDeltaFVarIds_1718_);
lean_ctor_set(v_reuseFailAlloc_1746_, 3, v_postponed_1719_);
lean_ctor_set(v_reuseFailAlloc_1746_, 4, v_diag_1720_);
v___x_1742_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1741_;
}
v_reusejp_1741_:
{
lean_object* v___x_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; 
v___x_1743_ = lean_st_ref_put(v___y_1713_, v___x_1742_);
v___x_1744_ = lean_box(0);
v___x_1745_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1745_, 0, v___x_1744_);
return v___x_1745_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg___boxed(lean_object* v_mvarId_1750_, lean_object* v_val_1751_, lean_object* v___y_1752_, lean_object* v___y_1753_){
_start:
{
lean_object* v_res_1754_; 
v_res_1754_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1750_, v_val_1751_, v___y_1752_);
lean_dec(v___y_1752_);
return v_res_1754_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(lean_object* v_argMVars_1755_, lean_object* v_argVars_1756_, lean_object* v_as_1757_, size_t v_sz_1758_, size_t v_i_1759_, lean_object* v_b_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_){
_start:
{
uint8_t v___x_1766_; 
v___x_1766_ = lean_usize_dec_lt(v_i_1759_, v_sz_1758_);
if (v___x_1766_ == 0)
{
lean_object* v___x_1767_; 
v___x_1767_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1767_, 0, v_b_1760_);
return v___x_1767_;
}
else
{
lean_object* v___x_1768_; lean_object* v_a_1769_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___x_1790_; lean_object* v___x_1791_; 
v___x_1768_ = lean_box(0);
v_a_1769_ = lean_array_uget_borrowed(v_as_1757_, v_i_1759_);
v___x_1790_ = lean_unsigned_to_nat(0u);
v___x_1791_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1769_, v_argMVars_1755_, v___x_1790_);
if (lean_obj_tag(v___x_1791_) == 1)
{
lean_object* v_val_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v_val_1792_ = lean_ctor_get(v___x_1791_, 0);
lean_inc(v_val_1792_);
lean_dec_ref_known(v___x_1791_, 1);
v___x_1793_ = l_Lean_instInhabitedExpr;
v___x_1794_ = lean_array_get_borrowed(v___x_1793_, v_argVars_1756_, v_val_1792_);
lean_dec(v_val_1792_);
lean_inc(v___x_1794_);
lean_inc(v_a_1769_);
v___x_1795_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_a_1769_, v___x_1794_, v___y_1762_);
if (lean_obj_tag(v___x_1795_) == 0)
{
lean_dec_ref_known(v___x_1795_, 1);
v___y_1771_ = v___y_1761_;
v___y_1772_ = v___y_1762_;
v___y_1773_ = v___y_1763_;
v___y_1774_ = v___y_1764_;
goto v___jp_1770_;
}
else
{
return v___x_1795_;
}
}
else
{
lean_dec(v___x_1791_);
v___y_1771_ = v___y_1761_;
v___y_1772_ = v___y_1762_;
v___y_1773_ = v___y_1763_;
v___y_1774_ = v___y_1764_;
goto v___jp_1770_;
}
v___jp_1770_:
{
lean_object* v___x_1775_; lean_object* v___x_1776_; 
lean_inc(v_a_1769_);
v___x_1775_ = l_Lean_Expr_mvar___override(v_a_1769_);
lean_inc(v___y_1774_);
lean_inc_ref(v___y_1773_);
lean_inc(v___y_1772_);
lean_inc_ref(v___y_1771_);
v___x_1776_ = lean_infer_type(v___x_1775_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1776_) == 0)
{
lean_object* v_a_1777_; lean_object* v___x_1778_; 
v_a_1777_ = lean_ctor_get(v___x_1776_, 0);
lean_inc(v_a_1777_);
lean_dec_ref_known(v___x_1776_, 1);
v___x_1778_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1755_, v_argVars_1756_, v_a_1777_, v___y_1771_, v___y_1772_, v___y_1773_, v___y_1774_);
if (lean_obj_tag(v___x_1778_) == 0)
{
size_t v___x_1779_; size_t v___x_1780_; 
lean_dec_ref_known(v___x_1778_, 1);
v___x_1779_ = ((size_t)1ULL);
v___x_1780_ = lean_usize_add(v_i_1759_, v___x_1779_);
v_i_1759_ = v___x_1780_;
v_b_1760_ = v___x_1768_;
goto _start;
}
else
{
return v___x_1778_;
}
}
else
{
lean_object* v_a_1782_; lean_object* v___x_1784_; uint8_t v_isShared_1785_; uint8_t v_isSharedCheck_1789_; 
v_a_1782_ = lean_ctor_get(v___x_1776_, 0);
v_isSharedCheck_1789_ = !lean_is_exclusive(v___x_1776_);
if (v_isSharedCheck_1789_ == 0)
{
v___x_1784_ = v___x_1776_;
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
else
{
lean_inc(v_a_1782_);
lean_dec(v___x_1776_);
v___x_1784_ = lean_box(0);
v_isShared_1785_ = v_isSharedCheck_1789_;
goto v_resetjp_1783_;
}
v_resetjp_1783_:
{
lean_object* v___x_1787_; 
if (v_isShared_1785_ == 0)
{
v___x_1787_ = v___x_1784_;
goto v_reusejp_1786_;
}
else
{
lean_object* v_reuseFailAlloc_1788_; 
v_reuseFailAlloc_1788_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1788_, 0, v_a_1782_);
v___x_1787_ = v_reuseFailAlloc_1788_;
goto v_reusejp_1786_;
}
v_reusejp_1786_:
{
return v___x_1787_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1796_, lean_object* v_argVars_1797_, lean_object* v_e_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_){
_start:
{
lean_object* v___x_1804_; 
v___x_1804_ = l_Lean_Meta_getMVars(v_e_1798_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
if (lean_obj_tag(v___x_1804_) == 0)
{
lean_object* v_a_1805_; lean_object* v___x_1806_; size_t v_sz_1807_; size_t v___x_1808_; lean_object* v___x_1809_; 
v_a_1805_ = lean_ctor_get(v___x_1804_, 0);
lean_inc(v_a_1805_);
lean_dec_ref_known(v___x_1804_, 1);
v___x_1806_ = lean_box(0);
v_sz_1807_ = lean_array_size(v_a_1805_);
v___x_1808_ = ((size_t)0ULL);
v___x_1809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1796_, v_argVars_1797_, v_a_1805_, v_sz_1807_, v___x_1808_, v___x_1806_, v_a_1799_, v_a_1800_, v_a_1801_, v_a_1802_);
lean_dec(v_a_1805_);
if (lean_obj_tag(v___x_1809_) == 0)
{
lean_object* v___x_1811_; uint8_t v_isShared_1812_; uint8_t v_isSharedCheck_1816_; 
v_isSharedCheck_1816_ = !lean_is_exclusive(v___x_1809_);
if (v_isSharedCheck_1816_ == 0)
{
lean_object* v_unused_1817_; 
v_unused_1817_ = lean_ctor_get(v___x_1809_, 0);
lean_dec(v_unused_1817_);
v___x_1811_ = v___x_1809_;
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
else
{
lean_dec(v___x_1809_);
v___x_1811_ = lean_box(0);
v_isShared_1812_ = v_isSharedCheck_1816_;
goto v_resetjp_1810_;
}
v_resetjp_1810_:
{
lean_object* v___x_1814_; 
if (v_isShared_1812_ == 0)
{
lean_ctor_set(v___x_1811_, 0, v___x_1806_);
v___x_1814_ = v___x_1811_;
goto v_reusejp_1813_;
}
else
{
lean_object* v_reuseFailAlloc_1815_; 
v_reuseFailAlloc_1815_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1815_, 0, v___x_1806_);
v___x_1814_ = v_reuseFailAlloc_1815_;
goto v_reusejp_1813_;
}
v_reusejp_1813_:
{
return v___x_1814_;
}
}
}
else
{
return v___x_1809_;
}
}
else
{
lean_object* v_a_1818_; lean_object* v___x_1820_; uint8_t v_isShared_1821_; uint8_t v_isSharedCheck_1825_; 
v_a_1818_ = lean_ctor_get(v___x_1804_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1804_);
if (v_isSharedCheck_1825_ == 0)
{
v___x_1820_ = v___x_1804_;
v_isShared_1821_ = v_isSharedCheck_1825_;
goto v_resetjp_1819_;
}
else
{
lean_inc(v_a_1818_);
lean_dec(v___x_1804_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1826_, lean_object* v_argVars_1827_, lean_object* v_e_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_){
_start:
{
lean_object* v_res_1834_; 
v_res_1834_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1826_, v_argVars_1827_, v_e_1828_, v_a_1829_, v_a_1830_, v_a_1831_, v_a_1832_);
lean_dec(v_a_1832_);
lean_dec_ref(v_a_1831_);
lean_dec(v_a_1830_);
lean_dec_ref(v_a_1829_);
lean_dec_ref(v_argVars_1827_);
lean_dec_ref(v_argMVars_1826_);
return v_res_1834_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2___boxed(lean_object* v_argMVars_1835_, lean_object* v_argVars_1836_, lean_object* v_as_1837_, lean_object* v_sz_1838_, lean_object* v_i_1839_, lean_object* v_b_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_){
_start:
{
size_t v_sz_boxed_1846_; size_t v_i_boxed_1847_; lean_object* v_res_1848_; 
v_sz_boxed_1846_ = lean_unbox_usize(v_sz_1838_);
lean_dec(v_sz_1838_);
v_i_boxed_1847_ = lean_unbox_usize(v_i_1839_);
lean_dec(v_i_1839_);
v_res_1848_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1835_, v_argVars_1836_, v_as_1837_, v_sz_boxed_1846_, v_i_boxed_1847_, v_b_1840_, v___y_1841_, v___y_1842_, v___y_1843_, v___y_1844_);
lean_dec(v___y_1844_);
lean_dec_ref(v___y_1843_);
lean_dec(v___y_1842_);
lean_dec_ref(v___y_1841_);
lean_dec_ref(v_as_1837_);
lean_dec_ref(v_argVars_1836_);
lean_dec_ref(v_argMVars_1835_);
return v_res_1848_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_mvarId_1849_, lean_object* v_val_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_){
_start:
{
lean_object* v___x_1856_; 
v___x_1856_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1849_, v_val_1850_, v___y_1852_);
return v___x_1856_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_mvarId_1857_, lean_object* v_val_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_){
_start:
{
lean_object* v_res_1864_; 
v_res_1864_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_mvarId_1857_, v_val_1858_, v___y_1859_, v___y_1860_, v___y_1861_, v___y_1862_);
lean_dec(v___y_1862_);
lean_dec_ref(v___y_1861_);
lean_dec(v___y_1860_);
lean_dec_ref(v___y_1859_);
return v_res_1864_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1(lean_object* v_00_u03b2_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_){
_start:
{
lean_object* v___x_1869_; 
v___x_1869_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_x_1866_, v_x_1867_, v_x_1868_);
return v___x_1869_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1870_, lean_object* v_x_1871_, size_t v_x_1872_, size_t v_x_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_){
_start:
{
lean_object* v___x_1876_; 
v___x_1876_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1871_, v_x_1872_, v_x_1873_, v_x_1874_, v_x_1875_);
return v___x_1876_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_){
_start:
{
size_t v_x_1986__boxed_1883_; size_t v_x_1987__boxed_1884_; lean_object* v_res_1885_; 
v_x_1986__boxed_1883_ = lean_unbox_usize(v_x_1879_);
lean_dec(v_x_1879_);
v_x_1987__boxed_1884_ = lean_unbox_usize(v_x_1880_);
lean_dec(v_x_1880_);
v_res_1885_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(v_00_u03b2_1877_, v_x_1878_, v_x_1986__boxed_1883_, v_x_1987__boxed_1884_, v_x_1881_, v_x_1882_);
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1886_, lean_object* v_n_1887_, lean_object* v_k_1888_, lean_object* v_v_1889_){
_start:
{
lean_object* v___x_1890_; 
v___x_1890_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v_n_1887_, v_k_1888_, v_v_1889_);
return v___x_1890_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1891_, size_t v_depth_1892_, lean_object* v_keys_1893_, lean_object* v_vals_1894_, lean_object* v_heq_1895_, lean_object* v_i_1896_, lean_object* v_entries_1897_){
_start:
{
lean_object* v___x_1898_; 
v___x_1898_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_1892_, v_keys_1893_, v_vals_1894_, v_i_1896_, v_entries_1897_);
return v___x_1898_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1899_, lean_object* v_depth_1900_, lean_object* v_keys_1901_, lean_object* v_vals_1902_, lean_object* v_heq_1903_, lean_object* v_i_1904_, lean_object* v_entries_1905_){
_start:
{
size_t v_depth_boxed_1906_; lean_object* v_res_1907_; 
v_depth_boxed_1906_ = lean_unbox_usize(v_depth_1900_);
lean_dec(v_depth_1900_);
v_res_1907_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_1899_, v_depth_boxed_1906_, v_keys_1901_, v_vals_1902_, v_heq_1903_, v_i_1904_, v_entries_1905_);
lean_dec_ref(v_vals_1902_);
lean_dec_ref(v_keys_1901_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_, lean_object* v_x_1912_){
_start:
{
lean_object* v___x_1913_; 
v___x_1913_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1909_, v_x_1910_, v_x_1911_, v_x_1912_);
return v___x_1913_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_1914_, lean_object* v___y_1915_){
_start:
{
uint8_t v___x_1917_; 
v___x_1917_ = l_Lean_Expr_hasMVar(v_e_1914_);
if (v___x_1917_ == 0)
{
lean_object* v___x_1918_; 
v___x_1918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1918_, 0, v_e_1914_);
return v___x_1918_;
}
else
{
lean_object* v___x_1919_; lean_object* v_mctx_1920_; lean_object* v___x_1921_; lean_object* v_fst_1922_; lean_object* v_snd_1923_; lean_object* v___x_1924_; lean_object* v_cache_1925_; lean_object* v_zetaDeltaFVarIds_1926_; lean_object* v_postponed_1927_; lean_object* v_diag_1928_; lean_object* v___x_1930_; uint8_t v_isShared_1931_; uint8_t v_isSharedCheck_1937_; 
v___x_1919_ = lean_st_ref_get(v___y_1915_);
v_mctx_1920_ = lean_ctor_get(v___x_1919_, 0);
lean_inc_ref(v_mctx_1920_);
lean_dec(v___x_1919_);
v___x_1921_ = l_Lean_instantiateMVarsCore(v_mctx_1920_, v_e_1914_);
v_fst_1922_ = lean_ctor_get(v___x_1921_, 0);
lean_inc(v_fst_1922_);
v_snd_1923_ = lean_ctor_get(v___x_1921_, 1);
lean_inc(v_snd_1923_);
lean_dec_ref(v___x_1921_);
v___x_1924_ = lean_st_ref_take(v___y_1915_);
v_cache_1925_ = lean_ctor_get(v___x_1924_, 1);
v_zetaDeltaFVarIds_1926_ = lean_ctor_get(v___x_1924_, 2);
v_postponed_1927_ = lean_ctor_get(v___x_1924_, 3);
v_diag_1928_ = lean_ctor_get(v___x_1924_, 4);
v_isSharedCheck_1937_ = !lean_is_exclusive(v___x_1924_);
if (v_isSharedCheck_1937_ == 0)
{
lean_object* v_unused_1938_; 
v_unused_1938_ = lean_ctor_get(v___x_1924_, 0);
lean_dec(v_unused_1938_);
v___x_1930_ = v___x_1924_;
v_isShared_1931_ = v_isSharedCheck_1937_;
goto v_resetjp_1929_;
}
else
{
lean_inc(v_diag_1928_);
lean_inc(v_postponed_1927_);
lean_inc(v_zetaDeltaFVarIds_1926_);
lean_inc(v_cache_1925_);
lean_dec(v___x_1924_);
v___x_1930_ = lean_box(0);
v_isShared_1931_ = v_isSharedCheck_1937_;
goto v_resetjp_1929_;
}
v_resetjp_1929_:
{
lean_object* v___x_1933_; 
if (v_isShared_1931_ == 0)
{
lean_ctor_set(v___x_1930_, 0, v_snd_1923_);
v___x_1933_ = v___x_1930_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1936_; 
v_reuseFailAlloc_1936_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1936_, 0, v_snd_1923_);
lean_ctor_set(v_reuseFailAlloc_1936_, 1, v_cache_1925_);
lean_ctor_set(v_reuseFailAlloc_1936_, 2, v_zetaDeltaFVarIds_1926_);
lean_ctor_set(v_reuseFailAlloc_1936_, 3, v_postponed_1927_);
lean_ctor_set(v_reuseFailAlloc_1936_, 4, v_diag_1928_);
v___x_1933_ = v_reuseFailAlloc_1936_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1934_; lean_object* v___x_1935_; 
v___x_1934_ = lean_st_ref_put(v___y_1915_, v___x_1933_);
v___x_1935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1935_, 0, v_fst_1922_);
return v___x_1935_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v_res_1942_; 
v_res_1942_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1939_, v___y_1940_);
lean_dec(v___y_1940_);
return v_res_1942_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_){
_start:
{
lean_object* v___x_1949_; 
v___x_1949_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1943_, v___y_1945_);
return v___x_1949_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_){
_start:
{
lean_object* v_res_1956_; 
v_res_1956_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_1950_, v___y_1951_, v___y_1952_, v___y_1953_, v___y_1954_);
lean_dec(v___y_1954_);
lean_dec_ref(v___y_1953_);
lean_dec(v___y_1952_);
lean_dec_ref(v___y_1951_);
return v_res_1956_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_1957_, lean_object* v_opt_1958_){
_start:
{
lean_object* v_name_1959_; lean_object* v_defValue_1960_; lean_object* v_map_1961_; lean_object* v___x_1962_; 
v_name_1959_ = lean_ctor_get(v_opt_1958_, 0);
v_defValue_1960_ = lean_ctor_get(v_opt_1958_, 1);
v_map_1961_ = lean_ctor_get(v_opts_1957_, 0);
v___x_1962_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1961_, v_name_1959_);
if (lean_obj_tag(v___x_1962_) == 0)
{
uint8_t v___x_1963_; 
v___x_1963_ = lean_unbox(v_defValue_1960_);
return v___x_1963_;
}
else
{
lean_object* v_val_1964_; 
v_val_1964_ = lean_ctor_get(v___x_1962_, 0);
lean_inc(v_val_1964_);
lean_dec_ref_known(v___x_1962_, 1);
if (lean_obj_tag(v_val_1964_) == 1)
{
uint8_t v_v_1965_; 
v_v_1965_ = lean_ctor_get_uint8(v_val_1964_, 0);
lean_dec_ref_known(v_val_1964_, 0);
return v_v_1965_;
}
else
{
uint8_t v___x_1966_; 
lean_dec(v_val_1964_);
v___x_1966_ = lean_unbox(v_defValue_1960_);
return v___x_1966_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_1967_, lean_object* v_opt_1968_){
_start:
{
uint8_t v_res_1969_; lean_object* v_r_1970_; 
v_res_1969_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_1967_, v_opt_1968_);
lean_dec_ref(v_opt_1968_);
lean_dec_ref(v_opts_1967_);
v_r_1970_ = lean_box(v_res_1969_);
return v_r_1970_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_1971_, lean_object* v_as_1972_, size_t v_i_1973_, size_t v_stop_1974_){
_start:
{
uint8_t v___x_1975_; 
v___x_1975_ = lean_usize_dec_eq(v_i_1973_, v_stop_1974_);
if (v___x_1975_ == 0)
{
lean_object* v___x_1976_; uint8_t v___x_1977_; 
v___x_1976_ = lean_array_uget_borrowed(v_as_1972_, v_i_1973_);
v___x_1977_ = lean_nat_dec_eq(v_a_1971_, v___x_1976_);
if (v___x_1977_ == 0)
{
size_t v___x_1978_; size_t v___x_1979_; 
v___x_1978_ = ((size_t)1ULL);
v___x_1979_ = lean_usize_add(v_i_1973_, v___x_1978_);
v_i_1973_ = v___x_1979_;
goto _start;
}
else
{
return v___x_1977_;
}
}
else
{
uint8_t v___x_1981_; 
v___x_1981_ = 0;
return v___x_1981_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_1982_, lean_object* v_as_1983_, lean_object* v_i_1984_, lean_object* v_stop_1985_){
_start:
{
size_t v_i_boxed_1986_; size_t v_stop_boxed_1987_; uint8_t v_res_1988_; lean_object* v_r_1989_; 
v_i_boxed_1986_ = lean_unbox_usize(v_i_1984_);
lean_dec(v_i_1984_);
v_stop_boxed_1987_ = lean_unbox_usize(v_stop_1985_);
lean_dec(v_stop_1985_);
v_res_1988_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1982_, v_as_1983_, v_i_boxed_1986_, v_stop_boxed_1987_);
lean_dec_ref(v_as_1983_);
lean_dec(v_a_1982_);
v_r_1989_ = lean_box(v_res_1988_);
return v_r_1989_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v___x_1992_; lean_object* v___x_1993_; uint8_t v___x_1994_; 
v___x_1992_ = lean_unsigned_to_nat(0u);
v___x_1993_ = lean_array_get_size(v_as_1990_);
v___x_1994_ = lean_nat_dec_lt(v___x_1992_, v___x_1993_);
if (v___x_1994_ == 0)
{
return v___x_1994_;
}
else
{
if (v___x_1994_ == 0)
{
return v___x_1994_;
}
else
{
size_t v___x_1995_; size_t v___x_1996_; uint8_t v___x_1997_; 
v___x_1995_ = ((size_t)0ULL);
v___x_1996_ = lean_usize_of_nat(v___x_1993_);
v___x_1997_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1991_, v_as_1990_, v___x_1995_, v___x_1996_);
return v___x_1997_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_1998_, lean_object* v_a_1999_){
_start:
{
uint8_t v_res_2000_; lean_object* v_r_2001_; 
v_res_2000_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_1998_, v_a_1999_);
lean_dec(v_a_1999_);
lean_dec_ref(v_as_1998_);
v_r_2001_ = lean_box(v_res_2000_);
return v_r_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_2002_, lean_object* v_fst_2003_, lean_object* v_argVars_2004_, lean_object* v_as_2005_, size_t v_sz_2006_, size_t v_i_2007_, lean_object* v_b_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_){
_start:
{
lean_object* v_a_2015_; uint8_t v___x_2019_; 
v___x_2019_ = lean_usize_dec_lt(v_i_2007_, v_sz_2006_);
if (v___x_2019_ == 0)
{
lean_object* v___x_2020_; 
v___x_2020_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2020_, 0, v_b_2008_);
return v___x_2020_;
}
else
{
lean_object* v_next_2021_; 
v_next_2021_ = lean_ctor_get(v_b_2008_, 0);
lean_inc(v_next_2021_);
if (lean_obj_tag(v_next_2021_) == 0)
{
lean_object* v___x_2022_; 
v___x_2022_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2022_, 0, v_b_2008_);
return v___x_2022_;
}
else
{
lean_object* v_upperBound_2023_; lean_object* v_val_2024_; lean_object* v___x_2026_; uint8_t v_isShared_2027_; uint8_t v_isSharedCheck_2055_; 
v_upperBound_2023_ = lean_ctor_get(v_b_2008_, 1);
v_val_2024_ = lean_ctor_get(v_next_2021_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v_next_2021_);
if (v_isSharedCheck_2055_ == 0)
{
v___x_2026_ = v_next_2021_;
v_isShared_2027_ = v_isSharedCheck_2055_;
goto v_resetjp_2025_;
}
else
{
lean_inc(v_val_2024_);
lean_dec(v_next_2021_);
v___x_2026_ = lean_box(0);
v_isShared_2027_ = v_isSharedCheck_2055_;
goto v_resetjp_2025_;
}
v_resetjp_2025_:
{
uint8_t v___x_2028_; 
v___x_2028_ = lean_nat_dec_lt(v_val_2024_, v_upperBound_2023_);
if (v___x_2028_ == 0)
{
lean_object* v___x_2029_; 
lean_del_object(v___x_2026_);
lean_dec(v_val_2024_);
v___x_2029_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2029_, 0, v_b_2008_);
return v___x_2029_;
}
else
{
lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2052_; 
lean_inc(v_upperBound_2023_);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_b_2008_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; lean_object* v_unused_2054_; 
v_unused_2053_ = lean_ctor_get(v_b_2008_, 1);
lean_dec(v_unused_2053_);
v_unused_2054_ = lean_ctor_get(v_b_2008_, 0);
lean_dec(v_unused_2054_);
v___x_2031_ = v_b_2008_;
v_isShared_2032_ = v_isSharedCheck_2052_;
goto v_resetjp_2030_;
}
else
{
lean_dec(v_b_2008_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2052_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; lean_object* v___x_2034_; lean_object* v___x_2036_; 
v___x_2033_ = lean_unsigned_to_nat(1u);
v___x_2034_ = lean_nat_add(v_val_2024_, v___x_2033_);
if (v_isShared_2027_ == 0)
{
lean_ctor_set(v___x_2026_, 0, v___x_2034_);
v___x_2036_ = v___x_2026_;
goto v_reusejp_2035_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2034_);
v___x_2036_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2035_;
}
v_reusejp_2035_:
{
lean_object* v___x_2038_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2036_);
v___x_2038_ = v___x_2031_;
goto v_reusejp_2037_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2036_);
lean_ctor_set(v_reuseFailAlloc_2050_, 1, v_upperBound_2023_);
v___x_2038_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2037_;
}
v_reusejp_2037_:
{
uint8_t v___x_2039_; 
v___x_2039_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2002_, v_val_2024_);
lean_dec(v_val_2024_);
if (v___x_2039_ == 0)
{
lean_object* v_a_2040_; lean_object* v___x_2041_; 
v_a_2040_ = lean_array_uget_borrowed(v_as_2005_, v_i_2007_);
lean_inc(v_a_2040_);
v___x_2041_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2003_, v_argVars_2004_, v_a_2040_, v___y_2009_, v___y_2010_, v___y_2011_, v___y_2012_);
if (lean_obj_tag(v___x_2041_) == 0)
{
lean_dec_ref_known(v___x_2041_, 1);
v_a_2015_ = v___x_2038_;
goto v___jp_2014_;
}
else
{
lean_object* v_a_2042_; lean_object* v___x_2044_; uint8_t v_isShared_2045_; uint8_t v_isSharedCheck_2049_; 
lean_dec_ref(v___x_2038_);
v_a_2042_ = lean_ctor_get(v___x_2041_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v___x_2041_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2044_ = v___x_2041_;
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
else
{
lean_inc(v_a_2042_);
lean_dec(v___x_2041_);
v___x_2044_ = lean_box(0);
v_isShared_2045_ = v_isSharedCheck_2049_;
goto v_resetjp_2043_;
}
v_resetjp_2043_:
{
lean_object* v___x_2047_; 
if (v_isShared_2045_ == 0)
{
v___x_2047_ = v___x_2044_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2048_; 
v_reuseFailAlloc_2048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2048_, 0, v_a_2042_);
v___x_2047_ = v_reuseFailAlloc_2048_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
return v___x_2047_;
}
}
}
}
else
{
v_a_2015_ = v___x_2038_;
goto v___jp_2014_;
}
}
}
}
}
}
}
}
v___jp_2014_:
{
size_t v___x_2016_; size_t v___x_2017_; 
v___x_2016_ = ((size_t)1ULL);
v___x_2017_ = lean_usize_add(v_i_2007_, v___x_2016_);
v_i_2007_ = v___x_2017_;
v_b_2008_ = v_a_2015_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2056_, lean_object* v_fst_2057_, lean_object* v_argVars_2058_, lean_object* v_as_2059_, lean_object* v_sz_2060_, lean_object* v_i_2061_, lean_object* v_b_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_){
_start:
{
size_t v_sz_boxed_2068_; size_t v_i_boxed_2069_; lean_object* v_res_2070_; 
v_sz_boxed_2068_ = lean_unbox_usize(v_sz_2060_);
lean_dec(v_sz_2060_);
v_i_boxed_2069_ = lean_unbox_usize(v_i_2061_);
lean_dec(v_i_2061_);
v_res_2070_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2056_, v_fst_2057_, v_argVars_2058_, v_as_2059_, v_sz_boxed_2068_, v_i_boxed_2069_, v_b_2062_, v___y_2063_, v___y_2064_, v___y_2065_, v___y_2066_);
lean_dec(v___y_2066_);
lean_dec_ref(v___y_2065_);
lean_dec(v___y_2064_);
lean_dec_ref(v___y_2063_);
lean_dec_ref(v_as_2059_);
lean_dec_ref(v_argVars_2058_);
lean_dec_ref(v_fst_2057_);
lean_dec_ref(v_a_2056_);
return v_res_2070_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2071_, lean_object* v___x_2072_, lean_object* v_a_2073_, lean_object* v_a_2074_, lean_object* v_b_2075_){
_start:
{
uint8_t v___x_2077_; 
v___x_2077_ = lean_nat_dec_lt(v_a_2074_, v_upperBound_2071_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
lean_dec(v_a_2074_);
v___x_2078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2078_, 0, v_b_2075_);
return v___x_2078_;
}
else
{
lean_object* v_snd_2079_; lean_object* v___x_2081_; uint8_t v_isShared_2082_; uint8_t v_isSharedCheck_2120_; 
v_snd_2079_ = lean_ctor_get(v_b_2075_, 1);
v_isSharedCheck_2120_ = !lean_is_exclusive(v_b_2075_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; 
v_unused_2121_ = lean_ctor_get(v_b_2075_, 0);
lean_dec(v_unused_2121_);
v___x_2081_ = v_b_2075_;
v_isShared_2082_ = v_isSharedCheck_2120_;
goto v_resetjp_2080_;
}
else
{
lean_inc(v_snd_2079_);
lean_dec(v_b_2075_);
v___x_2081_ = lean_box(0);
v_isShared_2082_ = v_isSharedCheck_2120_;
goto v_resetjp_2080_;
}
v_resetjp_2080_:
{
lean_object* v_array_2083_; lean_object* v_start_2084_; lean_object* v_stop_2085_; lean_object* v___x_2086_; uint8_t v___x_2087_; 
v_array_2083_ = lean_ctor_get(v_snd_2079_, 0);
v_start_2084_ = lean_ctor_get(v_snd_2079_, 1);
v_stop_2085_ = lean_ctor_get(v_snd_2079_, 2);
v___x_2086_ = lean_box(0);
v___x_2087_ = lean_nat_dec_lt(v_start_2084_, v_stop_2085_);
if (v___x_2087_ == 0)
{
lean_object* v___x_2089_; 
lean_dec(v_a_2074_);
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 0, v___x_2086_);
v___x_2089_ = v___x_2081_;
goto v_reusejp_2088_;
}
else
{
lean_object* v_reuseFailAlloc_2091_; 
v_reuseFailAlloc_2091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2091_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2091_, 1, v_snd_2079_);
v___x_2089_ = v_reuseFailAlloc_2091_;
goto v_reusejp_2088_;
}
v_reusejp_2088_:
{
lean_object* v___x_2090_; 
v___x_2090_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2090_, 0, v___x_2089_);
return v___x_2090_;
}
}
else
{
lean_object* v___x_2093_; uint8_t v_isShared_2094_; uint8_t v_isSharedCheck_2116_; 
lean_inc(v_stop_2085_);
lean_inc(v_start_2084_);
lean_inc_ref(v_array_2083_);
v_isSharedCheck_2116_ = !lean_is_exclusive(v_snd_2079_);
if (v_isSharedCheck_2116_ == 0)
{
lean_object* v_unused_2117_; lean_object* v_unused_2118_; lean_object* v_unused_2119_; 
v_unused_2117_ = lean_ctor_get(v_snd_2079_, 2);
lean_dec(v_unused_2117_);
v_unused_2118_ = lean_ctor_get(v_snd_2079_, 1);
lean_dec(v_unused_2118_);
v_unused_2119_ = lean_ctor_get(v_snd_2079_, 0);
lean_dec(v_unused_2119_);
v___x_2093_ = v_snd_2079_;
v_isShared_2094_ = v_isSharedCheck_2116_;
goto v_resetjp_2092_;
}
else
{
lean_dec(v_snd_2079_);
v___x_2093_ = lean_box(0);
v_isShared_2094_ = v_isSharedCheck_2116_;
goto v_resetjp_2092_;
}
v_resetjp_2092_:
{
lean_object* v___x_2095_; uint8_t v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; lean_object* v___x_2099_; lean_object* v___x_2101_; 
v___x_2095_ = lean_unsigned_to_nat(0u);
v___x_2096_ = lean_nat_dec_eq(v___x_2072_, v___x_2095_);
v___x_2097_ = lean_array_fget(v_array_2083_, v_start_2084_);
v___x_2098_ = lean_unsigned_to_nat(1u);
v___x_2099_ = lean_nat_add(v_start_2084_, v___x_2098_);
lean_dec(v_start_2084_);
if (v_isShared_2094_ == 0)
{
lean_ctor_set(v___x_2093_, 1, v___x_2099_);
v___x_2101_ = v___x_2093_;
goto v_reusejp_2100_;
}
else
{
lean_object* v_reuseFailAlloc_2115_; 
v_reuseFailAlloc_2115_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2115_, 0, v_array_2083_);
lean_ctor_set(v_reuseFailAlloc_2115_, 1, v___x_2099_);
lean_ctor_set(v_reuseFailAlloc_2115_, 2, v_stop_2085_);
v___x_2101_ = v_reuseFailAlloc_2115_;
goto v_reusejp_2100_;
}
v_reusejp_2100_:
{
uint8_t v___x_2114_; 
v___x_2114_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2073_, v_a_2074_);
if (v___x_2114_ == 0)
{
goto v___jp_2108_;
}
else
{
if (v___x_2096_ == 0)
{
lean_dec(v___x_2097_);
goto v___jp_2102_;
}
else
{
goto v___jp_2108_;
}
}
v___jp_2102_:
{
lean_object* v___x_2104_; 
if (v_isShared_2082_ == 0)
{
lean_ctor_set(v___x_2081_, 1, v___x_2101_);
lean_ctor_set(v___x_2081_, 0, v___x_2086_);
v___x_2104_ = v___x_2081_;
goto v_reusejp_2103_;
}
else
{
lean_object* v_reuseFailAlloc_2107_; 
v_reuseFailAlloc_2107_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2107_, 0, v___x_2086_);
lean_ctor_set(v_reuseFailAlloc_2107_, 1, v___x_2101_);
v___x_2104_ = v_reuseFailAlloc_2107_;
goto v_reusejp_2103_;
}
v_reusejp_2103_:
{
lean_object* v___x_2105_; 
v___x_2105_ = lean_nat_add(v_a_2074_, v___x_2098_);
lean_dec(v_a_2074_);
v_a_2074_ = v___x_2105_;
v_b_2075_ = v___x_2104_;
goto _start;
}
}
v___jp_2108_:
{
uint8_t v___x_2109_; 
v___x_2109_ = l_Lean_Expr_hasExprMVar(v___x_2097_);
lean_dec(v___x_2097_);
if (v___x_2109_ == 0)
{
goto v___jp_2102_;
}
else
{
lean_object* v___x_2110_; lean_object* v___x_2111_; lean_object* v___x_2112_; lean_object* v___x_2113_; 
lean_del_object(v___x_2081_);
lean_dec(v_a_2074_);
v___x_2110_ = lean_box(v___x_2096_);
v___x_2111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2111_, 0, v___x_2110_);
v___x_2112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2112_, 0, v___x_2111_);
lean_ctor_set(v___x_2112_, 1, v___x_2101_);
v___x_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2113_, 0, v___x_2112_);
return v___x_2113_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2122_, lean_object* v___x_2123_, lean_object* v_a_2124_, lean_object* v_a_2125_, lean_object* v_b_2126_, lean_object* v___y_2127_){
_start:
{
lean_object* v_res_2128_; 
v_res_2128_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2122_, v___x_2123_, v_a_2124_, v_a_2125_, v_b_2126_);
lean_dec_ref(v_a_2124_);
lean_dec(v___x_2123_);
lean_dec(v_upperBound_2122_);
return v_res_2128_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2129_; lean_object* v_dummy_2130_; 
v___x_2129_ = lean_box(0);
v_dummy_2130_ = l_Lean_Expr_sort___override(v___x_2129_);
return v_dummy_2130_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2131_, lean_object* v___x_2132_, uint8_t v___x_2133_, lean_object* v_x_2134_, lean_object* v_argTy_2135_, lean_object* v___y_2136_, lean_object* v___y_2137_, lean_object* v___y_2138_, lean_object* v___y_2139_){
_start:
{
lean_object* v___x_2141_; 
lean_inc(v___y_2139_);
lean_inc_ref(v___y_2138_);
lean_inc(v___y_2137_);
lean_inc_ref(v___y_2136_);
v___x_2141_ = lean_whnf(v_argTy_2135_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
if (lean_obj_tag(v___x_2141_) == 0)
{
lean_object* v_a_2142_; lean_object* v___x_2143_; 
v_a_2142_ = lean_ctor_get(v___x_2141_, 0);
lean_inc(v_a_2142_);
lean_dec_ref_known(v___x_2141_, 1);
v___x_2143_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2142_, v___y_2136_, v___y_2137_, v___y_2138_, v___y_2139_);
if (lean_obj_tag(v___x_2143_) == 0)
{
lean_object* v_a_2144_; lean_object* v_dummy_2145_; lean_object* v_nargs_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; lean_object* v___x_2150_; lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; lean_object* v___x_2155_; 
v_a_2144_ = lean_ctor_get(v___x_2143_, 0);
lean_inc(v_a_2144_);
lean_dec_ref_known(v___x_2143_, 1);
v_dummy_2145_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2146_ = l_Lean_Expr_getAppNumArgs(v_a_2142_);
lean_inc(v_nargs_2146_);
v___x_2147_ = lean_mk_array(v_nargs_2146_, v_dummy_2145_);
v___x_2148_ = lean_unsigned_to_nat(1u);
v___x_2149_ = lean_nat_sub(v_nargs_2146_, v___x_2148_);
lean_dec(v_nargs_2146_);
v___x_2150_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2142_, v___x_2147_, v___x_2149_);
v___x_2151_ = lean_array_get_size(v___x_2150_);
lean_inc(v___x_2131_);
v___x_2152_ = l_Array_toSubarray___redArg(v___x_2150_, v___x_2131_, v___x_2151_);
v___x_2153_ = lean_box(0);
v___x_2154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2154_, 0, v___x_2153_);
lean_ctor_set(v___x_2154_, 1, v___x_2152_);
v___x_2155_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2151_, v___x_2132_, v_a_2144_, v___x_2131_, v___x_2154_);
lean_dec(v_a_2144_);
if (lean_obj_tag(v___x_2155_) == 0)
{
lean_object* v_a_2156_; lean_object* v___x_2158_; uint8_t v_isShared_2159_; uint8_t v_isSharedCheck_2169_; 
v_a_2156_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2169_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2169_ == 0)
{
v___x_2158_ = v___x_2155_;
v_isShared_2159_ = v_isSharedCheck_2169_;
goto v_resetjp_2157_;
}
else
{
lean_inc(v_a_2156_);
lean_dec(v___x_2155_);
v___x_2158_ = lean_box(0);
v_isShared_2159_ = v_isSharedCheck_2169_;
goto v_resetjp_2157_;
}
v_resetjp_2157_:
{
lean_object* v_fst_2160_; 
v_fst_2160_ = lean_ctor_get(v_a_2156_, 0);
lean_inc(v_fst_2160_);
lean_dec(v_a_2156_);
if (lean_obj_tag(v_fst_2160_) == 0)
{
lean_object* v___x_2161_; lean_object* v___x_2163_; 
v___x_2161_ = lean_box(v___x_2133_);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v___x_2161_);
v___x_2163_ = v___x_2158_;
goto v_reusejp_2162_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v___x_2161_);
v___x_2163_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2162_;
}
v_reusejp_2162_:
{
return v___x_2163_;
}
}
else
{
lean_object* v_val_2165_; lean_object* v___x_2167_; 
v_val_2165_ = lean_ctor_get(v_fst_2160_, 0);
lean_inc(v_val_2165_);
lean_dec_ref_known(v_fst_2160_, 1);
if (v_isShared_2159_ == 0)
{
lean_ctor_set(v___x_2158_, 0, v_val_2165_);
v___x_2167_ = v___x_2158_;
goto v_reusejp_2166_;
}
else
{
lean_object* v_reuseFailAlloc_2168_; 
v_reuseFailAlloc_2168_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2168_, 0, v_val_2165_);
v___x_2167_ = v_reuseFailAlloc_2168_;
goto v_reusejp_2166_;
}
v_reusejp_2166_:
{
return v___x_2167_;
}
}
}
}
else
{
lean_object* v_a_2170_; lean_object* v___x_2172_; uint8_t v_isShared_2173_; uint8_t v_isSharedCheck_2177_; 
v_a_2170_ = lean_ctor_get(v___x_2155_, 0);
v_isSharedCheck_2177_ = !lean_is_exclusive(v___x_2155_);
if (v_isSharedCheck_2177_ == 0)
{
v___x_2172_ = v___x_2155_;
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
else
{
lean_inc(v_a_2170_);
lean_dec(v___x_2155_);
v___x_2172_ = lean_box(0);
v_isShared_2173_ = v_isSharedCheck_2177_;
goto v_resetjp_2171_;
}
v_resetjp_2171_:
{
lean_object* v___x_2175_; 
if (v_isShared_2173_ == 0)
{
v___x_2175_ = v___x_2172_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2176_; 
v_reuseFailAlloc_2176_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2176_, 0, v_a_2170_);
v___x_2175_ = v_reuseFailAlloc_2176_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
return v___x_2175_;
}
}
}
}
else
{
lean_object* v_a_2178_; lean_object* v___x_2180_; uint8_t v_isShared_2181_; uint8_t v_isSharedCheck_2185_; 
lean_dec(v_a_2142_);
lean_dec(v___x_2131_);
v_a_2178_ = lean_ctor_get(v___x_2143_, 0);
v_isSharedCheck_2185_ = !lean_is_exclusive(v___x_2143_);
if (v_isSharedCheck_2185_ == 0)
{
v___x_2180_ = v___x_2143_;
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
else
{
lean_inc(v_a_2178_);
lean_dec(v___x_2143_);
v___x_2180_ = lean_box(0);
v_isShared_2181_ = v_isSharedCheck_2185_;
goto v_resetjp_2179_;
}
v_resetjp_2179_:
{
lean_object* v___x_2183_; 
if (v_isShared_2181_ == 0)
{
v___x_2183_ = v___x_2180_;
goto v_reusejp_2182_;
}
else
{
lean_object* v_reuseFailAlloc_2184_; 
v_reuseFailAlloc_2184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2184_, 0, v_a_2178_);
v___x_2183_ = v_reuseFailAlloc_2184_;
goto v_reusejp_2182_;
}
v_reusejp_2182_:
{
return v___x_2183_;
}
}
}
}
else
{
lean_object* v_a_2186_; lean_object* v___x_2188_; uint8_t v_isShared_2189_; uint8_t v_isSharedCheck_2193_; 
lean_dec(v___x_2131_);
v_a_2186_ = lean_ctor_get(v___x_2141_, 0);
v_isSharedCheck_2193_ = !lean_is_exclusive(v___x_2141_);
if (v_isSharedCheck_2193_ == 0)
{
v___x_2188_ = v___x_2141_;
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
else
{
lean_inc(v_a_2186_);
lean_dec(v___x_2141_);
v___x_2188_ = lean_box(0);
v_isShared_2189_ = v_isSharedCheck_2193_;
goto v_resetjp_2187_;
}
v_resetjp_2187_:
{
lean_object* v___x_2191_; 
if (v_isShared_2189_ == 0)
{
v___x_2191_ = v___x_2188_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v_a_2186_);
v___x_2191_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
return v___x_2191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2194_, lean_object* v___x_2195_, lean_object* v___x_2196_, lean_object* v_x_2197_, lean_object* v_argTy_2198_, lean_object* v___y_2199_, lean_object* v___y_2200_, lean_object* v___y_2201_, lean_object* v___y_2202_, lean_object* v___y_2203_){
_start:
{
uint8_t v___x_25980__boxed_2204_; lean_object* v_res_2205_; 
v___x_25980__boxed_2204_ = lean_unbox(v___x_2196_);
v_res_2205_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2194_, v___x_2195_, v___x_25980__boxed_2204_, v_x_2197_, v_argTy_2198_, v___y_2199_, v___y_2200_, v___y_2201_, v___y_2202_);
lean_dec(v___y_2202_);
lean_dec_ref(v___y_2201_);
lean_dec(v___y_2200_);
lean_dec_ref(v___y_2199_);
lean_dec_ref(v_x_2197_);
lean_dec(v___x_2195_);
return v_res_2205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2209_, lean_object* v_projInfo_x3f_2210_, lean_object* v___x_2211_, lean_object* v_argVars_2212_, lean_object* v_as_2213_, size_t v_sz_2214_, size_t v_i_2215_, lean_object* v_b_2216_, lean_object* v___y_2217_, lean_object* v___y_2218_, lean_object* v___y_2219_, lean_object* v___y_2220_){
_start:
{
uint8_t v___x_2222_; 
v___x_2222_ = lean_usize_dec_lt(v_i_2215_, v_sz_2214_);
if (v___x_2222_ == 0)
{
lean_object* v___x_2223_; 
lean_dec(v___x_2211_);
v___x_2223_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2223_, 0, v_b_2216_);
return v___x_2223_;
}
else
{
lean_object* v_a_2224_; lean_object* v___x_2225_; lean_object* v___x_2226_; lean_object* v___x_2227_; 
lean_dec_ref(v_b_2216_);
v_a_2224_ = lean_array_uget_borrowed(v_as_2213_, v_i_2215_);
v___x_2225_ = l_Lean_instInhabitedExpr;
v___x_2226_ = lean_array_get_borrowed(v___x_2225_, v_fst_2209_, v_a_2224_);
lean_inc(v___y_2220_);
lean_inc_ref(v___y_2219_);
lean_inc(v___y_2218_);
lean_inc_ref(v___y_2217_);
lean_inc(v___x_2226_);
v___x_2227_ = lean_infer_type(v___x_2226_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2227_) == 0)
{
lean_object* v_a_2228_; lean_object* v___x_2229_; 
v_a_2228_ = lean_ctor_get(v___x_2227_, 0);
lean_inc(v_a_2228_);
lean_dec_ref_known(v___x_2227_, 1);
v___x_2229_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2228_, v___y_2218_);
if (lean_obj_tag(v___x_2229_) == 0)
{
lean_object* v_a_2230_; lean_object* v___x_2232_; uint8_t v_isShared_2233_; uint8_t v_isSharedCheck_2276_; 
v_a_2230_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2232_ = v___x_2229_;
v_isShared_2233_ = v_isSharedCheck_2276_;
goto v_resetjp_2231_;
}
else
{
lean_inc(v_a_2230_);
lean_dec(v___x_2229_);
v___x_2232_ = lean_box(0);
v_isShared_2233_ = v_isSharedCheck_2276_;
goto v_resetjp_2231_;
}
v_resetjp_2231_:
{
lean_object* v___x_2234_; lean_object* v___x_2242_; lean_object* v___y_2244_; lean_object* v___x_2258_; lean_object* v___x_2259_; lean_object* v___f_2260_; uint8_t v___x_2261_; 
v___x_2234_ = lean_box(0);
v___x_2242_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2258_ = lean_unsigned_to_nat(0u);
v___x_2259_ = lean_box(v___x_2222_);
lean_inc(v___x_2211_);
v___f_2260_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2260_, 0, v___x_2258_);
lean_closure_set(v___f_2260_, 1, v___x_2211_);
lean_closure_set(v___f_2260_, 2, v___x_2259_);
v___x_2261_ = lean_nat_dec_eq(v___x_2211_, v___x_2258_);
if (lean_obj_tag(v_projInfo_x3f_2210_) == 1)
{
lean_object* v_val_2262_; lean_object* v_numParams_2263_; uint8_t v___x_2264_; 
v_val_2262_ = lean_ctor_get(v_projInfo_x3f_2210_, 0);
v_numParams_2263_ = lean_ctor_get(v_val_2262_, 1);
v___x_2264_ = lean_nat_dec_eq(v_numParams_2263_, v_a_2224_);
if (v___x_2264_ == 0)
{
lean_object* v___x_2265_; 
v___x_2265_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2230_, v___f_2260_, v___x_2261_, v___x_2261_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
v___y_2244_ = v___x_2265_;
goto v___jp_2243_;
}
else
{
lean_object* v___x_2266_; 
lean_dec_ref(v___f_2260_);
lean_dec(v___x_2211_);
v___x_2266_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2209_, v_argVars_2212_, v_a_2230_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
if (lean_obj_tag(v___x_2266_) == 0)
{
lean_dec_ref_known(v___x_2266_, 1);
goto v___jp_2235_;
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
lean_del_object(v___x_2232_);
v_a_2267_ = lean_ctor_get(v___x_2266_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2266_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2266_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2266_);
v___x_2269_ = lean_box(0);
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
v_resetjp_2268_:
{
lean_object* v___x_2272_; 
if (v_isShared_2270_ == 0)
{
v___x_2272_ = v___x_2269_;
goto v_reusejp_2271_;
}
else
{
lean_object* v_reuseFailAlloc_2273_; 
v_reuseFailAlloc_2273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2273_, 0, v_a_2267_);
v___x_2272_ = v_reuseFailAlloc_2273_;
goto v_reusejp_2271_;
}
v_reusejp_2271_:
{
return v___x_2272_;
}
}
}
}
}
else
{
lean_object* v___x_2275_; 
v___x_2275_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2230_, v___f_2260_, v___x_2261_, v___x_2261_, v___y_2217_, v___y_2218_, v___y_2219_, v___y_2220_);
v___y_2244_ = v___x_2275_;
goto v___jp_2243_;
}
v___jp_2235_:
{
lean_object* v___x_2236_; lean_object* v___x_2237_; lean_object* v___x_2238_; lean_object* v___x_2240_; 
lean_inc(v_a_2224_);
v___x_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2236_, 0, v_a_2224_);
v___x_2237_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2237_, 0, v___x_2236_);
v___x_2238_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2238_, 0, v___x_2237_);
lean_ctor_set(v___x_2238_, 1, v___x_2234_);
if (v_isShared_2233_ == 0)
{
lean_ctor_set(v___x_2232_, 0, v___x_2238_);
v___x_2240_ = v___x_2232_;
goto v_reusejp_2239_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2238_);
v___x_2240_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2239_;
}
v_reusejp_2239_:
{
return v___x_2240_;
}
}
v___jp_2243_:
{
if (lean_obj_tag(v___y_2244_) == 0)
{
lean_object* v_a_2245_; uint8_t v___x_2246_; 
v_a_2245_ = lean_ctor_get(v___y_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___y_2244_, 1);
v___x_2246_ = lean_unbox(v_a_2245_);
lean_dec(v_a_2245_);
if (v___x_2246_ == 0)
{
size_t v___x_2247_; size_t v___x_2248_; 
lean_del_object(v___x_2232_);
v___x_2247_ = ((size_t)1ULL);
v___x_2248_ = lean_usize_add(v_i_2215_, v___x_2247_);
v_i_2215_ = v___x_2248_;
v_b_2216_ = v___x_2242_;
goto _start;
}
else
{
lean_dec(v___x_2211_);
goto v___jp_2235_;
}
}
else
{
lean_object* v_a_2250_; lean_object* v___x_2252_; uint8_t v_isShared_2253_; uint8_t v_isSharedCheck_2257_; 
lean_del_object(v___x_2232_);
lean_dec(v___x_2211_);
v_a_2250_ = lean_ctor_get(v___y_2244_, 0);
v_isSharedCheck_2257_ = !lean_is_exclusive(v___y_2244_);
if (v_isSharedCheck_2257_ == 0)
{
v___x_2252_ = v___y_2244_;
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
else
{
lean_inc(v_a_2250_);
lean_dec(v___y_2244_);
v___x_2252_ = lean_box(0);
v_isShared_2253_ = v_isSharedCheck_2257_;
goto v_resetjp_2251_;
}
v_resetjp_2251_:
{
lean_object* v___x_2255_; 
if (v_isShared_2253_ == 0)
{
v___x_2255_ = v___x_2252_;
goto v_reusejp_2254_;
}
else
{
lean_object* v_reuseFailAlloc_2256_; 
v_reuseFailAlloc_2256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2256_, 0, v_a_2250_);
v___x_2255_ = v_reuseFailAlloc_2256_;
goto v_reusejp_2254_;
}
v_reusejp_2254_:
{
return v___x_2255_;
}
}
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v___x_2211_);
v_a_2277_ = lean_ctor_get(v___x_2229_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2229_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2229_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2229_);
v___x_2279_ = lean_box(0);
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
v_resetjp_2278_:
{
lean_object* v___x_2282_; 
if (v_isShared_2280_ == 0)
{
v___x_2282_ = v___x_2279_;
goto v_reusejp_2281_;
}
else
{
lean_object* v_reuseFailAlloc_2283_; 
v_reuseFailAlloc_2283_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2283_, 0, v_a_2277_);
v___x_2282_ = v_reuseFailAlloc_2283_;
goto v_reusejp_2281_;
}
v_reusejp_2281_:
{
return v___x_2282_;
}
}
}
}
else
{
lean_object* v_a_2285_; lean_object* v___x_2287_; uint8_t v_isShared_2288_; uint8_t v_isSharedCheck_2292_; 
lean_dec(v___x_2211_);
v_a_2285_ = lean_ctor_get(v___x_2227_, 0);
v_isSharedCheck_2292_ = !lean_is_exclusive(v___x_2227_);
if (v_isSharedCheck_2292_ == 0)
{
v___x_2287_ = v___x_2227_;
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
else
{
lean_inc(v_a_2285_);
lean_dec(v___x_2227_);
v___x_2287_ = lean_box(0);
v_isShared_2288_ = v_isSharedCheck_2292_;
goto v_resetjp_2286_;
}
v_resetjp_2286_:
{
lean_object* v___x_2290_; 
if (v_isShared_2288_ == 0)
{
v___x_2290_ = v___x_2287_;
goto v_reusejp_2289_;
}
else
{
lean_object* v_reuseFailAlloc_2291_; 
v_reuseFailAlloc_2291_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2291_, 0, v_a_2285_);
v___x_2290_ = v_reuseFailAlloc_2291_;
goto v_reusejp_2289_;
}
v_reusejp_2289_:
{
return v___x_2290_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2293_, lean_object* v_projInfo_x3f_2294_, lean_object* v___x_2295_, lean_object* v_argVars_2296_, lean_object* v_as_2297_, lean_object* v_sz_2298_, lean_object* v_i_2299_, lean_object* v_b_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
size_t v_sz_boxed_2306_; size_t v_i_boxed_2307_; lean_object* v_res_2308_; 
v_sz_boxed_2306_ = lean_unbox_usize(v_sz_2298_);
lean_dec(v_sz_2298_);
v_i_boxed_2307_ = lean_unbox_usize(v_i_2299_);
lean_dec(v_i_2299_);
v_res_2308_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2293_, v_projInfo_x3f_2294_, v___x_2295_, v_argVars_2296_, v_as_2297_, v_sz_boxed_2306_, v_i_boxed_2307_, v_b_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec_ref(v_as_2297_);
lean_dec_ref(v_argVars_2296_);
lean_dec(v_projInfo_x3f_2294_);
lean_dec_ref(v_fst_2293_);
return v_res_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2309_, lean_object* v_as_2310_, size_t v_i_2311_, size_t v_stop_2312_, lean_object* v_b_2313_){
_start:
{
lean_object* v___y_2315_; uint8_t v___x_2319_; 
v___x_2319_ = lean_usize_dec_eq(v_i_2311_, v_stop_2312_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; uint8_t v___x_2321_; 
v___x_2320_ = lean_array_uget_borrowed(v_as_2310_, v_i_2311_);
v___x_2321_ = lean_nat_dec_eq(v___x_2320_, v_next_2309_);
if (v___x_2321_ == 0)
{
lean_object* v___x_2322_; 
lean_inc(v___x_2320_);
v___x_2322_ = lean_array_push(v_b_2313_, v___x_2320_);
v___y_2315_ = v___x_2322_;
goto v___jp_2314_;
}
else
{
v___y_2315_ = v_b_2313_;
goto v___jp_2314_;
}
}
else
{
return v_b_2313_;
}
v___jp_2314_:
{
size_t v___x_2316_; size_t v___x_2317_; 
v___x_2316_ = ((size_t)1ULL);
v___x_2317_ = lean_usize_add(v_i_2311_, v___x_2316_);
v_i_2311_ = v___x_2317_;
v_b_2313_ = v___y_2315_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2323_, lean_object* v_as_2324_, lean_object* v_i_2325_, lean_object* v_stop_2326_, lean_object* v_b_2327_){
_start:
{
size_t v_i_boxed_2328_; size_t v_stop_boxed_2329_; lean_object* v_res_2330_; 
v_i_boxed_2328_ = lean_unbox_usize(v_i_2325_);
lean_dec(v_i_2325_);
v_stop_boxed_2329_ = lean_unbox_usize(v_stop_2326_);
lean_dec(v_stop_2326_);
v_res_2330_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2323_, v_as_2324_, v_i_boxed_2328_, v_stop_boxed_2329_, v_b_2327_);
lean_dec_ref(v_as_2324_);
lean_dec(v_next_2323_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object* v_fst_2331_, lean_object* v_fst_2332_, lean_object* v_argVars_2333_, lean_object* v_snd_2334_, lean_object* v_next_2335_, lean_object* v___y_2336_, lean_object* v___y_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_){
_start:
{
lean_object* v___x_2341_; lean_object* v___y_2343_; lean_object* v___x_2384_; lean_object* v___x_2385_; lean_object* v___x_2386_; uint8_t v___x_2387_; 
lean_inc(v_next_2335_);
v___x_2341_ = lean_array_push(v_fst_2331_, v_next_2335_);
v___x_2384_ = lean_unsigned_to_nat(0u);
v___x_2385_ = lean_array_get_size(v_snd_2334_);
v___x_2386_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2387_ = lean_nat_dec_lt(v___x_2384_, v___x_2385_);
if (v___x_2387_ == 0)
{
v___y_2343_ = v___x_2386_;
goto v___jp_2342_;
}
else
{
uint8_t v___x_2388_; 
v___x_2388_ = lean_nat_dec_le(v___x_2385_, v___x_2385_);
if (v___x_2388_ == 0)
{
if (v___x_2387_ == 0)
{
v___y_2343_ = v___x_2386_;
goto v___jp_2342_;
}
else
{
size_t v___x_2389_; size_t v___x_2390_; lean_object* v___x_2391_; 
v___x_2389_ = ((size_t)0ULL);
v___x_2390_ = lean_usize_of_nat(v___x_2385_);
v___x_2391_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2335_, v_snd_2334_, v___x_2389_, v___x_2390_, v___x_2386_);
v___y_2343_ = v___x_2391_;
goto v___jp_2342_;
}
}
else
{
size_t v___x_2392_; size_t v___x_2393_; lean_object* v___x_2394_; 
v___x_2392_ = ((size_t)0ULL);
v___x_2393_ = lean_usize_of_nat(v___x_2385_);
v___x_2394_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2335_, v_snd_2334_, v___x_2392_, v___x_2393_, v___x_2386_);
v___y_2343_ = v___x_2394_;
goto v___jp_2342_;
}
}
v___jp_2342_:
{
lean_object* v___x_2344_; lean_object* v___x_2345_; lean_object* v___x_2346_; 
v___x_2344_ = l_Lean_instInhabitedExpr;
v___x_2345_ = lean_array_get_borrowed(v___x_2344_, v_fst_2332_, v_next_2335_);
lean_dec(v_next_2335_);
lean_inc(v___y_2339_);
lean_inc_ref(v___y_2338_);
lean_inc(v___y_2337_);
lean_inc_ref(v___y_2336_);
lean_inc(v___x_2345_);
v___x_2346_ = lean_infer_type(v___x_2345_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
if (lean_obj_tag(v___x_2346_) == 0)
{
lean_object* v_a_2347_; lean_object* v___x_2348_; 
v_a_2347_ = lean_ctor_get(v___x_2346_, 0);
lean_inc(v_a_2347_);
lean_dec_ref_known(v___x_2346_, 1);
v___x_2348_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2332_, v_argVars_2333_, v_a_2347_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v___x_2349_; 
lean_dec_ref_known(v___x_2348_, 1);
lean_inc(v___x_2345_);
v___x_2349_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2332_, v_argVars_2333_, v___x_2345_, v___y_2336_, v___y_2337_, v___y_2338_, v___y_2339_);
if (lean_obj_tag(v___x_2349_) == 0)
{
lean_object* v___x_2351_; uint8_t v_isShared_2352_; uint8_t v_isSharedCheck_2358_; 
v_isSharedCheck_2358_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2358_ == 0)
{
lean_object* v_unused_2359_; 
v_unused_2359_ = lean_ctor_get(v___x_2349_, 0);
lean_dec(v_unused_2359_);
v___x_2351_ = v___x_2349_;
v_isShared_2352_ = v_isSharedCheck_2358_;
goto v_resetjp_2350_;
}
else
{
lean_dec(v___x_2349_);
v___x_2351_ = lean_box(0);
v_isShared_2352_ = v_isSharedCheck_2358_;
goto v_resetjp_2350_;
}
v_resetjp_2350_:
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2356_; 
v___x_2353_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2353_, 0, v___x_2341_);
lean_ctor_set(v___x_2353_, 1, v___y_2343_);
v___x_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2354_, 0, v___x_2353_);
if (v_isShared_2352_ == 0)
{
lean_ctor_set(v___x_2351_, 0, v___x_2354_);
v___x_2356_ = v___x_2351_;
goto v_reusejp_2355_;
}
else
{
lean_object* v_reuseFailAlloc_2357_; 
v_reuseFailAlloc_2357_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2357_, 0, v___x_2354_);
v___x_2356_ = v_reuseFailAlloc_2357_;
goto v_reusejp_2355_;
}
v_reusejp_2355_:
{
return v___x_2356_;
}
}
}
else
{
lean_object* v_a_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2367_; 
lean_dec_ref(v___y_2343_);
lean_dec_ref(v___x_2341_);
v_a_2360_ = lean_ctor_get(v___x_2349_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2349_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2362_ = v___x_2349_;
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_a_2360_);
lean_dec(v___x_2349_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2367_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2365_; 
if (v_isShared_2363_ == 0)
{
v___x_2365_ = v___x_2362_;
goto v_reusejp_2364_;
}
else
{
lean_object* v_reuseFailAlloc_2366_; 
v_reuseFailAlloc_2366_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2366_, 0, v_a_2360_);
v___x_2365_ = v_reuseFailAlloc_2366_;
goto v_reusejp_2364_;
}
v_reusejp_2364_:
{
return v___x_2365_;
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec_ref(v___y_2343_);
lean_dec_ref(v___x_2341_);
v_a_2368_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2348_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2348_);
v___x_2370_ = lean_box(0);
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
v_resetjp_2369_:
{
lean_object* v___x_2373_; 
if (v_isShared_2371_ == 0)
{
v___x_2373_ = v___x_2370_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_a_2368_);
v___x_2373_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
return v___x_2373_;
}
}
}
}
else
{
lean_object* v_a_2376_; lean_object* v___x_2378_; uint8_t v_isShared_2379_; uint8_t v_isSharedCheck_2383_; 
lean_dec_ref(v___y_2343_);
lean_dec_ref(v___x_2341_);
v_a_2376_ = lean_ctor_get(v___x_2346_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2346_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2346_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2346_);
v___x_2378_ = lean_box(0);
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
v_resetjp_2377_:
{
lean_object* v___x_2381_; 
if (v_isShared_2379_ == 0)
{
v___x_2381_ = v___x_2378_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2382_; 
v_reuseFailAlloc_2382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2382_, 0, v_a_2376_);
v___x_2381_ = v_reuseFailAlloc_2382_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
return v___x_2381_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object* v_fst_2395_, lean_object* v_fst_2396_, lean_object* v_argVars_2397_, lean_object* v_snd_2398_, lean_object* v_next_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v_res_2405_; 
v_res_2405_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2395_, v_fst_2396_, v_argVars_2397_, v_snd_2398_, v_next_2399_, v___y_2400_, v___y_2401_, v___y_2402_, v___y_2403_);
lean_dec(v___y_2403_);
lean_dec_ref(v___y_2402_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v_snd_2398_);
lean_dec_ref(v_argVars_2397_);
lean_dec_ref(v_fst_2396_);
return v_res_2405_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_){
_start:
{
lean_object* v___x_2412_; lean_object* v_env_2413_; lean_object* v___x_2414_; lean_object* v_mctx_2415_; lean_object* v_lctx_2416_; lean_object* v_options_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
v___x_2412_ = lean_st_ref_get(v___y_2410_);
v_env_2413_ = lean_ctor_get(v___x_2412_, 0);
lean_inc_ref(v_env_2413_);
lean_dec(v___x_2412_);
v___x_2414_ = lean_st_ref_get(v___y_2408_);
v_mctx_2415_ = lean_ctor_get(v___x_2414_, 0);
lean_inc_ref(v_mctx_2415_);
lean_dec(v___x_2414_);
v_lctx_2416_ = lean_ctor_get(v___y_2407_, 2);
v_options_2417_ = lean_ctor_get(v___y_2409_, 2);
lean_inc_ref(v_options_2417_);
lean_inc_ref(v_lctx_2416_);
v___x_2418_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2418_, 0, v_env_2413_);
lean_ctor_set(v___x_2418_, 1, v_mctx_2415_);
lean_ctor_set(v___x_2418_, 2, v_lctx_2416_);
lean_ctor_set(v___x_2418_, 3, v_options_2417_);
v___x_2419_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
lean_ctor_set(v___x_2419_, 1, v_msgData_2406_);
v___x_2420_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
return v___x_2420_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_res_2427_; 
v_res_2427_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2421_, v___y_2422_, v___y_2423_, v___y_2424_, v___y_2425_);
lean_dec(v___y_2425_);
lean_dec_ref(v___y_2424_);
lean_dec(v___y_2423_);
lean_dec_ref(v___y_2422_);
return v_res_2427_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_){
_start:
{
lean_object* v_ref_2434_; lean_object* v___x_2435_; lean_object* v_a_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2444_; 
v_ref_2434_ = lean_ctor_get(v___y_2431_, 5);
v___x_2435_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2428_, v___y_2429_, v___y_2430_, v___y_2431_, v___y_2432_);
v_a_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2444_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2444_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_a_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2444_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2440_; lean_object* v___x_2442_; 
lean_inc(v_ref_2434_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v_ref_2434_);
lean_ctor_set(v___x_2440_, 1, v_a_2436_);
if (v_isShared_2439_ == 0)
{
lean_ctor_set_tag(v___x_2438_, 1);
lean_ctor_set(v___x_2438_, 0, v___x_2440_);
v___x_2442_ = v___x_2438_;
goto v_reusejp_2441_;
}
else
{
lean_object* v_reuseFailAlloc_2443_; 
v_reuseFailAlloc_2443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2443_, 0, v___x_2440_);
v___x_2442_ = v_reuseFailAlloc_2443_;
goto v_reusejp_2441_;
}
v_reusejp_2441_:
{
return v___x_2442_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_){
_start:
{
lean_object* v_res_2451_; 
v_res_2451_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2445_, v___y_2446_, v___y_2447_, v___y_2448_, v___y_2449_);
lean_dec(v___y_2449_);
lean_dec_ref(v___y_2448_);
lean_dec(v___y_2447_);
lean_dec_ref(v___y_2446_);
return v_res_2451_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2452_, size_t v_sz_2453_, size_t v_i_2454_, lean_object* v_bs_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_){
_start:
{
uint8_t v___x_2461_; 
v___x_2461_ = lean_usize_dec_lt(v_i_2454_, v_sz_2453_);
if (v___x_2461_ == 0)
{
lean_object* v___x_2462_; 
v___x_2462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2462_, 0, v_bs_2455_);
return v___x_2462_;
}
else
{
lean_object* v_v_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_v_2463_ = lean_array_uget_borrowed(v_bs_2455_, v_i_2454_);
v___x_2464_ = l_Lean_instInhabitedExpr;
v___x_2465_ = lean_array_get_borrowed(v___x_2464_, v_fst_2452_, v_v_2463_);
lean_inc(v___y_2459_);
lean_inc_ref(v___y_2458_);
lean_inc(v___y_2457_);
lean_inc_ref(v___y_2456_);
lean_inc(v___x_2465_);
v___x_2466_ = lean_infer_type(v___x_2465_, v___y_2456_, v___y_2457_, v___y_2458_, v___y_2459_);
if (lean_obj_tag(v___x_2466_) == 0)
{
lean_object* v_a_2467_; lean_object* v___x_2468_; 
v_a_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_a_2467_);
lean_dec_ref_known(v___x_2466_, 1);
v___x_2468_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2467_, v___y_2457_);
if (lean_obj_tag(v___x_2468_) == 0)
{
lean_object* v_a_2469_; lean_object* v___x_2470_; lean_object* v_bs_x27_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; size_t v___x_2474_; size_t v___x_2475_; lean_object* v___x_2476_; 
v_a_2469_ = lean_ctor_get(v___x_2468_, 0);
lean_inc(v_a_2469_);
lean_dec_ref_known(v___x_2468_, 1);
v___x_2470_ = lean_unsigned_to_nat(0u);
v_bs_x27_2471_ = lean_array_uset(v_bs_2455_, v_i_2454_, v___x_2470_);
v___x_2472_ = l_Lean_Expr_setPPExplicit(v_a_2469_, v___x_2461_);
v___x_2473_ = l_Lean_indentExpr(v___x_2472_);
v___x_2474_ = ((size_t)1ULL);
v___x_2475_ = lean_usize_add(v_i_2454_, v___x_2474_);
v___x_2476_ = lean_array_uset(v_bs_x27_2471_, v_i_2454_, v___x_2473_);
v_i_2454_ = v___x_2475_;
v_bs_2455_ = v___x_2476_;
goto _start;
}
else
{
lean_object* v_a_2478_; lean_object* v___x_2480_; uint8_t v_isShared_2481_; uint8_t v_isSharedCheck_2485_; 
lean_dec_ref(v_bs_2455_);
v_a_2478_ = lean_ctor_get(v___x_2468_, 0);
v_isSharedCheck_2485_ = !lean_is_exclusive(v___x_2468_);
if (v_isSharedCheck_2485_ == 0)
{
v___x_2480_ = v___x_2468_;
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
else
{
lean_inc(v_a_2478_);
lean_dec(v___x_2468_);
v___x_2480_ = lean_box(0);
v_isShared_2481_ = v_isSharedCheck_2485_;
goto v_resetjp_2479_;
}
v_resetjp_2479_:
{
lean_object* v___x_2483_; 
if (v_isShared_2481_ == 0)
{
v___x_2483_ = v___x_2480_;
goto v_reusejp_2482_;
}
else
{
lean_object* v_reuseFailAlloc_2484_; 
v_reuseFailAlloc_2484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2484_, 0, v_a_2478_);
v___x_2483_ = v_reuseFailAlloc_2484_;
goto v_reusejp_2482_;
}
v_reusejp_2482_:
{
return v___x_2483_;
}
}
}
}
else
{
lean_object* v_a_2486_; lean_object* v___x_2488_; uint8_t v_isShared_2489_; uint8_t v_isSharedCheck_2493_; 
lean_dec_ref(v_bs_2455_);
v_a_2486_ = lean_ctor_get(v___x_2466_, 0);
v_isSharedCheck_2493_ = !lean_is_exclusive(v___x_2466_);
if (v_isSharedCheck_2493_ == 0)
{
v___x_2488_ = v___x_2466_;
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
else
{
lean_inc(v_a_2486_);
lean_dec(v___x_2466_);
v___x_2488_ = lean_box(0);
v_isShared_2489_ = v_isSharedCheck_2493_;
goto v_resetjp_2487_;
}
v_resetjp_2487_:
{
lean_object* v___x_2491_; 
if (v_isShared_2489_ == 0)
{
v___x_2491_ = v___x_2488_;
goto v_reusejp_2490_;
}
else
{
lean_object* v_reuseFailAlloc_2492_; 
v_reuseFailAlloc_2492_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2492_, 0, v_a_2486_);
v___x_2491_ = v_reuseFailAlloc_2492_;
goto v_reusejp_2490_;
}
v_reusejp_2490_:
{
return v___x_2491_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2494_, lean_object* v_sz_2495_, lean_object* v_i_2496_, lean_object* v_bs_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_){
_start:
{
size_t v_sz_boxed_2503_; size_t v_i_boxed_2504_; lean_object* v_res_2505_; 
v_sz_boxed_2503_ = lean_unbox_usize(v_sz_2495_);
lean_dec(v_sz_2495_);
v_i_boxed_2504_ = lean_unbox_usize(v_i_2496_);
lean_dec(v_i_2496_);
v_res_2505_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2494_, v_sz_boxed_2503_, v_i_boxed_2504_, v_bs_2497_, v___y_2498_, v___y_2499_, v___y_2500_, v___y_2501_);
lean_dec(v___y_2501_);
lean_dec_ref(v___y_2500_);
lean_dec(v___y_2499_);
lean_dec_ref(v___y_2498_);
lean_dec_ref(v_fst_2494_);
return v_res_2505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object* v_snd_2506_, lean_object* v___f_2507_, lean_object* v_____r_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_){
_start:
{
lean_object* v___x_2514_; lean_object* v___x_2515_; lean_object* v___x_2516_; 
v___x_2514_ = lean_unsigned_to_nat(0u);
v___x_2515_ = lean_array_get_borrowed(v___x_2514_, v_snd_2506_, v___x_2514_);
lean_inc(v___y_2512_);
lean_inc_ref(v___y_2511_);
lean_inc(v___y_2510_);
lean_inc_ref(v___y_2509_);
lean_inc(v___x_2515_);
v___x_2516_ = lean_apply_6(v___f_2507_, v___x_2515_, v___y_2509_, v___y_2510_, v___y_2511_, v___y_2512_, lean_box(0));
return v___x_2516_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object* v_snd_2517_, lean_object* v___f_2518_, lean_object* v_____r_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_){
_start:
{
lean_object* v_res_2525_; 
v_res_2525_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2517_, v___f_2518_, v_____r_2519_, v___y_2520_, v___y_2521_, v___y_2522_, v___y_2523_);
lean_dec(v___y_2523_);
lean_dec_ref(v___y_2522_);
lean_dec(v___y_2521_);
lean_dec_ref(v___y_2520_);
lean_dec(v_snd_2517_);
return v_res_2525_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2529_; lean_object* v___x_2530_; 
v___x_2529_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1));
v___x_2530_ = l_Lean_MessageData_ofFormat(v___x_2529_);
return v___x_2530_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2532_; lean_object* v___x_2533_; 
v___x_2532_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3));
v___x_2533_ = l_Lean_stringToMessageData(v___x_2532_);
return v___x_2533_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2535_; lean_object* v___x_2536_; 
v___x_2535_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5));
v___x_2536_ = l_Lean_stringToMessageData(v___x_2535_);
return v___x_2536_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2538_; lean_object* v___x_2539_; 
v___x_2538_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7));
v___x_2539_ = l_Lean_stringToMessageData(v___x_2538_);
return v___x_2539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(lean_object* v_fst_2540_, lean_object* v_argVars_2541_, lean_object* v_inst_2542_, lean_object* v_a_2543_, lean_object* v_projInfo_x3f_2544_, lean_object* v_a_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_){
_start:
{
lean_object* v___y_2552_; lean_object* v_fst_2572_; lean_object* v_snd_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2649_; 
v_fst_2572_ = lean_ctor_get(v_a_2545_, 0);
v_snd_2573_ = lean_ctor_get(v_a_2545_, 1);
v_isSharedCheck_2649_ = !lean_is_exclusive(v_a_2545_);
if (v_isSharedCheck_2649_ == 0)
{
v___x_2575_ = v_a_2545_;
v_isShared_2576_ = v_isSharedCheck_2649_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_snd_2573_);
lean_inc(v_fst_2572_);
lean_dec(v_a_2545_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2649_;
goto v_resetjp_2574_;
}
v___jp_2551_:
{
if (lean_obj_tag(v___y_2552_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; uint8_t v_isShared_2556_; uint8_t v_isSharedCheck_2563_; 
v_a_2553_ = lean_ctor_get(v___y_2552_, 0);
v_isSharedCheck_2563_ = !lean_is_exclusive(v___y_2552_);
if (v_isSharedCheck_2563_ == 0)
{
v___x_2555_ = v___y_2552_;
v_isShared_2556_ = v_isSharedCheck_2563_;
goto v_resetjp_2554_;
}
else
{
lean_inc(v_a_2553_);
lean_dec(v___y_2552_);
v___x_2555_ = lean_box(0);
v_isShared_2556_ = v_isSharedCheck_2563_;
goto v_resetjp_2554_;
}
v_resetjp_2554_:
{
if (lean_obj_tag(v_a_2553_) == 0)
{
lean_object* v_a_2557_; lean_object* v___x_2559_; 
lean_dec_ref(v_a_2543_);
lean_dec_ref(v_inst_2542_);
lean_dec_ref(v_argVars_2541_);
lean_dec_ref(v_fst_2540_);
v_a_2557_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v_a_2553_, 1);
if (v_isShared_2556_ == 0)
{
lean_ctor_set(v___x_2555_, 0, v_a_2557_);
v___x_2559_ = v___x_2555_;
goto v_reusejp_2558_;
}
else
{
lean_object* v_reuseFailAlloc_2560_; 
v_reuseFailAlloc_2560_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2560_, 0, v_a_2557_);
v___x_2559_ = v_reuseFailAlloc_2560_;
goto v_reusejp_2558_;
}
v_reusejp_2558_:
{
return v___x_2559_;
}
}
else
{
lean_object* v_a_2561_; 
lean_del_object(v___x_2555_);
v_a_2561_ = lean_ctor_get(v_a_2553_, 0);
lean_inc(v_a_2561_);
lean_dec_ref_known(v_a_2553_, 1);
v_a_2545_ = v_a_2561_;
goto _start;
}
}
}
else
{
lean_object* v_a_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2571_; 
lean_dec_ref(v_a_2543_);
lean_dec_ref(v_inst_2542_);
lean_dec_ref(v_argVars_2541_);
lean_dec_ref(v_fst_2540_);
v_a_2564_ = lean_ctor_get(v___y_2552_, 0);
v_isSharedCheck_2571_ = !lean_is_exclusive(v___y_2552_);
if (v_isSharedCheck_2571_ == 0)
{
v___x_2566_ = v___y_2552_;
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_a_2564_);
lean_dec(v___y_2552_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2571_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2569_; 
if (v_isShared_2567_ == 0)
{
v___x_2569_ = v___x_2566_;
goto v_reusejp_2568_;
}
else
{
lean_object* v_reuseFailAlloc_2570_; 
v_reuseFailAlloc_2570_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2570_, 0, v_a_2564_);
v___x_2569_ = v_reuseFailAlloc_2570_;
goto v_reusejp_2568_;
}
v_reusejp_2568_:
{
return v___x_2569_;
}
}
}
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2578_; uint8_t v___x_2579_; 
v___x_2577_ = lean_array_get_size(v_snd_2573_);
v___x_2578_ = lean_unsigned_to_nat(0u);
v___x_2579_ = lean_nat_dec_eq(v___x_2577_, v___x_2578_);
if (v___x_2579_ == 0)
{
lean_object* v___x_2580_; lean_object* v___x_2581_; size_t v_sz_2582_; size_t v___x_2583_; lean_object* v___x_2584_; 
lean_del_object(v___x_2575_);
v___x_2580_ = lean_box(0);
v___x_2581_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2582_ = lean_array_size(v_snd_2573_);
v___x_2583_ = ((size_t)0ULL);
v___x_2584_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2540_, v_projInfo_x3f_2544_, v___x_2577_, v_argVars_2541_, v_snd_2573_, v_sz_2582_, v___x_2583_, v___x_2581_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
if (lean_obj_tag(v___x_2584_) == 0)
{
lean_object* v_a_2585_; lean_object* v_fst_2586_; lean_object* v___x_2588_; uint8_t v_isShared_2589_; uint8_t v_isSharedCheck_2635_; 
v_a_2585_ = lean_ctor_get(v___x_2584_, 0);
lean_inc(v_a_2585_);
lean_dec_ref_known(v___x_2584_, 1);
v_fst_2586_ = lean_ctor_get(v_a_2585_, 0);
v_isSharedCheck_2635_ = !lean_is_exclusive(v_a_2585_);
if (v_isSharedCheck_2635_ == 0)
{
lean_object* v_unused_2636_; 
v_unused_2636_ = lean_ctor_get(v_a_2585_, 1);
lean_dec(v_unused_2636_);
v___x_2588_ = v_a_2585_;
v_isShared_2589_ = v_isSharedCheck_2635_;
goto v_resetjp_2587_;
}
else
{
lean_inc(v_fst_2586_);
lean_dec(v_a_2585_);
v___x_2588_ = lean_box(0);
v_isShared_2589_ = v_isSharedCheck_2635_;
goto v_resetjp_2587_;
}
v_resetjp_2587_:
{
lean_object* v___f_2590_; 
lean_inc(v_snd_2573_);
lean_inc_ref(v_argVars_2541_);
lean_inc_ref(v_fst_2540_);
lean_inc(v_fst_2572_);
v___f_2590_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2590_, 0, v_fst_2572_);
lean_closure_set(v___f_2590_, 1, v_fst_2540_);
lean_closure_set(v___f_2590_, 2, v_argVars_2541_);
lean_closure_set(v___f_2590_, 3, v_snd_2573_);
if (lean_obj_tag(v_fst_2586_) == 0)
{
lean_dec(v_fst_2572_);
goto v___jp_2591_;
}
else
{
lean_object* v_val_2632_; 
v_val_2632_ = lean_ctor_get(v_fst_2586_, 0);
lean_inc(v_val_2632_);
lean_dec_ref_known(v_fst_2586_, 1);
if (lean_obj_tag(v_val_2632_) == 0)
{
lean_dec(v_fst_2572_);
goto v___jp_2591_;
}
else
{
lean_object* v_val_2633_; lean_object* v___x_2634_; 
lean_dec_ref(v___f_2590_);
lean_del_object(v___x_2588_);
v_val_2633_ = lean_ctor_get(v_val_2632_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v_val_2632_, 1);
v___x_2634_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2572_, v_fst_2540_, v_argVars_2541_, v_snd_2573_, v_val_2633_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v_snd_2573_);
v___y_2552_ = v___x_2634_;
goto v___jp_2551_;
}
}
v___jp_2591_:
{
lean_object* v_options_2592_; lean_object* v___x_2593_; uint8_t v___x_2594_; 
v_options_2592_ = lean_ctor_get(v___y_2548_, 2);
v___x_2593_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2594_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2592_, v___x_2593_);
if (v___x_2594_ == 0)
{
lean_object* v___x_2595_; 
lean_del_object(v___x_2588_);
v___x_2595_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2573_, v___f_2590_, v___x_2580_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v_snd_2573_);
v___y_2552_ = v___x_2595_;
goto v___jp_2551_;
}
else
{
lean_object* v___x_2596_; 
lean_inc(v_snd_2573_);
v___x_2596_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2540_, v_sz_2582_, v___x_2583_, v_snd_2573_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v_a_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2604_; 
v_a_2597_ = lean_ctor_get(v___x_2596_, 0);
lean_inc(v_a_2597_);
lean_dec_ref_known(v___x_2596_, 1);
v___x_2598_ = lean_array_to_list(v_a_2597_);
v___x_2599_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2600_ = l_Lean_MessageData_joinSep(v___x_2598_, v___x_2599_);
v___x_2601_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4);
lean_inc_ref(v_inst_2542_);
v___x_2602_ = l_Lean_MessageData_ofExpr(v_inst_2542_);
if (v_isShared_2589_ == 0)
{
lean_ctor_set_tag(v___x_2588_, 7);
lean_ctor_set(v___x_2588_, 1, v___x_2602_);
lean_ctor_set(v___x_2588_, 0, v___x_2601_);
v___x_2604_ = v___x_2588_;
goto v_reusejp_2603_;
}
else
{
lean_object* v_reuseFailAlloc_2623_; 
v_reuseFailAlloc_2623_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2623_, 0, v___x_2601_);
lean_ctor_set(v_reuseFailAlloc_2623_, 1, v___x_2602_);
v___x_2604_ = v_reuseFailAlloc_2623_;
goto v_reusejp_2603_;
}
v_reusejp_2603_:
{
lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; 
v___x_2605_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6);
v___x_2606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2606_, 0, v___x_2604_);
lean_ctor_set(v___x_2606_, 1, v___x_2605_);
lean_inc_ref(v_a_2543_);
v___x_2607_ = l_Lean_indentExpr(v_a_2543_);
v___x_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2606_);
lean_ctor_set(v___x_2608_, 1, v___x_2607_);
v___x_2609_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2608_);
lean_ctor_set(v___x_2610_, 1, v___x_2609_);
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2610_);
lean_ctor_set(v___x_2611_, 1, v___x_2600_);
v___x_2612_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2611_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
if (lean_obj_tag(v___x_2612_) == 0)
{
lean_object* v_a_2613_; lean_object* v___x_2614_; 
v_a_2613_ = lean_ctor_get(v___x_2612_, 0);
lean_inc(v_a_2613_);
lean_dec_ref_known(v___x_2612_, 1);
v___x_2614_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2573_, v___f_2590_, v_a_2613_, v___y_2546_, v___y_2547_, v___y_2548_, v___y_2549_);
lean_dec(v_snd_2573_);
v___y_2552_ = v___x_2614_;
goto v___jp_2551_;
}
else
{
lean_object* v_a_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2622_; 
lean_dec_ref(v___f_2590_);
lean_dec(v_snd_2573_);
lean_dec_ref(v_a_2543_);
lean_dec_ref(v_inst_2542_);
lean_dec_ref(v_argVars_2541_);
lean_dec_ref(v_fst_2540_);
v_a_2615_ = lean_ctor_get(v___x_2612_, 0);
v_isSharedCheck_2622_ = !lean_is_exclusive(v___x_2612_);
if (v_isSharedCheck_2622_ == 0)
{
v___x_2617_ = v___x_2612_;
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
else
{
lean_inc(v_a_2615_);
lean_dec(v___x_2612_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2622_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2620_; 
if (v_isShared_2618_ == 0)
{
v___x_2620_ = v___x_2617_;
goto v_reusejp_2619_;
}
else
{
lean_object* v_reuseFailAlloc_2621_; 
v_reuseFailAlloc_2621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2621_, 0, v_a_2615_);
v___x_2620_ = v_reuseFailAlloc_2621_;
goto v_reusejp_2619_;
}
v_reusejp_2619_:
{
return v___x_2620_;
}
}
}
}
}
else
{
lean_object* v_a_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2631_; 
lean_dec_ref(v___f_2590_);
lean_del_object(v___x_2588_);
lean_dec(v_snd_2573_);
lean_dec_ref(v_a_2543_);
lean_dec_ref(v_inst_2542_);
lean_dec_ref(v_argVars_2541_);
lean_dec_ref(v_fst_2540_);
v_a_2624_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2631_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2631_ == 0)
{
v___x_2626_ = v___x_2596_;
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_a_2624_);
lean_dec(v___x_2596_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2631_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2629_; 
if (v_isShared_2627_ == 0)
{
v___x_2629_ = v___x_2626_;
goto v_reusejp_2628_;
}
else
{
lean_object* v_reuseFailAlloc_2630_; 
v_reuseFailAlloc_2630_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2630_, 0, v_a_2624_);
v___x_2629_ = v_reuseFailAlloc_2630_;
goto v_reusejp_2628_;
}
v_reusejp_2628_:
{
return v___x_2629_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2637_; lean_object* v___x_2639_; uint8_t v_isShared_2640_; uint8_t v_isSharedCheck_2644_; 
lean_dec(v_snd_2573_);
lean_dec(v_fst_2572_);
lean_dec_ref(v_a_2543_);
lean_dec_ref(v_inst_2542_);
lean_dec_ref(v_argVars_2541_);
lean_dec_ref(v_fst_2540_);
v_a_2637_ = lean_ctor_get(v___x_2584_, 0);
v_isSharedCheck_2644_ = !lean_is_exclusive(v___x_2584_);
if (v_isSharedCheck_2644_ == 0)
{
v___x_2639_ = v___x_2584_;
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
else
{
lean_inc(v_a_2637_);
lean_dec(v___x_2584_);
v___x_2639_ = lean_box(0);
v_isShared_2640_ = v_isSharedCheck_2644_;
goto v_resetjp_2638_;
}
v_resetjp_2638_:
{
lean_object* v___x_2642_; 
if (v_isShared_2640_ == 0)
{
v___x_2642_ = v___x_2639_;
goto v_reusejp_2641_;
}
else
{
lean_object* v_reuseFailAlloc_2643_; 
v_reuseFailAlloc_2643_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2643_, 0, v_a_2637_);
v___x_2642_ = v_reuseFailAlloc_2643_;
goto v_reusejp_2641_;
}
v_reusejp_2641_:
{
return v___x_2642_;
}
}
}
}
else
{
lean_object* v___x_2646_; 
lean_dec_ref(v_a_2543_);
lean_dec_ref(v_inst_2542_);
lean_dec_ref(v_argVars_2541_);
lean_dec_ref(v_fst_2540_);
if (v_isShared_2576_ == 0)
{
v___x_2646_ = v___x_2575_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2648_; 
v_reuseFailAlloc_2648_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2648_, 0, v_fst_2572_);
lean_ctor_set(v_reuseFailAlloc_2648_, 1, v_snd_2573_);
v___x_2646_ = v_reuseFailAlloc_2648_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
lean_object* v___x_2647_; 
v___x_2647_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2647_, 0, v___x_2646_);
return v___x_2647_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___boxed(lean_object* v_fst_2650_, lean_object* v_argVars_2651_, lean_object* v_inst_2652_, lean_object* v_a_2653_, lean_object* v_projInfo_x3f_2654_, lean_object* v_a_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_){
_start:
{
lean_object* v_res_2661_; 
v_res_2661_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2650_, v_argVars_2651_, v_inst_2652_, v_a_2653_, v_projInfo_x3f_2654_, v_a_2655_, v___y_2656_, v___y_2657_, v___y_2658_, v___y_2659_);
lean_dec(v___y_2659_);
lean_dec_ref(v___y_2658_);
lean_dec(v___y_2657_);
lean_dec_ref(v___y_2656_);
lean_dec(v_projInfo_x3f_2654_);
return v_res_2661_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2662_, lean_object* v_a_2663_, lean_object* v_a_2664_){
_start:
{
if (lean_obj_tag(v_a_2663_) == 0)
{
lean_object* v___x_2665_; 
v___x_2665_ = l_List_reverse___redArg(v_a_2664_);
return v___x_2665_;
}
else
{
lean_object* v_head_2666_; lean_object* v_tail_2667_; lean_object* v___x_2669_; uint8_t v_isShared_2670_; uint8_t v_isSharedCheck_2682_; 
v_head_2666_ = lean_ctor_get(v_a_2663_, 0);
v_tail_2667_ = lean_ctor_get(v_a_2663_, 1);
v_isSharedCheck_2682_ = !lean_is_exclusive(v_a_2663_);
if (v_isSharedCheck_2682_ == 0)
{
v___x_2669_ = v_a_2663_;
v_isShared_2670_ = v_isSharedCheck_2682_;
goto v_resetjp_2668_;
}
else
{
lean_inc(v_tail_2667_);
lean_inc(v_head_2666_);
lean_dec(v_a_2663_);
v___x_2669_ = lean_box(0);
v_isShared_2670_ = v_isSharedCheck_2682_;
goto v_resetjp_2668_;
}
v_resetjp_2668_:
{
uint8_t v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; uint8_t v___x_2675_; uint8_t v___x_2676_; 
v___x_2671_ = 0;
v___x_2672_ = lean_box(v___x_2671_);
v___x_2673_ = lean_array_get(v___x_2672_, v_fst_2662_, v_head_2666_);
lean_dec(v___x_2672_);
v___x_2674_ = 3;
v___x_2675_ = lean_unbox(v___x_2673_);
lean_dec(v___x_2673_);
v___x_2676_ = l_Lean_instBEqBinderInfo_beq(v___x_2675_, v___x_2674_);
if (v___x_2676_ == 0)
{
lean_del_object(v___x_2669_);
lean_dec(v_head_2666_);
v_a_2663_ = v_tail_2667_;
goto _start;
}
else
{
lean_object* v___x_2679_; 
if (v_isShared_2670_ == 0)
{
lean_ctor_set(v___x_2669_, 1, v_a_2664_);
v___x_2679_ = v___x_2669_;
goto v_reusejp_2678_;
}
else
{
lean_object* v_reuseFailAlloc_2681_; 
v_reuseFailAlloc_2681_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2681_, 0, v_head_2666_);
lean_ctor_set(v_reuseFailAlloc_2681_, 1, v_a_2664_);
v___x_2679_ = v_reuseFailAlloc_2681_;
goto v_reusejp_2678_;
}
v_reusejp_2678_:
{
v_a_2663_ = v_tail_2667_;
v_a_2664_ = v___x_2679_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2683_, lean_object* v_a_2684_, lean_object* v_a_2685_){
_start:
{
lean_object* v_res_2686_; 
v_res_2686_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2683_, v_a_2684_, v_a_2685_);
lean_dec_ref(v_fst_2683_);
return v_res_2686_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2687_, size_t v_sz_2688_, size_t v_i_2689_, lean_object* v_bs_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_){
_start:
{
uint8_t v___x_2696_; 
v___x_2696_ = lean_usize_dec_lt(v_i_2689_, v_sz_2688_);
if (v___x_2696_ == 0)
{
lean_object* v___x_2697_; 
v___x_2697_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2697_, 0, v_bs_2690_);
return v___x_2697_;
}
else
{
lean_object* v_v_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_v_2698_ = lean_array_uget_borrowed(v_bs_2690_, v_i_2689_);
v___x_2699_ = l_Lean_instInhabitedExpr;
v___x_2700_ = lean_array_get_borrowed(v___x_2699_, v_argVars_2687_, v_v_2698_);
lean_inc(v___y_2694_);
lean_inc_ref(v___y_2693_);
lean_inc(v___y_2692_);
lean_inc_ref(v___y_2691_);
lean_inc(v___x_2700_);
v___x_2701_ = lean_infer_type(v___x_2700_, v___y_2691_, v___y_2692_, v___y_2693_, v___y_2694_);
if (lean_obj_tag(v___x_2701_) == 0)
{
lean_object* v_a_2702_; lean_object* v___x_2703_; lean_object* v_bs_x27_2704_; lean_object* v___x_2705_; size_t v___x_2706_; size_t v___x_2707_; lean_object* v___x_2708_; 
v_a_2702_ = lean_ctor_get(v___x_2701_, 0);
lean_inc(v_a_2702_);
lean_dec_ref_known(v___x_2701_, 1);
v___x_2703_ = lean_unsigned_to_nat(0u);
v_bs_x27_2704_ = lean_array_uset(v_bs_2690_, v_i_2689_, v___x_2703_);
v___x_2705_ = l_Lean_indentExpr(v_a_2702_);
v___x_2706_ = ((size_t)1ULL);
v___x_2707_ = lean_usize_add(v_i_2689_, v___x_2706_);
v___x_2708_ = lean_array_uset(v_bs_x27_2704_, v_i_2689_, v___x_2705_);
v_i_2689_ = v___x_2707_;
v_bs_2690_ = v___x_2708_;
goto _start;
}
else
{
lean_object* v_a_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2717_; 
lean_dec_ref(v_bs_2690_);
v_a_2710_ = lean_ctor_get(v___x_2701_, 0);
v_isSharedCheck_2717_ = !lean_is_exclusive(v___x_2701_);
if (v_isSharedCheck_2717_ == 0)
{
v___x_2712_ = v___x_2701_;
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_a_2710_);
lean_dec(v___x_2701_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2717_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v___x_2715_; 
if (v_isShared_2713_ == 0)
{
v___x_2715_ = v___x_2712_;
goto v_reusejp_2714_;
}
else
{
lean_object* v_reuseFailAlloc_2716_; 
v_reuseFailAlloc_2716_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2716_, 0, v_a_2710_);
v___x_2715_ = v_reuseFailAlloc_2716_;
goto v_reusejp_2714_;
}
v_reusejp_2714_:
{
return v___x_2715_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2718_, lean_object* v_sz_2719_, lean_object* v_i_2720_, lean_object* v_bs_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_){
_start:
{
size_t v_sz_boxed_2727_; size_t v_i_boxed_2728_; lean_object* v_res_2729_; 
v_sz_boxed_2727_ = lean_unbox_usize(v_sz_2719_);
lean_dec(v_sz_2719_);
v_i_boxed_2728_ = lean_unbox_usize(v_i_2720_);
lean_dec(v_i_2720_);
v_res_2729_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2718_, v_sz_boxed_2727_, v_i_boxed_2728_, v_bs_2721_, v___y_2722_, v___y_2723_, v___y_2724_, v___y_2725_);
lean_dec(v___y_2725_);
lean_dec_ref(v___y_2724_);
lean_dec(v___y_2723_);
lean_dec_ref(v___y_2722_);
lean_dec_ref(v_argVars_2718_);
return v_res_2729_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2730_, lean_object* v_a_2731_){
_start:
{
if (lean_obj_tag(v_a_2730_) == 0)
{
lean_object* v___x_2732_; 
v___x_2732_ = l_List_reverse___redArg(v_a_2731_);
return v___x_2732_;
}
else
{
lean_object* v_head_2733_; lean_object* v_tail_2734_; lean_object* v___x_2736_; uint8_t v_isShared_2737_; uint8_t v_isSharedCheck_2745_; 
v_head_2733_ = lean_ctor_get(v_a_2730_, 0);
v_tail_2734_ = lean_ctor_get(v_a_2730_, 1);
v_isSharedCheck_2745_ = !lean_is_exclusive(v_a_2730_);
if (v_isSharedCheck_2745_ == 0)
{
v___x_2736_ = v_a_2730_;
v_isShared_2737_ = v_isSharedCheck_2745_;
goto v_resetjp_2735_;
}
else
{
lean_inc(v_tail_2734_);
lean_inc(v_head_2733_);
lean_dec(v_a_2730_);
v___x_2736_ = lean_box(0);
v_isShared_2737_ = v_isSharedCheck_2745_;
goto v_resetjp_2735_;
}
v_resetjp_2735_:
{
lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2742_; 
v___x_2738_ = l_Nat_reprFast(v_head_2733_);
v___x_2739_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2739_, 0, v___x_2738_);
v___x_2740_ = l_Lean_MessageData_ofFormat(v___x_2739_);
if (v_isShared_2737_ == 0)
{
lean_ctor_set(v___x_2736_, 1, v_a_2731_);
lean_ctor_set(v___x_2736_, 0, v___x_2740_);
v___x_2742_ = v___x_2736_;
goto v_reusejp_2741_;
}
else
{
lean_object* v_reuseFailAlloc_2744_; 
v_reuseFailAlloc_2744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2744_, 0, v___x_2740_);
lean_ctor_set(v_reuseFailAlloc_2744_, 1, v_a_2731_);
v___x_2742_ = v_reuseFailAlloc_2744_;
goto v_reusejp_2741_;
}
v_reusejp_2741_:
{
v_a_2730_ = v_tail_2734_;
v_a_2731_ = v___x_2742_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2746_; double v___x_2747_; 
v___x_2746_ = lean_unsigned_to_nat(0u);
v___x_2747_ = lean_float_of_nat(v___x_2746_);
return v___x_2747_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2750_, lean_object* v_msg_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_){
_start:
{
lean_object* v_ref_2757_; lean_object* v___x_2758_; lean_object* v_a_2759_; lean_object* v___x_2761_; uint8_t v_isShared_2762_; uint8_t v_isSharedCheck_2803_; 
v_ref_2757_ = lean_ctor_get(v___y_2754_, 5);
v___x_2758_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
v_a_2759_ = lean_ctor_get(v___x_2758_, 0);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2758_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2761_ = v___x_2758_;
v_isShared_2762_ = v_isSharedCheck_2803_;
goto v_resetjp_2760_;
}
else
{
lean_inc(v_a_2759_);
lean_dec(v___x_2758_);
v___x_2761_ = lean_box(0);
v_isShared_2762_ = v_isSharedCheck_2803_;
goto v_resetjp_2760_;
}
v_resetjp_2760_:
{
lean_object* v___x_2763_; lean_object* v_traceState_2764_; lean_object* v_env_2765_; lean_object* v_nextMacroScope_2766_; lean_object* v_ngen_2767_; lean_object* v_auxDeclNGen_2768_; lean_object* v_cache_2769_; lean_object* v_messages_2770_; lean_object* v_infoState_2771_; lean_object* v_snapshotTasks_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2802_; 
v___x_2763_ = lean_st_ref_take(v___y_2755_);
v_traceState_2764_ = lean_ctor_get(v___x_2763_, 4);
v_env_2765_ = lean_ctor_get(v___x_2763_, 0);
v_nextMacroScope_2766_ = lean_ctor_get(v___x_2763_, 1);
v_ngen_2767_ = lean_ctor_get(v___x_2763_, 2);
v_auxDeclNGen_2768_ = lean_ctor_get(v___x_2763_, 3);
v_cache_2769_ = lean_ctor_get(v___x_2763_, 5);
v_messages_2770_ = lean_ctor_get(v___x_2763_, 6);
v_infoState_2771_ = lean_ctor_get(v___x_2763_, 7);
v_snapshotTasks_2772_ = lean_ctor_get(v___x_2763_, 8);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2763_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2774_ = v___x_2763_;
v_isShared_2775_ = v_isSharedCheck_2802_;
goto v_resetjp_2773_;
}
else
{
lean_inc(v_snapshotTasks_2772_);
lean_inc(v_infoState_2771_);
lean_inc(v_messages_2770_);
lean_inc(v_cache_2769_);
lean_inc(v_traceState_2764_);
lean_inc(v_auxDeclNGen_2768_);
lean_inc(v_ngen_2767_);
lean_inc(v_nextMacroScope_2766_);
lean_inc(v_env_2765_);
lean_dec(v___x_2763_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2802_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
uint64_t v_tid_2776_; lean_object* v_traces_2777_; lean_object* v___x_2779_; uint8_t v_isShared_2780_; uint8_t v_isSharedCheck_2801_; 
v_tid_2776_ = lean_ctor_get_uint64(v_traceState_2764_, sizeof(void*)*1);
v_traces_2777_ = lean_ctor_get(v_traceState_2764_, 0);
v_isSharedCheck_2801_ = !lean_is_exclusive(v_traceState_2764_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2779_ = v_traceState_2764_;
v_isShared_2780_ = v_isSharedCheck_2801_;
goto v_resetjp_2778_;
}
else
{
lean_inc(v_traces_2777_);
lean_dec(v_traceState_2764_);
v___x_2779_ = lean_box(0);
v_isShared_2780_ = v_isSharedCheck_2801_;
goto v_resetjp_2778_;
}
v_resetjp_2778_:
{
lean_object* v___x_2781_; double v___x_2782_; uint8_t v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2791_; 
v___x_2781_ = lean_box(0);
v___x_2782_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2783_ = 0;
v___x_2784_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___x_2785_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2785_, 0, v_cls_2750_);
lean_ctor_set(v___x_2785_, 1, v___x_2781_);
lean_ctor_set(v___x_2785_, 2, v___x_2784_);
lean_ctor_set_float(v___x_2785_, sizeof(void*)*3, v___x_2782_);
lean_ctor_set_float(v___x_2785_, sizeof(void*)*3 + 8, v___x_2782_);
lean_ctor_set_uint8(v___x_2785_, sizeof(void*)*3 + 16, v___x_2783_);
v___x_2786_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2787_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2787_, 0, v___x_2785_);
lean_ctor_set(v___x_2787_, 1, v_a_2759_);
lean_ctor_set(v___x_2787_, 2, v___x_2786_);
lean_inc(v_ref_2757_);
v___x_2788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2788_, 0, v_ref_2757_);
lean_ctor_set(v___x_2788_, 1, v___x_2787_);
v___x_2789_ = l_Lean_PersistentArray_push___redArg(v_traces_2777_, v___x_2788_);
if (v_isShared_2780_ == 0)
{
lean_ctor_set(v___x_2779_, 0, v___x_2789_);
v___x_2791_ = v___x_2779_;
goto v_reusejp_2790_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v___x_2789_);
lean_ctor_set_uint64(v_reuseFailAlloc_2800_, sizeof(void*)*1, v_tid_2776_);
v___x_2791_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2790_;
}
v_reusejp_2790_:
{
lean_object* v___x_2793_; 
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 4, v___x_2791_);
v___x_2793_ = v___x_2774_;
goto v_reusejp_2792_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_env_2765_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v_nextMacroScope_2766_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_ngen_2767_);
lean_ctor_set(v_reuseFailAlloc_2799_, 3, v_auxDeclNGen_2768_);
lean_ctor_set(v_reuseFailAlloc_2799_, 4, v___x_2791_);
lean_ctor_set(v_reuseFailAlloc_2799_, 5, v_cache_2769_);
lean_ctor_set(v_reuseFailAlloc_2799_, 6, v_messages_2770_);
lean_ctor_set(v_reuseFailAlloc_2799_, 7, v_infoState_2771_);
lean_ctor_set(v_reuseFailAlloc_2799_, 8, v_snapshotTasks_2772_);
v___x_2793_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2792_;
}
v_reusejp_2792_:
{
lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2797_; 
v___x_2794_ = lean_st_ref_put(v___y_2755_, v___x_2793_);
v___x_2795_ = lean_box(0);
if (v_isShared_2762_ == 0)
{
lean_ctor_set(v___x_2761_, 0, v___x_2795_);
v___x_2797_ = v___x_2761_;
goto v_reusejp_2796_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v___x_2795_);
v___x_2797_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2796_;
}
v_reusejp_2796_:
{
return v___x_2797_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2804_, lean_object* v_msg_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_){
_start:
{
lean_object* v_res_2811_; 
v_res_2811_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2804_, v_msg_2805_, v___y_2806_, v___y_2807_, v___y_2808_, v___y_2809_);
lean_dec(v___y_2809_);
lean_dec_ref(v___y_2808_);
lean_dec(v___y_2807_);
lean_dec_ref(v___y_2806_);
return v_res_2811_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2820_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2821_ = l_Lean_Name_append(v___x_2820_, v___x_2819_);
return v___x_2821_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2824_ = l_Lean_stringToMessageData(v___x_2823_);
return v___x_2824_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2827_ = l_Lean_stringToMessageData(v___x_2826_);
return v___x_2827_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2830_ = l_Lean_stringToMessageData(v___x_2829_);
return v___x_2830_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2832_; lean_object* v___x_2833_; 
v___x_2832_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2833_ = l_Lean_stringToMessageData(v___x_2832_);
return v___x_2833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2834_, lean_object* v_fst_2835_, lean_object* v_fst_2836_, lean_object* v_inst_2837_, lean_object* v_a_2838_, lean_object* v_projInfo_x3f_2839_, lean_object* v_argVars_2840_, lean_object* v_x_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_){
_start:
{
lean_object* v___x_2847_; 
v___x_2847_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2834_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2847_) == 0)
{
lean_object* v_a_2848_; lean_object* v_dummy_2849_; lean_object* v_nargs_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; size_t v_sz_2858_; size_t v___x_2859_; lean_object* v___x_2860_; 
v_a_2848_ = lean_ctor_get(v___x_2847_, 0);
lean_inc(v_a_2848_);
lean_dec_ref_known(v___x_2847_, 1);
v_dummy_2849_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2850_ = l_Lean_Expr_getAppNumArgs(v_a_2834_);
lean_inc(v_nargs_2850_);
v___x_2851_ = lean_mk_array(v_nargs_2850_, v_dummy_2849_);
v___x_2852_ = lean_unsigned_to_nat(1u);
v___x_2853_ = lean_nat_sub(v_nargs_2850_, v___x_2852_);
lean_dec(v_nargs_2850_);
lean_inc_ref(v_a_2834_);
v___x_2854_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2834_, v___x_2851_, v___x_2853_);
v___x_2855_ = lean_array_get_size(v___x_2854_);
v___x_2856_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2857_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2857_, 0, v___x_2856_);
lean_ctor_set(v___x_2857_, 1, v___x_2855_);
v_sz_2858_ = lean_array_size(v___x_2854_);
v___x_2859_ = ((size_t)0ULL);
v___x_2860_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2848_, v_fst_2835_, v_argVars_2840_, v___x_2854_, v_sz_2858_, v___x_2859_, v___x_2857_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
lean_dec_ref(v___x_2854_);
lean_dec(v_a_2848_);
if (lean_obj_tag(v___x_2860_) == 0)
{
lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; 
lean_dec_ref_known(v___x_2860_, 1);
v___x_2861_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2862_ = lean_array_get_size(v_fst_2835_);
v___x_2863_ = l_List_range(v___x_2862_);
v___x_2864_ = lean_box(0);
v___x_2865_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2836_, v___x_2863_, v___x_2864_);
v___x_2866_ = lean_array_mk(v___x_2865_);
v___x_2867_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2867_, 0, v___x_2861_);
lean_ctor_set(v___x_2867_, 1, v___x_2866_);
lean_inc_ref(v_inst_2837_);
lean_inc_ref(v_argVars_2840_);
v___x_2868_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2835_, v_argVars_2840_, v_inst_2837_, v_a_2838_, v_projInfo_x3f_2839_, v___x_2867_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
if (lean_obj_tag(v___x_2868_) == 0)
{
lean_object* v_a_2869_; lean_object* v___x_2871_; uint8_t v_isShared_2872_; uint8_t v_isSharedCheck_2961_; 
v_a_2869_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2961_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2961_ == 0)
{
v___x_2871_ = v___x_2868_;
v_isShared_2872_ = v_isSharedCheck_2961_;
goto v_resetjp_2870_;
}
else
{
lean_inc(v_a_2869_);
lean_dec(v___x_2868_);
v___x_2871_ = lean_box(0);
v_isShared_2872_ = v_isSharedCheck_2961_;
goto v_resetjp_2870_;
}
v_resetjp_2870_:
{
lean_object* v_fst_2873_; lean_object* v___x_2875_; uint8_t v_isShared_2876_; uint8_t v_isSharedCheck_2959_; 
v_fst_2873_ = lean_ctor_get(v_a_2869_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v_a_2869_);
if (v_isSharedCheck_2959_ == 0)
{
lean_object* v_unused_2960_; 
v_unused_2960_ = lean_ctor_get(v_a_2869_, 1);
lean_dec(v_unused_2960_);
v___x_2875_ = v_a_2869_;
v_isShared_2876_ = v_isSharedCheck_2959_;
goto v_resetjp_2874_;
}
else
{
lean_inc(v_fst_2873_);
lean_dec(v_a_2869_);
v___x_2875_ = lean_box(0);
v_isShared_2876_ = v_isSharedCheck_2959_;
goto v_resetjp_2874_;
}
v_resetjp_2874_:
{
lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v_options_2881_; lean_object* v_inheritedTraceOptions_2882_; lean_object* v___y_2883_; lean_object* v_options_2939_; lean_object* v_inheritedTraceOptions_2940_; lean_object* v___x_2941_; uint8_t v___x_2942_; 
v_options_2939_ = lean_ctor_get(v___y_2844_, 2);
v_inheritedTraceOptions_2940_ = lean_ctor_get(v___y_2844_, 13);
v___x_2941_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2942_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2939_, v___x_2941_);
if (v___x_2942_ == 0)
{
lean_dec_ref(v_a_2834_);
v___y_2878_ = v___y_2842_;
v___y_2879_ = v___y_2843_;
v___y_2880_ = v___y_2844_;
v_options_2881_ = v_options_2939_;
v_inheritedTraceOptions_2882_ = v_inheritedTraceOptions_2940_;
v___y_2883_ = v___y_2845_;
goto v___jp_2877_;
}
else
{
lean_object* v___x_2943_; lean_object* v_a_2944_; uint8_t v___x_2945_; 
v___x_2943_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2834_, v___y_2843_);
v_a_2944_ = lean_ctor_get(v___x_2943_, 0);
lean_inc(v_a_2944_);
lean_dec_ref(v___x_2943_);
v___x_2945_ = l_Lean_Expr_hasExprMVar(v_a_2944_);
if (v___x_2945_ == 0)
{
lean_dec(v_a_2944_);
v___y_2878_ = v___y_2842_;
v___y_2879_ = v___y_2843_;
v___y_2880_ = v___y_2844_;
v_options_2881_ = v_options_2939_;
v_inheritedTraceOptions_2882_ = v_inheritedTraceOptions_2940_;
v___y_2883_ = v___y_2845_;
goto v___jp_2877_;
}
else
{
lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v_a_2951_; lean_object* v___x_2953_; uint8_t v_isShared_2954_; uint8_t v_isSharedCheck_2958_; 
lean_del_object(v___x_2875_);
lean_dec(v_fst_2873_);
lean_del_object(v___x_2871_);
lean_dec_ref(v_argVars_2840_);
lean_dec_ref(v_inst_2837_);
v___x_2946_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_2947_ = l_Lean_Expr_setPPExplicit(v_a_2944_, v___x_2945_);
v___x_2948_ = l_Lean_indentExpr(v___x_2947_);
v___x_2949_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2949_, 0, v___x_2946_);
lean_ctor_set(v___x_2949_, 1, v___x_2948_);
v___x_2950_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2949_, v___y_2842_, v___y_2843_, v___y_2844_, v___y_2845_);
v_a_2951_ = lean_ctor_get(v___x_2950_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v___x_2950_);
if (v_isSharedCheck_2958_ == 0)
{
v___x_2953_ = v___x_2950_;
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
else
{
lean_inc(v_a_2951_);
lean_dec(v___x_2950_);
v___x_2953_ = lean_box(0);
v_isShared_2954_ = v_isSharedCheck_2958_;
goto v_resetjp_2952_;
}
v_resetjp_2952_:
{
lean_object* v___x_2956_; 
if (v_isShared_2954_ == 0)
{
v___x_2956_ = v___x_2953_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2957_; 
v_reuseFailAlloc_2957_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2957_, 0, v_a_2951_);
v___x_2956_ = v_reuseFailAlloc_2957_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
return v___x_2956_;
}
}
}
}
v___jp_2877_:
{
uint8_t v_hasTrace_2884_; 
v_hasTrace_2884_ = lean_ctor_get_uint8(v_options_2881_, sizeof(void*)*1);
if (v_hasTrace_2884_ == 0)
{
lean_object* v___x_2886_; 
lean_del_object(v___x_2875_);
lean_dec_ref(v_argVars_2840_);
lean_dec_ref(v_inst_2837_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v_fst_2873_);
v___x_2886_ = v___x_2871_;
goto v_reusejp_2885_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v_fst_2873_);
v___x_2886_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2885_;
}
v_reusejp_2885_:
{
return v___x_2886_;
}
}
else
{
lean_object* v___x_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v___x_2888_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2889_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2890_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2882_, v_options_2881_, v___x_2889_);
if (v___x_2890_ == 0)
{
lean_object* v___x_2892_; 
lean_del_object(v___x_2875_);
lean_dec_ref(v_argVars_2840_);
lean_dec_ref(v_inst_2837_);
if (v_isShared_2872_ == 0)
{
lean_ctor_set(v___x_2871_, 0, v_fst_2873_);
v___x_2892_ = v___x_2871_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2893_; 
v_reuseFailAlloc_2893_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2893_, 0, v_fst_2873_);
v___x_2892_ = v_reuseFailAlloc_2893_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
return v___x_2892_;
}
}
else
{
size_t v_sz_2894_; lean_object* v___x_2895_; 
lean_del_object(v___x_2871_);
v_sz_2894_ = lean_array_size(v_fst_2873_);
lean_inc(v_fst_2873_);
v___x_2895_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2840_, v_sz_2894_, v___x_2859_, v_fst_2873_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2883_);
lean_dec_ref(v_argVars_2840_);
if (lean_obj_tag(v___x_2895_) == 0)
{
lean_object* v_a_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2900_; 
v_a_2896_ = lean_ctor_get(v___x_2895_, 0);
lean_inc(v_a_2896_);
lean_dec_ref_known(v___x_2895_, 1);
v___x_2897_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_2898_ = l_Lean_MessageData_ofExpr(v_inst_2837_);
if (v_isShared_2876_ == 0)
{
lean_ctor_set_tag(v___x_2875_, 7);
lean_ctor_set(v___x_2875_, 1, v___x_2898_);
lean_ctor_set(v___x_2875_, 0, v___x_2897_);
v___x_2900_ = v___x_2875_;
goto v_reusejp_2899_;
}
else
{
lean_object* v_reuseFailAlloc_2930_; 
v_reuseFailAlloc_2930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2930_, 0, v___x_2897_);
lean_ctor_set(v_reuseFailAlloc_2930_, 1, v___x_2898_);
v___x_2900_ = v_reuseFailAlloc_2930_;
goto v_reusejp_2899_;
}
v_reusejp_2899_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; 
v___x_2901_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_2902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2902_, 0, v___x_2900_);
lean_ctor_set(v___x_2902_, 1, v___x_2901_);
lean_inc(v_fst_2873_);
v___x_2903_ = lean_array_to_list(v_fst_2873_);
v___x_2904_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_2903_, v___x_2864_);
v___x_2905_ = l_Lean_MessageData_ofList(v___x_2904_);
v___x_2906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2902_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_2908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2908_, 0, v___x_2906_);
lean_ctor_set(v___x_2908_, 1, v___x_2907_);
v___x_2909_ = lean_array_to_list(v_a_2896_);
v___x_2910_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2911_ = l_Lean_MessageData_joinSep(v___x_2909_, v___x_2910_);
v___x_2912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2912_, 0, v___x_2908_);
lean_ctor_set(v___x_2912_, 1, v___x_2911_);
v___x_2913_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2888_, v___x_2912_, v___y_2878_, v___y_2879_, v___y_2880_, v___y_2883_);
if (lean_obj_tag(v___x_2913_) == 0)
{
lean_object* v___x_2915_; uint8_t v_isShared_2916_; uint8_t v_isSharedCheck_2920_; 
v_isSharedCheck_2920_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2920_ == 0)
{
lean_object* v_unused_2921_; 
v_unused_2921_ = lean_ctor_get(v___x_2913_, 0);
lean_dec(v_unused_2921_);
v___x_2915_ = v___x_2913_;
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
else
{
lean_dec(v___x_2913_);
v___x_2915_ = lean_box(0);
v_isShared_2916_ = v_isSharedCheck_2920_;
goto v_resetjp_2914_;
}
v_resetjp_2914_:
{
lean_object* v___x_2918_; 
if (v_isShared_2916_ == 0)
{
lean_ctor_set(v___x_2915_, 0, v_fst_2873_);
v___x_2918_ = v___x_2915_;
goto v_reusejp_2917_;
}
else
{
lean_object* v_reuseFailAlloc_2919_; 
v_reuseFailAlloc_2919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2919_, 0, v_fst_2873_);
v___x_2918_ = v_reuseFailAlloc_2919_;
goto v_reusejp_2917_;
}
v_reusejp_2917_:
{
return v___x_2918_;
}
}
}
else
{
lean_object* v_a_2922_; lean_object* v___x_2924_; uint8_t v_isShared_2925_; uint8_t v_isSharedCheck_2929_; 
lean_dec(v_fst_2873_);
v_a_2922_ = lean_ctor_get(v___x_2913_, 0);
v_isSharedCheck_2929_ = !lean_is_exclusive(v___x_2913_);
if (v_isSharedCheck_2929_ == 0)
{
v___x_2924_ = v___x_2913_;
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
else
{
lean_inc(v_a_2922_);
lean_dec(v___x_2913_);
v___x_2924_ = lean_box(0);
v_isShared_2925_ = v_isSharedCheck_2929_;
goto v_resetjp_2923_;
}
v_resetjp_2923_:
{
lean_object* v___x_2927_; 
if (v_isShared_2925_ == 0)
{
v___x_2927_ = v___x_2924_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_a_2922_);
v___x_2927_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
return v___x_2927_;
}
}
}
}
}
else
{
lean_object* v_a_2931_; lean_object* v___x_2933_; uint8_t v_isShared_2934_; uint8_t v_isSharedCheck_2938_; 
lean_del_object(v___x_2875_);
lean_dec(v_fst_2873_);
lean_dec_ref(v_inst_2837_);
v_a_2931_ = lean_ctor_get(v___x_2895_, 0);
v_isSharedCheck_2938_ = !lean_is_exclusive(v___x_2895_);
if (v_isSharedCheck_2938_ == 0)
{
v___x_2933_ = v___x_2895_;
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
else
{
lean_inc(v_a_2931_);
lean_dec(v___x_2895_);
v___x_2933_ = lean_box(0);
v_isShared_2934_ = v_isSharedCheck_2938_;
goto v_resetjp_2932_;
}
v_resetjp_2932_:
{
lean_object* v___x_2936_; 
if (v_isShared_2934_ == 0)
{
v___x_2936_ = v___x_2933_;
goto v_reusejp_2935_;
}
else
{
lean_object* v_reuseFailAlloc_2937_; 
v_reuseFailAlloc_2937_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2937_, 0, v_a_2931_);
v___x_2936_ = v_reuseFailAlloc_2937_;
goto v_reusejp_2935_;
}
v_reusejp_2935_:
{
return v___x_2936_;
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
lean_object* v_a_2962_; lean_object* v___x_2964_; uint8_t v_isShared_2965_; uint8_t v_isSharedCheck_2969_; 
lean_dec_ref(v_argVars_2840_);
lean_dec_ref(v_inst_2837_);
lean_dec_ref(v_a_2834_);
v_a_2962_ = lean_ctor_get(v___x_2868_, 0);
v_isSharedCheck_2969_ = !lean_is_exclusive(v___x_2868_);
if (v_isSharedCheck_2969_ == 0)
{
v___x_2964_ = v___x_2868_;
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
else
{
lean_inc(v_a_2962_);
lean_dec(v___x_2868_);
v___x_2964_ = lean_box(0);
v_isShared_2965_ = v_isSharedCheck_2969_;
goto v_resetjp_2963_;
}
v_resetjp_2963_:
{
lean_object* v___x_2967_; 
if (v_isShared_2965_ == 0)
{
v___x_2967_ = v___x_2964_;
goto v_reusejp_2966_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_a_2962_);
v___x_2967_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2966_;
}
v_reusejp_2966_:
{
return v___x_2967_;
}
}
}
}
else
{
lean_object* v_a_2970_; lean_object* v___x_2972_; uint8_t v_isShared_2973_; uint8_t v_isSharedCheck_2977_; 
lean_dec_ref(v_argVars_2840_);
lean_dec_ref(v_a_2838_);
lean_dec_ref(v_inst_2837_);
lean_dec_ref(v_fst_2835_);
lean_dec_ref(v_a_2834_);
v_a_2970_ = lean_ctor_get(v___x_2860_, 0);
v_isSharedCheck_2977_ = !lean_is_exclusive(v___x_2860_);
if (v_isSharedCheck_2977_ == 0)
{
v___x_2972_ = v___x_2860_;
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
else
{
lean_inc(v_a_2970_);
lean_dec(v___x_2860_);
v___x_2972_ = lean_box(0);
v_isShared_2973_ = v_isSharedCheck_2977_;
goto v_resetjp_2971_;
}
v_resetjp_2971_:
{
lean_object* v___x_2975_; 
if (v_isShared_2973_ == 0)
{
v___x_2975_ = v___x_2972_;
goto v_reusejp_2974_;
}
else
{
lean_object* v_reuseFailAlloc_2976_; 
v_reuseFailAlloc_2976_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2976_, 0, v_a_2970_);
v___x_2975_ = v_reuseFailAlloc_2976_;
goto v_reusejp_2974_;
}
v_reusejp_2974_:
{
return v___x_2975_;
}
}
}
}
else
{
lean_dec_ref(v_argVars_2840_);
lean_dec_ref(v_a_2838_);
lean_dec_ref(v_inst_2837_);
lean_dec_ref(v_fst_2835_);
lean_dec_ref(v_a_2834_);
return v___x_2847_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_2978_, lean_object* v_fst_2979_, lean_object* v_fst_2980_, lean_object* v_inst_2981_, lean_object* v_a_2982_, lean_object* v_projInfo_x3f_2983_, lean_object* v_argVars_2984_, lean_object* v_x_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_){
_start:
{
lean_object* v_res_2991_; 
v_res_2991_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_2978_, v_fst_2979_, v_fst_2980_, v_inst_2981_, v_a_2982_, v_projInfo_x3f_2983_, v_argVars_2984_, v_x_2985_, v___y_2986_, v___y_2987_, v___y_2988_, v___y_2989_);
lean_dec(v___y_2989_);
lean_dec_ref(v___y_2988_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec_ref(v_x_2985_);
lean_dec(v_projInfo_x3f_2983_);
lean_dec_ref(v_fst_2980_);
return v_res_2991_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_2992_, lean_object* v_projInfo_x3f_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_){
_start:
{
lean_object* v_keyedConfig_2999_; uint8_t v_trackZetaDelta_3000_; lean_object* v_zetaDeltaSet_3001_; lean_object* v_lctx_3002_; lean_object* v_localInstances_3003_; lean_object* v_defEqCtx_x3f_3004_; lean_object* v_synthPendingDepth_3005_; lean_object* v_customCanUnfoldPredicate_x3f_3006_; uint8_t v_univApprox_3007_; uint8_t v_inTypeClassResolution_3008_; uint8_t v_cacheInferType_3009_; uint8_t v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; 
v_keyedConfig_2999_ = lean_ctor_get(v_a_2994_, 0);
v_trackZetaDelta_3000_ = lean_ctor_get_uint8(v_a_2994_, sizeof(void*)*7);
v_zetaDeltaSet_3001_ = lean_ctor_get(v_a_2994_, 1);
v_lctx_3002_ = lean_ctor_get(v_a_2994_, 2);
v_localInstances_3003_ = lean_ctor_get(v_a_2994_, 3);
v_defEqCtx_x3f_3004_ = lean_ctor_get(v_a_2994_, 4);
v_synthPendingDepth_3005_ = lean_ctor_get(v_a_2994_, 5);
v_customCanUnfoldPredicate_x3f_3006_ = lean_ctor_get(v_a_2994_, 6);
v_univApprox_3007_ = lean_ctor_get_uint8(v_a_2994_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3008_ = lean_ctor_get_uint8(v_a_2994_, sizeof(void*)*7 + 2);
v_cacheInferType_3009_ = lean_ctor_get_uint8(v_a_2994_, sizeof(void*)*7 + 3);
v___x_3010_ = 2;
lean_inc_ref(v_keyedConfig_2999_);
v___x_3011_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3010_, v_keyedConfig_2999_);
lean_inc(v_customCanUnfoldPredicate_x3f_3006_);
lean_inc(v_synthPendingDepth_3005_);
lean_inc(v_defEqCtx_x3f_3004_);
lean_inc_ref(v_localInstances_3003_);
lean_inc_ref(v_lctx_3002_);
lean_inc(v_zetaDeltaSet_3001_);
v___x_3012_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3012_, 0, v___x_3011_);
lean_ctor_set(v___x_3012_, 1, v_zetaDeltaSet_3001_);
lean_ctor_set(v___x_3012_, 2, v_lctx_3002_);
lean_ctor_set(v___x_3012_, 3, v_localInstances_3003_);
lean_ctor_set(v___x_3012_, 4, v_defEqCtx_x3f_3004_);
lean_ctor_set(v___x_3012_, 5, v_synthPendingDepth_3005_);
lean_ctor_set(v___x_3012_, 6, v_customCanUnfoldPredicate_x3f_3006_);
lean_ctor_set_uint8(v___x_3012_, sizeof(void*)*7, v_trackZetaDelta_3000_);
lean_ctor_set_uint8(v___x_3012_, sizeof(void*)*7 + 1, v_univApprox_3007_);
lean_ctor_set_uint8(v___x_3012_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3008_);
lean_ctor_set_uint8(v___x_3012_, sizeof(void*)*7 + 3, v_cacheInferType_3009_);
lean_inc(v_a_2997_);
lean_inc_ref(v_a_2996_);
lean_inc(v_a_2995_);
lean_inc_ref(v___x_3012_);
lean_inc_ref(v_inst_2992_);
v___x_3013_ = lean_infer_type(v_inst_2992_, v___x_3012_, v_a_2995_, v_a_2996_, v_a_2997_);
if (lean_obj_tag(v___x_3013_) == 0)
{
lean_object* v_a_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; lean_object* v___x_3017_; 
v_a_3014_ = lean_ctor_get(v___x_3013_, 0);
lean_inc_n(v_a_3014_, 2);
lean_dec_ref_known(v___x_3013_, 1);
v___x_3015_ = lean_box(0);
v___x_3016_ = 0;
v___x_3017_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3014_, v___x_3015_, v___x_3016_, v___x_3012_, v_a_2995_, v_a_2996_, v_a_2997_);
if (lean_obj_tag(v___x_3017_) == 0)
{
lean_object* v_a_3018_; lean_object* v_snd_3019_; lean_object* v_fst_3020_; lean_object* v_fst_3021_; lean_object* v_snd_3022_; lean_object* v___x_3023_; 
v_a_3018_ = lean_ctor_get(v___x_3017_, 0);
lean_inc(v_a_3018_);
lean_dec_ref_known(v___x_3017_, 1);
v_snd_3019_ = lean_ctor_get(v_a_3018_, 1);
lean_inc(v_snd_3019_);
v_fst_3020_ = lean_ctor_get(v_a_3018_, 0);
lean_inc(v_fst_3020_);
lean_dec(v_a_3018_);
v_fst_3021_ = lean_ctor_get(v_snd_3019_, 0);
lean_inc(v_fst_3021_);
v_snd_3022_ = lean_ctor_get(v_snd_3019_, 1);
lean_inc(v_snd_3022_);
lean_dec(v_snd_3019_);
lean_inc(v_a_2997_);
lean_inc_ref(v_a_2996_);
lean_inc(v_a_2995_);
lean_inc_ref(v___x_3012_);
v___x_3023_ = lean_whnf(v_snd_3022_, v___x_3012_, v_a_2995_, v_a_2996_, v_a_2997_);
if (lean_obj_tag(v___x_3023_) == 0)
{
lean_object* v_a_3024_; lean_object* v___f_3025_; uint8_t v___x_3026_; lean_object* v___x_3027_; 
v_a_3024_ = lean_ctor_get(v___x_3023_, 0);
lean_inc(v_a_3024_);
lean_dec_ref_known(v___x_3023_, 1);
lean_inc(v_a_3014_);
v___f_3025_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3025_, 0, v_a_3024_);
lean_closure_set(v___f_3025_, 1, v_fst_3020_);
lean_closure_set(v___f_3025_, 2, v_fst_3021_);
lean_closure_set(v___f_3025_, 3, v_inst_2992_);
lean_closure_set(v___f_3025_, 4, v_a_3014_);
lean_closure_set(v___f_3025_, 5, v_projInfo_x3f_2993_);
v___x_3026_ = 0;
v___x_3027_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3014_, v___f_3025_, v___x_3026_, v___x_3026_, v___x_3012_, v_a_2995_, v_a_2996_, v_a_2997_);
lean_dec_ref_known(v___x_3012_, 7);
return v___x_3027_;
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v_fst_3021_);
lean_dec(v_fst_3020_);
lean_dec(v_a_3014_);
lean_dec_ref_known(v___x_3012_, 7);
lean_dec(v_projInfo_x3f_2993_);
lean_dec_ref(v_inst_2992_);
v_a_3028_ = lean_ctor_get(v___x_3023_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_3023_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_3023_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_3023_);
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
else
{
lean_object* v_a_3036_; lean_object* v___x_3038_; uint8_t v_isShared_3039_; uint8_t v_isSharedCheck_3043_; 
lean_dec(v_a_3014_);
lean_dec_ref_known(v___x_3012_, 7);
lean_dec(v_projInfo_x3f_2993_);
lean_dec_ref(v_inst_2992_);
v_a_3036_ = lean_ctor_get(v___x_3017_, 0);
v_isSharedCheck_3043_ = !lean_is_exclusive(v___x_3017_);
if (v_isSharedCheck_3043_ == 0)
{
v___x_3038_ = v___x_3017_;
v_isShared_3039_ = v_isSharedCheck_3043_;
goto v_resetjp_3037_;
}
else
{
lean_inc(v_a_3036_);
lean_dec(v___x_3017_);
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
else
{
lean_object* v_a_3044_; lean_object* v___x_3046_; uint8_t v_isShared_3047_; uint8_t v_isSharedCheck_3051_; 
lean_dec_ref_known(v___x_3012_, 7);
lean_dec(v_projInfo_x3f_2993_);
lean_dec_ref(v_inst_2992_);
v_a_3044_ = lean_ctor_get(v___x_3013_, 0);
v_isSharedCheck_3051_ = !lean_is_exclusive(v___x_3013_);
if (v_isSharedCheck_3051_ == 0)
{
v___x_3046_ = v___x_3013_;
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
else
{
lean_inc(v_a_3044_);
lean_dec(v___x_3013_);
v___x_3046_ = lean_box(0);
v_isShared_3047_ = v_isSharedCheck_3051_;
goto v_resetjp_3045_;
}
v_resetjp_3045_:
{
lean_object* v___x_3049_; 
if (v_isShared_3047_ == 0)
{
v___x_3049_ = v___x_3046_;
goto v_reusejp_3048_;
}
else
{
lean_object* v_reuseFailAlloc_3050_; 
v_reuseFailAlloc_3050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3050_, 0, v_a_3044_);
v___x_3049_ = v_reuseFailAlloc_3050_;
goto v_reusejp_3048_;
}
v_reusejp_3048_:
{
return v___x_3049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_3052_, lean_object* v_projInfo_x3f_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_){
_start:
{
lean_object* v_res_3059_; 
v_res_3059_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_3052_, v_projInfo_x3f_3053_, v_a_3054_, v_a_3055_, v_a_3056_, v_a_3057_);
lean_dec(v_a_3057_);
lean_dec_ref(v_a_3056_);
lean_dec(v_a_3055_);
lean_dec_ref(v_a_3054_);
return v_res_3059_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_3060_, lean_object* v___x_3061_, lean_object* v_a_3062_, lean_object* v_inst_3063_, lean_object* v_R_3064_, lean_object* v_a_3065_, lean_object* v_b_3066_, lean_object* v_c_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_3060_, v___x_3061_, v_a_3062_, v_a_3065_, v_b_3066_);
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_3074_, lean_object* v___x_3075_, lean_object* v_a_3076_, lean_object* v_inst_3077_, lean_object* v_R_3078_, lean_object* v_a_3079_, lean_object* v_b_3080_, lean_object* v_c_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_){
_start:
{
lean_object* v_res_3087_; 
v_res_3087_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_3074_, v___x_3075_, v_a_3076_, v_inst_3077_, v_R_3078_, v_a_3079_, v_b_3080_, v_c_3081_, v___y_3082_, v___y_3083_, v___y_3084_, v___y_3085_);
lean_dec(v___y_3085_);
lean_dec_ref(v___y_3084_);
lean_dec(v___y_3083_);
lean_dec_ref(v___y_3082_);
lean_dec_ref(v_a_3076_);
lean_dec(v___x_3075_);
lean_dec(v_upperBound_3074_);
return v_res_3087_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3088_, lean_object* v_msg_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_){
_start:
{
lean_object* v___x_3095_; 
v___x_3095_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3089_, v___y_3090_, v___y_3091_, v___y_3092_, v___y_3093_);
return v___x_3095_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3096_, lean_object* v_msg_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_){
_start:
{
lean_object* v_res_3103_; 
v_res_3103_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3096_, v_msg_3097_, v___y_3098_, v___y_3099_, v___y_3100_, v___y_3101_);
lean_dec(v___y_3101_);
lean_dec_ref(v___y_3100_);
lean_dec(v___y_3099_);
lean_dec_ref(v___y_3098_);
return v_res_3103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_3104_, lean_object* v_argVars_3105_, lean_object* v_inst_3106_, lean_object* v_a_3107_, lean_object* v_projInfo_x3f_3108_, lean_object* v_inst_3109_, lean_object* v_a_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_){
_start:
{
lean_object* v___x_3116_; 
v___x_3116_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_3104_, v_argVars_3105_, v_inst_3106_, v_a_3107_, v_projInfo_x3f_3108_, v_a_3110_, v___y_3111_, v___y_3112_, v___y_3113_, v___y_3114_);
return v___x_3116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_3117_, lean_object* v_argVars_3118_, lean_object* v_inst_3119_, lean_object* v_a_3120_, lean_object* v_projInfo_x3f_3121_, lean_object* v_inst_3122_, lean_object* v_a_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_3117_, v_argVars_3118_, v_inst_3119_, v_a_3120_, v_projInfo_x3f_3121_, v_inst_3122_, v_a_3123_, v___y_3124_, v___y_3125_, v___y_3126_, v___y_3127_);
lean_dec(v___y_3127_);
lean_dec_ref(v___y_3126_);
lean_dec(v___y_3125_);
lean_dec_ref(v___y_3124_);
lean_dec(v_projInfo_x3f_3121_);
return v_res_3129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(lean_object* v_type_3130_, lean_object* v_k_3131_, uint8_t v_cleanupAnnotations_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_){
_start:
{
lean_object* v___f_3138_; uint8_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; 
v___f_3138_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3138_, 0, v_k_3131_);
v___x_3139_ = 0;
v___x_3140_ = lean_box(0);
v___x_3141_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3139_, v___x_3140_, v_type_3130_, v___f_3138_, v_cleanupAnnotations_3132_, v___x_3139_, v___y_3133_, v___y_3134_, v___y_3135_, v___y_3136_);
if (lean_obj_tag(v___x_3141_) == 0)
{
lean_object* v_a_3142_; lean_object* v___x_3144_; uint8_t v_isShared_3145_; uint8_t v_isSharedCheck_3149_; 
v_a_3142_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3149_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3149_ == 0)
{
v___x_3144_ = v___x_3141_;
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
else
{
lean_inc(v_a_3142_);
lean_dec(v___x_3141_);
v___x_3144_ = lean_box(0);
v_isShared_3145_ = v_isSharedCheck_3149_;
goto v_resetjp_3143_;
}
v_resetjp_3143_:
{
lean_object* v___x_3147_; 
if (v_isShared_3145_ == 0)
{
v___x_3147_ = v___x_3144_;
goto v_reusejp_3146_;
}
else
{
lean_object* v_reuseFailAlloc_3148_; 
v_reuseFailAlloc_3148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3148_, 0, v_a_3142_);
v___x_3147_ = v_reuseFailAlloc_3148_;
goto v_reusejp_3146_;
}
v_reusejp_3146_:
{
return v___x_3147_;
}
}
}
else
{
lean_object* v_a_3150_; lean_object* v___x_3152_; uint8_t v_isShared_3153_; uint8_t v_isSharedCheck_3157_; 
v_a_3150_ = lean_ctor_get(v___x_3141_, 0);
v_isSharedCheck_3157_ = !lean_is_exclusive(v___x_3141_);
if (v_isSharedCheck_3157_ == 0)
{
v___x_3152_ = v___x_3141_;
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
else
{
lean_inc(v_a_3150_);
lean_dec(v___x_3141_);
v___x_3152_ = lean_box(0);
v_isShared_3153_ = v_isSharedCheck_3157_;
goto v_resetjp_3151_;
}
v_resetjp_3151_:
{
lean_object* v___x_3155_; 
if (v_isShared_3153_ == 0)
{
v___x_3155_ = v___x_3152_;
goto v_reusejp_3154_;
}
else
{
lean_object* v_reuseFailAlloc_3156_; 
v_reuseFailAlloc_3156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3156_, 0, v_a_3150_);
v___x_3155_ = v_reuseFailAlloc_3156_;
goto v_reusejp_3154_;
}
v_reusejp_3154_:
{
return v___x_3155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg___boxed(lean_object* v_type_3158_, lean_object* v_k_3159_, lean_object* v_cleanupAnnotations_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3166_; lean_object* v_res_3167_; 
v_cleanupAnnotations_boxed_3166_ = lean_unbox(v_cleanupAnnotations_3160_);
v_res_3167_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3158_, v_k_3159_, v_cleanupAnnotations_boxed_3166_, v___y_3161_, v___y_3162_, v___y_3163_, v___y_3164_);
lean_dec(v___y_3164_);
lean_dec_ref(v___y_3163_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
return v_res_3167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(lean_object* v_00_u03b1_3168_, lean_object* v_type_3169_, lean_object* v_k_3170_, uint8_t v_cleanupAnnotations_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3169_, v_k_3170_, v_cleanupAnnotations_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___boxed(lean_object* v_00_u03b1_3178_, lean_object* v_type_3179_, lean_object* v_k_3180_, lean_object* v_cleanupAnnotations_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3187_; lean_object* v_res_3188_; 
v_cleanupAnnotations_boxed_3187_ = lean_unbox(v_cleanupAnnotations_3181_);
v_res_3188_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(v_00_u03b1_3178_, v_type_3179_, v_k_3180_, v_cleanupAnnotations_boxed_3187_, v___y_3182_, v___y_3183_, v___y_3184_, v___y_3185_);
lean_dec(v___y_3185_);
lean_dec_ref(v___y_3184_);
lean_dec(v___y_3183_);
lean_dec_ref(v___y_3182_);
return v_res_3188_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(lean_object* v_as_3189_, size_t v_sz_3190_, size_t v_i_3191_, lean_object* v_b_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_){
_start:
{
lean_object* v_a_3199_; uint8_t v___x_3203_; 
v___x_3203_ = lean_usize_dec_lt(v_i_3191_, v_sz_3190_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; 
v___x_3204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3204_, 0, v_b_3192_);
return v___x_3204_;
}
else
{
lean_object* v_a_3205_; lean_object* v___x_3206_; lean_object* v___x_3207_; 
v_a_3205_ = lean_array_uget_borrowed(v_as_3189_, v_i_3191_);
v___x_3206_ = l_Lean_Expr_fvarId_x21(v_a_3205_);
lean_inc(v___x_3206_);
v___x_3207_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_3206_, v___y_3194_, v___y_3195_, v___y_3196_);
if (lean_obj_tag(v___x_3207_) == 0)
{
lean_object* v_a_3208_; lean_object* v___x_3209_; uint8_t v___x_3210_; uint8_t v___x_3211_; 
v_a_3208_ = lean_ctor_get(v___x_3207_, 0);
lean_inc(v_a_3208_);
lean_dec_ref_known(v___x_3207_, 1);
v___x_3209_ = lean_box(0);
v___x_3210_ = lean_unbox(v_a_3208_);
lean_dec(v_a_3208_);
v___x_3211_ = l_Lean_BinderInfo_isInstImplicit(v___x_3210_);
if (v___x_3211_ == 0)
{
lean_dec(v___x_3206_);
v_a_3199_ = v___x_3209_;
goto v___jp_3198_;
}
else
{
lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; 
v___x_3212_ = lean_st_ref_take(v___y_3193_);
v___x_3213_ = l_Lean_CollectFVars_State_add(v___x_3212_, v___x_3206_);
v___x_3214_ = lean_st_ref_put(v___y_3193_, v___x_3213_);
v_a_3199_ = v___x_3209_;
goto v___jp_3198_;
}
}
else
{
lean_object* v_a_3215_; lean_object* v___x_3217_; uint8_t v_isShared_3218_; uint8_t v_isSharedCheck_3222_; 
lean_dec(v___x_3206_);
v_a_3215_ = lean_ctor_get(v___x_3207_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3207_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3217_ = v___x_3207_;
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
else
{
lean_inc(v_a_3215_);
lean_dec(v___x_3207_);
v___x_3217_ = lean_box(0);
v_isShared_3218_ = v_isSharedCheck_3222_;
goto v_resetjp_3216_;
}
v_resetjp_3216_:
{
lean_object* v___x_3220_; 
if (v_isShared_3218_ == 0)
{
v___x_3220_ = v___x_3217_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v_a_3215_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
v___jp_3198_:
{
size_t v___x_3200_; size_t v___x_3201_; 
v___x_3200_ = ((size_t)1ULL);
v___x_3201_ = lean_usize_add(v_i_3191_, v___x_3200_);
v_i_3191_ = v___x_3201_;
v_b_3192_ = v_a_3199_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg___boxed(lean_object* v_as_3223_, lean_object* v_sz_3224_, lean_object* v_i_3225_, lean_object* v_b_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_){
_start:
{
size_t v_sz_boxed_3232_; size_t v_i_boxed_3233_; lean_object* v_res_3234_; 
v_sz_boxed_3232_ = lean_unbox_usize(v_sz_3224_);
lean_dec(v_sz_3224_);
v_i_boxed_3233_ = lean_unbox_usize(v_i_3225_);
lean_dec(v_i_3225_);
v_res_3234_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_as_3223_, v_sz_boxed_3232_, v_i_boxed_3233_, v_b_3226_, v___y_3227_, v___y_3228_, v___y_3229_, v___y_3230_);
lean_dec(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec(v___y_3227_);
lean_dec_ref(v_as_3223_);
return v_res_3234_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(uint8_t v___y_3242_, uint8_t v_suppressElabErrors_3243_, lean_object* v_x_3244_){
_start:
{
if (lean_obj_tag(v_x_3244_) == 1)
{
lean_object* v_pre_3245_; 
v_pre_3245_ = lean_ctor_get(v_x_3244_, 0);
switch(lean_obj_tag(v_pre_3245_))
{
case 1:
{
lean_object* v_pre_3246_; 
v_pre_3246_ = lean_ctor_get(v_pre_3245_, 0);
switch(lean_obj_tag(v_pre_3246_))
{
case 0:
{
lean_object* v_str_3247_; lean_object* v_str_3248_; lean_object* v___x_3249_; uint8_t v___x_3250_; 
v_str_3247_ = lean_ctor_get(v_x_3244_, 1);
v_str_3248_ = lean_ctor_get(v_pre_3245_, 1);
v___x_3249_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__0));
v___x_3250_ = lean_string_dec_eq(v_str_3248_, v___x_3249_);
if (v___x_3250_ == 0)
{
lean_object* v___x_3251_; uint8_t v___x_3252_; 
v___x_3251_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__1));
v___x_3252_ = lean_string_dec_eq(v_str_3248_, v___x_3251_);
if (v___x_3252_ == 0)
{
return v___y_3242_;
}
else
{
lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__2));
v___x_3254_ = lean_string_dec_eq(v_str_3247_, v___x_3253_);
if (v___x_3254_ == 0)
{
return v___y_3242_;
}
else
{
return v_suppressElabErrors_3243_;
}
}
}
else
{
lean_object* v___x_3255_; uint8_t v___x_3256_; 
v___x_3255_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__3));
v___x_3256_ = lean_string_dec_eq(v_str_3247_, v___x_3255_);
if (v___x_3256_ == 0)
{
return v___y_3242_;
}
else
{
return v_suppressElabErrors_3243_;
}
}
}
case 1:
{
lean_object* v_pre_3257_; 
v_pre_3257_ = lean_ctor_get(v_pre_3246_, 0);
if (lean_obj_tag(v_pre_3257_) == 0)
{
lean_object* v_str_3258_; lean_object* v_str_3259_; lean_object* v_str_3260_; lean_object* v___x_3261_; uint8_t v___x_3262_; 
v_str_3258_ = lean_ctor_get(v_x_3244_, 1);
v_str_3259_ = lean_ctor_get(v_pre_3245_, 1);
v_str_3260_ = lean_ctor_get(v_pre_3246_, 1);
v___x_3261_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__4));
v___x_3262_ = lean_string_dec_eq(v_str_3260_, v___x_3261_);
if (v___x_3262_ == 0)
{
return v___y_3242_;
}
else
{
lean_object* v___x_3263_; uint8_t v___x_3264_; 
v___x_3263_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__5));
v___x_3264_ = lean_string_dec_eq(v_str_3259_, v___x_3263_);
if (v___x_3264_ == 0)
{
return v___y_3242_;
}
else
{
lean_object* v___x_3265_; uint8_t v___x_3266_; 
v___x_3265_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__6));
v___x_3266_ = lean_string_dec_eq(v_str_3258_, v___x_3265_);
if (v___x_3266_ == 0)
{
return v___y_3242_;
}
else
{
return v_suppressElabErrors_3243_;
}
}
}
}
else
{
return v___y_3242_;
}
}
default: 
{
return v___y_3242_;
}
}
}
case 0:
{
lean_object* v_str_3267_; lean_object* v___x_3268_; uint8_t v___x_3269_; 
v_str_3267_ = lean_ctor_get(v_x_3244_, 1);
v___x_3268_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3269_ = lean_string_dec_eq(v_str_3267_, v___x_3268_);
if (v___x_3269_ == 0)
{
return v___y_3242_;
}
else
{
return v_suppressElabErrors_3243_;
}
}
default: 
{
return v___y_3242_;
}
}
}
else
{
return v___y_3242_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed(lean_object* v___y_3270_, lean_object* v_suppressElabErrors_3271_, lean_object* v_x_3272_){
_start:
{
uint8_t v___y_11710__boxed_3273_; uint8_t v_suppressElabErrors_boxed_3274_; uint8_t v_res_3275_; lean_object* v_r_3276_; 
v___y_11710__boxed_3273_ = lean_unbox(v___y_3270_);
v_suppressElabErrors_boxed_3274_ = lean_unbox(v_suppressElabErrors_3271_);
v_res_3275_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(v___y_11710__boxed_3273_, v_suppressElabErrors_boxed_3274_, v_x_3272_);
lean_dec(v_x_3272_);
v_r_3276_ = lean_box(v_res_3275_);
return v_r_3276_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(lean_object* v_ref_3277_, lean_object* v_msgData_3278_, uint8_t v_severity_3279_, uint8_t v_isSilent_3280_, lean_object* v___y_3281_, lean_object* v___y_3282_, lean_object* v___y_3283_, lean_object* v___y_3284_){
_start:
{
lean_object* v___y_3287_; lean_object* v___y_3288_; uint8_t v___y_3289_; lean_object* v___y_3290_; lean_object* v___y_3291_; lean_object* v___y_3292_; uint8_t v___y_3293_; lean_object* v___y_3294_; lean_object* v___y_3295_; lean_object* v___y_3323_; lean_object* v___y_3324_; uint8_t v___y_3325_; lean_object* v___y_3326_; lean_object* v___y_3327_; uint8_t v___y_3328_; uint8_t v___y_3329_; lean_object* v___y_3330_; lean_object* v___y_3348_; lean_object* v___y_3349_; lean_object* v___y_3350_; uint8_t v___y_3351_; lean_object* v___y_3352_; uint8_t v___y_3353_; uint8_t v___y_3354_; lean_object* v___y_3355_; lean_object* v___y_3359_; lean_object* v___y_3360_; lean_object* v___y_3361_; lean_object* v___y_3362_; uint8_t v___y_3363_; uint8_t v___y_3364_; uint8_t v___y_3365_; uint8_t v___x_3370_; lean_object* v___y_3372_; lean_object* v___y_3373_; lean_object* v___y_3374_; lean_object* v___y_3375_; uint8_t v___y_3376_; uint8_t v___y_3377_; uint8_t v___y_3378_; uint8_t v___y_3380_; uint8_t v___x_3395_; 
v___x_3370_ = 2;
v___x_3395_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3279_, v___x_3370_);
if (v___x_3395_ == 0)
{
v___y_3380_ = v___x_3395_;
goto v___jp_3379_;
}
else
{
uint8_t v___x_3396_; 
lean_inc_ref(v_msgData_3278_);
v___x_3396_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3278_);
v___y_3380_ = v___x_3396_;
goto v___jp_3379_;
}
v___jp_3286_:
{
lean_object* v___x_3296_; lean_object* v_currNamespace_3297_; lean_object* v_openDecls_3298_; lean_object* v_env_3299_; lean_object* v_nextMacroScope_3300_; lean_object* v_ngen_3301_; lean_object* v_auxDeclNGen_3302_; lean_object* v_traceState_3303_; lean_object* v_cache_3304_; lean_object* v_messages_3305_; lean_object* v_infoState_3306_; lean_object* v_snapshotTasks_3307_; lean_object* v___x_3309_; uint8_t v_isShared_3310_; uint8_t v_isSharedCheck_3321_; 
v___x_3296_ = lean_st_ref_take(v___y_3295_);
v_currNamespace_3297_ = lean_ctor_get(v___y_3294_, 6);
v_openDecls_3298_ = lean_ctor_get(v___y_3294_, 7);
v_env_3299_ = lean_ctor_get(v___x_3296_, 0);
v_nextMacroScope_3300_ = lean_ctor_get(v___x_3296_, 1);
v_ngen_3301_ = lean_ctor_get(v___x_3296_, 2);
v_auxDeclNGen_3302_ = lean_ctor_get(v___x_3296_, 3);
v_traceState_3303_ = lean_ctor_get(v___x_3296_, 4);
v_cache_3304_ = lean_ctor_get(v___x_3296_, 5);
v_messages_3305_ = lean_ctor_get(v___x_3296_, 6);
v_infoState_3306_ = lean_ctor_get(v___x_3296_, 7);
v_snapshotTasks_3307_ = lean_ctor_get(v___x_3296_, 8);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3296_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3309_ = v___x_3296_;
v_isShared_3310_ = v_isSharedCheck_3321_;
goto v_resetjp_3308_;
}
else
{
lean_inc(v_snapshotTasks_3307_);
lean_inc(v_infoState_3306_);
lean_inc(v_messages_3305_);
lean_inc(v_cache_3304_);
lean_inc(v_traceState_3303_);
lean_inc(v_auxDeclNGen_3302_);
lean_inc(v_ngen_3301_);
lean_inc(v_nextMacroScope_3300_);
lean_inc(v_env_3299_);
lean_dec(v___x_3296_);
v___x_3309_ = lean_box(0);
v_isShared_3310_ = v_isSharedCheck_3321_;
goto v_resetjp_3308_;
}
v_resetjp_3308_:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3316_; 
lean_inc(v_openDecls_3298_);
lean_inc(v_currNamespace_3297_);
v___x_3311_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3311_, 0, v_currNamespace_3297_);
lean_ctor_set(v___x_3311_, 1, v_openDecls_3298_);
v___x_3312_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
lean_ctor_set(v___x_3312_, 1, v___y_3291_);
lean_inc_ref(v___y_3292_);
lean_inc_ref(v___y_3290_);
v___x_3313_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3313_, 0, v___y_3290_);
lean_ctor_set(v___x_3313_, 1, v___y_3288_);
lean_ctor_set(v___x_3313_, 2, v___y_3287_);
lean_ctor_set(v___x_3313_, 3, v___y_3292_);
lean_ctor_set(v___x_3313_, 4, v___x_3312_);
lean_ctor_set_uint8(v___x_3313_, sizeof(void*)*5, v___y_3293_);
lean_ctor_set_uint8(v___x_3313_, sizeof(void*)*5 + 1, v___y_3289_);
lean_ctor_set_uint8(v___x_3313_, sizeof(void*)*5 + 2, v_isSilent_3280_);
v___x_3314_ = l_Lean_MessageLog_add(v___x_3313_, v_messages_3305_);
if (v_isShared_3310_ == 0)
{
lean_ctor_set(v___x_3309_, 6, v___x_3314_);
v___x_3316_ = v___x_3309_;
goto v_reusejp_3315_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v_env_3299_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v_nextMacroScope_3300_);
lean_ctor_set(v_reuseFailAlloc_3320_, 2, v_ngen_3301_);
lean_ctor_set(v_reuseFailAlloc_3320_, 3, v_auxDeclNGen_3302_);
lean_ctor_set(v_reuseFailAlloc_3320_, 4, v_traceState_3303_);
lean_ctor_set(v_reuseFailAlloc_3320_, 5, v_cache_3304_);
lean_ctor_set(v_reuseFailAlloc_3320_, 6, v___x_3314_);
lean_ctor_set(v_reuseFailAlloc_3320_, 7, v_infoState_3306_);
lean_ctor_set(v_reuseFailAlloc_3320_, 8, v_snapshotTasks_3307_);
v___x_3316_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3315_;
}
v_reusejp_3315_:
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = lean_st_ref_put(v___y_3295_, v___x_3316_);
v___x_3318_ = lean_box(0);
v___x_3319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3319_, 0, v___x_3318_);
return v___x_3319_;
}
}
}
v___jp_3322_:
{
lean_object* v___x_3331_; lean_object* v___x_3332_; lean_object* v_a_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3346_; 
v___x_3331_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3278_);
v___x_3332_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3331_, v___y_3281_, v___y_3282_, v___y_3283_, v___y_3284_);
v_a_3333_ = lean_ctor_get(v___x_3332_, 0);
v_isSharedCheck_3346_ = !lean_is_exclusive(v___x_3332_);
if (v_isSharedCheck_3346_ == 0)
{
v___x_3335_ = v___x_3332_;
v_isShared_3336_ = v_isSharedCheck_3346_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_a_3333_);
lean_dec(v___x_3332_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3346_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3337_; lean_object* v___x_3338_; lean_object* v___x_3339_; lean_object* v___x_3340_; 
lean_inc_ref_n(v___y_3324_, 2);
v___x_3337_ = l_Lean_FileMap_toPosition(v___y_3324_, v___y_3326_);
lean_dec(v___y_3326_);
v___x_3338_ = l_Lean_FileMap_toPosition(v___y_3324_, v___y_3330_);
lean_dec(v___y_3330_);
v___x_3339_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
v___x_3340_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3329_ == 0)
{
lean_del_object(v___x_3335_);
lean_dec_ref(v___y_3323_);
v___y_3287_ = v___x_3339_;
v___y_3288_ = v___x_3337_;
v___y_3289_ = v___y_3325_;
v___y_3290_ = v___y_3327_;
v___y_3291_ = v_a_3333_;
v___y_3292_ = v___x_3340_;
v___y_3293_ = v___y_3328_;
v___y_3294_ = v___y_3283_;
v___y_3295_ = v___y_3284_;
goto v___jp_3286_;
}
else
{
uint8_t v___x_3341_; 
lean_inc(v_a_3333_);
v___x_3341_ = l_Lean_MessageData_hasTag(v___y_3323_, v_a_3333_);
if (v___x_3341_ == 0)
{
lean_object* v___x_3342_; lean_object* v___x_3344_; 
lean_dec_ref_known(v___x_3339_, 1);
lean_dec_ref(v___x_3337_);
lean_dec(v_a_3333_);
v___x_3342_ = lean_box(0);
if (v_isShared_3336_ == 0)
{
lean_ctor_set(v___x_3335_, 0, v___x_3342_);
v___x_3344_ = v___x_3335_;
goto v_reusejp_3343_;
}
else
{
lean_object* v_reuseFailAlloc_3345_; 
v_reuseFailAlloc_3345_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3345_, 0, v___x_3342_);
v___x_3344_ = v_reuseFailAlloc_3345_;
goto v_reusejp_3343_;
}
v_reusejp_3343_:
{
return v___x_3344_;
}
}
else
{
lean_del_object(v___x_3335_);
v___y_3287_ = v___x_3339_;
v___y_3288_ = v___x_3337_;
v___y_3289_ = v___y_3325_;
v___y_3290_ = v___y_3327_;
v___y_3291_ = v_a_3333_;
v___y_3292_ = v___x_3340_;
v___y_3293_ = v___y_3328_;
v___y_3294_ = v___y_3283_;
v___y_3295_ = v___y_3284_;
goto v___jp_3286_;
}
}
}
}
v___jp_3347_:
{
lean_object* v___x_3356_; 
v___x_3356_ = l_Lean_Syntax_getTailPos_x3f(v___y_3349_, v___y_3353_);
lean_dec(v___y_3349_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_inc(v___y_3355_);
v___y_3323_ = v___y_3348_;
v___y_3324_ = v___y_3350_;
v___y_3325_ = v___y_3351_;
v___y_3326_ = v___y_3355_;
v___y_3327_ = v___y_3352_;
v___y_3328_ = v___y_3353_;
v___y_3329_ = v___y_3354_;
v___y_3330_ = v___y_3355_;
goto v___jp_3322_;
}
else
{
lean_object* v_val_3357_; 
v_val_3357_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_val_3357_);
lean_dec_ref_known(v___x_3356_, 1);
v___y_3323_ = v___y_3348_;
v___y_3324_ = v___y_3350_;
v___y_3325_ = v___y_3351_;
v___y_3326_ = v___y_3355_;
v___y_3327_ = v___y_3352_;
v___y_3328_ = v___y_3353_;
v___y_3329_ = v___y_3354_;
v___y_3330_ = v_val_3357_;
goto v___jp_3322_;
}
}
v___jp_3358_:
{
lean_object* v_ref_3366_; lean_object* v___x_3367_; 
v_ref_3366_ = l_Lean_replaceRef(v_ref_3277_, v___y_3361_);
v___x_3367_ = l_Lean_Syntax_getPos_x3f(v_ref_3366_, v___y_3363_);
if (lean_obj_tag(v___x_3367_) == 0)
{
lean_object* v___x_3368_; 
v___x_3368_ = lean_unsigned_to_nat(0u);
v___y_3348_ = v___y_3359_;
v___y_3349_ = v_ref_3366_;
v___y_3350_ = v___y_3360_;
v___y_3351_ = v___y_3365_;
v___y_3352_ = v___y_3362_;
v___y_3353_ = v___y_3363_;
v___y_3354_ = v___y_3364_;
v___y_3355_ = v___x_3368_;
goto v___jp_3347_;
}
else
{
lean_object* v_val_3369_; 
v_val_3369_ = lean_ctor_get(v___x_3367_, 0);
lean_inc(v_val_3369_);
lean_dec_ref_known(v___x_3367_, 1);
v___y_3348_ = v___y_3359_;
v___y_3349_ = v_ref_3366_;
v___y_3350_ = v___y_3360_;
v___y_3351_ = v___y_3365_;
v___y_3352_ = v___y_3362_;
v___y_3353_ = v___y_3363_;
v___y_3354_ = v___y_3364_;
v___y_3355_ = v_val_3369_;
goto v___jp_3347_;
}
}
v___jp_3371_:
{
if (v___y_3378_ == 0)
{
v___y_3359_ = v___y_3372_;
v___y_3360_ = v___y_3373_;
v___y_3361_ = v___y_3374_;
v___y_3362_ = v___y_3375_;
v___y_3363_ = v___y_3377_;
v___y_3364_ = v___y_3376_;
v___y_3365_ = v_severity_3279_;
goto v___jp_3358_;
}
else
{
v___y_3359_ = v___y_3372_;
v___y_3360_ = v___y_3373_;
v___y_3361_ = v___y_3374_;
v___y_3362_ = v___y_3375_;
v___y_3363_ = v___y_3377_;
v___y_3364_ = v___y_3376_;
v___y_3365_ = v___x_3370_;
goto v___jp_3358_;
}
}
v___jp_3379_:
{
if (v___y_3380_ == 0)
{
lean_object* v_fileName_3381_; lean_object* v_fileMap_3382_; lean_object* v_options_3383_; lean_object* v_ref_3384_; uint8_t v_suppressElabErrors_3385_; lean_object* v___x_3386_; lean_object* v___x_3387_; lean_object* v___f_3388_; uint8_t v___x_3389_; uint8_t v___x_3390_; 
v_fileName_3381_ = lean_ctor_get(v___y_3283_, 0);
v_fileMap_3382_ = lean_ctor_get(v___y_3283_, 1);
v_options_3383_ = lean_ctor_get(v___y_3283_, 2);
v_ref_3384_ = lean_ctor_get(v___y_3283_, 5);
v_suppressElabErrors_3385_ = lean_ctor_get_uint8(v___y_3283_, sizeof(void*)*14 + 1);
v___x_3386_ = lean_box(v___y_3380_);
v___x_3387_ = lean_box(v_suppressElabErrors_3385_);
v___f_3388_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3388_, 0, v___x_3386_);
lean_closure_set(v___f_3388_, 1, v___x_3387_);
v___x_3389_ = 1;
v___x_3390_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3279_, v___x_3389_);
if (v___x_3390_ == 0)
{
v___y_3372_ = v___f_3388_;
v___y_3373_ = v_fileMap_3382_;
v___y_3374_ = v_ref_3384_;
v___y_3375_ = v_fileName_3381_;
v___y_3376_ = v_suppressElabErrors_3385_;
v___y_3377_ = v___y_3380_;
v___y_3378_ = v___x_3390_;
goto v___jp_3371_;
}
else
{
lean_object* v___x_3391_; uint8_t v___x_3392_; 
v___x_3391_ = l_Lean_warningAsError;
v___x_3392_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3383_, v___x_3391_);
v___y_3372_ = v___f_3388_;
v___y_3373_ = v_fileMap_3382_;
v___y_3374_ = v_ref_3384_;
v___y_3375_ = v_fileName_3381_;
v___y_3376_ = v_suppressElabErrors_3385_;
v___y_3377_ = v___y_3380_;
v___y_3378_ = v___x_3392_;
goto v___jp_3371_;
}
}
else
{
lean_object* v___x_3393_; lean_object* v___x_3394_; 
lean_dec_ref(v_msgData_3278_);
v___x_3393_ = lean_box(0);
v___x_3394_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3394_, 0, v___x_3393_);
return v___x_3394_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___boxed(lean_object* v_ref_3397_, lean_object* v_msgData_3398_, lean_object* v_severity_3399_, lean_object* v_isSilent_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_, lean_object* v___y_3404_, lean_object* v___y_3405_){
_start:
{
uint8_t v_severity_boxed_3406_; uint8_t v_isSilent_boxed_3407_; lean_object* v_res_3408_; 
v_severity_boxed_3406_ = lean_unbox(v_severity_3399_);
v_isSilent_boxed_3407_ = lean_unbox(v_isSilent_3400_);
v_res_3408_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3397_, v_msgData_3398_, v_severity_boxed_3406_, v_isSilent_boxed_3407_, v___y_3401_, v___y_3402_, v___y_3403_, v___y_3404_);
lean_dec(v___y_3404_);
lean_dec_ref(v___y_3403_);
lean_dec(v___y_3402_);
lean_dec_ref(v___y_3401_);
lean_dec(v_ref_3397_);
return v_res_3408_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(lean_object* v_msgData_3409_, uint8_t v_severity_3410_, uint8_t v_isSilent_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_, lean_object* v___y_3414_, lean_object* v___y_3415_){
_start:
{
lean_object* v_ref_3417_; lean_object* v___x_3418_; 
v_ref_3417_ = lean_ctor_get(v___y_3414_, 5);
v___x_3418_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3417_, v_msgData_3409_, v_severity_3410_, v_isSilent_3411_, v___y_3412_, v___y_3413_, v___y_3414_, v___y_3415_);
return v___x_3418_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3___boxed(lean_object* v_msgData_3419_, lean_object* v_severity_3420_, lean_object* v_isSilent_3421_, lean_object* v___y_3422_, lean_object* v___y_3423_, lean_object* v___y_3424_, lean_object* v___y_3425_, lean_object* v___y_3426_){
_start:
{
uint8_t v_severity_boxed_3427_; uint8_t v_isSilent_boxed_3428_; lean_object* v_res_3429_; 
v_severity_boxed_3427_ = lean_unbox(v_severity_3420_);
v_isSilent_boxed_3428_ = lean_unbox(v_isSilent_3421_);
v_res_3429_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3419_, v_severity_boxed_3427_, v_isSilent_boxed_3428_, v___y_3422_, v___y_3423_, v___y_3424_, v___y_3425_);
lean_dec(v___y_3425_);
lean_dec_ref(v___y_3424_);
lean_dec(v___y_3423_);
lean_dec_ref(v___y_3422_);
return v_res_3429_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object* v_msgData_3430_, lean_object* v___y_3431_, lean_object* v___y_3432_, lean_object* v___y_3433_, lean_object* v___y_3434_){
_start:
{
uint8_t v___x_3436_; uint8_t v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = 1;
v___x_3437_ = 0;
v___x_3438_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3430_, v___x_3436_, v___x_3437_, v___y_3431_, v___y_3432_, v___y_3433_, v___y_3434_);
return v___x_3438_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object* v_msgData_3439_, lean_object* v___y_3440_, lean_object* v___y_3441_, lean_object* v___y_3442_, lean_object* v___y_3443_, lean_object* v___y_3444_){
_start:
{
lean_object* v_res_3445_; 
v_res_3445_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v_msgData_3439_, v___y_3440_, v___y_3441_, v___y_3442_, v___y_3443_);
lean_dec(v___y_3443_);
lean_dec_ref(v___y_3442_);
lean_dec(v___y_3441_);
lean_dec_ref(v___y_3440_);
return v_res_3445_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object* v_k_3446_, lean_object* v_t_3447_){
_start:
{
if (lean_obj_tag(v_t_3447_) == 0)
{
lean_object* v_k_3448_; lean_object* v_l_3449_; lean_object* v_r_3450_; uint8_t v___x_3451_; 
v_k_3448_ = lean_ctor_get(v_t_3447_, 1);
v_l_3449_ = lean_ctor_get(v_t_3447_, 3);
v_r_3450_ = lean_ctor_get(v_t_3447_, 4);
v___x_3451_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3446_, v_k_3448_);
switch(v___x_3451_)
{
case 0:
{
v_t_3447_ = v_l_3449_;
goto _start;
}
case 1:
{
uint8_t v___x_3453_; 
v___x_3453_ = 1;
return v___x_3453_;
}
default: 
{
v_t_3447_ = v_r_3450_;
goto _start;
}
}
}
else
{
uint8_t v___x_3455_; 
v___x_3455_ = 0;
return v___x_3455_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object* v_k_3456_, lean_object* v_t_3457_){
_start:
{
uint8_t v_res_3458_; lean_object* v_r_3459_; 
v_res_3458_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3456_, v_t_3457_);
lean_dec(v_t_3457_);
lean_dec(v_k_3456_);
v_r_3459_ = lean_box(v_res_3458_);
return v_r_3459_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3461_; lean_object* v___x_3462_; 
v___x_3461_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__0));
v___x_3462_ = l_Lean_stringToMessageData(v___x_3461_);
return v___x_3462_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3464_; lean_object* v___x_3465_; 
v___x_3464_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__2));
v___x_3465_ = l_Lean_stringToMessageData(v___x_3464_);
return v___x_3465_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(lean_object* v_a_3466_, lean_object* v_as_3467_, size_t v_sz_3468_, size_t v_i_3469_, lean_object* v_b_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_){
_start:
{
lean_object* v_a_3476_; uint8_t v___x_3480_; 
v___x_3480_ = lean_usize_dec_lt(v_i_3469_, v_sz_3468_);
if (v___x_3480_ == 0)
{
lean_object* v___x_3481_; 
v___x_3481_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3481_, 0, v_b_3470_);
return v___x_3481_;
}
else
{
lean_object* v_snd_3482_; 
v_snd_3482_ = lean_ctor_get(v_b_3470_, 1);
lean_inc(v_snd_3482_);
if (lean_obj_tag(v_snd_3482_) == 0)
{
lean_object* v_fst_3483_; lean_object* v___x_3485_; uint8_t v_isShared_3486_; uint8_t v_isSharedCheck_3491_; 
v_fst_3483_ = lean_ctor_get(v_b_3470_, 0);
v_isSharedCheck_3491_ = !lean_is_exclusive(v_b_3470_);
if (v_isSharedCheck_3491_ == 0)
{
lean_object* v_unused_3492_; 
v_unused_3492_ = lean_ctor_get(v_b_3470_, 1);
lean_dec(v_unused_3492_);
v___x_3485_ = v_b_3470_;
v_isShared_3486_ = v_isSharedCheck_3491_;
goto v_resetjp_3484_;
}
else
{
lean_inc(v_fst_3483_);
lean_dec(v_b_3470_);
v___x_3485_ = lean_box(0);
v_isShared_3486_ = v_isSharedCheck_3491_;
goto v_resetjp_3484_;
}
v_resetjp_3484_:
{
lean_object* v___x_3488_; 
if (v_isShared_3486_ == 0)
{
v___x_3488_ = v___x_3485_;
goto v_reusejp_3487_;
}
else
{
lean_object* v_reuseFailAlloc_3490_; 
v_reuseFailAlloc_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3490_, 0, v_fst_3483_);
lean_ctor_set(v_reuseFailAlloc_3490_, 1, v_snd_3482_);
v___x_3488_ = v_reuseFailAlloc_3490_;
goto v_reusejp_3487_;
}
v_reusejp_3487_:
{
lean_object* v___x_3489_; 
v___x_3489_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3489_, 0, v___x_3488_);
return v___x_3489_;
}
}
}
else
{
lean_object* v_fst_3493_; lean_object* v___x_3495_; uint8_t v_isShared_3496_; uint8_t v_isSharedCheck_3550_; 
v_fst_3493_ = lean_ctor_get(v_b_3470_, 0);
v_isSharedCheck_3550_ = !lean_is_exclusive(v_b_3470_);
if (v_isSharedCheck_3550_ == 0)
{
lean_object* v_unused_3551_; 
v_unused_3551_ = lean_ctor_get(v_b_3470_, 1);
lean_dec(v_unused_3551_);
v___x_3495_ = v_b_3470_;
v_isShared_3496_ = v_isSharedCheck_3550_;
goto v_resetjp_3494_;
}
else
{
lean_inc(v_fst_3493_);
lean_dec(v_b_3470_);
v___x_3495_ = lean_box(0);
v_isShared_3496_ = v_isSharedCheck_3550_;
goto v_resetjp_3494_;
}
v_resetjp_3494_:
{
lean_object* v_val_3497_; lean_object* v___x_3499_; uint8_t v_isShared_3500_; uint8_t v_isSharedCheck_3549_; 
v_val_3497_ = lean_ctor_get(v_snd_3482_, 0);
v_isSharedCheck_3549_ = !lean_is_exclusive(v_snd_3482_);
if (v_isSharedCheck_3549_ == 0)
{
v___x_3499_ = v_snd_3482_;
v_isShared_3500_ = v_isSharedCheck_3549_;
goto v_resetjp_3498_;
}
else
{
lean_inc(v_val_3497_);
lean_dec(v_snd_3482_);
v___x_3499_ = lean_box(0);
v_isShared_3500_ = v_isSharedCheck_3549_;
goto v_resetjp_3498_;
}
v_resetjp_3498_:
{
lean_object* v_fvarSet_3501_; lean_object* v_a_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___x_3506_; 
v_fvarSet_3501_ = lean_ctor_get(v_a_3466_, 1);
v_a_3502_ = lean_array_uget_borrowed(v_as_3467_, v_i_3469_);
v___x_3503_ = lean_unsigned_to_nat(1u);
v___x_3504_ = lean_nat_add(v_val_3497_, v___x_3503_);
if (v_isShared_3500_ == 0)
{
lean_ctor_set(v___x_3499_, 0, v___x_3504_);
v___x_3506_ = v___x_3499_;
goto v_reusejp_3505_;
}
else
{
lean_object* v_reuseFailAlloc_3548_; 
v_reuseFailAlloc_3548_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3548_, 0, v___x_3504_);
v___x_3506_ = v_reuseFailAlloc_3548_;
goto v_reusejp_3505_;
}
v_reusejp_3505_:
{
lean_object* v___x_3507_; uint8_t v___x_3508_; 
v___x_3507_ = l_Lean_Expr_fvarId_x21(v_a_3502_);
v___x_3508_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v___x_3507_, v_fvarSet_3501_);
if (v___x_3508_ == 0)
{
lean_object* v___x_3509_; 
v___x_3509_ = l_Lean_FVarId_getDecl___redArg(v___x_3507_, v___y_3471_, v___y_3472_, v___y_3473_);
if (lean_obj_tag(v___x_3509_) == 0)
{
lean_object* v_a_3510_; lean_object* v___x_3511_; 
v_a_3510_ = lean_ctor_get(v___x_3509_, 0);
lean_inc(v_a_3510_);
lean_dec_ref_known(v___x_3509_, 1);
v___x_3511_ = l_Lean_LocalDecl_ppAsBinder(v_a_3510_);
if (lean_obj_tag(v___x_3511_) == 1)
{
lean_object* v_val_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3533_; 
v_val_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3533_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3533_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3533_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_val_3512_);
lean_dec(v___x_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3533_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3519_; 
v___x_3516_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1);
v___x_3517_ = l_Nat_reprFast(v_val_3497_);
if (v_isShared_3515_ == 0)
{
lean_ctor_set_tag(v___x_3514_, 3);
lean_ctor_set(v___x_3514_, 0, v___x_3517_);
v___x_3519_ = v___x_3514_;
goto v_reusejp_3518_;
}
else
{
lean_object* v_reuseFailAlloc_3532_; 
v_reuseFailAlloc_3532_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3532_, 0, v___x_3517_);
v___x_3519_ = v_reuseFailAlloc_3532_;
goto v_reusejp_3518_;
}
v_reusejp_3518_:
{
lean_object* v___x_3520_; lean_object* v___x_3521_; lean_object* v___x_3522_; lean_object* v___x_3523_; lean_object* v___x_3524_; lean_object* v___x_3525_; lean_object* v___x_3526_; lean_object* v___x_3527_; lean_object* v___x_3528_; lean_object* v___x_3530_; 
v___x_3520_ = l_Lean_MessageData_ofFormat(v___x_3519_);
v___x_3521_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3521_, 0, v___x_3516_);
lean_ctor_set(v___x_3521_, 1, v___x_3520_);
v___x_3522_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3);
v___x_3523_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3523_, 0, v___x_3521_);
lean_ctor_set(v___x_3523_, 1, v___x_3522_);
v___x_3524_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3524_, 0, v___x_3523_);
lean_ctor_set(v___x_3524_, 1, v_val_3512_);
v___x_3525_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3526_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3526_, 0, v___x_3524_);
lean_ctor_set(v___x_3526_, 1, v___x_3525_);
v___x_3527_ = l_Lean_indentD(v___x_3526_);
v___x_3528_ = lean_array_push(v_fst_3493_, v___x_3527_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 1, v___x_3506_);
lean_ctor_set(v___x_3495_, 0, v___x_3528_);
v___x_3530_ = v___x_3495_;
goto v_reusejp_3529_;
}
else
{
lean_object* v_reuseFailAlloc_3531_; 
v_reuseFailAlloc_3531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3531_, 0, v___x_3528_);
lean_ctor_set(v_reuseFailAlloc_3531_, 1, v___x_3506_);
v___x_3530_ = v_reuseFailAlloc_3531_;
goto v_reusejp_3529_;
}
v_reusejp_3529_:
{
v_a_3476_ = v___x_3530_;
goto v___jp_3475_;
}
}
}
}
else
{
lean_object* v___x_3535_; 
lean_dec(v___x_3511_);
lean_dec(v_val_3497_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 1, v___x_3506_);
v___x_3535_ = v___x_3495_;
goto v_reusejp_3534_;
}
else
{
lean_object* v_reuseFailAlloc_3536_; 
v_reuseFailAlloc_3536_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3536_, 0, v_fst_3493_);
lean_ctor_set(v_reuseFailAlloc_3536_, 1, v___x_3506_);
v___x_3535_ = v_reuseFailAlloc_3536_;
goto v_reusejp_3534_;
}
v_reusejp_3534_:
{
v_a_3476_ = v___x_3535_;
goto v___jp_3475_;
}
}
}
else
{
lean_object* v_a_3537_; lean_object* v___x_3539_; uint8_t v_isShared_3540_; uint8_t v_isSharedCheck_3544_; 
lean_dec_ref(v___x_3506_);
lean_dec(v_val_3497_);
lean_del_object(v___x_3495_);
lean_dec(v_fst_3493_);
v_a_3537_ = lean_ctor_get(v___x_3509_, 0);
v_isSharedCheck_3544_ = !lean_is_exclusive(v___x_3509_);
if (v_isSharedCheck_3544_ == 0)
{
v___x_3539_ = v___x_3509_;
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
else
{
lean_inc(v_a_3537_);
lean_dec(v___x_3509_);
v___x_3539_ = lean_box(0);
v_isShared_3540_ = v_isSharedCheck_3544_;
goto v_resetjp_3538_;
}
v_resetjp_3538_:
{
lean_object* v___x_3542_; 
if (v_isShared_3540_ == 0)
{
v___x_3542_ = v___x_3539_;
goto v_reusejp_3541_;
}
else
{
lean_object* v_reuseFailAlloc_3543_; 
v_reuseFailAlloc_3543_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3543_, 0, v_a_3537_);
v___x_3542_ = v_reuseFailAlloc_3543_;
goto v_reusejp_3541_;
}
v_reusejp_3541_:
{
return v___x_3542_;
}
}
}
}
else
{
lean_object* v___x_3546_; 
lean_dec(v___x_3507_);
lean_dec(v_val_3497_);
if (v_isShared_3496_ == 0)
{
lean_ctor_set(v___x_3495_, 1, v___x_3506_);
v___x_3546_ = v___x_3495_;
goto v_reusejp_3545_;
}
else
{
lean_object* v_reuseFailAlloc_3547_; 
v_reuseFailAlloc_3547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3547_, 0, v_fst_3493_);
lean_ctor_set(v_reuseFailAlloc_3547_, 1, v___x_3506_);
v___x_3546_ = v_reuseFailAlloc_3547_;
goto v_reusejp_3545_;
}
v_reusejp_3545_:
{
v_a_3476_ = v___x_3546_;
goto v___jp_3475_;
}
}
}
}
}
}
}
v___jp_3475_:
{
size_t v___x_3477_; size_t v___x_3478_; 
v___x_3477_ = ((size_t)1ULL);
v___x_3478_ = lean_usize_add(v_i_3469_, v___x_3477_);
v_i_3469_ = v___x_3478_;
v_b_3470_ = v_a_3476_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___boxed(lean_object* v_a_3552_, lean_object* v_as_3553_, lean_object* v_sz_3554_, lean_object* v_i_3555_, lean_object* v_b_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_){
_start:
{
size_t v_sz_boxed_3561_; size_t v_i_boxed_3562_; lean_object* v_res_3563_; 
v_sz_boxed_3561_ = lean_unbox_usize(v_sz_3554_);
lean_dec(v_sz_3554_);
v_i_boxed_3562_ = lean_unbox_usize(v_i_3555_);
lean_dec(v_i_3555_);
v_res_3563_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3552_, v_as_3553_, v_sz_boxed_3561_, v_i_boxed_3562_, v_b_3556_, v___y_3557_, v___y_3558_, v___y_3559_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
lean_dec_ref(v___y_3557_);
lean_dec_ref(v_as_3553_);
lean_dec_ref(v_a_3552_);
return v_res_3563_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3565_; lean_object* v___x_3566_; 
v___x_3565_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0));
v___x_3566_ = l_Lean_stringToMessageData(v___x_3565_);
return v___x_3566_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3568_; lean_object* v___x_3569_; 
v___x_3568_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2));
v___x_3569_ = l_Lean_stringToMessageData(v___x_3568_);
return v___x_3569_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4(void){
_start:
{
lean_object* v_cellCount_3570_; lean_object* v___x_3571_; 
v_cellCount_3570_ = lean_unsigned_to_nat(16u);
v___x_3571_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_3570_);
return v___x_3571_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5(void){
_start:
{
lean_object* v_cellCount_3572_; lean_object* v___x_3573_; 
v_cellCount_3572_ = lean_unsigned_to_nat(16u);
v___x_3573_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_3572_);
return v___x_3573_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; lean_object* v___x_3577_; 
v___x_3574_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5);
v___x_3575_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4);
v___x_3576_ = lean_unsigned_to_nat(0u);
v___x_3577_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3577_, 0, v___x_3576_);
lean_ctor_set(v___x_3577_, 1, v___x_3575_);
lean_ctor_set(v___x_3577_, 2, v___x_3574_);
return v___x_3577_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8(void){
_start:
{
lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; lean_object* v___x_3583_; 
v___x_3580_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7));
v___x_3581_ = lean_box(1);
v___x_3582_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6);
v___x_3583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3583_, 0, v___x_3582_);
lean_ctor_set(v___x_3583_, 1, v___x_3581_);
lean_ctor_set(v___x_3583_, 2, v___x_3580_);
return v___x_3583_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11));
v___x_3591_ = l_Lean_stringToMessageData(v___x_3590_);
return v___x_3591_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14(void){
_start:
{
lean_object* v___x_3593_; lean_object* v___x_3594_; 
v___x_3593_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13));
v___x_3594_ = l_Lean_stringToMessageData(v___x_3593_);
return v___x_3594_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v___x_3596_, lean_object* v_args_3597_, lean_object* v_ty_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_){
_start:
{
lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___y_3607_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___x_3623_; lean_object* v___y_3679_; lean_object* v___x_3680_; 
v___x_3621_ = lean_unsigned_to_nat(0u);
v___x_3622_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8);
v___x_3623_ = lean_st_mk_ref(v___x_3622_);
v___x_3680_ = l_Lean_Expr_collectFVars(v_ty_3598_, v___x_3623_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3680_) == 0)
{
lean_object* v___x_3681_; size_t v_sz_3682_; size_t v___x_3683_; lean_object* v___x_3684_; 
lean_dec_ref_known(v___x_3680_, 1);
v___x_3681_ = lean_box(0);
v_sz_3682_ = lean_array_size(v_args_3597_);
v___x_3683_ = ((size_t)0ULL);
v___x_3684_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_args_3597_, v_sz_3682_, v___x_3683_, v___x_3681_, v___x_3623_, v___y_3599_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3684_) == 0)
{
lean_dec_ref_known(v___x_3684_, 1);
goto v___jp_3624_;
}
else
{
v___y_3679_ = v___x_3684_;
goto v___jp_3678_;
}
}
else
{
v___y_3679_ = v___x_3680_;
goto v___jp_3678_;
}
v___jp_3604_:
{
lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; lean_object* v___x_3617_; uint8_t v___x_3618_; 
lean_inc_ref(v___y_3607_);
v___x_3608_ = l_Lean_stringToMessageData(v___y_3607_);
v___x_3609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___y_3606_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1);
v___x_3611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3611_, 0, v___x_3609_);
lean_ctor_set(v___x_3611_, 1, v___x_3610_);
v___x_3612_ = lean_array_to_list(v___y_3605_);
v___x_3613_ = l_Lean_MessageData_nil;
v___x_3614_ = l_Lean_MessageData_joinSep(v___x_3612_, v___x_3613_);
v___x_3615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3611_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3);
v___x_3617_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3617_, 0, v___x_3615_);
lean_ctor_set(v___x_3617_, 1, v___x_3616_);
v___x_3618_ = l_Lean_Expr_hasSorry(v___x_3596_);
if (v___x_3618_ == 0)
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3617_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
return v___x_3619_;
}
else
{
lean_object* v___x_3620_; 
v___x_3620_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_3617_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
return v___x_3620_;
}
}
v___jp_3624_:
{
lean_object* v___x_3625_; lean_object* v___x_3626_; 
v___x_3625_ = lean_st_ref_get(v___x_3623_);
lean_dec(v___x_3623_);
v___x_3626_ = l_Lean_CollectFVars_State_addDependencies(v___x_3625_, v___y_3599_, v___y_3600_, v___y_3601_, v___y_3602_);
if (lean_obj_tag(v___x_3626_) == 0)
{
lean_object* v_a_3627_; lean_object* v___x_3628_; lean_object* v___x_3629_; size_t v_sz_3630_; size_t v___x_3631_; lean_object* v___x_3632_; 
v_a_3627_ = lean_ctor_get(v___x_3626_, 0);
lean_inc(v_a_3627_);
lean_dec_ref_known(v___x_3626_, 1);
v___x_3628_ = lean_unsigned_to_nat(1u);
v___x_3629_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10));
v_sz_3630_ = lean_array_size(v_args_3597_);
v___x_3631_ = ((size_t)0ULL);
v___x_3632_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3627_, v_args_3597_, v_sz_3630_, v___x_3631_, v___x_3629_, v___y_3599_, v___y_3601_, v___y_3602_);
lean_dec(v_a_3627_);
if (lean_obj_tag(v___x_3632_) == 0)
{
lean_object* v_a_3633_; lean_object* v___x_3635_; uint8_t v_isShared_3636_; uint8_t v_isSharedCheck_3661_; 
v_a_3633_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3661_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3661_ == 0)
{
v___x_3635_ = v___x_3632_;
v_isShared_3636_ = v_isSharedCheck_3661_;
goto v_resetjp_3634_;
}
else
{
lean_inc(v_a_3633_);
lean_dec(v___x_3632_);
v___x_3635_ = lean_box(0);
v_isShared_3636_ = v_isSharedCheck_3661_;
goto v_resetjp_3634_;
}
v_resetjp_3634_:
{
lean_object* v_fst_3637_; lean_object* v___x_3639_; uint8_t v_isShared_3640_; uint8_t v_isSharedCheck_3659_; 
v_fst_3637_ = lean_ctor_get(v_a_3633_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v_a_3633_);
if (v_isSharedCheck_3659_ == 0)
{
lean_object* v_unused_3660_; 
v_unused_3660_ = lean_ctor_get(v_a_3633_, 1);
lean_dec(v_unused_3660_);
v___x_3639_ = v_a_3633_;
v_isShared_3640_ = v_isSharedCheck_3659_;
goto v_resetjp_3638_;
}
else
{
lean_inc(v_fst_3637_);
lean_dec(v_a_3633_);
v___x_3639_ = lean_box(0);
v_isShared_3640_ = v_isSharedCheck_3659_;
goto v_resetjp_3638_;
}
v_resetjp_3638_:
{
lean_object* v___x_3641_; uint8_t v___x_3642_; 
v___x_3641_ = lean_array_get_size(v_fst_3637_);
v___x_3642_ = lean_nat_dec_eq(v___x_3641_, v___x_3621_);
if (v___x_3642_ == 0)
{
lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3646_; lean_object* v___x_3648_; 
lean_del_object(v___x_3635_);
v___x_3643_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12);
v___x_3644_ = l_Nat_reprFast(v___x_3641_);
v___x_3645_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3644_);
v___x_3646_ = l_Lean_MessageData_ofFormat(v___x_3645_);
if (v_isShared_3640_ == 0)
{
lean_ctor_set_tag(v___x_3639_, 7);
lean_ctor_set(v___x_3639_, 1, v___x_3646_);
lean_ctor_set(v___x_3639_, 0, v___x_3643_);
v___x_3648_ = v___x_3639_;
goto v_reusejp_3647_;
}
else
{
lean_object* v_reuseFailAlloc_3654_; 
v_reuseFailAlloc_3654_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3654_, 0, v___x_3643_);
lean_ctor_set(v_reuseFailAlloc_3654_, 1, v___x_3646_);
v___x_3648_ = v_reuseFailAlloc_3654_;
goto v_reusejp_3647_;
}
v_reusejp_3647_:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; uint8_t v___x_3651_; 
v___x_3649_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14);
v___x_3650_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3650_, 0, v___x_3648_);
lean_ctor_set(v___x_3650_, 1, v___x_3649_);
v___x_3651_ = lean_nat_dec_eq(v___x_3641_, v___x_3628_);
if (v___x_3651_ == 0)
{
lean_object* v___x_3652_; 
v___x_3652_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__15));
v___y_3605_ = v_fst_3637_;
v___y_3606_ = v___x_3650_;
v___y_3607_ = v___x_3652_;
goto v___jp_3604_;
}
else
{
lean_object* v___x_3653_; 
v___x_3653_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___y_3605_ = v_fst_3637_;
v___y_3606_ = v___x_3650_;
v___y_3607_ = v___x_3653_;
goto v___jp_3604_;
}
}
}
else
{
lean_object* v___x_3655_; lean_object* v___x_3657_; 
lean_del_object(v___x_3639_);
lean_dec(v_fst_3637_);
v___x_3655_ = lean_box(0);
if (v_isShared_3636_ == 0)
{
lean_ctor_set(v___x_3635_, 0, v___x_3655_);
v___x_3657_ = v___x_3635_;
goto v_reusejp_3656_;
}
else
{
lean_object* v_reuseFailAlloc_3658_; 
v_reuseFailAlloc_3658_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3658_, 0, v___x_3655_);
v___x_3657_ = v_reuseFailAlloc_3658_;
goto v_reusejp_3656_;
}
v_reusejp_3656_:
{
return v___x_3657_;
}
}
}
}
}
else
{
lean_object* v_a_3662_; lean_object* v___x_3664_; uint8_t v_isShared_3665_; uint8_t v_isSharedCheck_3669_; 
v_a_3662_ = lean_ctor_get(v___x_3632_, 0);
v_isSharedCheck_3669_ = !lean_is_exclusive(v___x_3632_);
if (v_isSharedCheck_3669_ == 0)
{
v___x_3664_ = v___x_3632_;
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
else
{
lean_inc(v_a_3662_);
lean_dec(v___x_3632_);
v___x_3664_ = lean_box(0);
v_isShared_3665_ = v_isSharedCheck_3669_;
goto v_resetjp_3663_;
}
v_resetjp_3663_:
{
lean_object* v___x_3667_; 
if (v_isShared_3665_ == 0)
{
v___x_3667_ = v___x_3664_;
goto v_reusejp_3666_;
}
else
{
lean_object* v_reuseFailAlloc_3668_; 
v_reuseFailAlloc_3668_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3668_, 0, v_a_3662_);
v___x_3667_ = v_reuseFailAlloc_3668_;
goto v_reusejp_3666_;
}
v_reusejp_3666_:
{
return v___x_3667_;
}
}
}
}
else
{
lean_object* v_a_3670_; lean_object* v___x_3672_; uint8_t v_isShared_3673_; uint8_t v_isSharedCheck_3677_; 
v_a_3670_ = lean_ctor_get(v___x_3626_, 0);
v_isSharedCheck_3677_ = !lean_is_exclusive(v___x_3626_);
if (v_isSharedCheck_3677_ == 0)
{
v___x_3672_ = v___x_3626_;
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
else
{
lean_inc(v_a_3670_);
lean_dec(v___x_3626_);
v___x_3672_ = lean_box(0);
v_isShared_3673_ = v_isSharedCheck_3677_;
goto v_resetjp_3671_;
}
v_resetjp_3671_:
{
lean_object* v___x_3675_; 
if (v_isShared_3673_ == 0)
{
v___x_3675_ = v___x_3672_;
goto v_reusejp_3674_;
}
else
{
lean_object* v_reuseFailAlloc_3676_; 
v_reuseFailAlloc_3676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3676_, 0, v_a_3670_);
v___x_3675_ = v_reuseFailAlloc_3676_;
goto v_reusejp_3674_;
}
v_reusejp_3674_:
{
return v___x_3675_;
}
}
}
}
v___jp_3678_:
{
if (lean_obj_tag(v___y_3679_) == 0)
{
lean_dec_ref_known(v___y_3679_, 1);
goto v___jp_3624_;
}
else
{
lean_dec(v___x_3623_);
return v___y_3679_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v___x_3685_, lean_object* v_args_3686_, lean_object* v_ty_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_, lean_object* v___y_3692_){
_start:
{
lean_object* v_res_3693_; 
v_res_3693_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v___x_3685_, v_args_3686_, v_ty_3687_, v___y_3688_, v___y_3689_, v___y_3690_, v___y_3691_);
lean_dec(v___y_3691_);
lean_dec_ref(v___y_3690_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec_ref(v_args_3686_);
lean_dec_ref(v___x_3685_);
return v_res_3693_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object* v_e_3694_){
_start:
{
lean_object* v___x_3695_; 
v___x_3695_ = l_Lean_Expr_cleanupAnnotations(v_e_3694_);
switch(lean_obj_tag(v___x_3695_))
{
case 7:
{
lean_object* v_body_3696_; uint8_t v_binderInfo_3697_; uint8_t v___x_3698_; 
v_body_3696_ = lean_ctor_get(v___x_3695_, 2);
lean_inc_ref(v_body_3696_);
v_binderInfo_3697_ = lean_ctor_get_uint8(v___x_3695_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3695_, 3);
v___x_3698_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3697_);
if (v___x_3698_ == 0)
{
lean_object* v___x_3699_; uint8_t v___x_3700_; 
v___x_3699_ = lean_unsigned_to_nat(0u);
v___x_3700_ = lean_expr_has_loose_bvar(v_body_3696_, v___x_3699_);
if (v___x_3700_ == 0)
{
uint8_t v___x_3701_; 
lean_dec_ref(v_body_3696_);
v___x_3701_ = 1;
return v___x_3701_;
}
else
{
v_e_3694_ = v_body_3696_;
goto _start;
}
}
else
{
v_e_3694_ = v_body_3696_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3704_; 
v_body_3704_ = lean_ctor_get(v___x_3695_, 3);
lean_inc_ref(v_body_3704_);
lean_dec_ref_known(v___x_3695_, 4);
v_e_3694_ = v_body_3704_;
goto _start;
}
default: 
{
uint8_t v___x_3706_; 
lean_dec_ref(v___x_3695_);
v___x_3706_ = 0;
return v___x_3706_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_e_3707_){
_start:
{
uint8_t v_res_3708_; lean_object* v_r_3709_; 
v_res_3708_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_e_3707_);
v_r_3709_ = lean_box(v_res_3708_);
return v_r_3709_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_cinfo_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_, lean_object* v_a_3714_){
_start:
{
lean_object* v___x_3716_; uint8_t v___x_3717_; 
v___x_3716_ = l_Lean_ConstantInfo_type(v_cinfo_3710_);
lean_inc_ref(v___x_3716_);
v___x_3717_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(v___x_3716_);
if (v___x_3717_ == 0)
{
lean_object* v___x_3718_; lean_object* v___x_3719_; 
lean_dec_ref(v___x_3716_);
v___x_3718_ = lean_box(0);
v___x_3719_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3719_, 0, v___x_3718_);
return v___x_3719_;
}
else
{
lean_object* v___f_3720_; uint8_t v___x_3721_; lean_object* v___x_3722_; 
lean_inc_ref(v___x_3716_);
v___f_3720_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3720_, 0, v___x_3716_);
v___x_3721_ = 0;
v___x_3722_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v___x_3716_, v___f_3720_, v___x_3721_, v_a_3711_, v_a_3712_, v_a_3713_, v_a_3714_);
return v___x_3722_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_cinfo_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_, lean_object* v_a_3728_){
_start:
{
lean_object* v_res_3729_; 
v_res_3729_ = l_Lean_Meta_checkImpossibleInstance(v_cinfo_3723_, v_a_3724_, v_a_3725_, v_a_3726_, v_a_3727_);
lean_dec(v_a_3727_);
lean_dec_ref(v_a_3726_);
lean_dec(v_a_3725_);
lean_dec_ref(v_a_3724_);
lean_dec_ref(v_cinfo_3723_);
return v_res_3729_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v_00_u03b2_3730_, lean_object* v_k_3731_, lean_object* v_t_3732_){
_start:
{
uint8_t v___x_3733_; 
v___x_3733_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3731_, v_t_3732_);
return v___x_3733_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v_00_u03b2_3734_, lean_object* v_k_3735_, lean_object* v_t_3736_){
_start:
{
uint8_t v_res_3737_; lean_object* v_r_3738_; 
v_res_3737_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(v_00_u03b2_3734_, v_k_3735_, v_t_3736_);
lean_dec(v_t_3736_);
lean_dec(v_k_3735_);
v_r_3738_ = lean_box(v_res_3737_);
return v_r_3738_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_a_3739_, lean_object* v_as_3740_, size_t v_sz_3741_, size_t v_i_3742_, lean_object* v_b_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_, lean_object* v___y_3747_){
_start:
{
lean_object* v___x_3749_; 
v___x_3749_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3739_, v_as_3740_, v_sz_3741_, v_i_3742_, v_b_3743_, v___y_3744_, v___y_3746_, v___y_3747_);
return v___x_3749_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_a_3750_, lean_object* v_as_3751_, lean_object* v_sz_3752_, lean_object* v_i_3753_, lean_object* v_b_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_, lean_object* v___y_3759_){
_start:
{
size_t v_sz_boxed_3760_; size_t v_i_boxed_3761_; lean_object* v_res_3762_; 
v_sz_boxed_3760_ = lean_unbox_usize(v_sz_3752_);
lean_dec(v_sz_3752_);
v_i_boxed_3761_ = lean_unbox_usize(v_i_3753_);
lean_dec(v_i_3753_);
v_res_3762_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_a_3750_, v_as_3751_, v_sz_boxed_3760_, v_i_boxed_3761_, v_b_3754_, v___y_3755_, v___y_3756_, v___y_3757_, v___y_3758_);
lean_dec(v___y_3758_);
lean_dec_ref(v___y_3757_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec_ref(v_as_3751_);
lean_dec_ref(v_a_3750_);
return v_res_3762_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object* v_as_3763_, size_t v_sz_3764_, size_t v_i_3765_, lean_object* v_b_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_, lean_object* v___y_3771_){
_start:
{
lean_object* v___x_3773_; 
v___x_3773_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_as_3763_, v_sz_3764_, v_i_3765_, v_b_3766_, v___y_3767_, v___y_3768_, v___y_3770_, v___y_3771_);
return v___x_3773_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object* v_as_3774_, lean_object* v_sz_3775_, lean_object* v_i_3776_, lean_object* v_b_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_, lean_object* v___y_3783_){
_start:
{
size_t v_sz_boxed_3784_; size_t v_i_boxed_3785_; lean_object* v_res_3786_; 
v_sz_boxed_3784_ = lean_unbox_usize(v_sz_3775_);
lean_dec(v_sz_3775_);
v_i_boxed_3785_ = lean_unbox_usize(v_i_3776_);
lean_dec(v_i_3776_);
v_res_3786_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(v_as_3774_, v_sz_boxed_3784_, v_i_boxed_3785_, v_b_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_, v___y_3782_);
lean_dec(v___y_3782_);
lean_dec_ref(v___y_3781_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v_as_3774_);
return v_res_3786_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3789_ = l_Lean_stringToMessageData(v___x_3788_);
return v___x_3789_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3792_ = l_Lean_stringToMessageData(v___x_3791_);
return v___x_3792_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3794_; lean_object* v___x_3795_; 
v___x_3794_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3795_ = l_Lean_stringToMessageData(v___x_3794_);
return v___x_3795_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_c_3796_, lean_object* v_x_3797_, lean_object* v_target_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_){
_start:
{
lean_object* v___x_3804_; 
lean_inc_ref(v_target_3798_);
v___x_3804_ = l_Lean_Meta_isClass_x3f(v_target_3798_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
if (lean_obj_tag(v___x_3804_) == 0)
{
lean_object* v_a_3805_; lean_object* v___x_3807_; uint8_t v_isShared_3808_; uint8_t v_isSharedCheck_3823_; 
v_a_3805_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3823_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3823_ == 0)
{
v___x_3807_ = v___x_3804_;
v_isShared_3808_ = v_isSharedCheck_3823_;
goto v_resetjp_3806_;
}
else
{
lean_inc(v_a_3805_);
lean_dec(v___x_3804_);
v___x_3807_ = lean_box(0);
v_isShared_3808_ = v_isSharedCheck_3823_;
goto v_resetjp_3806_;
}
v_resetjp_3806_:
{
if (lean_obj_tag(v_a_3805_) == 0)
{
lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; lean_object* v___x_3818_; 
lean_del_object(v___x_3807_);
v___x_3809_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3810_ = l_Lean_MessageData_ofExpr(v_c_3796_);
v___x_3811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3811_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = l_Lean_MessageData_ofExpr(v_target_3798_);
v___x_3815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3813_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3817_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3817_, 0, v___x_3815_);
lean_ctor_set(v___x_3817_, 1, v___x_3816_);
v___x_3818_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3817_, v___y_3799_, v___y_3800_, v___y_3801_, v___y_3802_);
return v___x_3818_;
}
else
{
lean_object* v___x_3819_; lean_object* v___x_3821_; 
lean_dec_ref_known(v_a_3805_, 1);
lean_dec_ref(v_target_3798_);
lean_dec_ref(v_c_3796_);
v___x_3819_ = lean_box(0);
if (v_isShared_3808_ == 0)
{
lean_ctor_set(v___x_3807_, 0, v___x_3819_);
v___x_3821_ = v___x_3807_;
goto v_reusejp_3820_;
}
else
{
lean_object* v_reuseFailAlloc_3822_; 
v_reuseFailAlloc_3822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3822_, 0, v___x_3819_);
v___x_3821_ = v_reuseFailAlloc_3822_;
goto v_reusejp_3820_;
}
v_reusejp_3820_:
{
return v___x_3821_;
}
}
}
}
else
{
lean_object* v_a_3824_; lean_object* v___x_3826_; uint8_t v_isShared_3827_; uint8_t v_isSharedCheck_3831_; 
lean_dec_ref(v_target_3798_);
lean_dec_ref(v_c_3796_);
v_a_3824_ = lean_ctor_get(v___x_3804_, 0);
v_isSharedCheck_3831_ = !lean_is_exclusive(v___x_3804_);
if (v_isSharedCheck_3831_ == 0)
{
v___x_3826_ = v___x_3804_;
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
else
{
lean_inc(v_a_3824_);
lean_dec(v___x_3804_);
v___x_3826_ = lean_box(0);
v_isShared_3827_ = v_isSharedCheck_3831_;
goto v_resetjp_3825_;
}
v_resetjp_3825_:
{
lean_object* v___x_3829_; 
if (v_isShared_3827_ == 0)
{
v___x_3829_ = v___x_3826_;
goto v_reusejp_3828_;
}
else
{
lean_object* v_reuseFailAlloc_3830_; 
v_reuseFailAlloc_3830_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3830_, 0, v_a_3824_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_c_3832_, lean_object* v_x_3833_, lean_object* v_target_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_){
_start:
{
lean_object* v_res_3840_; 
v_res_3840_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_c_3832_, v_x_3833_, v_target_3834_, v___y_3835_, v___y_3836_, v___y_3837_, v___y_3838_);
lean_dec(v___y_3838_);
lean_dec_ref(v___y_3837_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec_ref(v_x_3833_);
return v_res_3840_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_c_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_, lean_object* v_a_3845_){
_start:
{
lean_object* v___x_3847_; 
lean_inc(v_a_3845_);
lean_inc_ref(v_a_3844_);
lean_inc(v_a_3843_);
lean_inc_ref(v_a_3842_);
lean_inc_ref(v_c_3841_);
v___x_3847_ = lean_infer_type(v_c_3841_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_);
if (lean_obj_tag(v___x_3847_) == 0)
{
lean_object* v_a_3848_; lean_object* v___f_3849_; uint8_t v___x_3850_; lean_object* v___x_3851_; 
v_a_3848_ = lean_ctor_get(v___x_3847_, 0);
lean_inc(v_a_3848_);
lean_dec_ref_known(v___x_3847_, 1);
v___f_3849_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3849_, 0, v_c_3841_);
v___x_3850_ = 0;
v___x_3851_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3848_, v___f_3849_, v___x_3850_, v___x_3850_, v_a_3842_, v_a_3843_, v_a_3844_, v_a_3845_);
return v___x_3851_;
}
else
{
lean_object* v_a_3852_; lean_object* v___x_3854_; uint8_t v_isShared_3855_; uint8_t v_isSharedCheck_3859_; 
lean_dec_ref(v_c_3841_);
v_a_3852_ = lean_ctor_get(v___x_3847_, 0);
v_isSharedCheck_3859_ = !lean_is_exclusive(v___x_3847_);
if (v_isSharedCheck_3859_ == 0)
{
v___x_3854_ = v___x_3847_;
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
else
{
lean_inc(v_a_3852_);
lean_dec(v___x_3847_);
v___x_3854_ = lean_box(0);
v_isShared_3855_ = v_isSharedCheck_3859_;
goto v_resetjp_3853_;
}
v_resetjp_3853_:
{
lean_object* v___x_3857_; 
if (v_isShared_3855_ == 0)
{
v___x_3857_ = v___x_3854_;
goto v_reusejp_3856_;
}
else
{
lean_object* v_reuseFailAlloc_3858_; 
v_reuseFailAlloc_3858_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3858_, 0, v_a_3852_);
v___x_3857_ = v_reuseFailAlloc_3858_;
goto v_reusejp_3856_;
}
v_reusejp_3856_:
{
return v___x_3857_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_c_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_, lean_object* v_a_3865_){
_start:
{
lean_object* v_res_3866_; 
v_res_3866_ = l_Lean_Meta_checkNonClassInstance(v_c_3860_, v_a_3861_, v_a_3862_, v_a_3863_, v_a_3864_);
lean_dec(v_a_3864_);
lean_dec_ref(v_a_3863_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
return v_res_3866_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3877_, lean_object* v___y_3878_){
_start:
{
lean_object* v___x_3880_; lean_object* v_env_3881_; lean_object* v___x_3882_; lean_object* v___x_3883_; 
v___x_3880_ = lean_st_ref_get(v___y_3878_);
v_env_3881_ = lean_ctor_get(v___x_3880_, 0);
lean_inc_ref(v_env_3881_);
lean_dec(v___x_3880_);
v___x_3882_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3881_, v_declName_3877_);
v___x_3883_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3883_, 0, v___x_3882_);
return v___x_3883_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3884_, lean_object* v___y_3885_, lean_object* v___y_3886_){
_start:
{
lean_object* v_res_3887_; 
v_res_3887_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3884_, v___y_3885_);
lean_dec(v___y_3885_);
return v_res_3887_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_, lean_object* v___y_3892_){
_start:
{
lean_object* v___x_3894_; 
v___x_3894_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3888_, v___y_3892_);
return v___x_3894_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_, lean_object* v___y_3900_){
_start:
{
lean_object* v_res_3901_; 
v_res_3901_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3895_, v___y_3896_, v___y_3897_, v___y_3898_, v___y_3899_);
lean_dec(v___y_3899_);
lean_dec_ref(v___y_3898_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
return v_res_3901_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3902_; 
v___x_3902_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3902_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3904_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
return v___x_3904_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
return v___x_3906_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3907_; lean_object* v___x_3908_; 
v___x_3907_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3908_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3908_, 0, v___x_3907_);
lean_ctor_set(v___x_3908_, 1, v___x_3907_);
lean_ctor_set(v___x_3908_, 2, v___x_3907_);
lean_ctor_set(v___x_3908_, 3, v___x_3907_);
lean_ctor_set(v___x_3908_, 4, v___x_3907_);
lean_ctor_set(v___x_3908_, 5, v___x_3907_);
return v___x_3908_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3909_, lean_object* v_b_3910_, uint8_t v_kind_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_, lean_object* v___y_3914_){
_start:
{
lean_object* v_currNamespace_3916_; lean_object* v___x_3917_; lean_object* v_env_3918_; lean_object* v_nextMacroScope_3919_; lean_object* v_ngen_3920_; lean_object* v_auxDeclNGen_3921_; lean_object* v_traceState_3922_; lean_object* v_messages_3923_; lean_object* v_infoState_3924_; lean_object* v_snapshotTasks_3925_; lean_object* v___x_3927_; uint8_t v_isShared_3928_; uint8_t v_isSharedCheck_3952_; 
v_currNamespace_3916_ = lean_ctor_get(v___y_3913_, 6);
v___x_3917_ = lean_st_ref_take(v___y_3914_);
v_env_3918_ = lean_ctor_get(v___x_3917_, 0);
v_nextMacroScope_3919_ = lean_ctor_get(v___x_3917_, 1);
v_ngen_3920_ = lean_ctor_get(v___x_3917_, 2);
v_auxDeclNGen_3921_ = lean_ctor_get(v___x_3917_, 3);
v_traceState_3922_ = lean_ctor_get(v___x_3917_, 4);
v_messages_3923_ = lean_ctor_get(v___x_3917_, 6);
v_infoState_3924_ = lean_ctor_get(v___x_3917_, 7);
v_snapshotTasks_3925_ = lean_ctor_get(v___x_3917_, 8);
v_isSharedCheck_3952_ = !lean_is_exclusive(v___x_3917_);
if (v_isSharedCheck_3952_ == 0)
{
lean_object* v_unused_3953_; 
v_unused_3953_ = lean_ctor_get(v___x_3917_, 5);
lean_dec(v_unused_3953_);
v___x_3927_ = v___x_3917_;
v_isShared_3928_ = v_isSharedCheck_3952_;
goto v_resetjp_3926_;
}
else
{
lean_inc(v_snapshotTasks_3925_);
lean_inc(v_infoState_3924_);
lean_inc(v_messages_3923_);
lean_inc(v_traceState_3922_);
lean_inc(v_auxDeclNGen_3921_);
lean_inc(v_ngen_3920_);
lean_inc(v_nextMacroScope_3919_);
lean_inc(v_env_3918_);
lean_dec(v___x_3917_);
v___x_3927_ = lean_box(0);
v_isShared_3928_ = v_isSharedCheck_3952_;
goto v_resetjp_3926_;
}
v_resetjp_3926_:
{
lean_object* v___x_3929_; lean_object* v___x_3930_; lean_object* v___x_3932_; 
lean_inc(v_currNamespace_3916_);
v___x_3929_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3918_, v_ext_3909_, v_b_3910_, v_kind_3911_, v_currNamespace_3916_);
v___x_3930_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3928_ == 0)
{
lean_ctor_set(v___x_3927_, 5, v___x_3930_);
lean_ctor_set(v___x_3927_, 0, v___x_3929_);
v___x_3932_ = v___x_3927_;
goto v_reusejp_3931_;
}
else
{
lean_object* v_reuseFailAlloc_3951_; 
v_reuseFailAlloc_3951_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3951_, 0, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3951_, 1, v_nextMacroScope_3919_);
lean_ctor_set(v_reuseFailAlloc_3951_, 2, v_ngen_3920_);
lean_ctor_set(v_reuseFailAlloc_3951_, 3, v_auxDeclNGen_3921_);
lean_ctor_set(v_reuseFailAlloc_3951_, 4, v_traceState_3922_);
lean_ctor_set(v_reuseFailAlloc_3951_, 5, v___x_3930_);
lean_ctor_set(v_reuseFailAlloc_3951_, 6, v_messages_3923_);
lean_ctor_set(v_reuseFailAlloc_3951_, 7, v_infoState_3924_);
lean_ctor_set(v_reuseFailAlloc_3951_, 8, v_snapshotTasks_3925_);
v___x_3932_ = v_reuseFailAlloc_3951_;
goto v_reusejp_3931_;
}
v_reusejp_3931_:
{
lean_object* v___x_3933_; lean_object* v___x_3934_; lean_object* v_mctx_3935_; lean_object* v_zetaDeltaFVarIds_3936_; lean_object* v_postponed_3937_; lean_object* v_diag_3938_; lean_object* v___x_3940_; uint8_t v_isShared_3941_; uint8_t v_isSharedCheck_3949_; 
v___x_3933_ = lean_st_ref_put(v___y_3914_, v___x_3932_);
v___x_3934_ = lean_st_ref_take(v___y_3912_);
v_mctx_3935_ = lean_ctor_get(v___x_3934_, 0);
v_zetaDeltaFVarIds_3936_ = lean_ctor_get(v___x_3934_, 2);
v_postponed_3937_ = lean_ctor_get(v___x_3934_, 3);
v_diag_3938_ = lean_ctor_get(v___x_3934_, 4);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3934_);
if (v_isSharedCheck_3949_ == 0)
{
lean_object* v_unused_3950_; 
v_unused_3950_ = lean_ctor_get(v___x_3934_, 1);
lean_dec(v_unused_3950_);
v___x_3940_ = v___x_3934_;
v_isShared_3941_ = v_isSharedCheck_3949_;
goto v_resetjp_3939_;
}
else
{
lean_inc(v_diag_3938_);
lean_inc(v_postponed_3937_);
lean_inc(v_zetaDeltaFVarIds_3936_);
lean_inc(v_mctx_3935_);
lean_dec(v___x_3934_);
v___x_3940_ = lean_box(0);
v_isShared_3941_ = v_isSharedCheck_3949_;
goto v_resetjp_3939_;
}
v_resetjp_3939_:
{
lean_object* v___x_3942_; lean_object* v___x_3944_; 
v___x_3942_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3941_ == 0)
{
lean_ctor_set(v___x_3940_, 1, v___x_3942_);
v___x_3944_ = v___x_3940_;
goto v_reusejp_3943_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v_mctx_3935_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v___x_3942_);
lean_ctor_set(v_reuseFailAlloc_3948_, 2, v_zetaDeltaFVarIds_3936_);
lean_ctor_set(v_reuseFailAlloc_3948_, 3, v_postponed_3937_);
lean_ctor_set(v_reuseFailAlloc_3948_, 4, v_diag_3938_);
v___x_3944_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3943_;
}
v_reusejp_3943_:
{
lean_object* v___x_3945_; lean_object* v___x_3946_; lean_object* v___x_3947_; 
v___x_3945_ = lean_st_ref_put(v___y_3912_, v___x_3944_);
v___x_3946_ = lean_box(0);
v___x_3947_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3947_, 0, v___x_3946_);
return v___x_3947_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3954_, lean_object* v_b_3955_, lean_object* v_kind_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_, lean_object* v___y_3960_){
_start:
{
uint8_t v_kind_boxed_3961_; lean_object* v_res_3962_; 
v_kind_boxed_3961_ = lean_unbox(v_kind_3956_);
v_res_3962_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3954_, v_b_3955_, v_kind_boxed_3961_, v___y_3957_, v___y_3958_, v___y_3959_);
lean_dec(v___y_3959_);
lean_dec_ref(v___y_3958_);
lean_dec(v___y_3957_);
return v_res_3962_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3963_, lean_object* v_00_u03b2_3964_, lean_object* v_00_u03c3_3965_, lean_object* v_ext_3966_, lean_object* v_b_3967_, uint8_t v_kind_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_, lean_object* v___y_3972_){
_start:
{
lean_object* v___x_3974_; 
v___x_3974_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3966_, v_b_3967_, v_kind_3968_, v___y_3970_, v___y_3971_, v___y_3972_);
return v___x_3974_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_3975_, lean_object* v_00_u03b2_3976_, lean_object* v_00_u03c3_3977_, lean_object* v_ext_3978_, lean_object* v_b_3979_, lean_object* v_kind_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_, lean_object* v___y_3985_){
_start:
{
uint8_t v_kind_boxed_3986_; lean_object* v_res_3987_; 
v_kind_boxed_3986_ = lean_unbox(v_kind_3980_);
v_res_3987_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_3975_, v_00_u03b2_3976_, v_00_u03c3_3977_, v_ext_3978_, v_b_3979_, v_kind_boxed_3986_, v___y_3981_, v___y_3982_, v___y_3983_, v___y_3984_);
lean_dec(v___y_3984_);
lean_dec_ref(v___y_3983_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
return v_res_3987_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_3988_, lean_object* v___y_3989_){
_start:
{
lean_object* v___x_3991_; lean_object* v_env_3992_; uint8_t v___x_3993_; lean_object* v___x_3994_; lean_object* v___x_3995_; 
v___x_3991_ = lean_st_ref_get(v___y_3989_);
v_env_3992_ = lean_ctor_get(v___x_3991_, 0);
lean_inc_ref(v_env_3992_);
lean_dec(v___x_3991_);
v___x_3993_ = l_Lean_getReducibilityStatusCore(v_env_3992_, v_declName_3988_);
v___x_3994_ = lean_box(v___x_3993_);
v___x_3995_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3995_, 0, v___x_3994_);
return v___x_3995_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_3996_, lean_object* v___y_3997_, lean_object* v___y_3998_){
_start:
{
lean_object* v_res_3999_; 
v_res_3999_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3996_, v___y_3997_);
lean_dec(v___y_3997_);
return v_res_3999_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4000_, v___y_4004_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_, lean_object* v___y_4012_){
_start:
{
lean_object* v_res_4013_; 
v_res_4013_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_4007_, v___y_4008_, v___y_4009_, v___y_4010_, v___y_4011_);
lean_dec(v___y_4011_);
lean_dec_ref(v___y_4010_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
return v_res_4013_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_4014_, lean_object* v_msg_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_, lean_object* v___y_4019_){
_start:
{
lean_object* v_fileName_4021_; lean_object* v_fileMap_4022_; lean_object* v_options_4023_; lean_object* v_currRecDepth_4024_; lean_object* v_maxRecDepth_4025_; lean_object* v_ref_4026_; lean_object* v_currNamespace_4027_; lean_object* v_openDecls_4028_; lean_object* v_initHeartbeats_4029_; lean_object* v_maxHeartbeats_4030_; lean_object* v_quotContext_4031_; lean_object* v_currMacroScope_4032_; uint8_t v_diag_4033_; lean_object* v_cancelTk_x3f_4034_; uint8_t v_suppressElabErrors_4035_; lean_object* v_inheritedTraceOptions_4036_; lean_object* v_ref_4037_; lean_object* v___x_4038_; lean_object* v___x_4039_; 
v_fileName_4021_ = lean_ctor_get(v___y_4018_, 0);
v_fileMap_4022_ = lean_ctor_get(v___y_4018_, 1);
v_options_4023_ = lean_ctor_get(v___y_4018_, 2);
v_currRecDepth_4024_ = lean_ctor_get(v___y_4018_, 3);
v_maxRecDepth_4025_ = lean_ctor_get(v___y_4018_, 4);
v_ref_4026_ = lean_ctor_get(v___y_4018_, 5);
v_currNamespace_4027_ = lean_ctor_get(v___y_4018_, 6);
v_openDecls_4028_ = lean_ctor_get(v___y_4018_, 7);
v_initHeartbeats_4029_ = lean_ctor_get(v___y_4018_, 8);
v_maxHeartbeats_4030_ = lean_ctor_get(v___y_4018_, 9);
v_quotContext_4031_ = lean_ctor_get(v___y_4018_, 10);
v_currMacroScope_4032_ = lean_ctor_get(v___y_4018_, 11);
v_diag_4033_ = lean_ctor_get_uint8(v___y_4018_, sizeof(void*)*14);
v_cancelTk_x3f_4034_ = lean_ctor_get(v___y_4018_, 12);
v_suppressElabErrors_4035_ = lean_ctor_get_uint8(v___y_4018_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4036_ = lean_ctor_get(v___y_4018_, 13);
v_ref_4037_ = l_Lean_replaceRef(v_ref_4014_, v_ref_4026_);
lean_inc_ref(v_inheritedTraceOptions_4036_);
lean_inc(v_cancelTk_x3f_4034_);
lean_inc(v_currMacroScope_4032_);
lean_inc(v_quotContext_4031_);
lean_inc(v_maxHeartbeats_4030_);
lean_inc(v_initHeartbeats_4029_);
lean_inc(v_openDecls_4028_);
lean_inc(v_currNamespace_4027_);
lean_inc(v_maxRecDepth_4025_);
lean_inc(v_currRecDepth_4024_);
lean_inc_ref(v_options_4023_);
lean_inc_ref(v_fileMap_4022_);
lean_inc_ref(v_fileName_4021_);
v___x_4038_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4038_, 0, v_fileName_4021_);
lean_ctor_set(v___x_4038_, 1, v_fileMap_4022_);
lean_ctor_set(v___x_4038_, 2, v_options_4023_);
lean_ctor_set(v___x_4038_, 3, v_currRecDepth_4024_);
lean_ctor_set(v___x_4038_, 4, v_maxRecDepth_4025_);
lean_ctor_set(v___x_4038_, 5, v_ref_4037_);
lean_ctor_set(v___x_4038_, 6, v_currNamespace_4027_);
lean_ctor_set(v___x_4038_, 7, v_openDecls_4028_);
lean_ctor_set(v___x_4038_, 8, v_initHeartbeats_4029_);
lean_ctor_set(v___x_4038_, 9, v_maxHeartbeats_4030_);
lean_ctor_set(v___x_4038_, 10, v_quotContext_4031_);
lean_ctor_set(v___x_4038_, 11, v_currMacroScope_4032_);
lean_ctor_set(v___x_4038_, 12, v_cancelTk_x3f_4034_);
lean_ctor_set(v___x_4038_, 13, v_inheritedTraceOptions_4036_);
lean_ctor_set_uint8(v___x_4038_, sizeof(void*)*14, v_diag_4033_);
lean_ctor_set_uint8(v___x_4038_, sizeof(void*)*14 + 1, v_suppressElabErrors_4035_);
v___x_4039_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_4015_, v___y_4016_, v___y_4017_, v___x_4038_, v___y_4019_);
lean_dec_ref_known(v___x_4038_, 14);
return v___x_4039_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_4040_, lean_object* v_msg_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_, lean_object* v___y_4046_){
_start:
{
lean_object* v_res_4047_; 
v_res_4047_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4040_, v_msg_4041_, v___y_4042_, v___y_4043_, v___y_4044_, v___y_4045_);
lean_dec(v___y_4045_);
lean_dec_ref(v___y_4044_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v_ref_4040_);
return v_res_4047_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_4048_; 
v___x_4048_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4048_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4049_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4050_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
return v___x_4050_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4051_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4052_ = lean_unsigned_to_nat(0u);
v___x_4053_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
lean_ctor_set(v___x_4053_, 1, v___x_4052_);
lean_ctor_set(v___x_4053_, 2, v___x_4052_);
lean_ctor_set(v___x_4053_, 3, v___x_4052_);
lean_ctor_set(v___x_4053_, 4, v___x_4051_);
lean_ctor_set(v___x_4053_, 5, v___x_4051_);
lean_ctor_set(v___x_4053_, 6, v___x_4051_);
lean_ctor_set(v___x_4053_, 7, v___x_4051_);
lean_ctor_set(v___x_4053_, 8, v___x_4051_);
lean_ctor_set(v___x_4053_, 9, v___x_4051_);
lean_ctor_set(v___x_4053_, 10, v___x_4051_);
return v___x_4053_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; 
v___x_4054_ = lean_unsigned_to_nat(32u);
v___x_4055_ = lean_mk_empty_array_with_capacity(v___x_4054_);
v___x_4056_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4056_, 0, v___x_4055_);
return v___x_4056_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; 
v___x_4057_ = ((size_t)5ULL);
v___x_4058_ = lean_unsigned_to_nat(0u);
v___x_4059_ = lean_unsigned_to_nat(32u);
v___x_4060_ = lean_mk_empty_array_with_capacity(v___x_4059_);
v___x_4061_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4062_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4062_, 0, v___x_4061_);
lean_ctor_set(v___x_4062_, 1, v___x_4060_);
lean_ctor_set(v___x_4062_, 2, v___x_4058_);
lean_ctor_set(v___x_4062_, 3, v___x_4058_);
lean_ctor_set_usize(v___x_4062_, 4, v___x_4057_);
return v___x_4062_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4063_ = lean_box(1);
v___x_4064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_4065_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4066_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4066_, 0, v___x_4065_);
lean_ctor_set(v___x_4066_, 1, v___x_4064_);
lean_ctor_set(v___x_4066_, 2, v___x_4063_);
return v___x_4066_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4068_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_4069_ = l_Lean_stringToMessageData(v___x_4068_);
return v___x_4069_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_4072_ = l_Lean_stringToMessageData(v___x_4071_);
return v___x_4072_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4074_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_4075_ = l_Lean_stringToMessageData(v___x_4074_);
return v___x_4075_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_4078_ = l_Lean_stringToMessageData(v___x_4077_);
return v___x_4078_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_4081_ = l_Lean_stringToMessageData(v___x_4080_);
return v___x_4081_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_4084_ = l_Lean_stringToMessageData(v___x_4083_);
return v___x_4084_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_4086_; lean_object* v___x_4087_; 
v___x_4086_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_4087_ = l_Lean_stringToMessageData(v___x_4086_);
return v___x_4087_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_4088_, lean_object* v_declHint_4089_, lean_object* v___y_4090_){
_start:
{
lean_object* v___x_4092_; lean_object* v_env_4093_; uint8_t v___x_4094_; 
v___x_4092_ = lean_st_ref_get(v___y_4090_);
v_env_4093_ = lean_ctor_get(v___x_4092_, 0);
lean_inc_ref(v_env_4093_);
lean_dec(v___x_4092_);
v___x_4094_ = l_Lean_Name_isAnonymous(v_declHint_4089_);
if (v___x_4094_ == 0)
{
uint8_t v_isExporting_4095_; 
v_isExporting_4095_ = lean_ctor_get_uint8(v_env_4093_, sizeof(void*)*8);
if (v_isExporting_4095_ == 0)
{
lean_object* v___x_4096_; 
lean_dec_ref(v_env_4093_);
lean_dec(v_declHint_4089_);
v___x_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4096_, 0, v_msg_4088_);
return v___x_4096_;
}
else
{
lean_object* v___x_4097_; uint8_t v___x_4098_; 
lean_inc_ref(v_env_4093_);
v___x_4097_ = l_Lean_Environment_setExporting(v_env_4093_, v___x_4094_);
lean_inc(v_declHint_4089_);
lean_inc_ref(v___x_4097_);
v___x_4098_ = l_Lean_Environment_contains(v___x_4097_, v_declHint_4089_, v_isExporting_4095_);
if (v___x_4098_ == 0)
{
lean_object* v___x_4099_; 
lean_dec_ref(v___x_4097_);
lean_dec_ref(v_env_4093_);
lean_dec(v_declHint_4089_);
v___x_4099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4099_, 0, v_msg_4088_);
return v___x_4099_;
}
else
{
lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v___x_4104_; lean_object* v_c_4105_; lean_object* v___x_4106_; 
v___x_4100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4101_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_4102_ = l_Lean_Options_empty;
v___x_4103_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4097_);
lean_ctor_set(v___x_4103_, 1, v___x_4100_);
lean_ctor_set(v___x_4103_, 2, v___x_4101_);
lean_ctor_set(v___x_4103_, 3, v___x_4102_);
lean_inc(v_declHint_4089_);
v___x_4104_ = l_Lean_MessageData_ofConstName(v_declHint_4089_, v___x_4094_);
v_c_4105_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4105_, 0, v___x_4103_);
lean_ctor_set(v_c_4105_, 1, v___x_4104_);
v___x_4106_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4093_, v_declHint_4089_);
if (lean_obj_tag(v___x_4106_) == 0)
{
lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; lean_object* v___x_4113_; 
lean_dec_ref(v_env_4093_);
lean_dec(v_declHint_4089_);
v___x_4107_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4107_);
lean_ctor_set(v___x_4108_, 1, v_c_4105_);
v___x_4109_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_4110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4108_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = l_Lean_MessageData_note(v___x_4110_);
v___x_4112_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4112_, 0, v_msg_4088_);
lean_ctor_set(v___x_4112_, 1, v___x_4111_);
v___x_4113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4112_);
return v___x_4113_;
}
else
{
lean_object* v_val_4114_; lean_object* v___x_4116_; uint8_t v_isShared_4117_; uint8_t v_isSharedCheck_4149_; 
v_val_4114_ = lean_ctor_get(v___x_4106_, 0);
v_isSharedCheck_4149_ = !lean_is_exclusive(v___x_4106_);
if (v_isSharedCheck_4149_ == 0)
{
v___x_4116_ = v___x_4106_;
v_isShared_4117_ = v_isSharedCheck_4149_;
goto v_resetjp_4115_;
}
else
{
lean_inc(v_val_4114_);
lean_dec(v___x_4106_);
v___x_4116_ = lean_box(0);
v_isShared_4117_ = v_isSharedCheck_4149_;
goto v_resetjp_4115_;
}
v_resetjp_4115_:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v___x_4120_; lean_object* v_mod_4121_; uint8_t v___x_4122_; 
v___x_4118_ = lean_box(0);
v___x_4119_ = l_Lean_Environment_header(v_env_4093_);
lean_dec_ref(v_env_4093_);
v___x_4120_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4119_);
v_mod_4121_ = lean_array_get(v___x_4118_, v___x_4120_, v_val_4114_);
lean_dec(v_val_4114_);
lean_dec_ref(v___x_4120_);
v___x_4122_ = l_Lean_isPrivateName(v_declHint_4089_);
lean_dec(v_declHint_4089_);
if (v___x_4122_ == 0)
{
lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v___x_4134_; 
v___x_4123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_4124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4123_);
lean_ctor_set(v___x_4124_, 1, v_c_4105_);
v___x_4125_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_4126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4124_);
lean_ctor_set(v___x_4126_, 1, v___x_4125_);
v___x_4127_ = l_Lean_MessageData_ofName(v_mod_4121_);
v___x_4128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4126_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
v___x_4129_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_4130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4130_, 0, v___x_4128_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
v___x_4131_ = l_Lean_MessageData_note(v___x_4130_);
v___x_4132_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4132_, 0, v_msg_4088_);
lean_ctor_set(v___x_4132_, 1, v___x_4131_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set_tag(v___x_4116_, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4132_);
v___x_4134_ = v___x_4116_;
goto v_reusejp_4133_;
}
else
{
lean_object* v_reuseFailAlloc_4135_; 
v_reuseFailAlloc_4135_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4135_, 0, v___x_4132_);
v___x_4134_ = v_reuseFailAlloc_4135_;
goto v_reusejp_4133_;
}
v_reusejp_4133_:
{
return v___x_4134_;
}
}
else
{
lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4145_; lean_object* v___x_4147_; 
v___x_4136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4136_);
lean_ctor_set(v___x_4137_, 1, v_c_4105_);
v___x_4138_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_4139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4137_);
lean_ctor_set(v___x_4139_, 1, v___x_4138_);
v___x_4140_ = l_Lean_MessageData_ofName(v_mod_4121_);
v___x_4141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4139_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_4143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4143_, 0, v___x_4141_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
v___x_4144_ = l_Lean_MessageData_note(v___x_4143_);
v___x_4145_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4145_, 0, v_msg_4088_);
lean_ctor_set(v___x_4145_, 1, v___x_4144_);
if (v_isShared_4117_ == 0)
{
lean_ctor_set_tag(v___x_4116_, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4145_);
v___x_4147_ = v___x_4116_;
goto v_reusejp_4146_;
}
else
{
lean_object* v_reuseFailAlloc_4148_; 
v_reuseFailAlloc_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4148_, 0, v___x_4145_);
v___x_4147_ = v_reuseFailAlloc_4148_;
goto v_reusejp_4146_;
}
v_reusejp_4146_:
{
return v___x_4147_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4150_; 
lean_dec_ref(v_env_4093_);
lean_dec(v_declHint_4089_);
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v_msg_4088_);
return v___x_4150_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_4151_, lean_object* v_declHint_4152_, lean_object* v___y_4153_, lean_object* v___y_4154_){
_start:
{
lean_object* v_res_4155_; 
v_res_4155_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4151_, v_declHint_4152_, v___y_4153_);
lean_dec(v___y_4153_);
return v_res_4155_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(lean_object* v_msg_4156_, lean_object* v_declHint_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_, lean_object* v___y_4161_){
_start:
{
lean_object* v___x_4163_; lean_object* v_a_4164_; lean_object* v___x_4166_; uint8_t v_isShared_4167_; uint8_t v_isSharedCheck_4173_; 
v___x_4163_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4156_, v_declHint_4157_, v___y_4161_);
v_a_4164_ = lean_ctor_get(v___x_4163_, 0);
v_isSharedCheck_4173_ = !lean_is_exclusive(v___x_4163_);
if (v_isSharedCheck_4173_ == 0)
{
v___x_4166_ = v___x_4163_;
v_isShared_4167_ = v_isSharedCheck_4173_;
goto v_resetjp_4165_;
}
else
{
lean_inc(v_a_4164_);
lean_dec(v___x_4163_);
v___x_4166_ = lean_box(0);
v_isShared_4167_ = v_isSharedCheck_4173_;
goto v_resetjp_4165_;
}
v_resetjp_4165_:
{
lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4171_; 
v___x_4168_ = l_Lean_unknownIdentifierMessageTag;
v___x_4169_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4168_);
lean_ctor_set(v___x_4169_, 1, v_a_4164_);
if (v_isShared_4167_ == 0)
{
lean_ctor_set(v___x_4166_, 0, v___x_4169_);
v___x_4171_ = v___x_4166_;
goto v_reusejp_4170_;
}
else
{
lean_object* v_reuseFailAlloc_4172_; 
v_reuseFailAlloc_4172_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4172_, 0, v___x_4169_);
v___x_4171_ = v_reuseFailAlloc_4172_;
goto v_reusejp_4170_;
}
v_reusejp_4170_:
{
return v___x_4171_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_4174_, lean_object* v_declHint_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_, lean_object* v___y_4180_){
_start:
{
lean_object* v_res_4181_; 
v_res_4181_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4174_, v_declHint_4175_, v___y_4176_, v___y_4177_, v___y_4178_, v___y_4179_);
lean_dec(v___y_4179_);
lean_dec_ref(v___y_4178_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
return v_res_4181_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_ref_4182_, lean_object* v_msg_4183_, lean_object* v_declHint_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_){
_start:
{
lean_object* v___x_4190_; lean_object* v_a_4191_; lean_object* v___x_4192_; 
v___x_4190_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4183_, v_declHint_4184_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
v_a_4191_ = lean_ctor_get(v___x_4190_, 0);
lean_inc(v_a_4191_);
lean_dec_ref(v___x_4190_);
v___x_4192_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4182_, v_a_4191_, v___y_4185_, v___y_4186_, v___y_4187_, v___y_4188_);
return v___x_4192_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_ref_4193_, lean_object* v_msg_4194_, lean_object* v_declHint_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_, lean_object* v___y_4200_){
_start:
{
lean_object* v_res_4201_; 
v_res_4201_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4193_, v_msg_4194_, v_declHint_4195_, v___y_4196_, v___y_4197_, v___y_4198_, v___y_4199_);
lean_dec(v___y_4199_);
lean_dec_ref(v___y_4198_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec(v_ref_4193_);
return v_res_4201_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_4203_; lean_object* v___x_4204_; 
v___x_4203_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_4204_ = l_Lean_stringToMessageData(v___x_4203_);
return v___x_4204_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_4205_, lean_object* v_constName_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_, lean_object* v___y_4210_){
_start:
{
lean_object* v___x_4212_; uint8_t v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; lean_object* v___x_4218_; 
v___x_4212_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_4213_ = 0;
lean_inc(v_constName_4206_);
v___x_4214_ = l_Lean_MessageData_ofConstName(v_constName_4206_, v___x_4213_);
v___x_4215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4212_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v___x_4216_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4217_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4217_, 0, v___x_4215_);
lean_ctor_set(v___x_4217_, 1, v___x_4216_);
v___x_4218_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4205_, v___x_4217_, v_constName_4206_, v___y_4207_, v___y_4208_, v___y_4209_, v___y_4210_);
return v___x_4218_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_4219_, lean_object* v_constName_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_){
_start:
{
lean_object* v_res_4226_; 
v_res_4226_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4219_, v_constName_4220_, v___y_4221_, v___y_4222_, v___y_4223_, v___y_4224_);
lean_dec(v___y_4224_);
lean_dec_ref(v___y_4223_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v_ref_4219_);
return v_res_4226_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_){
_start:
{
lean_object* v_ref_4233_; lean_object* v___x_4234_; 
v_ref_4233_ = lean_ctor_get(v___y_4230_, 5);
v___x_4234_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4233_, v_constName_4227_, v___y_4228_, v___y_4229_, v___y_4230_, v___y_4231_);
return v___x_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_){
_start:
{
lean_object* v_res_4241_; 
v_res_4241_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4235_, v___y_4236_, v___y_4237_, v___y_4238_, v___y_4239_);
lean_dec(v___y_4239_);
lean_dec_ref(v___y_4238_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
return v_res_4241_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_, lean_object* v___y_4246_){
_start:
{
lean_object* v___x_4248_; lean_object* v_env_4249_; uint8_t v___x_4250_; lean_object* v___x_4251_; 
v___x_4248_ = lean_st_ref_get(v___y_4246_);
v_env_4249_ = lean_ctor_get(v___x_4248_, 0);
lean_inc_ref(v_env_4249_);
lean_dec(v___x_4248_);
v___x_4250_ = 0;
lean_inc(v_constName_4242_);
v___x_4251_ = l_Lean_Environment_find_x3f(v_env_4249_, v_constName_4242_, v___x_4250_);
if (lean_obj_tag(v___x_4251_) == 0)
{
lean_object* v___x_4252_; 
v___x_4252_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4242_, v___y_4243_, v___y_4244_, v___y_4245_, v___y_4246_);
return v___x_4252_;
}
else
{
lean_object* v_val_4253_; lean_object* v___x_4255_; uint8_t v_isShared_4256_; uint8_t v_isSharedCheck_4260_; 
lean_dec(v_constName_4242_);
v_val_4253_ = lean_ctor_get(v___x_4251_, 0);
v_isSharedCheck_4260_ = !lean_is_exclusive(v___x_4251_);
if (v_isSharedCheck_4260_ == 0)
{
v___x_4255_ = v___x_4251_;
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
else
{
lean_inc(v_val_4253_);
lean_dec(v___x_4251_);
v___x_4255_ = lean_box(0);
v_isShared_4256_ = v_isSharedCheck_4260_;
goto v_resetjp_4254_;
}
v_resetjp_4254_:
{
lean_object* v___x_4258_; 
if (v_isShared_4256_ == 0)
{
lean_ctor_set_tag(v___x_4255_, 0);
v___x_4258_ = v___x_4255_;
goto v_reusejp_4257_;
}
else
{
lean_object* v_reuseFailAlloc_4259_; 
v_reuseFailAlloc_4259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4259_, 0, v_val_4253_);
v___x_4258_ = v_reuseFailAlloc_4259_;
goto v_reusejp_4257_;
}
v_reusejp_4257_:
{
return v___x_4258_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_){
_start:
{
lean_object* v_res_4267_; 
v_res_4267_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_4261_, v___y_4262_, v___y_4263_, v___y_4264_, v___y_4265_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
return v_res_4267_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_){
_start:
{
lean_object* v___x_4274_; lean_object* v_env_4275_; uint8_t v___x_4276_; lean_object* v___x_4277_; 
v___x_4274_ = lean_st_ref_get(v___y_4272_);
v_env_4275_ = lean_ctor_get(v___x_4274_, 0);
lean_inc_ref(v_env_4275_);
lean_dec(v___x_4274_);
v___x_4276_ = 0;
lean_inc(v_constName_4268_);
v___x_4277_ = l_Lean_Environment_findConstVal_x3f(v_env_4275_, v_constName_4268_, v___x_4276_);
if (lean_obj_tag(v___x_4277_) == 0)
{
lean_object* v___x_4278_; 
v___x_4278_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4268_, v___y_4269_, v___y_4270_, v___y_4271_, v___y_4272_);
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
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_){
_start:
{
lean_object* v_res_4293_; 
v_res_4293_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4287_, v___y_4288_, v___y_4289_, v___y_4290_, v___y_4291_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
return v_res_4293_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4294_, lean_object* v_a_4295_){
_start:
{
if (lean_obj_tag(v_a_4294_) == 0)
{
lean_object* v___x_4296_; 
v___x_4296_ = l_List_reverse___redArg(v_a_4295_);
return v___x_4296_;
}
else
{
lean_object* v_head_4297_; lean_object* v_tail_4298_; lean_object* v___x_4300_; uint8_t v_isShared_4301_; uint8_t v_isSharedCheck_4307_; 
v_head_4297_ = lean_ctor_get(v_a_4294_, 0);
v_tail_4298_ = lean_ctor_get(v_a_4294_, 1);
v_isSharedCheck_4307_ = !lean_is_exclusive(v_a_4294_);
if (v_isSharedCheck_4307_ == 0)
{
v___x_4300_ = v_a_4294_;
v_isShared_4301_ = v_isSharedCheck_4307_;
goto v_resetjp_4299_;
}
else
{
lean_inc(v_tail_4298_);
lean_inc(v_head_4297_);
lean_dec(v_a_4294_);
v___x_4300_ = lean_box(0);
v_isShared_4301_ = v_isSharedCheck_4307_;
goto v_resetjp_4299_;
}
v_resetjp_4299_:
{
lean_object* v___x_4302_; lean_object* v___x_4304_; 
v___x_4302_ = l_Lean_mkLevelParam(v_head_4297_);
if (v_isShared_4301_ == 0)
{
lean_ctor_set(v___x_4300_, 1, v_a_4295_);
lean_ctor_set(v___x_4300_, 0, v___x_4302_);
v___x_4304_ = v___x_4300_;
goto v_reusejp_4303_;
}
else
{
lean_object* v_reuseFailAlloc_4306_; 
v_reuseFailAlloc_4306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4306_, 0, v___x_4302_);
lean_ctor_set(v_reuseFailAlloc_4306_, 1, v_a_4295_);
v___x_4304_ = v_reuseFailAlloc_4306_;
goto v_reusejp_4303_;
}
v_reusejp_4303_:
{
v_a_4294_ = v_tail_4298_;
v_a_4295_ = v___x_4304_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_, lean_object* v___y_4312_){
_start:
{
lean_object* v___x_4314_; 
lean_inc(v_constName_4308_);
v___x_4314_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4308_, v___y_4309_, v___y_4310_, v___y_4311_, v___y_4312_);
if (lean_obj_tag(v___x_4314_) == 0)
{
lean_object* v_a_4315_; lean_object* v___x_4317_; uint8_t v_isShared_4318_; uint8_t v_isSharedCheck_4326_; 
v_a_4315_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4326_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4326_ == 0)
{
v___x_4317_ = v___x_4314_;
v_isShared_4318_ = v_isSharedCheck_4326_;
goto v_resetjp_4316_;
}
else
{
lean_inc(v_a_4315_);
lean_dec(v___x_4314_);
v___x_4317_ = lean_box(0);
v_isShared_4318_ = v_isSharedCheck_4326_;
goto v_resetjp_4316_;
}
v_resetjp_4316_:
{
lean_object* v_levelParams_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4322_; lean_object* v___x_4324_; 
v_levelParams_4319_ = lean_ctor_get(v_a_4315_, 1);
lean_inc(v_levelParams_4319_);
lean_dec(v_a_4315_);
v___x_4320_ = lean_box(0);
v___x_4321_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4319_, v___x_4320_);
v___x_4322_ = l_Lean_mkConst(v_constName_4308_, v___x_4321_);
if (v_isShared_4318_ == 0)
{
lean_ctor_set(v___x_4317_, 0, v___x_4322_);
v___x_4324_ = v___x_4317_;
goto v_reusejp_4323_;
}
else
{
lean_object* v_reuseFailAlloc_4325_; 
v_reuseFailAlloc_4325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4325_, 0, v___x_4322_);
v___x_4324_ = v_reuseFailAlloc_4325_;
goto v_reusejp_4323_;
}
v_reusejp_4323_:
{
return v___x_4324_;
}
}
}
else
{
lean_object* v_a_4327_; lean_object* v___x_4329_; uint8_t v_isShared_4330_; uint8_t v_isSharedCheck_4334_; 
lean_dec(v_constName_4308_);
v_a_4327_ = lean_ctor_get(v___x_4314_, 0);
v_isSharedCheck_4334_ = !lean_is_exclusive(v___x_4314_);
if (v_isSharedCheck_4334_ == 0)
{
v___x_4329_ = v___x_4314_;
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
else
{
lean_inc(v_a_4327_);
lean_dec(v___x_4314_);
v___x_4329_ = lean_box(0);
v_isShared_4330_ = v_isSharedCheck_4334_;
goto v_resetjp_4328_;
}
v_resetjp_4328_:
{
lean_object* v___x_4332_; 
if (v_isShared_4330_ == 0)
{
v___x_4332_ = v___x_4329_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4333_; 
v_reuseFailAlloc_4333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4333_, 0, v_a_4327_);
v___x_4332_ = v_reuseFailAlloc_4333_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
return v___x_4332_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v_res_4341_; 
v_res_4341_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4335_, v___y_4336_, v___y_4337_, v___y_4338_, v___y_4339_);
lean_dec(v___y_4339_);
lean_dec_ref(v___y_4338_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
return v_res_4341_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4343_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4344_ = l_Lean_stringToMessageData(v___x_4343_);
return v___x_4344_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4346_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4347_ = l_Lean_stringToMessageData(v___x_4346_);
return v___x_4347_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4349_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_4350_ = l_Lean_stringToMessageData(v___x_4349_);
return v___x_4350_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__7(void){
_start:
{
lean_object* v___x_4352_; lean_object* v___x_4353_; 
v___x_4352_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__6));
v___x_4353_ = l_Lean_stringToMessageData(v___x_4352_);
return v___x_4353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4354_, uint8_t v_attrKind_4355_, lean_object* v_prio_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_, lean_object* v_a_4360_){
_start:
{
lean_object* v___x_4362_; 
lean_inc(v_declName_4354_);
v___x_4362_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4354_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
if (lean_obj_tag(v___x_4362_) == 0)
{
lean_object* v_a_4363_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4369_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___x_4441_; 
v_a_4363_ = lean_ctor_get(v___x_4362_, 0);
lean_inc(v_a_4363_);
lean_dec_ref_known(v___x_4362_, 1);
lean_inc(v_declName_4354_);
v___x_4441_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4354_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
if (lean_obj_tag(v___x_4441_) == 0)
{
lean_object* v_a_4442_; lean_object* v___x_4443_; uint8_t v___x_4444_; 
v_a_4442_ = lean_ctor_get(v___x_4441_, 0);
lean_inc(v_a_4442_);
lean_dec_ref_known(v___x_4441_, 1);
v___x_4443_ = l_Lean_ConstantInfo_type(v_a_4442_);
v___x_4444_ = l_Lean_Expr_hasSorry(v___x_4443_);
lean_dec_ref(v___x_4443_);
if (v___x_4444_ == 0)
{
lean_object* v___x_4445_; 
lean_inc(v_a_4363_);
v___x_4445_ = l_Lean_Meta_checkNonClassInstance(v_a_4363_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_object* v___x_4446_; 
lean_dec_ref_known(v___x_4445_, 1);
v___x_4446_ = l_Lean_Meta_checkImpossibleInstance(v_a_4442_, v_a_4357_, v_a_4358_, v_a_4359_, v_a_4360_);
lean_dec(v_a_4442_);
if (lean_obj_tag(v___x_4446_) == 0)
{
lean_dec_ref_known(v___x_4446_, 1);
v___y_4393_ = v_a_4357_;
v___y_4394_ = v_a_4358_;
v___y_4395_ = v_a_4359_;
v___y_4396_ = v_a_4360_;
goto v___jp_4392_;
}
else
{
lean_dec(v_a_4363_);
lean_dec(v_prio_4356_);
lean_dec(v_declName_4354_);
return v___x_4446_;
}
}
else
{
lean_dec(v_a_4442_);
lean_dec(v_a_4363_);
lean_dec(v_prio_4356_);
lean_dec(v_declName_4354_);
return v___x_4445_;
}
}
else
{
lean_dec(v_a_4442_);
v___y_4393_ = v_a_4357_;
v___y_4394_ = v_a_4358_;
v___y_4395_ = v_a_4359_;
v___y_4396_ = v_a_4360_;
goto v___jp_4392_;
}
}
else
{
lean_object* v_a_4447_; lean_object* v___x_4449_; uint8_t v_isShared_4450_; uint8_t v_isSharedCheck_4454_; 
lean_dec(v_a_4363_);
lean_dec(v_prio_4356_);
lean_dec(v_declName_4354_);
v_a_4447_ = lean_ctor_get(v___x_4441_, 0);
v_isSharedCheck_4454_ = !lean_is_exclusive(v___x_4441_);
if (v_isSharedCheck_4454_ == 0)
{
v___x_4449_ = v___x_4441_;
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
else
{
lean_inc(v_a_4447_);
lean_dec(v___x_4441_);
v___x_4449_ = lean_box(0);
v_isShared_4450_ = v_isSharedCheck_4454_;
goto v_resetjp_4448_;
}
v_resetjp_4448_:
{
lean_object* v___x_4452_; 
if (v_isShared_4450_ == 0)
{
v___x_4452_ = v___x_4449_;
goto v_reusejp_4451_;
}
else
{
lean_object* v_reuseFailAlloc_4453_; 
v_reuseFailAlloc_4453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4453_, 0, v_a_4447_);
v___x_4452_ = v_reuseFailAlloc_4453_;
goto v_reusejp_4451_;
}
v_reusejp_4451_:
{
return v___x_4452_;
}
}
}
v___jp_4364_:
{
lean_object* v___x_4370_; lean_object* v_a_4371_; lean_object* v___x_4373_; uint8_t v_isShared_4374_; uint8_t v_isSharedCheck_4391_; 
lean_inc(v_declName_4354_);
v___x_4370_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4354_, v___y_4369_);
v_a_4371_ = lean_ctor_get(v___x_4370_, 0);
v_isSharedCheck_4391_ = !lean_is_exclusive(v___x_4370_);
if (v_isSharedCheck_4391_ == 0)
{
v___x_4373_ = v___x_4370_;
v_isShared_4374_ = v_isSharedCheck_4391_;
goto v_resetjp_4372_;
}
else
{
lean_inc(v_a_4371_);
lean_dec(v___x_4370_);
v___x_4373_ = lean_box(0);
v_isShared_4374_ = v_isSharedCheck_4391_;
goto v_resetjp_4372_;
}
v_resetjp_4372_:
{
lean_object* v___x_4375_; 
lean_inc(v_a_4363_);
v___x_4375_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4363_, v_a_4371_, v___y_4366_, v___y_4367_, v___y_4368_, v___y_4369_);
if (lean_obj_tag(v___x_4375_) == 0)
{
lean_object* v_a_4376_; lean_object* v___x_4377_; lean_object* v___x_4379_; 
v_a_4376_ = lean_ctor_get(v___x_4375_, 0);
lean_inc(v_a_4376_);
lean_dec_ref_known(v___x_4375_, 1);
v___x_4377_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4374_ == 0)
{
lean_ctor_set_tag(v___x_4373_, 1);
lean_ctor_set(v___x_4373_, 0, v_declName_4354_);
v___x_4379_ = v___x_4373_;
goto v_reusejp_4378_;
}
else
{
lean_object* v_reuseFailAlloc_4382_; 
v_reuseFailAlloc_4382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4382_, 0, v_declName_4354_);
v___x_4379_ = v_reuseFailAlloc_4382_;
goto v_reusejp_4378_;
}
v_reusejp_4378_:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4380_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4380_, 0, v___y_4365_);
lean_ctor_set(v___x_4380_, 1, v_a_4363_);
lean_ctor_set(v___x_4380_, 2, v_prio_4356_);
lean_ctor_set(v___x_4380_, 3, v___x_4379_);
lean_ctor_set(v___x_4380_, 4, v_a_4376_);
lean_ctor_set_uint8(v___x_4380_, sizeof(void*)*5, v_attrKind_4355_);
v___x_4381_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4377_, v___x_4380_, v_attrKind_4355_, v___y_4367_, v___y_4368_, v___y_4369_);
return v___x_4381_;
}
}
else
{
lean_object* v_a_4383_; lean_object* v___x_4385_; uint8_t v_isShared_4386_; uint8_t v_isSharedCheck_4390_; 
lean_del_object(v___x_4373_);
lean_dec_ref(v___y_4365_);
lean_dec(v_a_4363_);
lean_dec(v_prio_4356_);
lean_dec(v_declName_4354_);
v_a_4383_ = lean_ctor_get(v___x_4375_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4375_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4385_ = v___x_4375_;
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
else
{
lean_inc(v_a_4383_);
lean_dec(v___x_4375_);
v___x_4385_ = lean_box(0);
v_isShared_4386_ = v_isSharedCheck_4390_;
goto v_resetjp_4384_;
}
v_resetjp_4384_:
{
lean_object* v___x_4388_; 
if (v_isShared_4386_ == 0)
{
v___x_4388_ = v___x_4385_;
goto v_reusejp_4387_;
}
else
{
lean_object* v_reuseFailAlloc_4389_; 
v_reuseFailAlloc_4389_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4389_, 0, v_a_4383_);
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
v___jp_4392_:
{
lean_object* v___x_4397_; 
lean_inc(v_a_4363_);
v___x_4397_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4363_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
if (lean_obj_tag(v___x_4397_) == 0)
{
lean_object* v_a_4398_; lean_object* v___x_4399_; lean_object* v_a_4400_; uint8_t v___x_4401_; uint8_t v___x_4402_; uint8_t v___x_4403_; 
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref_known(v___x_4397_, 1);
lean_inc(v_declName_4354_);
v___x_4399_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4354_, v___y_4396_);
v_a_4400_ = lean_ctor_get(v___x_4399_, 0);
lean_inc(v_a_4400_);
lean_dec_ref(v___x_4399_);
v___x_4401_ = 1;
v___x_4402_ = lean_unbox(v_a_4400_);
lean_dec(v_a_4400_);
v___x_4403_ = l_Lean_instBEqReducibilityStatus_beq(v___x_4402_, v___x_4401_);
if (v___x_4403_ == 0)
{
v___y_4365_ = v_a_4398_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
v___y_4368_ = v___y_4395_;
v___y_4369_ = v___y_4396_;
goto v___jp_4364_;
}
else
{
lean_object* v___x_4404_; 
lean_inc(v_declName_4354_);
v___x_4404_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4354_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
if (lean_obj_tag(v___x_4404_) == 0)
{
lean_object* v_a_4405_; uint8_t v___x_4406_; 
v_a_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc(v_a_4405_);
lean_dec_ref_known(v___x_4404_, 1);
v___x_4406_ = l_Lean_ConstantInfo_isDefinition(v_a_4405_);
lean_dec(v_a_4405_);
if (v___x_4406_ == 0)
{
lean_object* v___x_4407_; lean_object* v_env_4408_; uint8_t v___x_4409_; 
v___x_4407_ = lean_st_ref_get(v___y_4396_);
v_env_4408_ = lean_ctor_get(v___x_4407_, 0);
lean_inc_ref(v_env_4408_);
lean_dec(v___x_4407_);
lean_inc(v_declName_4354_);
v___x_4409_ = l_Lean_wasOriginallyDefn(v_env_4408_, v_declName_4354_);
if (v___x_4409_ == 0)
{
v___y_4365_ = v_a_4398_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
v___y_4368_ = v___y_4395_;
v___y_4369_ = v___y_4396_;
goto v___jp_4364_;
}
else
{
lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; lean_object* v___x_4415_; 
v___x_4410_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4354_);
v___x_4411_ = l_Lean_MessageData_ofName(v_declName_4354_);
v___x_4412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4410_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
v___x_4413_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4414_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4414_, 0, v___x_4412_);
lean_ctor_set(v___x_4414_, 1, v___x_4413_);
v___x_4415_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4414_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
if (lean_obj_tag(v___x_4415_) == 0)
{
lean_dec_ref_known(v___x_4415_, 1);
v___y_4365_ = v_a_4398_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
v___y_4368_ = v___y_4395_;
v___y_4369_ = v___y_4396_;
goto v___jp_4364_;
}
else
{
lean_dec(v_a_4398_);
lean_dec(v_a_4363_);
lean_dec(v_prio_4356_);
lean_dec(v_declName_4354_);
return v___x_4415_;
}
}
}
else
{
lean_object* v_options_4416_; lean_object* v___x_4417_; uint8_t v___x_4418_; 
v_options_4416_ = lean_ctor_get(v___y_4395_, 2);
v___x_4417_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility));
v___x_4418_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_4416_, v___x_4417_);
if (v___x_4418_ == 0)
{
v___y_4365_ = v_a_4398_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
v___y_4368_ = v___y_4395_;
v___y_4369_ = v___y_4396_;
goto v___jp_4364_;
}
else
{
lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; lean_object* v___x_4424_; 
v___x_4419_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
lean_inc(v_declName_4354_);
v___x_4420_ = l_Lean_MessageData_ofName(v_declName_4354_);
v___x_4421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4419_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
v___x_4422_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__7, &l_Lean_Meta_addInstance___closed__7_once, _init_l_Lean_Meta_addInstance___closed__7);
v___x_4423_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4423_, 0, v___x_4421_);
lean_ctor_set(v___x_4423_, 1, v___x_4422_);
v___x_4424_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4423_, v___y_4393_, v___y_4394_, v___y_4395_, v___y_4396_);
if (lean_obj_tag(v___x_4424_) == 0)
{
lean_dec_ref_known(v___x_4424_, 1);
v___y_4365_ = v_a_4398_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
v___y_4368_ = v___y_4395_;
v___y_4369_ = v___y_4396_;
goto v___jp_4364_;
}
else
{
lean_dec(v_a_4398_);
lean_dec(v_a_4363_);
lean_dec(v_prio_4356_);
lean_dec(v_declName_4354_);
return v___x_4424_;
}
}
}
}
else
{
lean_object* v_a_4425_; lean_object* v___x_4427_; uint8_t v_isShared_4428_; uint8_t v_isSharedCheck_4432_; 
lean_dec(v_a_4398_);
lean_dec(v_a_4363_);
lean_dec(v_prio_4356_);
lean_dec(v_declName_4354_);
v_a_4425_ = lean_ctor_get(v___x_4404_, 0);
v_isSharedCheck_4432_ = !lean_is_exclusive(v___x_4404_);
if (v_isSharedCheck_4432_ == 0)
{
v___x_4427_ = v___x_4404_;
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
else
{
lean_inc(v_a_4425_);
lean_dec(v___x_4404_);
v___x_4427_ = lean_box(0);
v_isShared_4428_ = v_isSharedCheck_4432_;
goto v_resetjp_4426_;
}
v_resetjp_4426_:
{
lean_object* v___x_4430_; 
if (v_isShared_4428_ == 0)
{
v___x_4430_ = v___x_4427_;
goto v_reusejp_4429_;
}
else
{
lean_object* v_reuseFailAlloc_4431_; 
v_reuseFailAlloc_4431_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4431_, 0, v_a_4425_);
v___x_4430_ = v_reuseFailAlloc_4431_;
goto v_reusejp_4429_;
}
v_reusejp_4429_:
{
return v___x_4430_;
}
}
}
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_dec(v_a_4363_);
lean_dec(v_prio_4356_);
lean_dec(v_declName_4354_);
v_a_4433_ = lean_ctor_get(v___x_4397_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4397_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4397_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4397_);
v___x_4435_ = lean_box(0);
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
v_resetjp_4434_:
{
lean_object* v___x_4438_; 
if (v_isShared_4436_ == 0)
{
v___x_4438_ = v___x_4435_;
goto v_reusejp_4437_;
}
else
{
lean_object* v_reuseFailAlloc_4439_; 
v_reuseFailAlloc_4439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4439_, 0, v_a_4433_);
v___x_4438_ = v_reuseFailAlloc_4439_;
goto v_reusejp_4437_;
}
v_reusejp_4437_:
{
return v___x_4438_;
}
}
}
}
}
else
{
lean_object* v_a_4455_; lean_object* v___x_4457_; uint8_t v_isShared_4458_; uint8_t v_isSharedCheck_4462_; 
lean_dec(v_prio_4356_);
lean_dec(v_declName_4354_);
v_a_4455_ = lean_ctor_get(v___x_4362_, 0);
v_isSharedCheck_4462_ = !lean_is_exclusive(v___x_4362_);
if (v_isSharedCheck_4462_ == 0)
{
v___x_4457_ = v___x_4362_;
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
else
{
lean_inc(v_a_4455_);
lean_dec(v___x_4362_);
v___x_4457_ = lean_box(0);
v_isShared_4458_ = v_isSharedCheck_4462_;
goto v_resetjp_4456_;
}
v_resetjp_4456_:
{
lean_object* v___x_4460_; 
if (v_isShared_4458_ == 0)
{
v___x_4460_ = v___x_4457_;
goto v_reusejp_4459_;
}
else
{
lean_object* v_reuseFailAlloc_4461_; 
v_reuseFailAlloc_4461_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4461_, 0, v_a_4455_);
v___x_4460_ = v_reuseFailAlloc_4461_;
goto v_reusejp_4459_;
}
v_reusejp_4459_:
{
return v___x_4460_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4463_, lean_object* v_attrKind_4464_, lean_object* v_prio_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_, lean_object* v_a_4470_){
_start:
{
uint8_t v_attrKind_boxed_4471_; lean_object* v_res_4472_; 
v_attrKind_boxed_4471_ = lean_unbox(v_attrKind_4464_);
v_res_4472_ = l_Lean_Meta_addInstance(v_declName_4463_, v_attrKind_boxed_4471_, v_prio_4465_, v_a_4466_, v_a_4467_, v_a_4468_, v_a_4469_);
lean_dec(v_a_4469_);
lean_dec_ref(v_a_4468_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
return v_res_4472_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_4473_, lean_object* v_constName_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_, lean_object* v___y_4478_){
_start:
{
lean_object* v___x_4480_; 
v___x_4480_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4474_, v___y_4475_, v___y_4476_, v___y_4477_, v___y_4478_);
return v___x_4480_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4481_, lean_object* v_constName_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_, lean_object* v___y_4487_){
_start:
{
lean_object* v_res_4488_; 
v_res_4488_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_4481_, v_constName_4482_, v___y_4483_, v___y_4484_, v___y_4485_, v___y_4486_);
lean_dec(v___y_4486_);
lean_dec_ref(v___y_4485_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
return v_res_4488_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_4489_, lean_object* v_ref_4490_, lean_object* v_constName_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_, lean_object* v___y_4495_){
_start:
{
lean_object* v___x_4497_; 
v___x_4497_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4490_, v_constName_4491_, v___y_4492_, v___y_4493_, v___y_4494_, v___y_4495_);
return v___x_4497_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4498_, lean_object* v_ref_4499_, lean_object* v_constName_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_){
_start:
{
lean_object* v_res_4506_; 
v_res_4506_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_4498_, v_ref_4499_, v_constName_4500_, v___y_4501_, v___y_4502_, v___y_4503_, v___y_4504_);
lean_dec(v___y_4504_);
lean_dec_ref(v___y_4503_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v_ref_4499_);
return v_res_4506_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b1_4507_, lean_object* v_ref_4508_, lean_object* v_msg_4509_, lean_object* v_declHint_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_){
_start:
{
lean_object* v___x_4516_; 
v___x_4516_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4508_, v_msg_4509_, v_declHint_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
return v___x_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4517_, lean_object* v_ref_4518_, lean_object* v_msg_4519_, lean_object* v_declHint_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_, lean_object* v___y_4525_){
_start:
{
lean_object* v_res_4526_; 
v_res_4526_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(v_00_u03b1_4517_, v_ref_4518_, v_msg_4519_, v_declHint_4520_, v___y_4521_, v___y_4522_, v___y_4523_, v___y_4524_);
lean_dec(v___y_4524_);
lean_dec_ref(v___y_4523_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v_ref_4518_);
return v_res_4526_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_4527_, lean_object* v_declHint_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v___x_4534_; 
v___x_4534_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4527_, v_declHint_4528_, v___y_4532_);
return v___x_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_4535_, lean_object* v_declHint_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_){
_start:
{
lean_object* v_res_4542_; 
v_res_4542_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(v_msg_4535_, v_declHint_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
lean_dec(v___y_4540_);
lean_dec_ref(v___y_4539_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
return v_res_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_4543_, lean_object* v_ref_4544_, lean_object* v_msg_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_){
_start:
{
lean_object* v___x_4551_; 
v___x_4551_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4544_, v_msg_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
return v___x_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4552_, lean_object* v_ref_4553_, lean_object* v_msg_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v_res_4560_; 
v_res_4560_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_4552_, v_ref_4553_, v_msg_4554_, v___y_4555_, v___y_4556_, v___y_4557_, v___y_4558_);
lean_dec(v___y_4558_);
lean_dec_ref(v___y_4557_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v_ref_4553_);
return v_res_4560_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4561_, uint8_t v_s_4562_, lean_object* v___y_4563_, lean_object* v___y_4564_){
_start:
{
lean_object* v___x_4566_; lean_object* v_env_4567_; lean_object* v_nextMacroScope_4568_; lean_object* v_ngen_4569_; lean_object* v_auxDeclNGen_4570_; lean_object* v_traceState_4571_; lean_object* v_messages_4572_; lean_object* v_infoState_4573_; lean_object* v_snapshotTasks_4574_; lean_object* v___x_4576_; uint8_t v_isShared_4577_; uint8_t v_isSharedCheck_4603_; 
v___x_4566_ = lean_st_ref_take(v___y_4564_);
v_env_4567_ = lean_ctor_get(v___x_4566_, 0);
v_nextMacroScope_4568_ = lean_ctor_get(v___x_4566_, 1);
v_ngen_4569_ = lean_ctor_get(v___x_4566_, 2);
v_auxDeclNGen_4570_ = lean_ctor_get(v___x_4566_, 3);
v_traceState_4571_ = lean_ctor_get(v___x_4566_, 4);
v_messages_4572_ = lean_ctor_get(v___x_4566_, 6);
v_infoState_4573_ = lean_ctor_get(v___x_4566_, 7);
v_snapshotTasks_4574_ = lean_ctor_get(v___x_4566_, 8);
v_isSharedCheck_4603_ = !lean_is_exclusive(v___x_4566_);
if (v_isSharedCheck_4603_ == 0)
{
lean_object* v_unused_4604_; 
v_unused_4604_ = lean_ctor_get(v___x_4566_, 5);
lean_dec(v_unused_4604_);
v___x_4576_ = v___x_4566_;
v_isShared_4577_ = v_isSharedCheck_4603_;
goto v_resetjp_4575_;
}
else
{
lean_inc(v_snapshotTasks_4574_);
lean_inc(v_infoState_4573_);
lean_inc(v_messages_4572_);
lean_inc(v_traceState_4571_);
lean_inc(v_auxDeclNGen_4570_);
lean_inc(v_ngen_4569_);
lean_inc(v_nextMacroScope_4568_);
lean_inc(v_env_4567_);
lean_dec(v___x_4566_);
v___x_4576_ = lean_box(0);
v_isShared_4577_ = v_isSharedCheck_4603_;
goto v_resetjp_4575_;
}
v_resetjp_4575_:
{
uint8_t v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4581_; lean_object* v___x_4583_; 
v___x_4578_ = 0;
v___x_4579_ = lean_box(0);
v___x_4580_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4567_, v_declName_4561_, v_s_4562_, v___x_4578_, v___x_4579_);
v___x_4581_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4577_ == 0)
{
lean_ctor_set(v___x_4576_, 5, v___x_4581_);
lean_ctor_set(v___x_4576_, 0, v___x_4580_);
v___x_4583_ = v___x_4576_;
goto v_reusejp_4582_;
}
else
{
lean_object* v_reuseFailAlloc_4602_; 
v_reuseFailAlloc_4602_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4602_, 0, v___x_4580_);
lean_ctor_set(v_reuseFailAlloc_4602_, 1, v_nextMacroScope_4568_);
lean_ctor_set(v_reuseFailAlloc_4602_, 2, v_ngen_4569_);
lean_ctor_set(v_reuseFailAlloc_4602_, 3, v_auxDeclNGen_4570_);
lean_ctor_set(v_reuseFailAlloc_4602_, 4, v_traceState_4571_);
lean_ctor_set(v_reuseFailAlloc_4602_, 5, v___x_4581_);
lean_ctor_set(v_reuseFailAlloc_4602_, 6, v_messages_4572_);
lean_ctor_set(v_reuseFailAlloc_4602_, 7, v_infoState_4573_);
lean_ctor_set(v_reuseFailAlloc_4602_, 8, v_snapshotTasks_4574_);
v___x_4583_ = v_reuseFailAlloc_4602_;
goto v_reusejp_4582_;
}
v_reusejp_4582_:
{
lean_object* v___x_4584_; lean_object* v___x_4585_; lean_object* v_mctx_4586_; lean_object* v_zetaDeltaFVarIds_4587_; lean_object* v_postponed_4588_; lean_object* v_diag_4589_; lean_object* v___x_4591_; uint8_t v_isShared_4592_; uint8_t v_isSharedCheck_4600_; 
v___x_4584_ = lean_st_ref_put(v___y_4564_, v___x_4583_);
v___x_4585_ = lean_st_ref_take(v___y_4563_);
v_mctx_4586_ = lean_ctor_get(v___x_4585_, 0);
v_zetaDeltaFVarIds_4587_ = lean_ctor_get(v___x_4585_, 2);
v_postponed_4588_ = lean_ctor_get(v___x_4585_, 3);
v_diag_4589_ = lean_ctor_get(v___x_4585_, 4);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4585_);
if (v_isSharedCheck_4600_ == 0)
{
lean_object* v_unused_4601_; 
v_unused_4601_ = lean_ctor_get(v___x_4585_, 1);
lean_dec(v_unused_4601_);
v___x_4591_ = v___x_4585_;
v_isShared_4592_ = v_isSharedCheck_4600_;
goto v_resetjp_4590_;
}
else
{
lean_inc(v_diag_4589_);
lean_inc(v_postponed_4588_);
lean_inc(v_zetaDeltaFVarIds_4587_);
lean_inc(v_mctx_4586_);
lean_dec(v___x_4585_);
v___x_4591_ = lean_box(0);
v_isShared_4592_ = v_isSharedCheck_4600_;
goto v_resetjp_4590_;
}
v_resetjp_4590_:
{
lean_object* v___x_4593_; lean_object* v___x_4595_; 
v___x_4593_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_4592_ == 0)
{
lean_ctor_set(v___x_4591_, 1, v___x_4593_);
v___x_4595_ = v___x_4591_;
goto v_reusejp_4594_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v_mctx_4586_);
lean_ctor_set(v_reuseFailAlloc_4599_, 1, v___x_4593_);
lean_ctor_set(v_reuseFailAlloc_4599_, 2, v_zetaDeltaFVarIds_4587_);
lean_ctor_set(v_reuseFailAlloc_4599_, 3, v_postponed_4588_);
lean_ctor_set(v_reuseFailAlloc_4599_, 4, v_diag_4589_);
v___x_4595_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4594_;
}
v_reusejp_4594_:
{
lean_object* v___x_4596_; lean_object* v___x_4597_; lean_object* v___x_4598_; 
v___x_4596_ = lean_st_ref_put(v___y_4563_, v___x_4595_);
v___x_4597_ = lean_box(0);
v___x_4598_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4598_, 0, v___x_4597_);
return v___x_4598_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4605_, lean_object* v_s_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
uint8_t v_s_boxed_4610_; lean_object* v_res_4611_; 
v_s_boxed_4610_ = lean_unbox(v_s_4606_);
v_res_4611_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4605_, v_s_boxed_4610_, v___y_4607_, v___y_4608_);
lean_dec(v___y_4608_);
lean_dec(v___y_4607_);
return v_res_4611_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4612_, uint8_t v_s_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_, lean_object* v___y_4617_){
_start:
{
lean_object* v___x_4619_; 
v___x_4619_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4612_, v_s_4613_, v___y_4615_, v___y_4617_);
return v___x_4619_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4620_, lean_object* v_s_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_, lean_object* v___y_4626_){
_start:
{
uint8_t v_s_boxed_4627_; lean_object* v_res_4628_; 
v_s_boxed_4627_ = lean_unbox(v_s_4621_);
v_res_4628_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4620_, v_s_boxed_4627_, v___y_4622_, v___y_4623_, v___y_4624_, v___y_4625_);
lean_dec(v___y_4625_);
lean_dec_ref(v___y_4624_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
return v_res_4628_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4629_, uint8_t v_attrKind_4630_, lean_object* v_prio_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_, lean_object* v_a_4635_){
_start:
{
uint8_t v___x_4637_; lean_object* v___x_4638_; lean_object* v___x_4639_; 
v___x_4637_ = 4;
lean_inc(v_declName_4629_);
v___x_4638_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4629_, v___x_4637_, v_a_4633_, v_a_4635_);
lean_dec_ref(v___x_4638_);
v___x_4639_ = l_Lean_Meta_addInstance(v_declName_4629_, v_attrKind_4630_, v_prio_4631_, v_a_4632_, v_a_4633_, v_a_4634_, v_a_4635_);
return v___x_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4640_, lean_object* v_attrKind_4641_, lean_object* v_prio_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_, lean_object* v_a_4647_){
_start:
{
uint8_t v_attrKind_boxed_4648_; lean_object* v_res_4649_; 
v_attrKind_boxed_4648_ = lean_unbox(v_attrKind_4641_);
v_res_4649_ = l_Lean_Meta_registerInstance(v_declName_4640_, v_attrKind_boxed_4648_, v_prio_4642_, v_a_4643_, v_a_4644_, v_a_4645_, v_a_4646_);
lean_dec(v_a_4646_);
lean_dec_ref(v_a_4645_);
lean_dec(v_a_4644_);
lean_dec_ref(v_a_4643_);
return v_res_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4650_, lean_object* v_x_4651_){
_start:
{
lean_inc_ref(v_a_4650_);
return v_a_4650_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4652_, lean_object* v_x_4653_){
_start:
{
lean_object* v_res_4654_; 
v_res_4654_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4652_, v_x_4653_);
lean_dec_ref(v_x_4653_);
lean_dec_ref(v_a_4652_);
return v_res_4654_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4655_, lean_object* v___y_4656_, lean_object* v___y_4657_){
_start:
{
lean_object* v___x_4659_; lean_object* v_env_4660_; lean_object* v_options_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; lean_object* v___x_4668_; 
v___x_4659_ = lean_st_ref_get(v___y_4657_);
v_env_4660_ = lean_ctor_get(v___x_4659_, 0);
lean_inc_ref(v_env_4660_);
lean_dec(v___x_4659_);
v_options_4661_ = lean_ctor_get(v___y_4656_, 2);
v___x_4662_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4663_ = lean_unsigned_to_nat(32u);
v___x_4664_ = lean_mk_empty_array_with_capacity(v___x_4663_);
lean_dec_ref(v___x_4664_);
v___x_4665_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_4661_);
v___x_4666_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4666_, 0, v_env_4660_);
lean_ctor_set(v___x_4666_, 1, v___x_4662_);
lean_ctor_set(v___x_4666_, 2, v___x_4665_);
lean_ctor_set(v___x_4666_, 3, v_options_4661_);
v___x_4667_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4666_);
lean_ctor_set(v___x_4667_, 1, v_msgData_4655_);
v___x_4668_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4668_, 0, v___x_4667_);
return v___x_4668_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_, lean_object* v___y_4672_){
_start:
{
lean_object* v_res_4673_; 
v_res_4673_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4669_, v___y_4670_, v___y_4671_);
lean_dec(v___y_4671_);
lean_dec_ref(v___y_4670_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4674_, lean_object* v___y_4675_, lean_object* v___y_4676_){
_start:
{
lean_object* v_ref_4678_; lean_object* v___x_4679_; lean_object* v_a_4680_; lean_object* v___x_4682_; uint8_t v_isShared_4683_; uint8_t v_isSharedCheck_4688_; 
v_ref_4678_ = lean_ctor_get(v___y_4675_, 5);
v___x_4679_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4674_, v___y_4675_, v___y_4676_);
v_a_4680_ = lean_ctor_get(v___x_4679_, 0);
v_isSharedCheck_4688_ = !lean_is_exclusive(v___x_4679_);
if (v_isSharedCheck_4688_ == 0)
{
v___x_4682_ = v___x_4679_;
v_isShared_4683_ = v_isSharedCheck_4688_;
goto v_resetjp_4681_;
}
else
{
lean_inc(v_a_4680_);
lean_dec(v___x_4679_);
v___x_4682_ = lean_box(0);
v_isShared_4683_ = v_isSharedCheck_4688_;
goto v_resetjp_4681_;
}
v_resetjp_4681_:
{
lean_object* v___x_4684_; lean_object* v___x_4686_; 
lean_inc(v_ref_4678_);
v___x_4684_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4684_, 0, v_ref_4678_);
lean_ctor_set(v___x_4684_, 1, v_a_4680_);
if (v_isShared_4683_ == 0)
{
lean_ctor_set_tag(v___x_4682_, 1);
lean_ctor_set(v___x_4682_, 0, v___x_4684_);
v___x_4686_ = v___x_4682_;
goto v_reusejp_4685_;
}
else
{
lean_object* v_reuseFailAlloc_4687_; 
v_reuseFailAlloc_4687_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4687_, 0, v___x_4684_);
v___x_4686_ = v_reuseFailAlloc_4687_;
goto v_reusejp_4685_;
}
v_reusejp_4685_:
{
return v___x_4686_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_, lean_object* v___y_4692_){
_start:
{
lean_object* v_res_4693_; 
v_res_4693_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4689_, v___y_4690_, v___y_4691_);
lean_dec(v___y_4691_);
lean_dec_ref(v___y_4690_);
return v_res_4693_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4694_, lean_object* v_i_4695_, lean_object* v_k_4696_){
_start:
{
lean_object* v___x_4697_; uint8_t v___x_4698_; 
v___x_4697_ = lean_array_get_size(v_keys_4694_);
v___x_4698_ = lean_nat_dec_lt(v_i_4695_, v___x_4697_);
if (v___x_4698_ == 0)
{
lean_dec(v_i_4695_);
return v___x_4698_;
}
else
{
lean_object* v_k_x27_4699_; uint8_t v___x_4700_; 
v_k_x27_4699_ = lean_array_fget_borrowed(v_keys_4694_, v_i_4695_);
v___x_4700_ = lean_name_eq(v_k_4696_, v_k_x27_4699_);
if (v___x_4700_ == 0)
{
lean_object* v___x_4701_; lean_object* v___x_4702_; 
v___x_4701_ = lean_unsigned_to_nat(1u);
v___x_4702_ = lean_nat_add(v_i_4695_, v___x_4701_);
lean_dec(v_i_4695_);
v_i_4695_ = v___x_4702_;
goto _start;
}
else
{
lean_dec(v_i_4695_);
return v___x_4700_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4704_, lean_object* v_i_4705_, lean_object* v_k_4706_){
_start:
{
uint8_t v_res_4707_; lean_object* v_r_4708_; 
v_res_4707_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4704_, v_i_4705_, v_k_4706_);
lean_dec(v_k_4706_);
lean_dec_ref(v_keys_4704_);
v_r_4708_ = lean_box(v_res_4707_);
return v_r_4708_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4709_, size_t v_x_4710_, lean_object* v_x_4711_){
_start:
{
if (lean_obj_tag(v_x_4709_) == 0)
{
lean_object* v_es_4712_; lean_object* v___x_4713_; size_t v___x_4714_; size_t v___x_4715_; lean_object* v_j_4716_; lean_object* v___x_4717_; 
v_es_4712_ = lean_ctor_get(v_x_4709_, 0);
v___x_4713_ = lean_box(2);
v___x_4714_ = ((size_t)31ULL);
v___x_4715_ = lean_usize_land(v_x_4710_, v___x_4714_);
v_j_4716_ = lean_usize_to_nat(v___x_4715_);
v___x_4717_ = lean_array_get_borrowed(v___x_4713_, v_es_4712_, v_j_4716_);
lean_dec(v_j_4716_);
switch(lean_obj_tag(v___x_4717_))
{
case 0:
{
lean_object* v_key_4718_; uint8_t v___x_4719_; 
v_key_4718_ = lean_ctor_get(v___x_4717_, 0);
v___x_4719_ = lean_name_eq(v_x_4711_, v_key_4718_);
return v___x_4719_;
}
case 1:
{
lean_object* v_node_4720_; size_t v___x_4721_; size_t v___x_4722_; 
v_node_4720_ = lean_ctor_get(v___x_4717_, 0);
v___x_4721_ = ((size_t)5ULL);
v___x_4722_ = lean_usize_shift_right(v_x_4710_, v___x_4721_);
v_x_4709_ = v_node_4720_;
v_x_4710_ = v___x_4722_;
goto _start;
}
default: 
{
uint8_t v___x_4724_; 
v___x_4724_ = 0;
return v___x_4724_;
}
}
}
else
{
lean_object* v_ks_4725_; lean_object* v___x_4726_; uint8_t v___x_4727_; 
v_ks_4725_ = lean_ctor_get(v_x_4709_, 0);
v___x_4726_ = lean_unsigned_to_nat(0u);
v___x_4727_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4725_, v___x_4726_, v_x_4711_);
return v___x_4727_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4728_, lean_object* v_x_4729_, lean_object* v_x_4730_){
_start:
{
size_t v_x_2375__boxed_4731_; uint8_t v_res_4732_; lean_object* v_r_4733_; 
v_x_2375__boxed_4731_ = lean_unbox_usize(v_x_4729_);
lean_dec(v_x_4729_);
v_res_4732_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4728_, v_x_2375__boxed_4731_, v_x_4730_);
lean_dec(v_x_4730_);
lean_dec_ref(v_x_4728_);
v_r_4733_ = lean_box(v_res_4732_);
return v_r_4733_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4734_, lean_object* v_x_4735_){
_start:
{
uint64_t v___y_4737_; 
if (lean_obj_tag(v_x_4735_) == 0)
{
uint64_t v___x_4740_; 
v___x_4740_ = 1723ULL;
v___y_4737_ = v___x_4740_;
goto v___jp_4736_;
}
else
{
uint64_t v_hash_4741_; 
v_hash_4741_ = lean_ctor_get_uint64(v_x_4735_, sizeof(void*)*2);
v___y_4737_ = v_hash_4741_;
goto v___jp_4736_;
}
v___jp_4736_:
{
size_t v___x_4738_; uint8_t v___x_4739_; 
v___x_4738_ = lean_uint64_to_usize(v___y_4737_);
v___x_4739_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4734_, v___x_4738_, v_x_4735_);
return v___x_4739_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4742_, lean_object* v_x_4743_){
_start:
{
uint8_t v_res_4744_; lean_object* v_r_4745_; 
v_res_4744_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4742_, v_x_4743_);
lean_dec(v_x_4743_);
lean_dec_ref(v_x_4742_);
v_r_4745_ = lean_box(v_res_4744_);
return v_r_4745_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4746_, lean_object* v_declName_4747_, lean_object* v___y_4748_, lean_object* v___y_4749_){
_start:
{
lean_object* v_instanceNames_4754_; uint8_t v___x_4755_; 
v_instanceNames_4754_ = lean_ctor_get(v_d_4746_, 1);
v___x_4755_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4754_, v_declName_4747_);
if (v___x_4755_ == 0)
{
lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v___x_4761_; lean_object* v_a_4762_; lean_object* v___x_4764_; uint8_t v_isShared_4765_; uint8_t v_isSharedCheck_4769_; 
lean_dec_ref(v_d_4746_);
v___x_4756_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4757_ = l_Lean_MessageData_ofConstName(v_declName_4747_, v___x_4755_);
v___x_4758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4756_);
lean_ctor_set(v___x_4758_, 1, v___x_4757_);
v___x_4759_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4760_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4760_, 0, v___x_4758_);
lean_ctor_set(v___x_4760_, 1, v___x_4759_);
v___x_4761_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4760_, v___y_4748_, v___y_4749_);
v_a_4762_ = lean_ctor_get(v___x_4761_, 0);
v_isSharedCheck_4769_ = !lean_is_exclusive(v___x_4761_);
if (v_isSharedCheck_4769_ == 0)
{
v___x_4764_ = v___x_4761_;
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
else
{
lean_inc(v_a_4762_);
lean_dec(v___x_4761_);
v___x_4764_ = lean_box(0);
v_isShared_4765_ = v_isSharedCheck_4769_;
goto v_resetjp_4763_;
}
v_resetjp_4763_:
{
lean_object* v___x_4767_; 
if (v_isShared_4765_ == 0)
{
v___x_4767_ = v___x_4764_;
goto v_reusejp_4766_;
}
else
{
lean_object* v_reuseFailAlloc_4768_; 
v_reuseFailAlloc_4768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4768_, 0, v_a_4762_);
v___x_4767_ = v_reuseFailAlloc_4768_;
goto v_reusejp_4766_;
}
v_reusejp_4766_:
{
return v___x_4767_;
}
}
}
else
{
goto v___jp_4751_;
}
v___jp_4751_:
{
lean_object* v___x_4752_; lean_object* v___x_4753_; 
v___x_4752_ = l_Lean_Meta_Instances_eraseCore(v_d_4746_, v_declName_4747_);
v___x_4753_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4753_, 0, v___x_4752_);
return v___x_4753_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4770_, lean_object* v_declName_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_, lean_object* v___y_4774_){
_start:
{
lean_object* v_res_4775_; 
v_res_4775_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4770_, v_declName_4771_, v___y_4772_, v___y_4773_);
lean_dec(v___y_4773_);
lean_dec_ref(v___y_4772_);
return v_res_4775_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4776_, lean_object* v_declName_4777_, lean_object* v___y_4778_, lean_object* v___y_4779_){
_start:
{
lean_object* v___x_4781_; lean_object* v_env_4782_; lean_object* v___x_4783_; lean_object* v_ext_4784_; lean_object* v_toEnvExtension_4785_; lean_object* v_asyncMode_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; 
v___x_4781_ = lean_st_ref_get(v___y_4779_);
v_env_4782_ = lean_ctor_get(v___x_4781_, 0);
lean_inc_ref(v_env_4782_);
lean_dec(v___x_4781_);
v___x_4783_ = l_Lean_Meta_instanceExtension;
v_ext_4784_ = lean_ctor_get(v___x_4783_, 1);
v_toEnvExtension_4785_ = lean_ctor_get(v_ext_4784_, 0);
v_asyncMode_4786_ = lean_ctor_get(v_toEnvExtension_4785_, 2);
v___x_4787_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4776_, v___x_4783_, v_env_4782_, v_asyncMode_4786_);
v___x_4788_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4787_, v_declName_4777_, v___y_4778_, v___y_4779_);
if (lean_obj_tag(v___x_4788_) == 0)
{
lean_object* v_a_4789_; lean_object* v___x_4791_; uint8_t v_isShared_4792_; uint8_t v_isSharedCheck_4818_; 
v_a_4789_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4818_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4818_ == 0)
{
v___x_4791_ = v___x_4788_;
v_isShared_4792_ = v_isSharedCheck_4818_;
goto v_resetjp_4790_;
}
else
{
lean_inc(v_a_4789_);
lean_dec(v___x_4788_);
v___x_4791_ = lean_box(0);
v_isShared_4792_ = v_isSharedCheck_4818_;
goto v_resetjp_4790_;
}
v_resetjp_4790_:
{
lean_object* v___x_4793_; lean_object* v_env_4794_; lean_object* v_nextMacroScope_4795_; lean_object* v_ngen_4796_; lean_object* v_auxDeclNGen_4797_; lean_object* v_traceState_4798_; lean_object* v_messages_4799_; lean_object* v_infoState_4800_; lean_object* v_snapshotTasks_4801_; lean_object* v___x_4803_; uint8_t v_isShared_4804_; uint8_t v_isSharedCheck_4816_; 
v___x_4793_ = lean_st_ref_take(v___y_4779_);
v_env_4794_ = lean_ctor_get(v___x_4793_, 0);
v_nextMacroScope_4795_ = lean_ctor_get(v___x_4793_, 1);
v_ngen_4796_ = lean_ctor_get(v___x_4793_, 2);
v_auxDeclNGen_4797_ = lean_ctor_get(v___x_4793_, 3);
v_traceState_4798_ = lean_ctor_get(v___x_4793_, 4);
v_messages_4799_ = lean_ctor_get(v___x_4793_, 6);
v_infoState_4800_ = lean_ctor_get(v___x_4793_, 7);
v_snapshotTasks_4801_ = lean_ctor_get(v___x_4793_, 8);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4793_);
if (v_isSharedCheck_4816_ == 0)
{
lean_object* v_unused_4817_; 
v_unused_4817_ = lean_ctor_get(v___x_4793_, 5);
lean_dec(v_unused_4817_);
v___x_4803_ = v___x_4793_;
v_isShared_4804_ = v_isSharedCheck_4816_;
goto v_resetjp_4802_;
}
else
{
lean_inc(v_snapshotTasks_4801_);
lean_inc(v_infoState_4800_);
lean_inc(v_messages_4799_);
lean_inc(v_traceState_4798_);
lean_inc(v_auxDeclNGen_4797_);
lean_inc(v_ngen_4796_);
lean_inc(v_nextMacroScope_4795_);
lean_inc(v_env_4794_);
lean_dec(v___x_4793_);
v___x_4803_ = lean_box(0);
v_isShared_4804_ = v_isSharedCheck_4816_;
goto v_resetjp_4802_;
}
v_resetjp_4802_:
{
lean_object* v___f_4805_; lean_object* v___x_4806_; lean_object* v___x_4807_; lean_object* v___x_4809_; 
v___f_4805_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4805_, 0, v_a_4789_);
v___x_4806_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4783_, v_env_4794_, v___f_4805_);
v___x_4807_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4804_ == 0)
{
lean_ctor_set(v___x_4803_, 5, v___x_4807_);
lean_ctor_set(v___x_4803_, 0, v___x_4806_);
v___x_4809_ = v___x_4803_;
goto v_reusejp_4808_;
}
else
{
lean_object* v_reuseFailAlloc_4815_; 
v_reuseFailAlloc_4815_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4815_, 0, v___x_4806_);
lean_ctor_set(v_reuseFailAlloc_4815_, 1, v_nextMacroScope_4795_);
lean_ctor_set(v_reuseFailAlloc_4815_, 2, v_ngen_4796_);
lean_ctor_set(v_reuseFailAlloc_4815_, 3, v_auxDeclNGen_4797_);
lean_ctor_set(v_reuseFailAlloc_4815_, 4, v_traceState_4798_);
lean_ctor_set(v_reuseFailAlloc_4815_, 5, v___x_4807_);
lean_ctor_set(v_reuseFailAlloc_4815_, 6, v_messages_4799_);
lean_ctor_set(v_reuseFailAlloc_4815_, 7, v_infoState_4800_);
lean_ctor_set(v_reuseFailAlloc_4815_, 8, v_snapshotTasks_4801_);
v___x_4809_ = v_reuseFailAlloc_4815_;
goto v_reusejp_4808_;
}
v_reusejp_4808_:
{
lean_object* v___x_4810_; lean_object* v___x_4811_; lean_object* v___x_4813_; 
v___x_4810_ = lean_st_ref_put(v___y_4779_, v___x_4809_);
v___x_4811_ = lean_box(0);
if (v_isShared_4792_ == 0)
{
lean_ctor_set(v___x_4791_, 0, v___x_4811_);
v___x_4813_ = v___x_4791_;
goto v_reusejp_4812_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4811_);
v___x_4813_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4812_;
}
v_reusejp_4812_:
{
return v___x_4813_;
}
}
}
}
}
else
{
lean_object* v_a_4819_; lean_object* v___x_4821_; uint8_t v_isShared_4822_; uint8_t v_isSharedCheck_4826_; 
v_a_4819_ = lean_ctor_get(v___x_4788_, 0);
v_isSharedCheck_4826_ = !lean_is_exclusive(v___x_4788_);
if (v_isSharedCheck_4826_ == 0)
{
v___x_4821_ = v___x_4788_;
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
else
{
lean_inc(v_a_4819_);
lean_dec(v___x_4788_);
v___x_4821_ = lean_box(0);
v_isShared_4822_ = v_isSharedCheck_4826_;
goto v_resetjp_4820_;
}
v_resetjp_4820_:
{
lean_object* v___x_4824_; 
if (v_isShared_4822_ == 0)
{
v___x_4824_ = v___x_4821_;
goto v_reusejp_4823_;
}
else
{
lean_object* v_reuseFailAlloc_4825_; 
v_reuseFailAlloc_4825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4825_, 0, v_a_4819_);
v___x_4824_ = v_reuseFailAlloc_4825_;
goto v_reusejp_4823_;
}
v_reusejp_4823_:
{
return v___x_4824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4827_, lean_object* v_declName_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_, lean_object* v___y_4831_){
_start:
{
lean_object* v_res_4832_; 
v_res_4832_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4827_, v_declName_4828_, v___y_4829_, v___y_4830_);
lean_dec(v___y_4830_);
lean_dec_ref(v___y_4829_);
lean_dec_ref(v___x_4827_);
return v_res_4832_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4839_; uint64_t v___x_4840_; 
v___x_4839_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4840_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4839_);
return v___x_4840_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4841_; lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4841_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4842_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4843_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4843_, 0, v___x_4842_);
lean_ctor_set_uint64(v___x_4843_, sizeof(void*)*1, v___x_4841_);
return v___x_4843_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4844_; 
v___x_4844_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4844_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4845_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4846_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4845_);
return v___x_4846_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4847_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4848_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4847_);
lean_ctor_set(v___x_4848_, 1, v___x_4847_);
lean_ctor_set(v___x_4848_, 2, v___x_4847_);
lean_ctor_set(v___x_4848_, 3, v___x_4847_);
lean_ctor_set(v___x_4848_, 4, v___x_4847_);
lean_ctor_set(v___x_4848_, 5, v___x_4847_);
return v___x_4848_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4849_; lean_object* v___x_4850_; 
v___x_4849_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4850_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4850_, 0, v___x_4849_);
lean_ctor_set(v___x_4850_, 1, v___x_4849_);
lean_ctor_set(v___x_4850_, 2, v___x_4849_);
lean_ctor_set(v___x_4850_, 3, v___x_4849_);
lean_ctor_set(v___x_4850_, 4, v___x_4849_);
return v___x_4850_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4851_, lean_object* v___x_4852_, lean_object* v_declName_4853_, lean_object* v_stx_4854_, uint8_t v_attrKind_4855_, lean_object* v___y_4856_, lean_object* v___y_4857_){
_start:
{
lean_object* v___x_4859_; lean_object* v___x_4860_; lean_object* v___x_4861_; 
v___x_4859_ = lean_unsigned_to_nat(1u);
v___x_4860_ = l_Lean_Syntax_getArg(v_stx_4854_, v___x_4859_);
v___x_4861_ = l_Lean_getAttrParamOptPrio(v___x_4860_, v___y_4856_, v___y_4857_);
if (lean_obj_tag(v___x_4861_) == 0)
{
lean_object* v_a_4862_; uint8_t v___x_4863_; uint8_t v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; size_t v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; lean_object* v___x_4882_; 
v_a_4862_ = lean_ctor_get(v___x_4861_, 0);
lean_inc(v_a_4862_);
lean_dec_ref_known(v___x_4861_, 1);
v___x_4863_ = 0;
v___x_4864_ = 1;
v___x_4865_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4866_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4867_ = lean_unsigned_to_nat(32u);
v___x_4868_ = lean_mk_empty_array_with_capacity(v___x_4867_);
v___x_4869_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4870_ = ((size_t)5ULL);
lean_inc_n(v___x_4851_, 6);
v___x_4871_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4871_, 0, v___x_4869_);
lean_ctor_set(v___x_4871_, 1, v___x_4868_);
lean_ctor_set(v___x_4871_, 2, v___x_4851_);
lean_ctor_set(v___x_4871_, 3, v___x_4851_);
lean_ctor_set_usize(v___x_4871_, 4, v___x_4870_);
v___x_4872_ = lean_box(1);
lean_inc_ref(v___x_4871_);
v___x_4873_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4873_, 0, v___x_4866_);
lean_ctor_set(v___x_4873_, 1, v___x_4871_);
lean_ctor_set(v___x_4873_, 2, v___x_4872_);
v___x_4874_ = lean_mk_empty_array_with_capacity(v___x_4851_);
v___x_4875_ = lean_box(0);
lean_inc(v___x_4852_);
v___x_4876_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4876_, 0, v___x_4865_);
lean_ctor_set(v___x_4876_, 1, v___x_4852_);
lean_ctor_set(v___x_4876_, 2, v___x_4873_);
lean_ctor_set(v___x_4876_, 3, v___x_4874_);
lean_ctor_set(v___x_4876_, 4, v___x_4875_);
lean_ctor_set(v___x_4876_, 5, v___x_4851_);
lean_ctor_set(v___x_4876_, 6, v___x_4875_);
lean_ctor_set_uint8(v___x_4876_, sizeof(void*)*7, v___x_4863_);
lean_ctor_set_uint8(v___x_4876_, sizeof(void*)*7 + 1, v___x_4863_);
lean_ctor_set_uint8(v___x_4876_, sizeof(void*)*7 + 2, v___x_4863_);
lean_ctor_set_uint8(v___x_4876_, sizeof(void*)*7 + 3, v___x_4864_);
v___x_4877_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4851_);
lean_ctor_set(v___x_4877_, 1, v___x_4851_);
lean_ctor_set(v___x_4877_, 2, v___x_4851_);
lean_ctor_set(v___x_4877_, 3, v___x_4851_);
lean_ctor_set(v___x_4877_, 4, v___x_4866_);
lean_ctor_set(v___x_4877_, 5, v___x_4866_);
lean_ctor_set(v___x_4877_, 6, v___x_4866_);
lean_ctor_set(v___x_4877_, 7, v___x_4866_);
lean_ctor_set(v___x_4877_, 8, v___x_4866_);
lean_ctor_set(v___x_4877_, 9, v___x_4866_);
lean_ctor_set(v___x_4877_, 10, v___x_4866_);
v___x_4878_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4879_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4880_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4880_, 0, v___x_4877_);
lean_ctor_set(v___x_4880_, 1, v___x_4878_);
lean_ctor_set(v___x_4880_, 2, v___x_4852_);
lean_ctor_set(v___x_4880_, 3, v___x_4871_);
lean_ctor_set(v___x_4880_, 4, v___x_4879_);
v___x_4881_ = lean_st_mk_ref(v___x_4880_);
v___x_4882_ = l_Lean_Meta_addInstance(v_declName_4853_, v_attrKind_4855_, v_a_4862_, v___x_4876_, v___x_4881_, v___y_4856_, v___y_4857_);
lean_dec_ref_known(v___x_4876_, 7);
if (lean_obj_tag(v___x_4882_) == 0)
{
lean_object* v___x_4884_; uint8_t v_isShared_4885_; uint8_t v_isSharedCheck_4891_; 
v_isSharedCheck_4891_ = !lean_is_exclusive(v___x_4882_);
if (v_isSharedCheck_4891_ == 0)
{
lean_object* v_unused_4892_; 
v_unused_4892_ = lean_ctor_get(v___x_4882_, 0);
lean_dec(v_unused_4892_);
v___x_4884_ = v___x_4882_;
v_isShared_4885_ = v_isSharedCheck_4891_;
goto v_resetjp_4883_;
}
else
{
lean_dec(v___x_4882_);
v___x_4884_ = lean_box(0);
v_isShared_4885_ = v_isSharedCheck_4891_;
goto v_resetjp_4883_;
}
v_resetjp_4883_:
{
lean_object* v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4889_; 
v___x_4886_ = lean_st_ref_get(v___x_4881_);
lean_dec(v___x_4881_);
lean_dec(v___x_4886_);
v___x_4887_ = lean_box(0);
if (v_isShared_4885_ == 0)
{
lean_ctor_set(v___x_4884_, 0, v___x_4887_);
v___x_4889_ = v___x_4884_;
goto v_reusejp_4888_;
}
else
{
lean_object* v_reuseFailAlloc_4890_; 
v_reuseFailAlloc_4890_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4890_, 0, v___x_4887_);
v___x_4889_ = v_reuseFailAlloc_4890_;
goto v_reusejp_4888_;
}
v_reusejp_4888_:
{
return v___x_4889_;
}
}
}
else
{
lean_dec(v___x_4881_);
return v___x_4882_;
}
}
else
{
lean_object* v_a_4893_; lean_object* v___x_4895_; uint8_t v_isShared_4896_; uint8_t v_isSharedCheck_4900_; 
lean_dec(v_declName_4853_);
lean_dec(v___x_4852_);
lean_dec(v___x_4851_);
v_a_4893_ = lean_ctor_get(v___x_4861_, 0);
v_isSharedCheck_4900_ = !lean_is_exclusive(v___x_4861_);
if (v_isSharedCheck_4900_ == 0)
{
v___x_4895_ = v___x_4861_;
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
else
{
lean_inc(v_a_4893_);
lean_dec(v___x_4861_);
v___x_4895_ = lean_box(0);
v_isShared_4896_ = v_isSharedCheck_4900_;
goto v_resetjp_4894_;
}
v_resetjp_4894_:
{
lean_object* v___x_4898_; 
if (v_isShared_4896_ == 0)
{
v___x_4898_ = v___x_4895_;
goto v_reusejp_4897_;
}
else
{
lean_object* v_reuseFailAlloc_4899_; 
v_reuseFailAlloc_4899_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4899_, 0, v_a_4893_);
v___x_4898_ = v_reuseFailAlloc_4899_;
goto v_reusejp_4897_;
}
v_reusejp_4897_:
{
return v___x_4898_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4901_, lean_object* v___x_4902_, lean_object* v_declName_4903_, lean_object* v_stx_4904_, lean_object* v_attrKind_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_, lean_object* v___y_4908_){
_start:
{
uint8_t v_attrKind_boxed_4909_; lean_object* v_res_4910_; 
v_attrKind_boxed_4909_ = lean_unbox(v_attrKind_4905_);
v_res_4910_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4901_, v___x_4902_, v_declName_4903_, v_stx_4904_, v_attrKind_boxed_4909_, v___y_4906_, v___y_4907_);
lean_dec(v___y_4907_);
lean_dec_ref(v___y_4906_);
lean_dec(v_stx_4904_);
return v_res_4910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4911_; lean_object* v___f_4912_; 
v___x_4911_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4912_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4912_, 0, v___x_4911_);
return v___f_4912_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4979_; lean_object* v___f_4980_; lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___f_4979_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_4980_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4981_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4982_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4982_, 0, v___x_4981_);
lean_ctor_set(v___x_4982_, 1, v___f_4980_);
lean_ctor_set(v___x_4982_, 2, v___f_4979_);
return v___x_4982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4984_; lean_object* v___x_4985_; 
v___x_4984_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4985_ = l_Lean_registerBuiltinAttribute(v___x_4984_);
return v___x_4985_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4986_){
_start:
{
lean_object* v_res_4987_; 
v_res_4987_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4987_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4988_, lean_object* v_x_4989_, lean_object* v_x_4990_){
_start:
{
uint8_t v___x_4991_; 
v___x_4991_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4989_, v_x_4990_);
return v___x_4991_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_4992_, lean_object* v_x_4993_, lean_object* v_x_4994_){
_start:
{
uint8_t v_res_4995_; lean_object* v_r_4996_; 
v_res_4995_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_4992_, v_x_4993_, v_x_4994_);
lean_dec(v_x_4994_);
lean_dec_ref(v_x_4993_);
v_r_4996_ = lean_box(v_res_4995_);
return v_r_4996_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_4997_, lean_object* v_msg_4998_, lean_object* v___y_4999_, lean_object* v___y_5000_){
_start:
{
lean_object* v___x_5002_; 
v___x_5002_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4998_, v___y_4999_, v___y_5000_);
return v___x_5002_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_5003_, lean_object* v_msg_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_, lean_object* v___y_5007_){
_start:
{
lean_object* v_res_5008_; 
v_res_5008_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_5003_, v_msg_5004_, v___y_5005_, v___y_5006_);
lean_dec(v___y_5006_);
lean_dec_ref(v___y_5005_);
return v_res_5008_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5009_, lean_object* v_x_5010_, size_t v_x_5011_, lean_object* v_x_5012_){
_start:
{
uint8_t v___x_5013_; 
v___x_5013_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5010_, v_x_5011_, v_x_5012_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5014_, lean_object* v_x_5015_, lean_object* v_x_5016_, lean_object* v_x_5017_){
_start:
{
size_t v_x_3024__boxed_5018_; uint8_t v_res_5019_; lean_object* v_r_5020_; 
v_x_3024__boxed_5018_ = lean_unbox_usize(v_x_5016_);
lean_dec(v_x_5016_);
v_res_5019_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_5014_, v_x_5015_, v_x_3024__boxed_5018_, v_x_5017_);
lean_dec(v_x_5017_);
lean_dec_ref(v_x_5015_);
v_r_5020_ = lean_box(v_res_5019_);
return v_r_5020_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5021_, lean_object* v_keys_5022_, lean_object* v_vals_5023_, lean_object* v_heq_5024_, lean_object* v_i_5025_, lean_object* v_k_5026_){
_start:
{
uint8_t v___x_5027_; 
v___x_5027_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_5022_, v_i_5025_, v_k_5026_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5028_, lean_object* v_keys_5029_, lean_object* v_vals_5030_, lean_object* v_heq_5031_, lean_object* v_i_5032_, lean_object* v_k_5033_){
_start:
{
uint8_t v_res_5034_; lean_object* v_r_5035_; 
v_res_5034_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_5028_, v_keys_5029_, v_vals_5030_, v_heq_5031_, v_i_5032_, v_k_5033_);
lean_dec(v_k_5033_);
lean_dec_ref(v_vals_5030_);
lean_dec_ref(v_keys_5029_);
v_r_5035_ = lean_box(v_res_5034_);
return v_r_5035_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5038_; lean_object* v___x_5039_; lean_object* v___x_5040_; 
v___x_5038_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5039_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5040_ = l_Lean_addBuiltinDocString(v___x_5038_, v___x_5039_);
return v___x_5040_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5041_){
_start:
{
lean_object* v_res_5042_; 
v_res_5042_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5042_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_5043_){
_start:
{
lean_object* v___x_5045_; lean_object* v_env_5046_; lean_object* v___x_5047_; lean_object* v_ext_5048_; lean_object* v_toEnvExtension_5049_; lean_object* v_asyncMode_5050_; lean_object* v___x_5051_; lean_object* v___x_5052_; lean_object* v_discrTree_5053_; lean_object* v___x_5054_; 
v___x_5045_ = lean_st_ref_get(v_a_5043_);
v_env_5046_ = lean_ctor_get(v___x_5045_, 0);
lean_inc_ref(v_env_5046_);
lean_dec(v___x_5045_);
v___x_5047_ = l_Lean_Meta_instanceExtension;
v_ext_5048_ = lean_ctor_get(v___x_5047_, 1);
v_toEnvExtension_5049_ = lean_ctor_get(v_ext_5048_, 0);
v_asyncMode_5050_ = lean_ctor_get(v_toEnvExtension_5049_, 2);
v___x_5051_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5052_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5051_, v___x_5047_, v_env_5046_, v_asyncMode_5050_);
v_discrTree_5053_ = lean_ctor_get(v___x_5052_, 0);
lean_inc_ref(v_discrTree_5053_);
lean_dec(v___x_5052_);
v___x_5054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5054_, 0, v_discrTree_5053_);
return v___x_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_5055_, lean_object* v_a_5056_){
_start:
{
lean_object* v_res_5057_; 
v_res_5057_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5055_);
lean_dec(v_a_5055_);
return v_res_5057_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_5058_, lean_object* v_a_5059_){
_start:
{
lean_object* v___x_5061_; 
v___x_5061_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5059_);
return v___x_5061_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_5062_, lean_object* v_a_5063_, lean_object* v_a_5064_){
_start:
{
lean_object* v_res_5065_; 
v_res_5065_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_5062_, v_a_5063_);
lean_dec(v_a_5063_);
lean_dec_ref(v_a_5062_);
return v_res_5065_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_5066_){
_start:
{
lean_object* v___x_5068_; lean_object* v_env_5069_; lean_object* v___x_5070_; lean_object* v_ext_5071_; lean_object* v_toEnvExtension_5072_; lean_object* v_asyncMode_5073_; lean_object* v___x_5074_; lean_object* v___x_5075_; lean_object* v_erased_5076_; lean_object* v___x_5077_; 
v___x_5068_ = lean_st_ref_get(v_a_5066_);
v_env_5069_ = lean_ctor_get(v___x_5068_, 0);
lean_inc_ref(v_env_5069_);
lean_dec(v___x_5068_);
v___x_5070_ = l_Lean_Meta_instanceExtension;
v_ext_5071_ = lean_ctor_get(v___x_5070_, 1);
v_toEnvExtension_5072_ = lean_ctor_get(v_ext_5071_, 0);
v_asyncMode_5073_ = lean_ctor_get(v_toEnvExtension_5072_, 2);
v___x_5074_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5075_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5074_, v___x_5070_, v_env_5069_, v_asyncMode_5073_);
v_erased_5076_ = lean_ctor_get(v___x_5075_, 2);
lean_inc_ref(v_erased_5076_);
lean_dec(v___x_5075_);
v___x_5077_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5077_, 0, v_erased_5076_);
return v___x_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_5078_, lean_object* v_a_5079_){
_start:
{
lean_object* v_res_5080_; 
v_res_5080_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5078_);
lean_dec(v_a_5078_);
return v_res_5080_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_5081_, lean_object* v_a_5082_){
_start:
{
lean_object* v___x_5084_; 
v___x_5084_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5082_);
return v___x_5084_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_5085_, lean_object* v_a_5086_, lean_object* v_a_5087_){
_start:
{
lean_object* v_res_5088_; 
v_res_5088_ = l_Lean_Meta_getErasedInstances(v_a_5085_, v_a_5086_);
lean_dec(v_a_5086_);
lean_dec_ref(v_a_5085_);
return v_res_5088_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_5089_, lean_object* v_declName_5090_){
_start:
{
lean_object* v___x_5091_; lean_object* v_ext_5092_; lean_object* v_toEnvExtension_5093_; lean_object* v_asyncMode_5094_; lean_object* v___x_5095_; lean_object* v___x_5096_; lean_object* v_instanceNames_5097_; uint8_t v___x_5098_; 
v___x_5091_ = l_Lean_Meta_instanceExtension;
v_ext_5092_ = lean_ctor_get(v___x_5091_, 1);
v_toEnvExtension_5093_ = lean_ctor_get(v_ext_5092_, 0);
v_asyncMode_5094_ = lean_ctor_get(v_toEnvExtension_5093_, 2);
v___x_5095_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5096_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5095_, v___x_5091_, v_env_5089_, v_asyncMode_5094_);
v_instanceNames_5097_ = lean_ctor_get(v___x_5096_, 1);
lean_inc_ref(v_instanceNames_5097_);
lean_dec(v___x_5096_);
v___x_5098_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_5097_, v_declName_5090_);
lean_dec_ref(v_instanceNames_5097_);
return v___x_5098_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_5099_, lean_object* v_declName_5100_){
_start:
{
uint8_t v_res_5101_; lean_object* v_r_5102_; 
v_res_5101_ = l_Lean_Meta_isInstanceCore(v_env_5099_, v_declName_5100_);
lean_dec(v_declName_5100_);
v_r_5102_ = lean_box(v_res_5101_);
return v_r_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_5103_, lean_object* v_a_5104_){
_start:
{
lean_object* v___x_5106_; lean_object* v_env_5107_; uint8_t v___x_5108_; lean_object* v___x_5109_; lean_object* v___x_5110_; 
v___x_5106_ = lean_st_ref_get(v_a_5104_);
v_env_5107_ = lean_ctor_get(v___x_5106_, 0);
lean_inc_ref(v_env_5107_);
lean_dec(v___x_5106_);
v___x_5108_ = l_Lean_Meta_isInstanceCore(v_env_5107_, v_declName_5103_);
v___x_5109_ = lean_box(v___x_5108_);
v___x_5110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5110_, 0, v___x_5109_);
return v___x_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_5111_, lean_object* v_a_5112_, lean_object* v_a_5113_){
_start:
{
lean_object* v_res_5114_; 
v_res_5114_ = l_Lean_Meta_isInstance___redArg(v_declName_5111_, v_a_5112_);
lean_dec(v_a_5112_);
lean_dec(v_declName_5111_);
return v_res_5114_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_5115_, lean_object* v_a_5116_, lean_object* v_a_5117_){
_start:
{
lean_object* v___x_5119_; 
v___x_5119_ = l_Lean_Meta_isInstance___redArg(v_declName_5115_, v_a_5117_);
return v___x_5119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_, lean_object* v_a_5123_){
_start:
{
lean_object* v_res_5124_; 
v_res_5124_ = l_Lean_Meta_isInstance(v_declName_5120_, v_a_5121_, v_a_5122_);
lean_dec(v_a_5122_);
lean_dec_ref(v_a_5121_);
lean_dec(v_declName_5120_);
return v_res_5124_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5125_, lean_object* v_vals_5126_, lean_object* v_i_5127_, lean_object* v_k_5128_){
_start:
{
lean_object* v___x_5129_; uint8_t v___x_5130_; 
v___x_5129_ = lean_array_get_size(v_keys_5125_);
v___x_5130_ = lean_nat_dec_lt(v_i_5127_, v___x_5129_);
if (v___x_5130_ == 0)
{
lean_object* v___x_5131_; 
lean_dec(v_i_5127_);
v___x_5131_ = lean_box(0);
return v___x_5131_;
}
else
{
lean_object* v_k_x27_5132_; uint8_t v___x_5133_; 
v_k_x27_5132_ = lean_array_fget_borrowed(v_keys_5125_, v_i_5127_);
v___x_5133_ = lean_name_eq(v_k_5128_, v_k_x27_5132_);
if (v___x_5133_ == 0)
{
lean_object* v___x_5134_; lean_object* v___x_5135_; 
v___x_5134_ = lean_unsigned_to_nat(1u);
v___x_5135_ = lean_nat_add(v_i_5127_, v___x_5134_);
lean_dec(v_i_5127_);
v_i_5127_ = v___x_5135_;
goto _start;
}
else
{
lean_object* v___x_5137_; lean_object* v___x_5138_; 
v___x_5137_ = lean_array_fget_borrowed(v_vals_5126_, v_i_5127_);
lean_dec(v_i_5127_);
lean_inc(v___x_5137_);
v___x_5138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5138_, 0, v___x_5137_);
return v___x_5138_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5139_, lean_object* v_vals_5140_, lean_object* v_i_5141_, lean_object* v_k_5142_){
_start:
{
lean_object* v_res_5143_; 
v_res_5143_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5139_, v_vals_5140_, v_i_5141_, v_k_5142_);
lean_dec(v_k_5142_);
lean_dec_ref(v_vals_5140_);
lean_dec_ref(v_keys_5139_);
return v_res_5143_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_5144_, size_t v_x_5145_, lean_object* v_x_5146_){
_start:
{
if (lean_obj_tag(v_x_5144_) == 0)
{
lean_object* v_es_5147_; lean_object* v___x_5148_; size_t v___x_5149_; size_t v___x_5150_; lean_object* v_j_5151_; lean_object* v___x_5152_; 
v_es_5147_ = lean_ctor_get(v_x_5144_, 0);
v___x_5148_ = lean_box(2);
v___x_5149_ = ((size_t)31ULL);
v___x_5150_ = lean_usize_land(v_x_5145_, v___x_5149_);
v_j_5151_ = lean_usize_to_nat(v___x_5150_);
v___x_5152_ = lean_array_get_borrowed(v___x_5148_, v_es_5147_, v_j_5151_);
lean_dec(v_j_5151_);
switch(lean_obj_tag(v___x_5152_))
{
case 0:
{
lean_object* v_key_5153_; lean_object* v_val_5154_; uint8_t v___x_5155_; 
v_key_5153_ = lean_ctor_get(v___x_5152_, 0);
v_val_5154_ = lean_ctor_get(v___x_5152_, 1);
v___x_5155_ = lean_name_eq(v_x_5146_, v_key_5153_);
if (v___x_5155_ == 0)
{
lean_object* v___x_5156_; 
v___x_5156_ = lean_box(0);
return v___x_5156_;
}
else
{
lean_object* v___x_5157_; 
lean_inc(v_val_5154_);
v___x_5157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5157_, 0, v_val_5154_);
return v___x_5157_;
}
}
case 1:
{
lean_object* v_node_5158_; size_t v___x_5159_; size_t v___x_5160_; 
v_node_5158_ = lean_ctor_get(v___x_5152_, 0);
v___x_5159_ = ((size_t)5ULL);
v___x_5160_ = lean_usize_shift_right(v_x_5145_, v___x_5159_);
v_x_5144_ = v_node_5158_;
v_x_5145_ = v___x_5160_;
goto _start;
}
default: 
{
lean_object* v___x_5162_; 
v___x_5162_ = lean_box(0);
return v___x_5162_;
}
}
}
else
{
lean_object* v_ks_5163_; lean_object* v_vs_5164_; lean_object* v___x_5165_; lean_object* v___x_5166_; 
v_ks_5163_ = lean_ctor_get(v_x_5144_, 0);
v_vs_5164_ = lean_ctor_get(v_x_5144_, 1);
v___x_5165_ = lean_unsigned_to_nat(0u);
v___x_5166_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5163_, v_vs_5164_, v___x_5165_, v_x_5146_);
return v___x_5166_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5167_, lean_object* v_x_5168_, lean_object* v_x_5169_){
_start:
{
size_t v_x_478__boxed_5170_; lean_object* v_res_5171_; 
v_x_478__boxed_5170_ = lean_unbox_usize(v_x_5168_);
lean_dec(v_x_5168_);
v_res_5171_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5167_, v_x_478__boxed_5170_, v_x_5169_);
lean_dec(v_x_5169_);
lean_dec_ref(v_x_5167_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_5172_, lean_object* v_x_5173_){
_start:
{
uint64_t v___y_5175_; 
if (lean_obj_tag(v_x_5173_) == 0)
{
uint64_t v___x_5178_; 
v___x_5178_ = 1723ULL;
v___y_5175_ = v___x_5178_;
goto v___jp_5174_;
}
else
{
uint64_t v_hash_5179_; 
v_hash_5179_ = lean_ctor_get_uint64(v_x_5173_, sizeof(void*)*2);
v___y_5175_ = v_hash_5179_;
goto v___jp_5174_;
}
v___jp_5174_:
{
size_t v___x_5176_; lean_object* v___x_5177_; 
v___x_5176_ = lean_uint64_to_usize(v___y_5175_);
v___x_5177_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5172_, v___x_5176_, v_x_5173_);
return v___x_5177_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_5180_, lean_object* v_x_5181_){
_start:
{
lean_object* v_res_5182_; 
v_res_5182_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5180_, v_x_5181_);
lean_dec(v_x_5181_);
lean_dec_ref(v_x_5180_);
return v_res_5182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_5183_, lean_object* v_a_5184_){
_start:
{
lean_object* v___x_5186_; lean_object* v_env_5187_; lean_object* v___x_5188_; lean_object* v_ext_5189_; lean_object* v_toEnvExtension_5190_; lean_object* v_asyncMode_5191_; lean_object* v___x_5192_; lean_object* v___x_5193_; lean_object* v_instanceNames_5194_; lean_object* v___x_5195_; 
v___x_5186_ = lean_st_ref_get(v_a_5184_);
v_env_5187_ = lean_ctor_get(v___x_5186_, 0);
lean_inc_ref(v_env_5187_);
lean_dec(v___x_5186_);
v___x_5188_ = l_Lean_Meta_instanceExtension;
v_ext_5189_ = lean_ctor_get(v___x_5188_, 1);
v_toEnvExtension_5190_ = lean_ctor_get(v_ext_5189_, 0);
v_asyncMode_5191_ = lean_ctor_get(v_toEnvExtension_5190_, 2);
v___x_5192_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5193_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5192_, v___x_5188_, v_env_5187_, v_asyncMode_5191_);
v_instanceNames_5194_ = lean_ctor_get(v___x_5193_, 1);
lean_inc_ref(v_instanceNames_5194_);
lean_dec(v___x_5193_);
v___x_5195_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5194_, v_declName_5183_);
lean_dec_ref(v_instanceNames_5194_);
if (lean_obj_tag(v___x_5195_) == 1)
{
lean_object* v_val_5196_; lean_object* v___x_5198_; uint8_t v_isShared_5199_; uint8_t v_isSharedCheck_5205_; 
v_val_5196_ = lean_ctor_get(v___x_5195_, 0);
v_isSharedCheck_5205_ = !lean_is_exclusive(v___x_5195_);
if (v_isSharedCheck_5205_ == 0)
{
v___x_5198_ = v___x_5195_;
v_isShared_5199_ = v_isSharedCheck_5205_;
goto v_resetjp_5197_;
}
else
{
lean_inc(v_val_5196_);
lean_dec(v___x_5195_);
v___x_5198_ = lean_box(0);
v_isShared_5199_ = v_isSharedCheck_5205_;
goto v_resetjp_5197_;
}
v_resetjp_5197_:
{
lean_object* v_priority_5200_; lean_object* v___x_5202_; 
v_priority_5200_ = lean_ctor_get(v_val_5196_, 2);
lean_inc(v_priority_5200_);
lean_dec(v_val_5196_);
if (v_isShared_5199_ == 0)
{
lean_ctor_set(v___x_5198_, 0, v_priority_5200_);
v___x_5202_ = v___x_5198_;
goto v_reusejp_5201_;
}
else
{
lean_object* v_reuseFailAlloc_5204_; 
v_reuseFailAlloc_5204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5204_, 0, v_priority_5200_);
v___x_5202_ = v_reuseFailAlloc_5204_;
goto v_reusejp_5201_;
}
v_reusejp_5201_:
{
lean_object* v___x_5203_; 
v___x_5203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5203_, 0, v___x_5202_);
return v___x_5203_;
}
}
}
else
{
lean_object* v___x_5206_; lean_object* v___x_5207_; 
lean_dec(v___x_5195_);
v___x_5206_ = lean_box(0);
v___x_5207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5207_, 0, v___x_5206_);
return v___x_5207_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_5208_, lean_object* v_a_5209_, lean_object* v_a_5210_){
_start:
{
lean_object* v_res_5211_; 
v_res_5211_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5208_, v_a_5209_);
lean_dec(v_a_5209_);
lean_dec(v_declName_5208_);
return v_res_5211_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_5212_, lean_object* v_a_5213_, lean_object* v_a_5214_){
_start:
{
lean_object* v___x_5216_; 
v___x_5216_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5212_, v_a_5214_);
return v___x_5216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_, lean_object* v_a_5220_){
_start:
{
lean_object* v_res_5221_; 
v_res_5221_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_5217_, v_a_5218_, v_a_5219_);
lean_dec(v_a_5219_);
lean_dec_ref(v_a_5218_);
lean_dec(v_declName_5217_);
return v_res_5221_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_5222_, lean_object* v_x_5223_, lean_object* v_x_5224_){
_start:
{
lean_object* v___x_5225_; 
v___x_5225_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5223_, v_x_5224_);
return v___x_5225_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_5226_, lean_object* v_x_5227_, lean_object* v_x_5228_){
_start:
{
lean_object* v_res_5229_; 
v_res_5229_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_5226_, v_x_5227_, v_x_5228_);
lean_dec(v_x_5228_);
lean_dec_ref(v_x_5227_);
return v_res_5229_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5230_, lean_object* v_x_5231_, size_t v_x_5232_, lean_object* v_x_5233_){
_start:
{
lean_object* v___x_5234_; 
v___x_5234_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5231_, v_x_5232_, v_x_5233_);
return v___x_5234_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5235_, lean_object* v_x_5236_, lean_object* v_x_5237_, lean_object* v_x_5238_){
_start:
{
size_t v_x_589__boxed_5239_; lean_object* v_res_5240_; 
v_x_589__boxed_5239_ = lean_unbox_usize(v_x_5237_);
lean_dec(v_x_5237_);
v_res_5240_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_5235_, v_x_5236_, v_x_589__boxed_5239_, v_x_5238_);
lean_dec(v_x_5238_);
lean_dec_ref(v_x_5236_);
return v_res_5240_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5241_, lean_object* v_keys_5242_, lean_object* v_vals_5243_, lean_object* v_heq_5244_, lean_object* v_i_5245_, lean_object* v_k_5246_){
_start:
{
lean_object* v___x_5247_; 
v___x_5247_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5242_, v_vals_5243_, v_i_5245_, v_k_5246_);
return v___x_5247_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5248_, lean_object* v_keys_5249_, lean_object* v_vals_5250_, lean_object* v_heq_5251_, lean_object* v_i_5252_, lean_object* v_k_5253_){
_start:
{
lean_object* v_res_5254_; 
v_res_5254_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5248_, v_keys_5249_, v_vals_5250_, v_heq_5251_, v_i_5252_, v_k_5253_);
lean_dec(v_k_5253_);
lean_dec_ref(v_vals_5250_);
lean_dec_ref(v_keys_5249_);
return v_res_5254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_5255_, lean_object* v_a_5256_){
_start:
{
lean_object* v___x_5258_; lean_object* v_env_5259_; lean_object* v___x_5260_; lean_object* v_ext_5261_; lean_object* v_toEnvExtension_5262_; lean_object* v_asyncMode_5263_; lean_object* v___x_5264_; lean_object* v___x_5265_; lean_object* v_instanceNames_5266_; lean_object* v___x_5267_; 
v___x_5258_ = lean_st_ref_get(v_a_5256_);
v_env_5259_ = lean_ctor_get(v___x_5258_, 0);
lean_inc_ref(v_env_5259_);
lean_dec(v___x_5258_);
v___x_5260_ = l_Lean_Meta_instanceExtension;
v_ext_5261_ = lean_ctor_get(v___x_5260_, 1);
v_toEnvExtension_5262_ = lean_ctor_get(v_ext_5261_, 0);
v_asyncMode_5263_ = lean_ctor_get(v_toEnvExtension_5262_, 2);
v___x_5264_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5265_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5264_, v___x_5260_, v_env_5259_, v_asyncMode_5263_);
v_instanceNames_5266_ = lean_ctor_get(v___x_5265_, 1);
lean_inc_ref(v_instanceNames_5266_);
lean_dec(v___x_5265_);
v___x_5267_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5266_, v_declName_5255_);
lean_dec_ref(v_instanceNames_5266_);
if (lean_obj_tag(v___x_5267_) == 1)
{
lean_object* v_val_5268_; lean_object* v___x_5270_; uint8_t v_isShared_5271_; uint8_t v_isSharedCheck_5278_; 
v_val_5268_ = lean_ctor_get(v___x_5267_, 0);
v_isSharedCheck_5278_ = !lean_is_exclusive(v___x_5267_);
if (v_isSharedCheck_5278_ == 0)
{
v___x_5270_ = v___x_5267_;
v_isShared_5271_ = v_isSharedCheck_5278_;
goto v_resetjp_5269_;
}
else
{
lean_inc(v_val_5268_);
lean_dec(v___x_5267_);
v___x_5270_ = lean_box(0);
v_isShared_5271_ = v_isSharedCheck_5278_;
goto v_resetjp_5269_;
}
v_resetjp_5269_:
{
uint8_t v_attrKind_5272_; lean_object* v___x_5273_; lean_object* v___x_5275_; 
v_attrKind_5272_ = lean_ctor_get_uint8(v_val_5268_, sizeof(void*)*5);
lean_dec(v_val_5268_);
v___x_5273_ = lean_box(v_attrKind_5272_);
if (v_isShared_5271_ == 0)
{
lean_ctor_set(v___x_5270_, 0, v___x_5273_);
v___x_5275_ = v___x_5270_;
goto v_reusejp_5274_;
}
else
{
lean_object* v_reuseFailAlloc_5277_; 
v_reuseFailAlloc_5277_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5277_, 0, v___x_5273_);
v___x_5275_ = v_reuseFailAlloc_5277_;
goto v_reusejp_5274_;
}
v_reusejp_5274_:
{
lean_object* v___x_5276_; 
v___x_5276_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5276_, 0, v___x_5275_);
return v___x_5276_;
}
}
}
else
{
lean_object* v___x_5279_; lean_object* v___x_5280_; 
lean_dec(v___x_5267_);
v___x_5279_ = lean_box(0);
v___x_5280_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5280_, 0, v___x_5279_);
return v___x_5280_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_5281_, lean_object* v_a_5282_, lean_object* v_a_5283_){
_start:
{
lean_object* v_res_5284_; 
v_res_5284_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5281_, v_a_5282_);
lean_dec(v_a_5282_);
lean_dec(v_declName_5281_);
return v_res_5284_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_5285_, lean_object* v_a_5286_, lean_object* v_a_5287_){
_start:
{
lean_object* v___x_5289_; 
v___x_5289_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5285_, v_a_5287_);
return v___x_5289_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_, lean_object* v_a_5293_){
_start:
{
lean_object* v_res_5294_; 
v_res_5294_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_5290_, v_a_5291_, v_a_5292_);
lean_dec(v_a_5292_);
lean_dec_ref(v_a_5291_);
lean_dec(v_declName_5290_);
return v_res_5294_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5299_, lean_object* v_v_5300_, lean_object* v_t_5301_){
_start:
{
if (lean_obj_tag(v_t_5301_) == 0)
{
lean_object* v_size_5302_; lean_object* v_k_5303_; lean_object* v_v_5304_; lean_object* v_l_5305_; lean_object* v_r_5306_; lean_object* v___x_5308_; uint8_t v_isShared_5309_; uint8_t v_isSharedCheck_5587_; 
v_size_5302_ = lean_ctor_get(v_t_5301_, 0);
v_k_5303_ = lean_ctor_get(v_t_5301_, 1);
v_v_5304_ = lean_ctor_get(v_t_5301_, 2);
v_l_5305_ = lean_ctor_get(v_t_5301_, 3);
v_r_5306_ = lean_ctor_get(v_t_5301_, 4);
v_isSharedCheck_5587_ = !lean_is_exclusive(v_t_5301_);
if (v_isSharedCheck_5587_ == 0)
{
v___x_5308_ = v_t_5301_;
v_isShared_5309_ = v_isSharedCheck_5587_;
goto v_resetjp_5307_;
}
else
{
lean_inc(v_r_5306_);
lean_inc(v_l_5305_);
lean_inc(v_v_5304_);
lean_inc(v_k_5303_);
lean_inc(v_size_5302_);
lean_dec(v_t_5301_);
v___x_5308_ = lean_box(0);
v_isShared_5309_ = v_isSharedCheck_5587_;
goto v_resetjp_5307_;
}
v_resetjp_5307_:
{
uint8_t v___x_5310_; 
v___x_5310_ = lean_nat_dec_lt(v_k_5303_, v_k_5299_);
if (v___x_5310_ == 0)
{
uint8_t v___x_5311_; 
v___x_5311_ = lean_nat_dec_eq(v_k_5303_, v_k_5299_);
if (v___x_5311_ == 0)
{
lean_object* v_impl_5312_; lean_object* v___x_5313_; 
lean_dec(v_size_5302_);
v_impl_5312_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5299_, v_v_5300_, v_r_5306_);
v___x_5313_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5305_) == 0)
{
lean_object* v_size_5314_; lean_object* v_size_5315_; lean_object* v_k_5316_; lean_object* v_v_5317_; lean_object* v_l_5318_; lean_object* v_r_5319_; lean_object* v___x_5320_; lean_object* v___x_5321_; uint8_t v___x_5322_; 
v_size_5314_ = lean_ctor_get(v_l_5305_, 0);
v_size_5315_ = lean_ctor_get(v_impl_5312_, 0);
lean_inc(v_size_5315_);
v_k_5316_ = lean_ctor_get(v_impl_5312_, 1);
lean_inc(v_k_5316_);
v_v_5317_ = lean_ctor_get(v_impl_5312_, 2);
lean_inc(v_v_5317_);
v_l_5318_ = lean_ctor_get(v_impl_5312_, 3);
lean_inc(v_l_5318_);
v_r_5319_ = lean_ctor_get(v_impl_5312_, 4);
lean_inc(v_r_5319_);
v___x_5320_ = lean_unsigned_to_nat(3u);
v___x_5321_ = lean_nat_mul(v___x_5320_, v_size_5314_);
v___x_5322_ = lean_nat_dec_lt(v___x_5321_, v_size_5315_);
lean_dec(v___x_5321_);
if (v___x_5322_ == 0)
{
lean_object* v___x_5323_; lean_object* v___x_5324_; lean_object* v___x_5326_; 
lean_dec(v_r_5319_);
lean_dec(v_l_5318_);
lean_dec(v_v_5317_);
lean_dec(v_k_5316_);
v___x_5323_ = lean_nat_add(v___x_5313_, v_size_5314_);
v___x_5324_ = lean_nat_add(v___x_5323_, v_size_5315_);
lean_dec(v_size_5315_);
lean_dec(v___x_5323_);
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 4, v_impl_5312_);
lean_ctor_set(v___x_5308_, 0, v___x_5324_);
v___x_5326_ = v___x_5308_;
goto v_reusejp_5325_;
}
else
{
lean_object* v_reuseFailAlloc_5327_; 
v_reuseFailAlloc_5327_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5327_, 0, v___x_5324_);
lean_ctor_set(v_reuseFailAlloc_5327_, 1, v_k_5303_);
lean_ctor_set(v_reuseFailAlloc_5327_, 2, v_v_5304_);
lean_ctor_set(v_reuseFailAlloc_5327_, 3, v_l_5305_);
lean_ctor_set(v_reuseFailAlloc_5327_, 4, v_impl_5312_);
v___x_5326_ = v_reuseFailAlloc_5327_;
goto v_reusejp_5325_;
}
v_reusejp_5325_:
{
return v___x_5326_;
}
}
else
{
lean_object* v___x_5329_; uint8_t v_isShared_5330_; uint8_t v_isSharedCheck_5391_; 
v_isSharedCheck_5391_ = !lean_is_exclusive(v_impl_5312_);
if (v_isSharedCheck_5391_ == 0)
{
lean_object* v_unused_5392_; lean_object* v_unused_5393_; lean_object* v_unused_5394_; lean_object* v_unused_5395_; lean_object* v_unused_5396_; 
v_unused_5392_ = lean_ctor_get(v_impl_5312_, 4);
lean_dec(v_unused_5392_);
v_unused_5393_ = lean_ctor_get(v_impl_5312_, 3);
lean_dec(v_unused_5393_);
v_unused_5394_ = lean_ctor_get(v_impl_5312_, 2);
lean_dec(v_unused_5394_);
v_unused_5395_ = lean_ctor_get(v_impl_5312_, 1);
lean_dec(v_unused_5395_);
v_unused_5396_ = lean_ctor_get(v_impl_5312_, 0);
lean_dec(v_unused_5396_);
v___x_5329_ = v_impl_5312_;
v_isShared_5330_ = v_isSharedCheck_5391_;
goto v_resetjp_5328_;
}
else
{
lean_dec(v_impl_5312_);
v___x_5329_ = lean_box(0);
v_isShared_5330_ = v_isSharedCheck_5391_;
goto v_resetjp_5328_;
}
v_resetjp_5328_:
{
lean_object* v_size_5331_; lean_object* v_k_5332_; lean_object* v_v_5333_; lean_object* v_l_5334_; lean_object* v_r_5335_; lean_object* v_size_5336_; lean_object* v___x_5337_; lean_object* v___x_5338_; uint8_t v___x_5339_; 
v_size_5331_ = lean_ctor_get(v_l_5318_, 0);
v_k_5332_ = lean_ctor_get(v_l_5318_, 1);
v_v_5333_ = lean_ctor_get(v_l_5318_, 2);
v_l_5334_ = lean_ctor_get(v_l_5318_, 3);
v_r_5335_ = lean_ctor_get(v_l_5318_, 4);
v_size_5336_ = lean_ctor_get(v_r_5319_, 0);
v___x_5337_ = lean_unsigned_to_nat(2u);
v___x_5338_ = lean_nat_mul(v___x_5337_, v_size_5336_);
v___x_5339_ = lean_nat_dec_lt(v_size_5331_, v___x_5338_);
lean_dec(v___x_5338_);
if (v___x_5339_ == 0)
{
lean_object* v___x_5341_; uint8_t v_isShared_5342_; uint8_t v_isSharedCheck_5367_; 
lean_inc(v_r_5335_);
lean_inc(v_l_5334_);
lean_inc(v_v_5333_);
lean_inc(v_k_5332_);
v_isSharedCheck_5367_ = !lean_is_exclusive(v_l_5318_);
if (v_isSharedCheck_5367_ == 0)
{
lean_object* v_unused_5368_; lean_object* v_unused_5369_; lean_object* v_unused_5370_; lean_object* v_unused_5371_; lean_object* v_unused_5372_; 
v_unused_5368_ = lean_ctor_get(v_l_5318_, 4);
lean_dec(v_unused_5368_);
v_unused_5369_ = lean_ctor_get(v_l_5318_, 3);
lean_dec(v_unused_5369_);
v_unused_5370_ = lean_ctor_get(v_l_5318_, 2);
lean_dec(v_unused_5370_);
v_unused_5371_ = lean_ctor_get(v_l_5318_, 1);
lean_dec(v_unused_5371_);
v_unused_5372_ = lean_ctor_get(v_l_5318_, 0);
lean_dec(v_unused_5372_);
v___x_5341_ = v_l_5318_;
v_isShared_5342_ = v_isSharedCheck_5367_;
goto v_resetjp_5340_;
}
else
{
lean_dec(v_l_5318_);
v___x_5341_ = lean_box(0);
v_isShared_5342_ = v_isSharedCheck_5367_;
goto v_resetjp_5340_;
}
v_resetjp_5340_:
{
lean_object* v___x_5343_; lean_object* v___x_5344_; lean_object* v___y_5346_; lean_object* v___y_5347_; lean_object* v___y_5348_; lean_object* v___y_5357_; 
v___x_5343_ = lean_nat_add(v___x_5313_, v_size_5314_);
v___x_5344_ = lean_nat_add(v___x_5343_, v_size_5315_);
lean_dec(v_size_5315_);
if (lean_obj_tag(v_l_5334_) == 0)
{
lean_object* v_size_5365_; 
v_size_5365_ = lean_ctor_get(v_l_5334_, 0);
lean_inc(v_size_5365_);
v___y_5357_ = v_size_5365_;
goto v___jp_5356_;
}
else
{
lean_object* v___x_5366_; 
v___x_5366_ = lean_unsigned_to_nat(0u);
v___y_5357_ = v___x_5366_;
goto v___jp_5356_;
}
v___jp_5345_:
{
lean_object* v___x_5349_; lean_object* v___x_5351_; 
v___x_5349_ = lean_nat_add(v___y_5347_, v___y_5348_);
lean_dec(v___y_5348_);
lean_dec(v___y_5347_);
if (v_isShared_5342_ == 0)
{
lean_ctor_set(v___x_5341_, 4, v_r_5319_);
lean_ctor_set(v___x_5341_, 3, v_r_5335_);
lean_ctor_set(v___x_5341_, 2, v_v_5317_);
lean_ctor_set(v___x_5341_, 1, v_k_5316_);
lean_ctor_set(v___x_5341_, 0, v___x_5349_);
v___x_5351_ = v___x_5341_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v___x_5349_);
lean_ctor_set(v_reuseFailAlloc_5355_, 1, v_k_5316_);
lean_ctor_set(v_reuseFailAlloc_5355_, 2, v_v_5317_);
lean_ctor_set(v_reuseFailAlloc_5355_, 3, v_r_5335_);
lean_ctor_set(v_reuseFailAlloc_5355_, 4, v_r_5319_);
v___x_5351_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
lean_object* v___x_5353_; 
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 4, v___x_5351_);
lean_ctor_set(v___x_5329_, 3, v___y_5346_);
lean_ctor_set(v___x_5329_, 2, v_v_5333_);
lean_ctor_set(v___x_5329_, 1, v_k_5332_);
lean_ctor_set(v___x_5329_, 0, v___x_5344_);
v___x_5353_ = v___x_5329_;
goto v_reusejp_5352_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v___x_5344_);
lean_ctor_set(v_reuseFailAlloc_5354_, 1, v_k_5332_);
lean_ctor_set(v_reuseFailAlloc_5354_, 2, v_v_5333_);
lean_ctor_set(v_reuseFailAlloc_5354_, 3, v___y_5346_);
lean_ctor_set(v_reuseFailAlloc_5354_, 4, v___x_5351_);
v___x_5353_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5352_;
}
v_reusejp_5352_:
{
return v___x_5353_;
}
}
}
v___jp_5356_:
{
lean_object* v___x_5358_; lean_object* v___x_5360_; 
v___x_5358_ = lean_nat_add(v___x_5343_, v___y_5357_);
lean_dec(v___y_5357_);
lean_dec(v___x_5343_);
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 4, v_l_5334_);
lean_ctor_set(v___x_5308_, 0, v___x_5358_);
v___x_5360_ = v___x_5308_;
goto v_reusejp_5359_;
}
else
{
lean_object* v_reuseFailAlloc_5364_; 
v_reuseFailAlloc_5364_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5364_, 0, v___x_5358_);
lean_ctor_set(v_reuseFailAlloc_5364_, 1, v_k_5303_);
lean_ctor_set(v_reuseFailAlloc_5364_, 2, v_v_5304_);
lean_ctor_set(v_reuseFailAlloc_5364_, 3, v_l_5305_);
lean_ctor_set(v_reuseFailAlloc_5364_, 4, v_l_5334_);
v___x_5360_ = v_reuseFailAlloc_5364_;
goto v_reusejp_5359_;
}
v_reusejp_5359_:
{
lean_object* v___x_5361_; 
v___x_5361_ = lean_nat_add(v___x_5313_, v_size_5336_);
if (lean_obj_tag(v_r_5335_) == 0)
{
lean_object* v_size_5362_; 
v_size_5362_ = lean_ctor_get(v_r_5335_, 0);
lean_inc(v_size_5362_);
v___y_5346_ = v___x_5360_;
v___y_5347_ = v___x_5361_;
v___y_5348_ = v_size_5362_;
goto v___jp_5345_;
}
else
{
lean_object* v___x_5363_; 
v___x_5363_ = lean_unsigned_to_nat(0u);
v___y_5346_ = v___x_5360_;
v___y_5347_ = v___x_5361_;
v___y_5348_ = v___x_5363_;
goto v___jp_5345_;
}
}
}
}
}
else
{
lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5375_; lean_object* v___x_5377_; 
lean_del_object(v___x_5308_);
v___x_5373_ = lean_nat_add(v___x_5313_, v_size_5314_);
v___x_5374_ = lean_nat_add(v___x_5373_, v_size_5315_);
lean_dec(v_size_5315_);
v___x_5375_ = lean_nat_add(v___x_5373_, v_size_5331_);
lean_dec(v___x_5373_);
lean_inc_ref(v_l_5305_);
if (v_isShared_5330_ == 0)
{
lean_ctor_set(v___x_5329_, 4, v_l_5318_);
lean_ctor_set(v___x_5329_, 3, v_l_5305_);
lean_ctor_set(v___x_5329_, 2, v_v_5304_);
lean_ctor_set(v___x_5329_, 1, v_k_5303_);
lean_ctor_set(v___x_5329_, 0, v___x_5375_);
v___x_5377_ = v___x_5329_;
goto v_reusejp_5376_;
}
else
{
lean_object* v_reuseFailAlloc_5390_; 
v_reuseFailAlloc_5390_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5390_, 0, v___x_5375_);
lean_ctor_set(v_reuseFailAlloc_5390_, 1, v_k_5303_);
lean_ctor_set(v_reuseFailAlloc_5390_, 2, v_v_5304_);
lean_ctor_set(v_reuseFailAlloc_5390_, 3, v_l_5305_);
lean_ctor_set(v_reuseFailAlloc_5390_, 4, v_l_5318_);
v___x_5377_ = v_reuseFailAlloc_5390_;
goto v_reusejp_5376_;
}
v_reusejp_5376_:
{
lean_object* v___x_5379_; uint8_t v_isShared_5380_; uint8_t v_isSharedCheck_5384_; 
v_isSharedCheck_5384_ = !lean_is_exclusive(v_l_5305_);
if (v_isSharedCheck_5384_ == 0)
{
lean_object* v_unused_5385_; lean_object* v_unused_5386_; lean_object* v_unused_5387_; lean_object* v_unused_5388_; lean_object* v_unused_5389_; 
v_unused_5385_ = lean_ctor_get(v_l_5305_, 4);
lean_dec(v_unused_5385_);
v_unused_5386_ = lean_ctor_get(v_l_5305_, 3);
lean_dec(v_unused_5386_);
v_unused_5387_ = lean_ctor_get(v_l_5305_, 2);
lean_dec(v_unused_5387_);
v_unused_5388_ = lean_ctor_get(v_l_5305_, 1);
lean_dec(v_unused_5388_);
v_unused_5389_ = lean_ctor_get(v_l_5305_, 0);
lean_dec(v_unused_5389_);
v___x_5379_ = v_l_5305_;
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
else
{
lean_dec(v_l_5305_);
v___x_5379_ = lean_box(0);
v_isShared_5380_ = v_isSharedCheck_5384_;
goto v_resetjp_5378_;
}
v_resetjp_5378_:
{
lean_object* v___x_5382_; 
if (v_isShared_5380_ == 0)
{
lean_ctor_set(v___x_5379_, 4, v_r_5319_);
lean_ctor_set(v___x_5379_, 3, v___x_5377_);
lean_ctor_set(v___x_5379_, 2, v_v_5317_);
lean_ctor_set(v___x_5379_, 1, v_k_5316_);
lean_ctor_set(v___x_5379_, 0, v___x_5374_);
v___x_5382_ = v___x_5379_;
goto v_reusejp_5381_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5374_);
lean_ctor_set(v_reuseFailAlloc_5383_, 1, v_k_5316_);
lean_ctor_set(v_reuseFailAlloc_5383_, 2, v_v_5317_);
lean_ctor_set(v_reuseFailAlloc_5383_, 3, v___x_5377_);
lean_ctor_set(v_reuseFailAlloc_5383_, 4, v_r_5319_);
v___x_5382_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5381_;
}
v_reusejp_5381_:
{
return v___x_5382_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5397_; 
v_l_5397_ = lean_ctor_get(v_impl_5312_, 3);
lean_inc(v_l_5397_);
if (lean_obj_tag(v_l_5397_) == 0)
{
lean_object* v_r_5398_; lean_object* v_k_5399_; lean_object* v_v_5400_; lean_object* v___x_5402_; uint8_t v_isShared_5403_; uint8_t v_isSharedCheck_5423_; 
v_r_5398_ = lean_ctor_get(v_impl_5312_, 4);
v_k_5399_ = lean_ctor_get(v_impl_5312_, 1);
v_v_5400_ = lean_ctor_get(v_impl_5312_, 2);
v_isSharedCheck_5423_ = !lean_is_exclusive(v_impl_5312_);
if (v_isSharedCheck_5423_ == 0)
{
lean_object* v_unused_5424_; lean_object* v_unused_5425_; 
v_unused_5424_ = lean_ctor_get(v_impl_5312_, 3);
lean_dec(v_unused_5424_);
v_unused_5425_ = lean_ctor_get(v_impl_5312_, 0);
lean_dec(v_unused_5425_);
v___x_5402_ = v_impl_5312_;
v_isShared_5403_ = v_isSharedCheck_5423_;
goto v_resetjp_5401_;
}
else
{
lean_inc(v_r_5398_);
lean_inc(v_v_5400_);
lean_inc(v_k_5399_);
lean_dec(v_impl_5312_);
v___x_5402_ = lean_box(0);
v_isShared_5403_ = v_isSharedCheck_5423_;
goto v_resetjp_5401_;
}
v_resetjp_5401_:
{
lean_object* v_k_5404_; lean_object* v_v_5405_; lean_object* v___x_5407_; uint8_t v_isShared_5408_; uint8_t v_isSharedCheck_5419_; 
v_k_5404_ = lean_ctor_get(v_l_5397_, 1);
v_v_5405_ = lean_ctor_get(v_l_5397_, 2);
v_isSharedCheck_5419_ = !lean_is_exclusive(v_l_5397_);
if (v_isSharedCheck_5419_ == 0)
{
lean_object* v_unused_5420_; lean_object* v_unused_5421_; lean_object* v_unused_5422_; 
v_unused_5420_ = lean_ctor_get(v_l_5397_, 4);
lean_dec(v_unused_5420_);
v_unused_5421_ = lean_ctor_get(v_l_5397_, 3);
lean_dec(v_unused_5421_);
v_unused_5422_ = lean_ctor_get(v_l_5397_, 0);
lean_dec(v_unused_5422_);
v___x_5407_ = v_l_5397_;
v_isShared_5408_ = v_isSharedCheck_5419_;
goto v_resetjp_5406_;
}
else
{
lean_inc(v_v_5405_);
lean_inc(v_k_5404_);
lean_dec(v_l_5397_);
v___x_5407_ = lean_box(0);
v_isShared_5408_ = v_isSharedCheck_5419_;
goto v_resetjp_5406_;
}
v_resetjp_5406_:
{
lean_object* v___x_5409_; lean_object* v___x_5411_; 
v___x_5409_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5398_, 2);
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 4, v_r_5398_);
lean_ctor_set(v___x_5407_, 3, v_r_5398_);
lean_ctor_set(v___x_5407_, 2, v_v_5304_);
lean_ctor_set(v___x_5407_, 1, v_k_5303_);
lean_ctor_set(v___x_5407_, 0, v___x_5313_);
v___x_5411_ = v___x_5407_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v___x_5313_);
lean_ctor_set(v_reuseFailAlloc_5418_, 1, v_k_5303_);
lean_ctor_set(v_reuseFailAlloc_5418_, 2, v_v_5304_);
lean_ctor_set(v_reuseFailAlloc_5418_, 3, v_r_5398_);
lean_ctor_set(v_reuseFailAlloc_5418_, 4, v_r_5398_);
v___x_5411_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
lean_object* v___x_5413_; 
lean_inc(v_r_5398_);
if (v_isShared_5403_ == 0)
{
lean_ctor_set(v___x_5402_, 3, v_r_5398_);
lean_ctor_set(v___x_5402_, 0, v___x_5313_);
v___x_5413_ = v___x_5402_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v___x_5313_);
lean_ctor_set(v_reuseFailAlloc_5417_, 1, v_k_5399_);
lean_ctor_set(v_reuseFailAlloc_5417_, 2, v_v_5400_);
lean_ctor_set(v_reuseFailAlloc_5417_, 3, v_r_5398_);
lean_ctor_set(v_reuseFailAlloc_5417_, 4, v_r_5398_);
v___x_5413_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
lean_object* v___x_5415_; 
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 4, v___x_5413_);
lean_ctor_set(v___x_5308_, 3, v___x_5411_);
lean_ctor_set(v___x_5308_, 2, v_v_5405_);
lean_ctor_set(v___x_5308_, 1, v_k_5404_);
lean_ctor_set(v___x_5308_, 0, v___x_5409_);
v___x_5415_ = v___x_5308_;
goto v_reusejp_5414_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v___x_5409_);
lean_ctor_set(v_reuseFailAlloc_5416_, 1, v_k_5404_);
lean_ctor_set(v_reuseFailAlloc_5416_, 2, v_v_5405_);
lean_ctor_set(v_reuseFailAlloc_5416_, 3, v___x_5411_);
lean_ctor_set(v_reuseFailAlloc_5416_, 4, v___x_5413_);
v___x_5415_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5414_;
}
v_reusejp_5414_:
{
return v___x_5415_;
}
}
}
}
}
}
else
{
lean_object* v_r_5426_; 
v_r_5426_ = lean_ctor_get(v_impl_5312_, 4);
lean_inc(v_r_5426_);
if (lean_obj_tag(v_r_5426_) == 0)
{
lean_object* v_k_5427_; lean_object* v_v_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5439_; 
v_k_5427_ = lean_ctor_get(v_impl_5312_, 1);
v_v_5428_ = lean_ctor_get(v_impl_5312_, 2);
v_isSharedCheck_5439_ = !lean_is_exclusive(v_impl_5312_);
if (v_isSharedCheck_5439_ == 0)
{
lean_object* v_unused_5440_; lean_object* v_unused_5441_; lean_object* v_unused_5442_; 
v_unused_5440_ = lean_ctor_get(v_impl_5312_, 4);
lean_dec(v_unused_5440_);
v_unused_5441_ = lean_ctor_get(v_impl_5312_, 3);
lean_dec(v_unused_5441_);
v_unused_5442_ = lean_ctor_get(v_impl_5312_, 0);
lean_dec(v_unused_5442_);
v___x_5430_ = v_impl_5312_;
v_isShared_5431_ = v_isSharedCheck_5439_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_v_5428_);
lean_inc(v_k_5427_);
lean_dec(v_impl_5312_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5439_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v___x_5432_; lean_object* v___x_5434_; 
v___x_5432_ = lean_unsigned_to_nat(3u);
if (v_isShared_5431_ == 0)
{
lean_ctor_set(v___x_5430_, 4, v_l_5397_);
lean_ctor_set(v___x_5430_, 2, v_v_5304_);
lean_ctor_set(v___x_5430_, 1, v_k_5303_);
lean_ctor_set(v___x_5430_, 0, v___x_5313_);
v___x_5434_ = v___x_5430_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5438_; 
v_reuseFailAlloc_5438_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5438_, 0, v___x_5313_);
lean_ctor_set(v_reuseFailAlloc_5438_, 1, v_k_5303_);
lean_ctor_set(v_reuseFailAlloc_5438_, 2, v_v_5304_);
lean_ctor_set(v_reuseFailAlloc_5438_, 3, v_l_5397_);
lean_ctor_set(v_reuseFailAlloc_5438_, 4, v_l_5397_);
v___x_5434_ = v_reuseFailAlloc_5438_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
lean_object* v___x_5436_; 
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 4, v_r_5426_);
lean_ctor_set(v___x_5308_, 3, v___x_5434_);
lean_ctor_set(v___x_5308_, 2, v_v_5428_);
lean_ctor_set(v___x_5308_, 1, v_k_5427_);
lean_ctor_set(v___x_5308_, 0, v___x_5432_);
v___x_5436_ = v___x_5308_;
goto v_reusejp_5435_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___x_5432_);
lean_ctor_set(v_reuseFailAlloc_5437_, 1, v_k_5427_);
lean_ctor_set(v_reuseFailAlloc_5437_, 2, v_v_5428_);
lean_ctor_set(v_reuseFailAlloc_5437_, 3, v___x_5434_);
lean_ctor_set(v_reuseFailAlloc_5437_, 4, v_r_5426_);
v___x_5436_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5435_;
}
v_reusejp_5435_:
{
return v___x_5436_;
}
}
}
}
else
{
lean_object* v___x_5443_; lean_object* v___x_5445_; 
v___x_5443_ = lean_unsigned_to_nat(2u);
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 4, v_impl_5312_);
lean_ctor_set(v___x_5308_, 3, v_r_5426_);
lean_ctor_set(v___x_5308_, 0, v___x_5443_);
v___x_5445_ = v___x_5308_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v___x_5443_);
lean_ctor_set(v_reuseFailAlloc_5446_, 1, v_k_5303_);
lean_ctor_set(v_reuseFailAlloc_5446_, 2, v_v_5304_);
lean_ctor_set(v_reuseFailAlloc_5446_, 3, v_r_5426_);
lean_ctor_set(v_reuseFailAlloc_5446_, 4, v_impl_5312_);
v___x_5445_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
return v___x_5445_;
}
}
}
}
}
else
{
lean_object* v___x_5448_; 
lean_dec(v_v_5304_);
lean_dec(v_k_5303_);
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 2, v_v_5300_);
lean_ctor_set(v___x_5308_, 1, v_k_5299_);
v___x_5448_ = v___x_5308_;
goto v_reusejp_5447_;
}
else
{
lean_object* v_reuseFailAlloc_5449_; 
v_reuseFailAlloc_5449_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5449_, 0, v_size_5302_);
lean_ctor_set(v_reuseFailAlloc_5449_, 1, v_k_5299_);
lean_ctor_set(v_reuseFailAlloc_5449_, 2, v_v_5300_);
lean_ctor_set(v_reuseFailAlloc_5449_, 3, v_l_5305_);
lean_ctor_set(v_reuseFailAlloc_5449_, 4, v_r_5306_);
v___x_5448_ = v_reuseFailAlloc_5449_;
goto v_reusejp_5447_;
}
v_reusejp_5447_:
{
return v___x_5448_;
}
}
}
else
{
lean_object* v_impl_5450_; lean_object* v___x_5451_; 
lean_dec(v_size_5302_);
v_impl_5450_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5299_, v_v_5300_, v_l_5305_);
v___x_5451_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5306_) == 0)
{
lean_object* v_size_5452_; lean_object* v_size_5453_; lean_object* v_k_5454_; lean_object* v_v_5455_; lean_object* v_l_5456_; lean_object* v_r_5457_; lean_object* v___x_5458_; lean_object* v___x_5459_; uint8_t v___x_5460_; 
v_size_5452_ = lean_ctor_get(v_r_5306_, 0);
v_size_5453_ = lean_ctor_get(v_impl_5450_, 0);
lean_inc(v_size_5453_);
v_k_5454_ = lean_ctor_get(v_impl_5450_, 1);
lean_inc(v_k_5454_);
v_v_5455_ = lean_ctor_get(v_impl_5450_, 2);
lean_inc(v_v_5455_);
v_l_5456_ = lean_ctor_get(v_impl_5450_, 3);
lean_inc(v_l_5456_);
v_r_5457_ = lean_ctor_get(v_impl_5450_, 4);
lean_inc(v_r_5457_);
v___x_5458_ = lean_unsigned_to_nat(3u);
v___x_5459_ = lean_nat_mul(v___x_5458_, v_size_5452_);
v___x_5460_ = lean_nat_dec_lt(v___x_5459_, v_size_5453_);
lean_dec(v___x_5459_);
if (v___x_5460_ == 0)
{
lean_object* v___x_5461_; lean_object* v___x_5462_; lean_object* v___x_5464_; 
lean_dec(v_r_5457_);
lean_dec(v_l_5456_);
lean_dec(v_v_5455_);
lean_dec(v_k_5454_);
v___x_5461_ = lean_nat_add(v___x_5451_, v_size_5453_);
lean_dec(v_size_5453_);
v___x_5462_ = lean_nat_add(v___x_5461_, v_size_5452_);
lean_dec(v___x_5461_);
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 3, v_impl_5450_);
lean_ctor_set(v___x_5308_, 0, v___x_5462_);
v___x_5464_ = v___x_5308_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v___x_5462_);
lean_ctor_set(v_reuseFailAlloc_5465_, 1, v_k_5303_);
lean_ctor_set(v_reuseFailAlloc_5465_, 2, v_v_5304_);
lean_ctor_set(v_reuseFailAlloc_5465_, 3, v_impl_5450_);
lean_ctor_set(v_reuseFailAlloc_5465_, 4, v_r_5306_);
v___x_5464_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
return v___x_5464_;
}
}
else
{
lean_object* v___x_5467_; uint8_t v_isShared_5468_; uint8_t v_isSharedCheck_5531_; 
v_isSharedCheck_5531_ = !lean_is_exclusive(v_impl_5450_);
if (v_isSharedCheck_5531_ == 0)
{
lean_object* v_unused_5532_; lean_object* v_unused_5533_; lean_object* v_unused_5534_; lean_object* v_unused_5535_; lean_object* v_unused_5536_; 
v_unused_5532_ = lean_ctor_get(v_impl_5450_, 4);
lean_dec(v_unused_5532_);
v_unused_5533_ = lean_ctor_get(v_impl_5450_, 3);
lean_dec(v_unused_5533_);
v_unused_5534_ = lean_ctor_get(v_impl_5450_, 2);
lean_dec(v_unused_5534_);
v_unused_5535_ = lean_ctor_get(v_impl_5450_, 1);
lean_dec(v_unused_5535_);
v_unused_5536_ = lean_ctor_get(v_impl_5450_, 0);
lean_dec(v_unused_5536_);
v___x_5467_ = v_impl_5450_;
v_isShared_5468_ = v_isSharedCheck_5531_;
goto v_resetjp_5466_;
}
else
{
lean_dec(v_impl_5450_);
v___x_5467_ = lean_box(0);
v_isShared_5468_ = v_isSharedCheck_5531_;
goto v_resetjp_5466_;
}
v_resetjp_5466_:
{
lean_object* v_size_5469_; lean_object* v_size_5470_; lean_object* v_k_5471_; lean_object* v_v_5472_; lean_object* v_l_5473_; lean_object* v_r_5474_; lean_object* v___x_5475_; lean_object* v___x_5476_; uint8_t v___x_5477_; 
v_size_5469_ = lean_ctor_get(v_l_5456_, 0);
v_size_5470_ = lean_ctor_get(v_r_5457_, 0);
v_k_5471_ = lean_ctor_get(v_r_5457_, 1);
v_v_5472_ = lean_ctor_get(v_r_5457_, 2);
v_l_5473_ = lean_ctor_get(v_r_5457_, 3);
v_r_5474_ = lean_ctor_get(v_r_5457_, 4);
v___x_5475_ = lean_unsigned_to_nat(2u);
v___x_5476_ = lean_nat_mul(v___x_5475_, v_size_5469_);
v___x_5477_ = lean_nat_dec_lt(v_size_5470_, v___x_5476_);
lean_dec(v___x_5476_);
if (v___x_5477_ == 0)
{
lean_object* v___x_5479_; uint8_t v_isShared_5480_; uint8_t v_isSharedCheck_5506_; 
lean_inc(v_r_5474_);
lean_inc(v_l_5473_);
lean_inc(v_v_5472_);
lean_inc(v_k_5471_);
v_isSharedCheck_5506_ = !lean_is_exclusive(v_r_5457_);
if (v_isSharedCheck_5506_ == 0)
{
lean_object* v_unused_5507_; lean_object* v_unused_5508_; lean_object* v_unused_5509_; lean_object* v_unused_5510_; lean_object* v_unused_5511_; 
v_unused_5507_ = lean_ctor_get(v_r_5457_, 4);
lean_dec(v_unused_5507_);
v_unused_5508_ = lean_ctor_get(v_r_5457_, 3);
lean_dec(v_unused_5508_);
v_unused_5509_ = lean_ctor_get(v_r_5457_, 2);
lean_dec(v_unused_5509_);
v_unused_5510_ = lean_ctor_get(v_r_5457_, 1);
lean_dec(v_unused_5510_);
v_unused_5511_ = lean_ctor_get(v_r_5457_, 0);
lean_dec(v_unused_5511_);
v___x_5479_ = v_r_5457_;
v_isShared_5480_ = v_isSharedCheck_5506_;
goto v_resetjp_5478_;
}
else
{
lean_dec(v_r_5457_);
v___x_5479_ = lean_box(0);
v_isShared_5480_ = v_isSharedCheck_5506_;
goto v_resetjp_5478_;
}
v_resetjp_5478_:
{
lean_object* v___x_5481_; lean_object* v___x_5482_; lean_object* v___y_5484_; lean_object* v___y_5485_; lean_object* v___y_5486_; lean_object* v___x_5494_; lean_object* v___y_5496_; 
v___x_5481_ = lean_nat_add(v___x_5451_, v_size_5453_);
lean_dec(v_size_5453_);
v___x_5482_ = lean_nat_add(v___x_5481_, v_size_5452_);
lean_dec(v___x_5481_);
v___x_5494_ = lean_nat_add(v___x_5451_, v_size_5469_);
if (lean_obj_tag(v_l_5473_) == 0)
{
lean_object* v_size_5504_; 
v_size_5504_ = lean_ctor_get(v_l_5473_, 0);
lean_inc(v_size_5504_);
v___y_5496_ = v_size_5504_;
goto v___jp_5495_;
}
else
{
lean_object* v___x_5505_; 
v___x_5505_ = lean_unsigned_to_nat(0u);
v___y_5496_ = v___x_5505_;
goto v___jp_5495_;
}
v___jp_5483_:
{
lean_object* v___x_5487_; lean_object* v___x_5489_; 
v___x_5487_ = lean_nat_add(v___y_5484_, v___y_5486_);
lean_dec(v___y_5486_);
lean_dec(v___y_5484_);
if (v_isShared_5480_ == 0)
{
lean_ctor_set(v___x_5479_, 4, v_r_5306_);
lean_ctor_set(v___x_5479_, 3, v_r_5474_);
lean_ctor_set(v___x_5479_, 2, v_v_5304_);
lean_ctor_set(v___x_5479_, 1, v_k_5303_);
lean_ctor_set(v___x_5479_, 0, v___x_5487_);
v___x_5489_ = v___x_5479_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5487_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v_k_5303_);
lean_ctor_set(v_reuseFailAlloc_5493_, 2, v_v_5304_);
lean_ctor_set(v_reuseFailAlloc_5493_, 3, v_r_5474_);
lean_ctor_set(v_reuseFailAlloc_5493_, 4, v_r_5306_);
v___x_5489_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
lean_object* v___x_5491_; 
if (v_isShared_5468_ == 0)
{
lean_ctor_set(v___x_5467_, 4, v___x_5489_);
lean_ctor_set(v___x_5467_, 3, v___y_5485_);
lean_ctor_set(v___x_5467_, 2, v_v_5472_);
lean_ctor_set(v___x_5467_, 1, v_k_5471_);
lean_ctor_set(v___x_5467_, 0, v___x_5482_);
v___x_5491_ = v___x_5467_;
goto v_reusejp_5490_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v___x_5482_);
lean_ctor_set(v_reuseFailAlloc_5492_, 1, v_k_5471_);
lean_ctor_set(v_reuseFailAlloc_5492_, 2, v_v_5472_);
lean_ctor_set(v_reuseFailAlloc_5492_, 3, v___y_5485_);
lean_ctor_set(v_reuseFailAlloc_5492_, 4, v___x_5489_);
v___x_5491_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5490_;
}
v_reusejp_5490_:
{
return v___x_5491_;
}
}
}
v___jp_5495_:
{
lean_object* v___x_5497_; lean_object* v___x_5499_; 
v___x_5497_ = lean_nat_add(v___x_5494_, v___y_5496_);
lean_dec(v___y_5496_);
lean_dec(v___x_5494_);
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 4, v_l_5473_);
lean_ctor_set(v___x_5308_, 3, v_l_5456_);
lean_ctor_set(v___x_5308_, 2, v_v_5455_);
lean_ctor_set(v___x_5308_, 1, v_k_5454_);
lean_ctor_set(v___x_5308_, 0, v___x_5497_);
v___x_5499_ = v___x_5308_;
goto v_reusejp_5498_;
}
else
{
lean_object* v_reuseFailAlloc_5503_; 
v_reuseFailAlloc_5503_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5503_, 0, v___x_5497_);
lean_ctor_set(v_reuseFailAlloc_5503_, 1, v_k_5454_);
lean_ctor_set(v_reuseFailAlloc_5503_, 2, v_v_5455_);
lean_ctor_set(v_reuseFailAlloc_5503_, 3, v_l_5456_);
lean_ctor_set(v_reuseFailAlloc_5503_, 4, v_l_5473_);
v___x_5499_ = v_reuseFailAlloc_5503_;
goto v_reusejp_5498_;
}
v_reusejp_5498_:
{
lean_object* v___x_5500_; 
v___x_5500_ = lean_nat_add(v___x_5451_, v_size_5452_);
if (lean_obj_tag(v_r_5474_) == 0)
{
lean_object* v_size_5501_; 
v_size_5501_ = lean_ctor_get(v_r_5474_, 0);
lean_inc(v_size_5501_);
v___y_5484_ = v___x_5500_;
v___y_5485_ = v___x_5499_;
v___y_5486_ = v_size_5501_;
goto v___jp_5483_;
}
else
{
lean_object* v___x_5502_; 
v___x_5502_ = lean_unsigned_to_nat(0u);
v___y_5484_ = v___x_5500_;
v___y_5485_ = v___x_5499_;
v___y_5486_ = v___x_5502_;
goto v___jp_5483_;
}
}
}
}
}
else
{
lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5515_; lean_object* v___x_5517_; 
lean_del_object(v___x_5308_);
v___x_5512_ = lean_nat_add(v___x_5451_, v_size_5453_);
lean_dec(v_size_5453_);
v___x_5513_ = lean_nat_add(v___x_5512_, v_size_5452_);
lean_dec(v___x_5512_);
v___x_5514_ = lean_nat_add(v___x_5451_, v_size_5452_);
v___x_5515_ = lean_nat_add(v___x_5514_, v_size_5470_);
lean_dec(v___x_5514_);
lean_inc_ref(v_r_5306_);
if (v_isShared_5468_ == 0)
{
lean_ctor_set(v___x_5467_, 4, v_r_5306_);
lean_ctor_set(v___x_5467_, 3, v_r_5457_);
lean_ctor_set(v___x_5467_, 2, v_v_5304_);
lean_ctor_set(v___x_5467_, 1, v_k_5303_);
lean_ctor_set(v___x_5467_, 0, v___x_5515_);
v___x_5517_ = v___x_5467_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5530_; 
v_reuseFailAlloc_5530_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5530_, 0, v___x_5515_);
lean_ctor_set(v_reuseFailAlloc_5530_, 1, v_k_5303_);
lean_ctor_set(v_reuseFailAlloc_5530_, 2, v_v_5304_);
lean_ctor_set(v_reuseFailAlloc_5530_, 3, v_r_5457_);
lean_ctor_set(v_reuseFailAlloc_5530_, 4, v_r_5306_);
v___x_5517_ = v_reuseFailAlloc_5530_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
lean_object* v___x_5519_; uint8_t v_isShared_5520_; uint8_t v_isSharedCheck_5524_; 
v_isSharedCheck_5524_ = !lean_is_exclusive(v_r_5306_);
if (v_isSharedCheck_5524_ == 0)
{
lean_object* v_unused_5525_; lean_object* v_unused_5526_; lean_object* v_unused_5527_; lean_object* v_unused_5528_; lean_object* v_unused_5529_; 
v_unused_5525_ = lean_ctor_get(v_r_5306_, 4);
lean_dec(v_unused_5525_);
v_unused_5526_ = lean_ctor_get(v_r_5306_, 3);
lean_dec(v_unused_5526_);
v_unused_5527_ = lean_ctor_get(v_r_5306_, 2);
lean_dec(v_unused_5527_);
v_unused_5528_ = lean_ctor_get(v_r_5306_, 1);
lean_dec(v_unused_5528_);
v_unused_5529_ = lean_ctor_get(v_r_5306_, 0);
lean_dec(v_unused_5529_);
v___x_5519_ = v_r_5306_;
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
else
{
lean_dec(v_r_5306_);
v___x_5519_ = lean_box(0);
v_isShared_5520_ = v_isSharedCheck_5524_;
goto v_resetjp_5518_;
}
v_resetjp_5518_:
{
lean_object* v___x_5522_; 
if (v_isShared_5520_ == 0)
{
lean_ctor_set(v___x_5519_, 4, v___x_5517_);
lean_ctor_set(v___x_5519_, 3, v_l_5456_);
lean_ctor_set(v___x_5519_, 2, v_v_5455_);
lean_ctor_set(v___x_5519_, 1, v_k_5454_);
lean_ctor_set(v___x_5519_, 0, v___x_5513_);
v___x_5522_ = v___x_5519_;
goto v_reusejp_5521_;
}
else
{
lean_object* v_reuseFailAlloc_5523_; 
v_reuseFailAlloc_5523_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5523_, 0, v___x_5513_);
lean_ctor_set(v_reuseFailAlloc_5523_, 1, v_k_5454_);
lean_ctor_set(v_reuseFailAlloc_5523_, 2, v_v_5455_);
lean_ctor_set(v_reuseFailAlloc_5523_, 3, v_l_5456_);
lean_ctor_set(v_reuseFailAlloc_5523_, 4, v___x_5517_);
v___x_5522_ = v_reuseFailAlloc_5523_;
goto v_reusejp_5521_;
}
v_reusejp_5521_:
{
return v___x_5522_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5537_; 
v_l_5537_ = lean_ctor_get(v_impl_5450_, 3);
lean_inc(v_l_5537_);
if (lean_obj_tag(v_l_5537_) == 0)
{
lean_object* v_r_5538_; lean_object* v_k_5539_; lean_object* v_v_5540_; lean_object* v___x_5542_; uint8_t v_isShared_5543_; uint8_t v_isSharedCheck_5551_; 
v_r_5538_ = lean_ctor_get(v_impl_5450_, 4);
v_k_5539_ = lean_ctor_get(v_impl_5450_, 1);
v_v_5540_ = lean_ctor_get(v_impl_5450_, 2);
v_isSharedCheck_5551_ = !lean_is_exclusive(v_impl_5450_);
if (v_isSharedCheck_5551_ == 0)
{
lean_object* v_unused_5552_; lean_object* v_unused_5553_; 
v_unused_5552_ = lean_ctor_get(v_impl_5450_, 3);
lean_dec(v_unused_5552_);
v_unused_5553_ = lean_ctor_get(v_impl_5450_, 0);
lean_dec(v_unused_5553_);
v___x_5542_ = v_impl_5450_;
v_isShared_5543_ = v_isSharedCheck_5551_;
goto v_resetjp_5541_;
}
else
{
lean_inc(v_r_5538_);
lean_inc(v_v_5540_);
lean_inc(v_k_5539_);
lean_dec(v_impl_5450_);
v___x_5542_ = lean_box(0);
v_isShared_5543_ = v_isSharedCheck_5551_;
goto v_resetjp_5541_;
}
v_resetjp_5541_:
{
lean_object* v___x_5544_; lean_object* v___x_5546_; 
v___x_5544_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5538_);
if (v_isShared_5543_ == 0)
{
lean_ctor_set(v___x_5542_, 3, v_r_5538_);
lean_ctor_set(v___x_5542_, 2, v_v_5304_);
lean_ctor_set(v___x_5542_, 1, v_k_5303_);
lean_ctor_set(v___x_5542_, 0, v___x_5451_);
v___x_5546_ = v___x_5542_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5550_; 
v_reuseFailAlloc_5550_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5550_, 0, v___x_5451_);
lean_ctor_set(v_reuseFailAlloc_5550_, 1, v_k_5303_);
lean_ctor_set(v_reuseFailAlloc_5550_, 2, v_v_5304_);
lean_ctor_set(v_reuseFailAlloc_5550_, 3, v_r_5538_);
lean_ctor_set(v_reuseFailAlloc_5550_, 4, v_r_5538_);
v___x_5546_ = v_reuseFailAlloc_5550_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
lean_object* v___x_5548_; 
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 4, v___x_5546_);
lean_ctor_set(v___x_5308_, 3, v_l_5537_);
lean_ctor_set(v___x_5308_, 2, v_v_5540_);
lean_ctor_set(v___x_5308_, 1, v_k_5539_);
lean_ctor_set(v___x_5308_, 0, v___x_5544_);
v___x_5548_ = v___x_5308_;
goto v_reusejp_5547_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v___x_5544_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v_k_5539_);
lean_ctor_set(v_reuseFailAlloc_5549_, 2, v_v_5540_);
lean_ctor_set(v_reuseFailAlloc_5549_, 3, v_l_5537_);
lean_ctor_set(v_reuseFailAlloc_5549_, 4, v___x_5546_);
v___x_5548_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5547_;
}
v_reusejp_5547_:
{
return v___x_5548_;
}
}
}
}
else
{
lean_object* v_r_5554_; 
v_r_5554_ = lean_ctor_get(v_impl_5450_, 4);
lean_inc(v_r_5554_);
if (lean_obj_tag(v_r_5554_) == 0)
{
lean_object* v_k_5555_; lean_object* v_v_5556_; lean_object* v___x_5558_; uint8_t v_isShared_5559_; uint8_t v_isSharedCheck_5579_; 
v_k_5555_ = lean_ctor_get(v_impl_5450_, 1);
v_v_5556_ = lean_ctor_get(v_impl_5450_, 2);
v_isSharedCheck_5579_ = !lean_is_exclusive(v_impl_5450_);
if (v_isSharedCheck_5579_ == 0)
{
lean_object* v_unused_5580_; lean_object* v_unused_5581_; lean_object* v_unused_5582_; 
v_unused_5580_ = lean_ctor_get(v_impl_5450_, 4);
lean_dec(v_unused_5580_);
v_unused_5581_ = lean_ctor_get(v_impl_5450_, 3);
lean_dec(v_unused_5581_);
v_unused_5582_ = lean_ctor_get(v_impl_5450_, 0);
lean_dec(v_unused_5582_);
v___x_5558_ = v_impl_5450_;
v_isShared_5559_ = v_isSharedCheck_5579_;
goto v_resetjp_5557_;
}
else
{
lean_inc(v_v_5556_);
lean_inc(v_k_5555_);
lean_dec(v_impl_5450_);
v___x_5558_ = lean_box(0);
v_isShared_5559_ = v_isSharedCheck_5579_;
goto v_resetjp_5557_;
}
v_resetjp_5557_:
{
lean_object* v_k_5560_; lean_object* v_v_5561_; lean_object* v___x_5563_; uint8_t v_isShared_5564_; uint8_t v_isSharedCheck_5575_; 
v_k_5560_ = lean_ctor_get(v_r_5554_, 1);
v_v_5561_ = lean_ctor_get(v_r_5554_, 2);
v_isSharedCheck_5575_ = !lean_is_exclusive(v_r_5554_);
if (v_isSharedCheck_5575_ == 0)
{
lean_object* v_unused_5576_; lean_object* v_unused_5577_; lean_object* v_unused_5578_; 
v_unused_5576_ = lean_ctor_get(v_r_5554_, 4);
lean_dec(v_unused_5576_);
v_unused_5577_ = lean_ctor_get(v_r_5554_, 3);
lean_dec(v_unused_5577_);
v_unused_5578_ = lean_ctor_get(v_r_5554_, 0);
lean_dec(v_unused_5578_);
v___x_5563_ = v_r_5554_;
v_isShared_5564_ = v_isSharedCheck_5575_;
goto v_resetjp_5562_;
}
else
{
lean_inc(v_v_5561_);
lean_inc(v_k_5560_);
lean_dec(v_r_5554_);
v___x_5563_ = lean_box(0);
v_isShared_5564_ = v_isSharedCheck_5575_;
goto v_resetjp_5562_;
}
v_resetjp_5562_:
{
lean_object* v___x_5565_; lean_object* v___x_5567_; 
v___x_5565_ = lean_unsigned_to_nat(3u);
if (v_isShared_5564_ == 0)
{
lean_ctor_set(v___x_5563_, 4, v_l_5537_);
lean_ctor_set(v___x_5563_, 3, v_l_5537_);
lean_ctor_set(v___x_5563_, 2, v_v_5556_);
lean_ctor_set(v___x_5563_, 1, v_k_5555_);
lean_ctor_set(v___x_5563_, 0, v___x_5451_);
v___x_5567_ = v___x_5563_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5574_; 
v_reuseFailAlloc_5574_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5574_, 0, v___x_5451_);
lean_ctor_set(v_reuseFailAlloc_5574_, 1, v_k_5555_);
lean_ctor_set(v_reuseFailAlloc_5574_, 2, v_v_5556_);
lean_ctor_set(v_reuseFailAlloc_5574_, 3, v_l_5537_);
lean_ctor_set(v_reuseFailAlloc_5574_, 4, v_l_5537_);
v___x_5567_ = v_reuseFailAlloc_5574_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
lean_object* v___x_5569_; 
if (v_isShared_5559_ == 0)
{
lean_ctor_set(v___x_5558_, 4, v_l_5537_);
lean_ctor_set(v___x_5558_, 2, v_v_5304_);
lean_ctor_set(v___x_5558_, 1, v_k_5303_);
lean_ctor_set(v___x_5558_, 0, v___x_5451_);
v___x_5569_ = v___x_5558_;
goto v_reusejp_5568_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5451_);
lean_ctor_set(v_reuseFailAlloc_5573_, 1, v_k_5303_);
lean_ctor_set(v_reuseFailAlloc_5573_, 2, v_v_5304_);
lean_ctor_set(v_reuseFailAlloc_5573_, 3, v_l_5537_);
lean_ctor_set(v_reuseFailAlloc_5573_, 4, v_l_5537_);
v___x_5569_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5568_;
}
v_reusejp_5568_:
{
lean_object* v___x_5571_; 
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 4, v___x_5569_);
lean_ctor_set(v___x_5308_, 3, v___x_5567_);
lean_ctor_set(v___x_5308_, 2, v_v_5561_);
lean_ctor_set(v___x_5308_, 1, v_k_5560_);
lean_ctor_set(v___x_5308_, 0, v___x_5565_);
v___x_5571_ = v___x_5308_;
goto v_reusejp_5570_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v___x_5565_);
lean_ctor_set(v_reuseFailAlloc_5572_, 1, v_k_5560_);
lean_ctor_set(v_reuseFailAlloc_5572_, 2, v_v_5561_);
lean_ctor_set(v_reuseFailAlloc_5572_, 3, v___x_5567_);
lean_ctor_set(v_reuseFailAlloc_5572_, 4, v___x_5569_);
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
}
else
{
lean_object* v___x_5583_; lean_object* v___x_5585_; 
v___x_5583_ = lean_unsigned_to_nat(2u);
if (v_isShared_5309_ == 0)
{
lean_ctor_set(v___x_5308_, 4, v_r_5554_);
lean_ctor_set(v___x_5308_, 3, v_impl_5450_);
lean_ctor_set(v___x_5308_, 0, v___x_5583_);
v___x_5585_ = v___x_5308_;
goto v_reusejp_5584_;
}
else
{
lean_object* v_reuseFailAlloc_5586_; 
v_reuseFailAlloc_5586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5586_, 0, v___x_5583_);
lean_ctor_set(v_reuseFailAlloc_5586_, 1, v_k_5303_);
lean_ctor_set(v_reuseFailAlloc_5586_, 2, v_v_5304_);
lean_ctor_set(v_reuseFailAlloc_5586_, 3, v_impl_5450_);
lean_ctor_set(v_reuseFailAlloc_5586_, 4, v_r_5554_);
v___x_5585_ = v_reuseFailAlloc_5586_;
goto v_reusejp_5584_;
}
v_reusejp_5584_:
{
return v___x_5585_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5588_; lean_object* v___x_5589_; 
v___x_5588_ = lean_unsigned_to_nat(1u);
v___x_5589_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5589_, 0, v___x_5588_);
lean_ctor_set(v___x_5589_, 1, v_k_5299_);
lean_ctor_set(v___x_5589_, 2, v_v_5300_);
lean_ctor_set(v___x_5589_, 3, v_t_5301_);
lean_ctor_set(v___x_5589_, 4, v_t_5301_);
return v___x_5589_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5590_, lean_object* v_t_5591_){
_start:
{
if (lean_obj_tag(v_t_5591_) == 0)
{
lean_object* v_k_5592_; lean_object* v_l_5593_; lean_object* v_r_5594_; uint8_t v___x_5595_; 
v_k_5592_ = lean_ctor_get(v_t_5591_, 1);
v_l_5593_ = lean_ctor_get(v_t_5591_, 3);
v_r_5594_ = lean_ctor_get(v_t_5591_, 4);
v___x_5595_ = lean_nat_dec_lt(v_k_5592_, v_k_5590_);
if (v___x_5595_ == 0)
{
uint8_t v___x_5596_; 
v___x_5596_ = lean_nat_dec_eq(v_k_5592_, v_k_5590_);
if (v___x_5596_ == 0)
{
v_t_5591_ = v_r_5594_;
goto _start;
}
else
{
return v___x_5596_;
}
}
else
{
v_t_5591_ = v_l_5593_;
goto _start;
}
}
else
{
uint8_t v___x_5599_; 
v___x_5599_ = 0;
return v___x_5599_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5600_, lean_object* v_t_5601_){
_start:
{
uint8_t v_res_5602_; lean_object* v_r_5603_; 
v_res_5602_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5600_, v_t_5601_);
lean_dec(v_t_5601_);
lean_dec(v_k_5600_);
v_r_5603_ = lean_box(v_res_5602_);
return v_r_5603_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5604_, lean_object* v_e_5605_){
_start:
{
lean_object* v_defaultInstances_5606_; lean_object* v_priorities_5607_; lean_object* v___x_5609_; uint8_t v_isShared_5610_; uint8_t v_isSharedCheck_5634_; 
v_defaultInstances_5606_ = lean_ctor_get(v_d_5604_, 0);
v_priorities_5607_ = lean_ctor_get(v_d_5604_, 1);
v_isSharedCheck_5634_ = !lean_is_exclusive(v_d_5604_);
if (v_isSharedCheck_5634_ == 0)
{
v___x_5609_ = v_d_5604_;
v_isShared_5610_ = v_isSharedCheck_5634_;
goto v_resetjp_5608_;
}
else
{
lean_inc(v_priorities_5607_);
lean_inc(v_defaultInstances_5606_);
lean_dec(v_d_5604_);
v___x_5609_ = lean_box(0);
v_isShared_5610_ = v_isSharedCheck_5634_;
goto v_resetjp_5608_;
}
v_resetjp_5608_:
{
lean_object* v_className_5611_; lean_object* v_instanceName_5612_; lean_object* v_priority_5613_; lean_object* v___y_5615_; uint8_t v___x_5631_; 
v_className_5611_ = lean_ctor_get(v_e_5605_, 0);
lean_inc(v_className_5611_);
v_instanceName_5612_ = lean_ctor_get(v_e_5605_, 1);
lean_inc(v_instanceName_5612_);
v_priority_5613_ = lean_ctor_get(v_e_5605_, 2);
lean_inc(v_priority_5613_);
lean_dec_ref(v_e_5605_);
v___x_5631_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5613_, v_priorities_5607_);
if (v___x_5631_ == 0)
{
lean_object* v___x_5632_; lean_object* v___x_5633_; 
v___x_5632_ = lean_box(0);
lean_inc(v_priority_5613_);
v___x_5633_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5613_, v___x_5632_, v_priorities_5607_);
v___y_5615_ = v___x_5633_;
goto v___jp_5614_;
}
else
{
v___y_5615_ = v_priorities_5607_;
goto v___jp_5614_;
}
v___jp_5614_:
{
lean_object* v___x_5616_; 
v___x_5616_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5606_, v_className_5611_);
if (lean_obj_tag(v___x_5616_) == 0)
{
lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5620_; lean_object* v___x_5622_; 
v___x_5617_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5617_, 0, v_instanceName_5612_);
lean_ctor_set(v___x_5617_, 1, v_priority_5613_);
v___x_5618_ = lean_box(0);
v___x_5619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5619_, 0, v___x_5617_);
lean_ctor_set(v___x_5619_, 1, v___x_5618_);
v___x_5620_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5611_, v___x_5619_, v_defaultInstances_5606_);
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 1, v___y_5615_);
lean_ctor_set(v___x_5609_, 0, v___x_5620_);
v___x_5622_ = v___x_5609_;
goto v_reusejp_5621_;
}
else
{
lean_object* v_reuseFailAlloc_5623_; 
v_reuseFailAlloc_5623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5623_, 0, v___x_5620_);
lean_ctor_set(v_reuseFailAlloc_5623_, 1, v___y_5615_);
v___x_5622_ = v_reuseFailAlloc_5623_;
goto v_reusejp_5621_;
}
v_reusejp_5621_:
{
return v___x_5622_;
}
}
else
{
lean_object* v_val_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5627_; lean_object* v___x_5629_; 
v_val_5624_ = lean_ctor_get(v___x_5616_, 0);
lean_inc(v_val_5624_);
lean_dec_ref_known(v___x_5616_, 1);
v___x_5625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5625_, 0, v_instanceName_5612_);
lean_ctor_set(v___x_5625_, 1, v_priority_5613_);
v___x_5626_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5626_, 0, v___x_5625_);
lean_ctor_set(v___x_5626_, 1, v_val_5624_);
v___x_5627_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5611_, v___x_5626_, v_defaultInstances_5606_);
if (v_isShared_5610_ == 0)
{
lean_ctor_set(v___x_5609_, 1, v___y_5615_);
lean_ctor_set(v___x_5609_, 0, v___x_5627_);
v___x_5629_ = v___x_5609_;
goto v_reusejp_5628_;
}
else
{
lean_object* v_reuseFailAlloc_5630_; 
v_reuseFailAlloc_5630_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5630_, 0, v___x_5627_);
lean_ctor_set(v_reuseFailAlloc_5630_, 1, v___y_5615_);
v___x_5629_ = v_reuseFailAlloc_5630_;
goto v_reusejp_5628_;
}
v_reusejp_5628_:
{
return v___x_5629_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5635_, lean_object* v_k_5636_, lean_object* v_t_5637_){
_start:
{
uint8_t v___x_5638_; 
v___x_5638_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5636_, v_t_5637_);
return v___x_5638_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5639_, lean_object* v_k_5640_, lean_object* v_t_5641_){
_start:
{
uint8_t v_res_5642_; lean_object* v_r_5643_; 
v_res_5642_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5639_, v_k_5640_, v_t_5641_);
lean_dec(v_t_5641_);
lean_dec(v_k_5640_);
v_r_5643_ = lean_box(v_res_5642_);
return v_r_5643_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5644_, lean_object* v_k_5645_, lean_object* v_v_5646_, lean_object* v_t_5647_, lean_object* v_hl_5648_){
_start:
{
lean_object* v___x_5649_; 
v___x_5649_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5645_, v_v_5646_, v_t_5647_);
return v___x_5649_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object* v_env_5650_, lean_object* v_as_5651_, size_t v_i_5652_, size_t v_stop_5653_, lean_object* v_b_5654_){
_start:
{
lean_object* v___y_5656_; uint8_t v___x_5660_; 
v___x_5660_ = lean_usize_dec_eq(v_i_5652_, v_stop_5653_);
if (v___x_5660_ == 0)
{
lean_object* v___x_5661_; lean_object* v_instanceName_5662_; uint8_t v___x_5663_; lean_object* v___x_5664_; uint8_t v___x_5665_; 
v___x_5661_ = lean_array_uget_borrowed(v_as_5651_, v_i_5652_);
v_instanceName_5662_ = lean_ctor_get(v___x_5661_, 1);
v___x_5663_ = 1;
lean_inc_ref(v_env_5650_);
v___x_5664_ = l_Lean_Environment_setExporting(v_env_5650_, v___x_5663_);
lean_inc(v_instanceName_5662_);
v___x_5665_ = l_Lean_Environment_contains(v___x_5664_, v_instanceName_5662_, v___x_5660_);
if (v___x_5665_ == 0)
{
v___y_5656_ = v_b_5654_;
goto v___jp_5655_;
}
else
{
lean_object* v___x_5666_; 
lean_inc(v___x_5661_);
v___x_5666_ = lean_array_push(v_b_5654_, v___x_5661_);
v___y_5656_ = v___x_5666_;
goto v___jp_5655_;
}
}
else
{
lean_dec_ref(v_env_5650_);
return v_b_5654_;
}
v___jp_5655_:
{
size_t v___x_5657_; size_t v___x_5658_; 
v___x_5657_ = ((size_t)1ULL);
v___x_5658_ = lean_usize_add(v_i_5652_, v___x_5657_);
v_i_5652_ = v___x_5658_;
v_b_5654_ = v___y_5656_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_5667_, lean_object* v_as_5668_, lean_object* v_i_5669_, lean_object* v_stop_5670_, lean_object* v_b_5671_){
_start:
{
size_t v_i_boxed_5672_; size_t v_stop_boxed_5673_; lean_object* v_res_5674_; 
v_i_boxed_5672_ = lean_unbox_usize(v_i_5669_);
lean_dec(v_i_5669_);
v_stop_boxed_5673_ = lean_unbox_usize(v_stop_5670_);
lean_dec(v_stop_5670_);
v_res_5674_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5667_, v_as_5668_, v_i_boxed_5672_, v_stop_boxed_5673_, v_b_5671_);
lean_dec_ref(v_as_5668_);
return v_res_5674_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_env_5677_, lean_object* v_x_5678_, lean_object* v_entries_5679_){
_start:
{
lean_object* v_all_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; lean_object* v___x_5683_; uint8_t v___x_5684_; 
v_all_5680_ = lean_array_mk(v_entries_5679_);
v___x_5681_ = lean_unsigned_to_nat(0u);
v___x_5682_ = lean_array_get_size(v_all_5680_);
v___x_5683_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5684_ = lean_nat_dec_lt(v___x_5681_, v___x_5682_);
if (v___x_5684_ == 0)
{
lean_object* v___x_5685_; 
lean_dec_ref(v_env_5677_);
v___x_5685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5685_, 0, v___x_5683_);
lean_ctor_set(v___x_5685_, 1, v___x_5683_);
lean_ctor_set(v___x_5685_, 2, v_all_5680_);
return v___x_5685_;
}
else
{
uint8_t v___x_5686_; 
v___x_5686_ = lean_nat_dec_le(v___x_5682_, v___x_5682_);
if (v___x_5686_ == 0)
{
if (v___x_5684_ == 0)
{
lean_object* v___x_5687_; 
lean_dec_ref(v_env_5677_);
v___x_5687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5687_, 0, v___x_5683_);
lean_ctor_set(v___x_5687_, 1, v___x_5683_);
lean_ctor_set(v___x_5687_, 2, v_all_5680_);
return v___x_5687_;
}
else
{
size_t v___x_5688_; size_t v___x_5689_; lean_object* v___x_5690_; lean_object* v___x_5691_; 
v___x_5688_ = ((size_t)0ULL);
v___x_5689_ = lean_usize_of_nat(v___x_5682_);
v___x_5690_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5677_, v_all_5680_, v___x_5688_, v___x_5689_, v___x_5683_);
lean_inc_ref(v___x_5690_);
v___x_5691_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5691_, 0, v___x_5690_);
lean_ctor_set(v___x_5691_, 1, v___x_5690_);
lean_ctor_set(v___x_5691_, 2, v_all_5680_);
return v___x_5691_;
}
}
else
{
size_t v___x_5692_; size_t v___x_5693_; lean_object* v___x_5694_; lean_object* v___x_5695_; 
v___x_5692_ = ((size_t)0ULL);
v___x_5693_ = lean_usize_of_nat(v___x_5682_);
v___x_5694_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5677_, v_all_5680_, v___x_5692_, v___x_5693_, v___x_5683_);
lean_inc_ref(v___x_5694_);
v___x_5695_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5695_, 0, v___x_5694_);
lean_ctor_set(v___x_5695_, 1, v___x_5694_);
lean_ctor_set(v___x_5695_, 2, v_all_5680_);
return v___x_5695_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5696_, lean_object* v_x_5697_, lean_object* v_entries_5698_){
_start:
{
lean_object* v_res_5699_; 
v_res_5699_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5696_, v_x_5697_, v_entries_5698_);
lean_dec_ref(v_x_5697_);
return v_res_5699_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5700_){
_start:
{
lean_object* v___x_5701_; 
v___x_5701_ = lean_array_mk(v_es_5700_);
return v___x_5701_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5702_, size_t v_i_5703_, size_t v_stop_5704_, lean_object* v_b_5705_){
_start:
{
uint8_t v___x_5706_; 
v___x_5706_ = lean_usize_dec_eq(v_i_5703_, v_stop_5704_);
if (v___x_5706_ == 0)
{
lean_object* v___x_5707_; lean_object* v___x_5708_; size_t v___x_5709_; size_t v___x_5710_; 
v___x_5707_ = lean_array_uget_borrowed(v_as_5702_, v_i_5703_);
lean_inc(v___x_5707_);
v___x_5708_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5705_, v___x_5707_);
v___x_5709_ = ((size_t)1ULL);
v___x_5710_ = lean_usize_add(v_i_5703_, v___x_5709_);
v_i_5703_ = v___x_5710_;
v_b_5705_ = v___x_5708_;
goto _start;
}
else
{
return v_b_5705_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5712_, lean_object* v_i_5713_, lean_object* v_stop_5714_, lean_object* v_b_5715_){
_start:
{
size_t v_i_boxed_5716_; size_t v_stop_boxed_5717_; lean_object* v_res_5718_; 
v_i_boxed_5716_ = lean_unbox_usize(v_i_5713_);
lean_dec(v_i_5713_);
v_stop_boxed_5717_ = lean_unbox_usize(v_stop_5714_);
lean_dec(v_stop_5714_);
v_res_5718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5712_, v_i_boxed_5716_, v_stop_boxed_5717_, v_b_5715_);
lean_dec_ref(v_as_5712_);
return v_res_5718_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5719_, size_t v_i_5720_, size_t v_stop_5721_, lean_object* v_b_5722_){
_start:
{
lean_object* v___y_5724_; uint8_t v___x_5728_; 
v___x_5728_ = lean_usize_dec_eq(v_i_5720_, v_stop_5721_);
if (v___x_5728_ == 0)
{
lean_object* v___x_5729_; lean_object* v___x_5730_; lean_object* v___x_5731_; uint8_t v___x_5732_; 
v___x_5729_ = lean_array_uget_borrowed(v_as_5719_, v_i_5720_);
v___x_5730_ = lean_unsigned_to_nat(0u);
v___x_5731_ = lean_array_get_size(v___x_5729_);
v___x_5732_ = lean_nat_dec_lt(v___x_5730_, v___x_5731_);
if (v___x_5732_ == 0)
{
v___y_5724_ = v_b_5722_;
goto v___jp_5723_;
}
else
{
uint8_t v___x_5733_; 
v___x_5733_ = lean_nat_dec_le(v___x_5731_, v___x_5731_);
if (v___x_5733_ == 0)
{
if (v___x_5732_ == 0)
{
v___y_5724_ = v_b_5722_;
goto v___jp_5723_;
}
else
{
size_t v___x_5734_; size_t v___x_5735_; lean_object* v___x_5736_; 
v___x_5734_ = ((size_t)0ULL);
v___x_5735_ = lean_usize_of_nat(v___x_5731_);
v___x_5736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5729_, v___x_5734_, v___x_5735_, v_b_5722_);
v___y_5724_ = v___x_5736_;
goto v___jp_5723_;
}
}
else
{
size_t v___x_5737_; size_t v___x_5738_; lean_object* v___x_5739_; 
v___x_5737_ = ((size_t)0ULL);
v___x_5738_ = lean_usize_of_nat(v___x_5731_);
v___x_5739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5729_, v___x_5737_, v___x_5738_, v_b_5722_);
v___y_5724_ = v___x_5739_;
goto v___jp_5723_;
}
}
}
else
{
return v_b_5722_;
}
v___jp_5723_:
{
size_t v___x_5725_; size_t v___x_5726_; 
v___x_5725_ = ((size_t)1ULL);
v___x_5726_ = lean_usize_add(v_i_5720_, v___x_5725_);
v_i_5720_ = v___x_5726_;
v_b_5722_ = v___y_5724_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5740_, lean_object* v_i_5741_, lean_object* v_stop_5742_, lean_object* v_b_5743_){
_start:
{
size_t v_i_boxed_5744_; size_t v_stop_boxed_5745_; lean_object* v_res_5746_; 
v_i_boxed_5744_ = lean_unbox_usize(v_i_5741_);
lean_dec(v_i_5741_);
v_stop_boxed_5745_ = lean_unbox_usize(v_stop_5742_);
lean_dec(v_stop_5742_);
v_res_5746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5740_, v_i_boxed_5744_, v_stop_boxed_5745_, v_b_5743_);
lean_dec_ref(v_as_5740_);
return v_res_5746_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_5747_, lean_object* v_as_5748_){
_start:
{
lean_object* v___x_5749_; lean_object* v___x_5750_; uint8_t v___x_5751_; 
v___x_5749_ = lean_unsigned_to_nat(0u);
v___x_5750_ = lean_array_get_size(v_as_5748_);
v___x_5751_ = lean_nat_dec_lt(v___x_5749_, v___x_5750_);
if (v___x_5751_ == 0)
{
return v_initState_5747_;
}
else
{
uint8_t v___x_5752_; 
v___x_5752_ = lean_nat_dec_le(v___x_5750_, v___x_5750_);
if (v___x_5752_ == 0)
{
if (v___x_5751_ == 0)
{
return v_initState_5747_;
}
else
{
size_t v___x_5753_; size_t v___x_5754_; lean_object* v___x_5755_; 
v___x_5753_ = ((size_t)0ULL);
v___x_5754_ = lean_usize_of_nat(v___x_5750_);
v___x_5755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5748_, v___x_5753_, v___x_5754_, v_initState_5747_);
return v___x_5755_;
}
}
else
{
size_t v___x_5756_; size_t v___x_5757_; lean_object* v___x_5758_; 
v___x_5756_ = ((size_t)0ULL);
v___x_5757_ = lean_usize_of_nat(v___x_5750_);
v___x_5758_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5748_, v___x_5756_, v___x_5757_, v_initState_5747_);
return v___x_5758_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_5759_, lean_object* v_as_5760_){
_start:
{
lean_object* v_res_5761_; 
v_res_5761_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_5759_, v_as_5760_);
lean_dec_ref(v_as_5760_);
return v_res_5761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5762_){
_start:
{
lean_object* v___x_5763_; lean_object* v___x_5764_; 
v___x_5763_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5764_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_5763_, v_es_5762_);
return v___x_5764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_5765_){
_start:
{
lean_object* v_res_5766_; 
v_res_5766_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_5765_);
lean_dec_ref(v_es_5765_);
return v_res_5766_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5787_; lean_object* v___x_5788_; 
v___x_5787_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5788_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5787_);
return v___x_5788_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_5789_){
_start:
{
lean_object* v_res_5790_; 
v_res_5790_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_5790_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5791_, lean_object* v___y_5792_, lean_object* v___y_5793_){
_start:
{
lean_object* v___x_5795_; lean_object* v_nextMacroScope_5796_; lean_object* v_ngen_5797_; lean_object* v_auxDeclNGen_5798_; lean_object* v_traceState_5799_; lean_object* v_messages_5800_; lean_object* v_infoState_5801_; lean_object* v_snapshotTasks_5802_; lean_object* v___x_5804_; uint8_t v_isShared_5805_; uint8_t v_isSharedCheck_5828_; 
v___x_5795_ = lean_st_ref_take(v___y_5793_);
v_nextMacroScope_5796_ = lean_ctor_get(v___x_5795_, 1);
v_ngen_5797_ = lean_ctor_get(v___x_5795_, 2);
v_auxDeclNGen_5798_ = lean_ctor_get(v___x_5795_, 3);
v_traceState_5799_ = lean_ctor_get(v___x_5795_, 4);
v_messages_5800_ = lean_ctor_get(v___x_5795_, 6);
v_infoState_5801_ = lean_ctor_get(v___x_5795_, 7);
v_snapshotTasks_5802_ = lean_ctor_get(v___x_5795_, 8);
v_isSharedCheck_5828_ = !lean_is_exclusive(v___x_5795_);
if (v_isSharedCheck_5828_ == 0)
{
lean_object* v_unused_5829_; lean_object* v_unused_5830_; 
v_unused_5829_ = lean_ctor_get(v___x_5795_, 5);
lean_dec(v_unused_5829_);
v_unused_5830_ = lean_ctor_get(v___x_5795_, 0);
lean_dec(v_unused_5830_);
v___x_5804_ = v___x_5795_;
v_isShared_5805_ = v_isSharedCheck_5828_;
goto v_resetjp_5803_;
}
else
{
lean_inc(v_snapshotTasks_5802_);
lean_inc(v_infoState_5801_);
lean_inc(v_messages_5800_);
lean_inc(v_traceState_5799_);
lean_inc(v_auxDeclNGen_5798_);
lean_inc(v_ngen_5797_);
lean_inc(v_nextMacroScope_5796_);
lean_dec(v___x_5795_);
v___x_5804_ = lean_box(0);
v_isShared_5805_ = v_isSharedCheck_5828_;
goto v_resetjp_5803_;
}
v_resetjp_5803_:
{
lean_object* v___x_5806_; lean_object* v___x_5808_; 
v___x_5806_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5805_ == 0)
{
lean_ctor_set(v___x_5804_, 5, v___x_5806_);
lean_ctor_set(v___x_5804_, 0, v_env_5791_);
v___x_5808_ = v___x_5804_;
goto v_reusejp_5807_;
}
else
{
lean_object* v_reuseFailAlloc_5827_; 
v_reuseFailAlloc_5827_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5827_, 0, v_env_5791_);
lean_ctor_set(v_reuseFailAlloc_5827_, 1, v_nextMacroScope_5796_);
lean_ctor_set(v_reuseFailAlloc_5827_, 2, v_ngen_5797_);
lean_ctor_set(v_reuseFailAlloc_5827_, 3, v_auxDeclNGen_5798_);
lean_ctor_set(v_reuseFailAlloc_5827_, 4, v_traceState_5799_);
lean_ctor_set(v_reuseFailAlloc_5827_, 5, v___x_5806_);
lean_ctor_set(v_reuseFailAlloc_5827_, 6, v_messages_5800_);
lean_ctor_set(v_reuseFailAlloc_5827_, 7, v_infoState_5801_);
lean_ctor_set(v_reuseFailAlloc_5827_, 8, v_snapshotTasks_5802_);
v___x_5808_ = v_reuseFailAlloc_5827_;
goto v_reusejp_5807_;
}
v_reusejp_5807_:
{
lean_object* v___x_5809_; lean_object* v___x_5810_; lean_object* v_mctx_5811_; lean_object* v_zetaDeltaFVarIds_5812_; lean_object* v_postponed_5813_; lean_object* v_diag_5814_; lean_object* v___x_5816_; uint8_t v_isShared_5817_; uint8_t v_isSharedCheck_5825_; 
v___x_5809_ = lean_st_ref_put(v___y_5793_, v___x_5808_);
v___x_5810_ = lean_st_ref_take(v___y_5792_);
v_mctx_5811_ = lean_ctor_get(v___x_5810_, 0);
v_zetaDeltaFVarIds_5812_ = lean_ctor_get(v___x_5810_, 2);
v_postponed_5813_ = lean_ctor_get(v___x_5810_, 3);
v_diag_5814_ = lean_ctor_get(v___x_5810_, 4);
v_isSharedCheck_5825_ = !lean_is_exclusive(v___x_5810_);
if (v_isSharedCheck_5825_ == 0)
{
lean_object* v_unused_5826_; 
v_unused_5826_ = lean_ctor_get(v___x_5810_, 1);
lean_dec(v_unused_5826_);
v___x_5816_ = v___x_5810_;
v_isShared_5817_ = v_isSharedCheck_5825_;
goto v_resetjp_5815_;
}
else
{
lean_inc(v_diag_5814_);
lean_inc(v_postponed_5813_);
lean_inc(v_zetaDeltaFVarIds_5812_);
lean_inc(v_mctx_5811_);
lean_dec(v___x_5810_);
v___x_5816_ = lean_box(0);
v_isShared_5817_ = v_isSharedCheck_5825_;
goto v_resetjp_5815_;
}
v_resetjp_5815_:
{
lean_object* v___x_5818_; lean_object* v___x_5820_; 
v___x_5818_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5817_ == 0)
{
lean_ctor_set(v___x_5816_, 1, v___x_5818_);
v___x_5820_ = v___x_5816_;
goto v_reusejp_5819_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v_mctx_5811_);
lean_ctor_set(v_reuseFailAlloc_5824_, 1, v___x_5818_);
lean_ctor_set(v_reuseFailAlloc_5824_, 2, v_zetaDeltaFVarIds_5812_);
lean_ctor_set(v_reuseFailAlloc_5824_, 3, v_postponed_5813_);
lean_ctor_set(v_reuseFailAlloc_5824_, 4, v_diag_5814_);
v___x_5820_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5819_;
}
v_reusejp_5819_:
{
lean_object* v___x_5821_; lean_object* v___x_5822_; lean_object* v___x_5823_; 
v___x_5821_ = lean_st_ref_put(v___y_5792_, v___x_5820_);
v___x_5822_ = lean_box(0);
v___x_5823_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5823_, 0, v___x_5822_);
return v___x_5823_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_, lean_object* v___y_5834_){
_start:
{
lean_object* v_res_5835_; 
v_res_5835_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5831_, v___y_5832_, v___y_5833_);
lean_dec(v___y_5833_);
lean_dec(v___y_5832_);
return v_res_5835_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_, lean_object* v___y_5840_){
_start:
{
lean_object* v___x_5842_; 
v___x_5842_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5836_, v___y_5838_, v___y_5840_);
return v___x_5842_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_, lean_object* v___y_5848_){
_start:
{
lean_object* v_res_5849_; 
v_res_5849_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5843_, v___y_5844_, v___y_5845_, v___y_5846_, v___y_5847_);
lean_dec(v___y_5847_);
lean_dec_ref(v___y_5846_);
lean_dec(v___y_5845_);
lean_dec_ref(v___y_5844_);
return v_res_5849_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5851_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5852_ = l_Lean_stringToMessageData(v___x_5851_);
return v___x_5852_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5854_; lean_object* v___x_5855_; 
v___x_5854_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5855_ = l_Lean_stringToMessageData(v___x_5854_);
return v___x_5855_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; 
v___x_5857_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5858_ = l_Lean_stringToMessageData(v___x_5857_);
return v___x_5858_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5860_; lean_object* v___x_5861_; 
v___x_5860_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5861_ = l_Lean_stringToMessageData(v___x_5860_);
return v___x_5861_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5863_; lean_object* v___x_5864_; 
v___x_5863_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5864_ = l_Lean_stringToMessageData(v___x_5863_);
return v___x_5864_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5865_, lean_object* v_prio_5866_, lean_object* v_x_5867_, lean_object* v_type_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_, lean_object* v___y_5872_){
_start:
{
lean_object* v___x_5874_; 
v___x_5874_ = l_Lean_Expr_getAppFn(v_type_5868_);
if (lean_obj_tag(v___x_5874_) == 4)
{
lean_object* v_declName_5875_; lean_object* v___y_5877_; lean_object* v___y_5878_; lean_object* v___y_5879_; lean_object* v___y_5880_; lean_object* v___x_5890_; lean_object* v_env_5891_; uint8_t v___x_5892_; 
v_declName_5875_ = lean_ctor_get(v___x_5874_, 0);
lean_inc(v_declName_5875_);
lean_dec_ref_known(v___x_5874_, 2);
v___x_5890_ = lean_st_ref_get(v___y_5872_);
v_env_5891_ = lean_ctor_get(v___x_5890_, 0);
lean_inc_ref(v_env_5891_);
lean_dec(v___x_5890_);
v___x_5892_ = l_Lean_isClass(v_env_5891_, v_declName_5875_);
if (v___x_5892_ == 0)
{
lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; lean_object* v___x_5906_; 
lean_dec(v_prio_5866_);
v___x_5893_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5894_ = l_Lean_MessageData_ofConstName(v_declName_5865_, v___x_5892_);
v___x_5895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5893_);
lean_ctor_set(v___x_5895_, 1, v___x_5894_);
v___x_5896_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5895_);
lean_ctor_set(v___x_5897_, 1, v___x_5896_);
lean_inc(v_declName_5875_);
v___x_5898_ = l_Lean_MessageData_ofName(v_declName_5875_);
v___x_5899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5897_);
lean_ctor_set(v___x_5899_, 1, v___x_5898_);
v___x_5900_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5901_, 0, v___x_5899_);
lean_ctor_set(v___x_5901_, 1, v___x_5900_);
v___x_5902_ = l_Lean_MessageData_ofConstName(v_declName_5875_, v___x_5892_);
v___x_5903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5903_, 0, v___x_5901_);
lean_ctor_set(v___x_5903_, 1, v___x_5902_);
v___x_5904_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5905_, 0, v___x_5903_);
lean_ctor_set(v___x_5905_, 1, v___x_5904_);
v___x_5906_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5905_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_);
return v___x_5906_;
}
else
{
v___y_5877_ = v___y_5869_;
v___y_5878_ = v___y_5870_;
v___y_5879_ = v___y_5871_;
v___y_5880_ = v___y_5872_;
goto v___jp_5876_;
}
v___jp_5876_:
{
lean_object* v___x_5881_; lean_object* v_env_5882_; lean_object* v___x_5883_; lean_object* v_toEnvExtension_5884_; lean_object* v_asyncMode_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; lean_object* v___x_5889_; 
v___x_5881_ = lean_st_ref_get(v___y_5880_);
v_env_5882_ = lean_ctor_get(v___x_5881_, 0);
lean_inc_ref(v_env_5882_);
lean_dec(v___x_5881_);
v___x_5883_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5884_ = lean_ctor_get(v___x_5883_, 0);
v_asyncMode_5885_ = lean_ctor_get(v_toEnvExtension_5884_, 2);
v___x_5886_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5886_, 0, v_declName_5875_);
lean_ctor_set(v___x_5886_, 1, v_declName_5865_);
lean_ctor_set(v___x_5886_, 2, v_prio_5866_);
v___x_5887_ = lean_box(0);
v___x_5888_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5883_, v_env_5882_, v___x_5886_, v_asyncMode_5885_, v___x_5887_);
v___x_5889_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5888_, v___y_5878_, v___y_5880_);
return v___x_5889_;
}
}
else
{
lean_object* v___x_5907_; uint8_t v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; lean_object* v___x_5913_; 
lean_dec_ref(v___x_5874_);
lean_dec(v_prio_5866_);
v___x_5907_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5908_ = 0;
v___x_5909_ = l_Lean_MessageData_ofConstName(v_declName_5865_, v___x_5908_);
v___x_5910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5907_);
lean_ctor_set(v___x_5910_, 1, v___x_5909_);
v___x_5911_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5912_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5912_, 0, v___x_5910_);
lean_ctor_set(v___x_5912_, 1, v___x_5911_);
v___x_5913_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5912_, v___y_5869_, v___y_5870_, v___y_5871_, v___y_5872_);
return v___x_5913_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5914_, lean_object* v_prio_5915_, lean_object* v_x_5916_, lean_object* v_type_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_, lean_object* v___y_5922_){
_start:
{
lean_object* v_res_5923_; 
v_res_5923_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5914_, v_prio_5915_, v_x_5916_, v_type_5917_, v___y_5918_, v___y_5919_, v___y_5920_, v___y_5921_);
lean_dec(v___y_5921_);
lean_dec_ref(v___y_5920_);
lean_dec(v___y_5919_);
lean_dec_ref(v___y_5918_);
lean_dec_ref(v_type_5917_);
lean_dec_ref(v_x_5916_);
return v_res_5923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5924_, lean_object* v_prio_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_, lean_object* v_a_5928_, lean_object* v_a_5929_){
_start:
{
lean_object* v___x_5931_; lean_object* v_env_5932_; uint8_t v___x_5933_; lean_object* v___x_5934_; 
v___x_5931_ = lean_st_ref_get(v_a_5929_);
v_env_5932_ = lean_ctor_get(v___x_5931_, 0);
lean_inc_ref(v_env_5932_);
lean_dec(v___x_5931_);
v___x_5933_ = 0;
lean_inc(v_declName_5924_);
v___x_5934_ = l_Lean_Environment_find_x3f(v_env_5932_, v_declName_5924_, v___x_5933_);
if (lean_obj_tag(v___x_5934_) == 0)
{
lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; 
lean_dec(v_prio_5925_);
v___x_5935_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5936_ = l_Lean_MessageData_ofConstName(v_declName_5924_, v___x_5933_);
v___x_5937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5937_, 0, v___x_5935_);
lean_ctor_set(v___x_5937_, 1, v___x_5936_);
v___x_5938_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5939_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5939_, 0, v___x_5937_);
lean_ctor_set(v___x_5939_, 1, v___x_5938_);
v___x_5940_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5939_, v_a_5926_, v_a_5927_, v_a_5928_, v_a_5929_);
return v___x_5940_;
}
else
{
lean_object* v_val_5941_; lean_object* v___f_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; 
v_val_5941_ = lean_ctor_get(v___x_5934_, 0);
lean_inc(v_val_5941_);
lean_dec_ref_known(v___x_5934_, 1);
v___f_5942_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5942_, 0, v_declName_5924_);
lean_closure_set(v___f_5942_, 1, v_prio_5925_);
v___x_5943_ = l_Lean_ConstantInfo_type(v_val_5941_);
lean_dec(v_val_5941_);
v___x_5944_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5943_, v___f_5942_, v___x_5933_, v___x_5933_, v_a_5926_, v_a_5927_, v_a_5928_, v_a_5929_);
return v___x_5944_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5945_, lean_object* v_prio_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_, lean_object* v_a_5951_){
_start:
{
lean_object* v_res_5952_; 
v_res_5952_ = l_Lean_Meta_addDefaultInstance(v_declName_5945_, v_prio_5946_, v_a_5947_, v_a_5948_, v_a_5949_, v_a_5950_);
lean_dec(v_a_5950_);
lean_dec_ref(v_a_5949_);
lean_dec(v_a_5948_);
lean_dec_ref(v_a_5947_);
return v_res_5952_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5954_; lean_object* v___x_5955_; 
v___x_5954_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5955_ = l_Lean_stringToMessageData(v___x_5954_);
return v___x_5955_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5957_; lean_object* v___x_5958_; 
v___x_5957_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5958_ = l_Lean_stringToMessageData(v___x_5957_);
return v___x_5958_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5962_, uint8_t v_kind_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_){
_start:
{
lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___x_5971_; lean_object* v___y_5973_; 
v___x_5967_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5968_ = l_Lean_MessageData_ofName(v_name_5962_);
v___x_5969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5967_);
lean_ctor_set(v___x_5969_, 1, v___x_5968_);
v___x_5970_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5971_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5971_, 0, v___x_5969_);
lean_ctor_set(v___x_5971_, 1, v___x_5970_);
switch(v_kind_5963_)
{
case 0:
{
lean_object* v___x_5980_; 
v___x_5980_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5973_ = v___x_5980_;
goto v___jp_5972_;
}
case 1:
{
lean_object* v___x_5981_; 
v___x_5981_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5973_ = v___x_5981_;
goto v___jp_5972_;
}
default: 
{
lean_object* v___x_5982_; 
v___x_5982_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5973_ = v___x_5982_;
goto v___jp_5972_;
}
}
v___jp_5972_:
{
lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; lean_object* v___x_5979_; 
lean_inc_ref(v___y_5973_);
v___x_5974_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5974_, 0, v___y_5973_);
v___x_5975_ = l_Lean_MessageData_ofFormat(v___x_5974_);
v___x_5976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5971_);
lean_ctor_set(v___x_5976_, 1, v___x_5975_);
v___x_5977_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5978_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5978_, 0, v___x_5976_);
lean_ctor_set(v___x_5978_, 1, v___x_5977_);
v___x_5979_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5978_, v___y_5964_, v___y_5965_);
return v___x_5979_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_5983_, lean_object* v_kind_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_, lean_object* v___y_5987_){
_start:
{
uint8_t v_kind_boxed_5988_; lean_object* v_res_5989_; 
v_kind_boxed_5988_ = lean_unbox(v_kind_5984_);
v_res_5989_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5983_, v_kind_boxed_5988_, v___y_5985_, v___y_5986_);
lean_dec(v___y_5986_);
lean_dec_ref(v___y_5985_);
return v_res_5989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5990_, lean_object* v___x_5991_, lean_object* v___x_5992_, lean_object* v_declName_5993_, lean_object* v_stx_5994_, uint8_t v_kind_5995_, lean_object* v___y_5996_, lean_object* v___y_5997_){
_start:
{
lean_object* v___x_5999_; lean_object* v___x_6000_; lean_object* v___x_6001_; 
v___x_5999_ = lean_unsigned_to_nat(1u);
v___x_6000_ = l_Lean_Syntax_getArg(v_stx_5994_, v___x_5999_);
v___x_6001_ = l_Lean_getAttrParamOptPrio(v___x_6000_, v___y_5996_, v___y_5997_);
if (lean_obj_tag(v___x_6001_) == 0)
{
lean_object* v_a_6002_; lean_object* v___y_6004_; lean_object* v___y_6005_; uint8_t v___x_6036_; uint8_t v___x_6037_; 
v_a_6002_ = lean_ctor_get(v___x_6001_, 0);
lean_inc(v_a_6002_);
lean_dec_ref_known(v___x_6001_, 1);
v___x_6036_ = 0;
v___x_6037_ = l_Lean_instBEqAttributeKind_beq(v_kind_5995_, v___x_6036_);
if (v___x_6037_ == 0)
{
lean_object* v___x_6038_; 
lean_dec(v_a_6002_);
lean_dec(v_declName_5993_);
lean_dec(v___x_5991_);
lean_dec(v___x_5990_);
v___x_6038_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_5992_, v_kind_5995_, v___y_5996_, v___y_5997_);
return v___x_6038_;
}
else
{
lean_dec(v___x_5992_);
v___y_6004_ = v___y_5996_;
v___y_6005_ = v___y_5997_;
goto v___jp_6003_;
}
v___jp_6003_:
{
uint8_t v___x_6006_; uint8_t v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; size_t v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; lean_object* v___x_6025_; 
v___x_6006_ = 0;
v___x_6007_ = 1;
v___x_6008_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6009_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6010_ = lean_unsigned_to_nat(32u);
v___x_6011_ = lean_mk_empty_array_with_capacity(v___x_6010_);
v___x_6012_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_6013_ = ((size_t)5ULL);
lean_inc_n(v___x_5990_, 6);
v___x_6014_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6014_, 0, v___x_6012_);
lean_ctor_set(v___x_6014_, 1, v___x_6011_);
lean_ctor_set(v___x_6014_, 2, v___x_5990_);
lean_ctor_set(v___x_6014_, 3, v___x_5990_);
lean_ctor_set_usize(v___x_6014_, 4, v___x_6013_);
v___x_6015_ = lean_box(1);
lean_inc_ref(v___x_6014_);
v___x_6016_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6009_);
lean_ctor_set(v___x_6016_, 1, v___x_6014_);
lean_ctor_set(v___x_6016_, 2, v___x_6015_);
v___x_6017_ = lean_mk_empty_array_with_capacity(v___x_5990_);
v___x_6018_ = lean_box(0);
lean_inc(v___x_5991_);
v___x_6019_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6019_, 0, v___x_6008_);
lean_ctor_set(v___x_6019_, 1, v___x_5991_);
lean_ctor_set(v___x_6019_, 2, v___x_6016_);
lean_ctor_set(v___x_6019_, 3, v___x_6017_);
lean_ctor_set(v___x_6019_, 4, v___x_6018_);
lean_ctor_set(v___x_6019_, 5, v___x_5990_);
lean_ctor_set(v___x_6019_, 6, v___x_6018_);
lean_ctor_set_uint8(v___x_6019_, sizeof(void*)*7, v___x_6006_);
lean_ctor_set_uint8(v___x_6019_, sizeof(void*)*7 + 1, v___x_6006_);
lean_ctor_set_uint8(v___x_6019_, sizeof(void*)*7 + 2, v___x_6006_);
lean_ctor_set_uint8(v___x_6019_, sizeof(void*)*7 + 3, v___x_6007_);
v___x_6020_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6020_, 0, v___x_5990_);
lean_ctor_set(v___x_6020_, 1, v___x_5990_);
lean_ctor_set(v___x_6020_, 2, v___x_5990_);
lean_ctor_set(v___x_6020_, 3, v___x_5990_);
lean_ctor_set(v___x_6020_, 4, v___x_6009_);
lean_ctor_set(v___x_6020_, 5, v___x_6009_);
lean_ctor_set(v___x_6020_, 6, v___x_6009_);
lean_ctor_set(v___x_6020_, 7, v___x_6009_);
lean_ctor_set(v___x_6020_, 8, v___x_6009_);
lean_ctor_set(v___x_6020_, 9, v___x_6009_);
lean_ctor_set(v___x_6020_, 10, v___x_6009_);
v___x_6021_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6022_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6023_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6020_);
lean_ctor_set(v___x_6023_, 1, v___x_6021_);
lean_ctor_set(v___x_6023_, 2, v___x_5991_);
lean_ctor_set(v___x_6023_, 3, v___x_6014_);
lean_ctor_set(v___x_6023_, 4, v___x_6022_);
v___x_6024_ = lean_st_mk_ref(v___x_6023_);
v___x_6025_ = l_Lean_Meta_addDefaultInstance(v_declName_5993_, v_a_6002_, v___x_6019_, v___x_6024_, v___y_6004_, v___y_6005_);
lean_dec_ref_known(v___x_6019_, 7);
if (lean_obj_tag(v___x_6025_) == 0)
{
lean_object* v___x_6027_; uint8_t v_isShared_6028_; uint8_t v_isSharedCheck_6034_; 
v_isSharedCheck_6034_ = !lean_is_exclusive(v___x_6025_);
if (v_isSharedCheck_6034_ == 0)
{
lean_object* v_unused_6035_; 
v_unused_6035_ = lean_ctor_get(v___x_6025_, 0);
lean_dec(v_unused_6035_);
v___x_6027_ = v___x_6025_;
v_isShared_6028_ = v_isSharedCheck_6034_;
goto v_resetjp_6026_;
}
else
{
lean_dec(v___x_6025_);
v___x_6027_ = lean_box(0);
v_isShared_6028_ = v_isSharedCheck_6034_;
goto v_resetjp_6026_;
}
v_resetjp_6026_:
{
lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6032_; 
v___x_6029_ = lean_st_ref_get(v___x_6024_);
lean_dec(v___x_6024_);
lean_dec(v___x_6029_);
v___x_6030_ = lean_box(0);
if (v_isShared_6028_ == 0)
{
lean_ctor_set(v___x_6027_, 0, v___x_6030_);
v___x_6032_ = v___x_6027_;
goto v_reusejp_6031_;
}
else
{
lean_object* v_reuseFailAlloc_6033_; 
v_reuseFailAlloc_6033_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6033_, 0, v___x_6030_);
v___x_6032_ = v_reuseFailAlloc_6033_;
goto v_reusejp_6031_;
}
v_reusejp_6031_:
{
return v___x_6032_;
}
}
}
else
{
lean_dec(v___x_6024_);
return v___x_6025_;
}
}
}
else
{
lean_object* v_a_6039_; lean_object* v___x_6041_; uint8_t v_isShared_6042_; uint8_t v_isSharedCheck_6046_; 
lean_dec(v_declName_5993_);
lean_dec(v___x_5992_);
lean_dec(v___x_5991_);
lean_dec(v___x_5990_);
v_a_6039_ = lean_ctor_get(v___x_6001_, 0);
v_isSharedCheck_6046_ = !lean_is_exclusive(v___x_6001_);
if (v_isSharedCheck_6046_ == 0)
{
v___x_6041_ = v___x_6001_;
v_isShared_6042_ = v_isSharedCheck_6046_;
goto v_resetjp_6040_;
}
else
{
lean_inc(v_a_6039_);
lean_dec(v___x_6001_);
v___x_6041_ = lean_box(0);
v_isShared_6042_ = v_isSharedCheck_6046_;
goto v_resetjp_6040_;
}
v_resetjp_6040_:
{
lean_object* v___x_6044_; 
if (v_isShared_6042_ == 0)
{
v___x_6044_ = v___x_6041_;
goto v_reusejp_6043_;
}
else
{
lean_object* v_reuseFailAlloc_6045_; 
v_reuseFailAlloc_6045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6045_, 0, v_a_6039_);
v___x_6044_ = v_reuseFailAlloc_6045_;
goto v_reusejp_6043_;
}
v_reusejp_6043_:
{
return v___x_6044_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6047_, lean_object* v___x_6048_, lean_object* v___x_6049_, lean_object* v_declName_6050_, lean_object* v_stx_6051_, lean_object* v_kind_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_, lean_object* v___y_6055_){
_start:
{
uint8_t v_kind_boxed_6056_; lean_object* v_res_6057_; 
v_kind_boxed_6056_ = lean_unbox(v_kind_6052_);
v_res_6057_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6047_, v___x_6048_, v___x_6049_, v_declName_6050_, v_stx_6051_, v_kind_boxed_6056_, v___y_6053_, v___y_6054_);
lean_dec(v___y_6054_);
lean_dec_ref(v___y_6053_);
lean_dec(v_stx_6051_);
return v_res_6057_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6059_; lean_object* v___x_6060_; 
v___x_6059_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6060_ = l_Lean_stringToMessageData(v___x_6059_);
return v___x_6060_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6062_; lean_object* v___x_6063_; 
v___x_6062_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6063_ = l_Lean_stringToMessageData(v___x_6062_);
return v___x_6063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6064_, lean_object* v_decl_6065_, lean_object* v___y_6066_, lean_object* v___y_6067_){
_start:
{
lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; lean_object* v___x_6074_; 
v___x_6069_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6070_ = l_Lean_MessageData_ofName(v___x_6064_);
v___x_6071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6069_);
lean_ctor_set(v___x_6071_, 1, v___x_6070_);
v___x_6072_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6073_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6073_, 0, v___x_6071_);
lean_ctor_set(v___x_6073_, 1, v___x_6072_);
v___x_6074_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6073_, v___y_6066_, v___y_6067_);
return v___x_6074_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6075_, lean_object* v_decl_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_, lean_object* v___y_6079_){
_start:
{
lean_object* v_res_6080_; 
v_res_6080_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6075_, v_decl_6076_, v___y_6077_, v___y_6078_);
lean_dec(v___y_6078_);
lean_dec_ref(v___y_6077_);
lean_dec(v_decl_6076_);
return v_res_6080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6113_; lean_object* v___x_6114_; lean_object* v___x_6115_; 
v___x_6113_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6114_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6115_ = l_Lean_registerBuiltinAttribute(v___x_6114_);
if (lean_obj_tag(v___x_6115_) == 0)
{
lean_object* v___x_6116_; uint8_t v___x_6117_; lean_object* v___x_6118_; 
lean_dec_ref_known(v___x_6115_, 1);
v___x_6116_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_6117_ = 0;
v___x_6118_ = l_Lean_registerTraceClass(v___x_6116_, v___x_6117_, v___x_6113_);
return v___x_6118_;
}
else
{
return v___x_6115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_6119_){
_start:
{
lean_object* v_res_6120_; 
v_res_6120_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_6120_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_6121_, lean_object* v_name_6122_, uint8_t v_kind_6123_, lean_object* v___y_6124_, lean_object* v___y_6125_){
_start:
{
lean_object* v___x_6127_; 
v___x_6127_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6122_, v_kind_6123_, v___y_6124_, v___y_6125_);
return v___x_6127_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_6128_, lean_object* v_name_6129_, lean_object* v_kind_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_, lean_object* v___y_6133_){
_start:
{
uint8_t v_kind_boxed_6134_; lean_object* v_res_6135_; 
v_kind_boxed_6134_ = lean_unbox(v_kind_6130_);
v_res_6135_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_6128_, v_name_6129_, v_kind_boxed_6134_, v___y_6131_, v___y_6132_);
lean_dec(v___y_6132_);
lean_dec_ref(v___y_6131_);
return v_res_6135_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_6136_, lean_object* v_toPure_6137_, lean_object* v_____do__lift_6138_){
_start:
{
lean_object* v___x_6139_; lean_object* v_toEnvExtension_6140_; lean_object* v_asyncMode_6141_; lean_object* v___x_6142_; lean_object* v___x_6143_; lean_object* v_priorities_6144_; lean_object* v___x_6145_; 
v___x_6139_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6140_ = lean_ctor_get(v___x_6139_, 0);
v_asyncMode_6141_ = lean_ctor_get(v_toEnvExtension_6140_, 2);
v___x_6142_ = lean_box(0);
v___x_6143_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6136_, v___x_6139_, v_____do__lift_6138_, v_asyncMode_6141_, v___x_6142_);
v_priorities_6144_ = lean_ctor_get(v___x_6143_, 1);
lean_inc(v_priorities_6144_);
lean_dec(v___x_6143_);
v___x_6145_ = lean_apply_2(v_toPure_6137_, lean_box(0), v_priorities_6144_);
return v___x_6145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_6146_, lean_object* v_inst_6147_){
_start:
{
lean_object* v_toApplicative_6148_; lean_object* v_toBind_6149_; lean_object* v_getEnv_6150_; lean_object* v_toPure_6151_; lean_object* v___x_6152_; lean_object* v___f_6153_; lean_object* v___x_6154_; 
v_toApplicative_6148_ = lean_ctor_get(v_inst_6146_, 0);
lean_inc_ref(v_toApplicative_6148_);
v_toBind_6149_ = lean_ctor_get(v_inst_6146_, 1);
lean_inc(v_toBind_6149_);
lean_dec_ref(v_inst_6146_);
v_getEnv_6150_ = lean_ctor_get(v_inst_6147_, 0);
lean_inc(v_getEnv_6150_);
lean_dec_ref(v_inst_6147_);
v_toPure_6151_ = lean_ctor_get(v_toApplicative_6148_, 1);
lean_inc(v_toPure_6151_);
lean_dec_ref(v_toApplicative_6148_);
v___x_6152_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6153_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6153_, 0, v___x_6152_);
lean_closure_set(v___f_6153_, 1, v_toPure_6151_);
v___x_6154_ = lean_apply_4(v_toBind_6149_, lean_box(0), lean_box(0), v_getEnv_6150_, v___f_6153_);
return v___x_6154_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_6155_, lean_object* v_inst_6156_, lean_object* v_inst_6157_){
_start:
{
lean_object* v___x_6158_; 
v___x_6158_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_6156_, v_inst_6157_);
return v___x_6158_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_6159_, uint8_t v_isExporting_6160_, lean_object* v_x_6161_){
_start:
{
lean_object* v_fst_6162_; uint8_t v___x_6163_; 
v_fst_6162_ = lean_ctor_get(v_x_6161_, 0);
lean_inc(v_fst_6162_);
lean_dec_ref(v_x_6161_);
v___x_6163_ = l_Lean_Environment_contains(v_env_6159_, v_fst_6162_, v_isExporting_6160_);
return v___x_6163_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_6164_, lean_object* v_isExporting_6165_, lean_object* v_x_6166_){
_start:
{
uint8_t v_isExporting_boxed_6167_; uint8_t v_res_6168_; lean_object* v_r_6169_; 
v_isExporting_boxed_6167_ = lean_unbox(v_isExporting_6165_);
v_res_6168_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_6164_, v_isExporting_boxed_6167_, v_x_6166_);
v_r_6169_ = lean_box(v_res_6168_);
return v_r_6169_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_6170_, lean_object* v_toApplicative_6171_, lean_object* v_className_6172_, lean_object* v_env_6173_){
_start:
{
lean_object* v___y_6175_; lean_object* v___x_6185_; lean_object* v_toEnvExtension_6186_; lean_object* v_asyncMode_6187_; lean_object* v___x_6188_; lean_object* v___x_6189_; lean_object* v_defaultInstances_6190_; lean_object* v___x_6191_; 
v___x_6185_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6186_ = lean_ctor_get(v___x_6185_, 0);
v_asyncMode_6187_ = lean_ctor_get(v_toEnvExtension_6186_, 2);
v___x_6188_ = lean_box(0);
lean_inc_ref(v_env_6173_);
v___x_6189_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6170_, v___x_6185_, v_env_6173_, v_asyncMode_6187_, v___x_6188_);
v_defaultInstances_6190_ = lean_ctor_get(v___x_6189_, 0);
lean_inc(v_defaultInstances_6190_);
lean_dec(v___x_6189_);
v___x_6191_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_6190_, v_className_6172_);
lean_dec(v_defaultInstances_6190_);
if (lean_obj_tag(v___x_6191_) == 0)
{
lean_object* v___x_6192_; 
v___x_6192_ = lean_box(0);
v___y_6175_ = v___x_6192_;
goto v___jp_6174_;
}
else
{
lean_object* v_val_6193_; 
v_val_6193_ = lean_ctor_get(v___x_6191_, 0);
lean_inc(v_val_6193_);
lean_dec_ref_known(v___x_6191_, 1);
v___y_6175_ = v_val_6193_;
goto v___jp_6174_;
}
v___jp_6174_:
{
uint8_t v_isExporting_6176_; 
v_isExporting_6176_ = lean_ctor_get_uint8(v_env_6173_, sizeof(void*)*8);
if (v_isExporting_6176_ == 0)
{
lean_object* v_toPure_6177_; lean_object* v___x_6178_; 
lean_dec_ref(v_env_6173_);
v_toPure_6177_ = lean_ctor_get(v_toApplicative_6171_, 1);
lean_inc(v_toPure_6177_);
lean_dec_ref(v_toApplicative_6171_);
v___x_6178_ = lean_apply_2(v_toPure_6177_, lean_box(0), v___y_6175_);
return v___x_6178_;
}
else
{
lean_object* v_toPure_6179_; lean_object* v___x_6180_; lean_object* v___f_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; lean_object* v___x_6184_; 
v_toPure_6179_ = lean_ctor_get(v_toApplicative_6171_, 1);
lean_inc(v_toPure_6179_);
lean_dec_ref(v_toApplicative_6171_);
v___x_6180_ = lean_box(v_isExporting_6176_);
v___f_6181_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6181_, 0, v_env_6173_);
lean_closure_set(v___f_6181_, 1, v___x_6180_);
v___x_6182_ = lean_box(0);
v___x_6183_ = l_List_filterTR_loop___redArg(v___f_6181_, v___y_6175_, v___x_6182_);
v___x_6184_ = lean_apply_2(v_toPure_6179_, lean_box(0), v___x_6183_);
return v___x_6184_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_6194_, lean_object* v_toApplicative_6195_, lean_object* v_className_6196_, lean_object* v_env_6197_){
_start:
{
lean_object* v_res_6198_; 
v_res_6198_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_6194_, v_toApplicative_6195_, v_className_6196_, v_env_6197_);
lean_dec(v_className_6196_);
return v_res_6198_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_6199_, lean_object* v_inst_6200_, lean_object* v_className_6201_){
_start:
{
lean_object* v_toApplicative_6202_; lean_object* v_toBind_6203_; lean_object* v_getEnv_6204_; lean_object* v___x_6205_; lean_object* v___f_6206_; lean_object* v___x_6207_; 
v_toApplicative_6202_ = lean_ctor_get(v_inst_6199_, 0);
lean_inc_ref(v_toApplicative_6202_);
v_toBind_6203_ = lean_ctor_get(v_inst_6199_, 1);
lean_inc(v_toBind_6203_);
lean_dec_ref(v_inst_6199_);
v_getEnv_6204_ = lean_ctor_get(v_inst_6200_, 0);
lean_inc(v_getEnv_6204_);
lean_dec_ref(v_inst_6200_);
v___x_6205_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6206_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_6206_, 0, v___x_6205_);
lean_closure_set(v___f_6206_, 1, v_toApplicative_6202_);
lean_closure_set(v___f_6206_, 2, v_className_6201_);
v___x_6207_ = lean_apply_4(v_toBind_6203_, lean_box(0), lean_box(0), v_getEnv_6204_, v___f_6206_);
return v___x_6207_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6208_, lean_object* v_inst_6209_, lean_object* v_inst_6210_, lean_object* v_className_6211_){
_start:
{
lean_object* v___x_6212_; 
v___x_6212_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6209_, v_inst_6210_, v_className_6211_);
return v___x_6212_;
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
res = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_();
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
