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
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_Lean_PersistentHashMap_mkCollisionNode___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
uint8_t lean_usize_dec_le(size_t, size_t);
lean_object* l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(lean_object*);
lean_object* l_Lean_PersistentHashMap_mkEmptyEntries(lean_object*, lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_mul(size_t, size_t);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(lean_object*, size_t, size_t, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(size_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16___redArg(lean_object* v_x_120_, lean_object* v_x_121_, lean_object* v_x_122_, lean_object* v_x_123_){
_start:
{
lean_object* v_ks_124_; lean_object* v_vs_125_; lean_object* v___x_127_; uint8_t v_isShared_128_; uint8_t v_isSharedCheck_149_; 
v_ks_124_ = lean_ctor_get(v_x_120_, 0);
v_vs_125_ = lean_ctor_get(v_x_120_, 1);
v_isSharedCheck_149_ = !lean_is_exclusive(v_x_120_);
if (v_isSharedCheck_149_ == 0)
{
v___x_127_ = v_x_120_;
v_isShared_128_ = v_isSharedCheck_149_;
goto v_resetjp_126_;
}
else
{
lean_inc(v_vs_125_);
lean_inc(v_ks_124_);
lean_dec(v_x_120_);
v___x_127_ = lean_box(0);
v_isShared_128_ = v_isSharedCheck_149_;
goto v_resetjp_126_;
}
v_resetjp_126_:
{
lean_object* v___x_129_; uint8_t v___x_130_; 
v___x_129_ = lean_array_get_size(v_ks_124_);
v___x_130_ = lean_nat_dec_lt(v_x_121_, v___x_129_);
if (v___x_130_ == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_134_; 
lean_dec(v_x_121_);
v___x_131_ = lean_array_push(v_ks_124_, v_x_122_);
v___x_132_ = lean_array_push(v_vs_125_, v_x_123_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_132_);
lean_ctor_set(v___x_127_, 0, v___x_131_);
v___x_134_ = v___x_127_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v___x_131_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
else
{
lean_object* v_k_x27_136_; uint8_t v___x_137_; 
v_k_x27_136_ = lean_array_fget_borrowed(v_ks_124_, v_x_121_);
v___x_137_ = lean_name_eq(v_x_122_, v_k_x27_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_139_; 
if (v_isShared_128_ == 0)
{
v___x_139_ = v___x_127_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_ks_124_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_vs_125_);
v___x_139_ = v_reuseFailAlloc_143_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
lean_object* v___x_140_; lean_object* v___x_141_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = lean_nat_add(v_x_121_, v___x_140_);
lean_dec(v_x_121_);
v_x_120_ = v___x_139_;
v_x_121_ = v___x_141_;
goto _start;
}
}
else
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_147_; 
v___x_144_ = lean_array_fset(v_ks_124_, v_x_121_, v_x_122_);
v___x_145_ = lean_array_fset(v_vs_125_, v_x_121_, v_x_123_);
lean_dec(v_x_121_);
if (v_isShared_128_ == 0)
{
lean_ctor_set(v___x_127_, 1, v___x_145_);
lean_ctor_set(v___x_127_, 0, v___x_144_);
v___x_147_ = v___x_127_;
goto v_reusejp_146_;
}
else
{
lean_object* v_reuseFailAlloc_148_; 
v_reuseFailAlloc_148_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_148_, 0, v___x_144_);
lean_ctor_set(v_reuseFailAlloc_148_, 1, v___x_145_);
v___x_147_ = v_reuseFailAlloc_148_;
goto v_reusejp_146_;
}
v_reusejp_146_:
{
return v___x_147_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9___redArg(lean_object* v_n_150_, lean_object* v_k_151_, lean_object* v_v_152_){
_start:
{
lean_object* v___x_153_; lean_object* v___x_154_; 
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16___redArg(v_n_150_, v___x_153_, v_k_151_, v_v_152_);
return v___x_154_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(lean_object* v_x_156_, size_t v_x_157_, size_t v_x_158_, lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
if (lean_obj_tag(v_x_156_) == 0)
{
lean_object* v_es_161_; size_t v___x_162_; size_t v___x_163_; lean_object* v_j_164_; lean_object* v___x_165_; uint8_t v___x_166_; 
v_es_161_ = lean_ctor_get(v_x_156_, 0);
v___x_162_ = ((size_t)31ULL);
v___x_163_ = lean_usize_land(v_x_157_, v___x_162_);
v_j_164_ = lean_usize_to_nat(v___x_163_);
v___x_165_ = lean_array_get_size(v_es_161_);
v___x_166_ = lean_nat_dec_lt(v_j_164_, v___x_165_);
if (v___x_166_ == 0)
{
lean_dec(v_j_164_);
lean_dec(v_x_160_);
lean_dec(v_x_159_);
return v_x_156_;
}
else
{
lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_205_; 
lean_inc_ref(v_es_161_);
v_isSharedCheck_205_ = !lean_is_exclusive(v_x_156_);
if (v_isSharedCheck_205_ == 0)
{
lean_object* v_unused_206_; 
v_unused_206_ = lean_ctor_get(v_x_156_, 0);
lean_dec(v_unused_206_);
v___x_168_ = v_x_156_;
v_isShared_169_ = v_isSharedCheck_205_;
goto v_resetjp_167_;
}
else
{
lean_dec(v_x_156_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_205_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v_v_170_; lean_object* v___x_171_; lean_object* v_xs_x27_172_; lean_object* v___y_174_; 
v_v_170_ = lean_array_fget(v_es_161_, v_j_164_);
v___x_171_ = lean_box(0);
v_xs_x27_172_ = lean_array_fset(v_es_161_, v_j_164_, v___x_171_);
switch(lean_obj_tag(v_v_170_))
{
case 0:
{
lean_object* v_key_179_; lean_object* v_val_180_; lean_object* v___x_182_; uint8_t v_isShared_183_; uint8_t v_isSharedCheck_190_; 
v_key_179_ = lean_ctor_get(v_v_170_, 0);
v_val_180_ = lean_ctor_get(v_v_170_, 1);
v_isSharedCheck_190_ = !lean_is_exclusive(v_v_170_);
if (v_isSharedCheck_190_ == 0)
{
v___x_182_ = v_v_170_;
v_isShared_183_ = v_isSharedCheck_190_;
goto v_resetjp_181_;
}
else
{
lean_inc(v_val_180_);
lean_inc(v_key_179_);
lean_dec(v_v_170_);
v___x_182_ = lean_box(0);
v_isShared_183_ = v_isSharedCheck_190_;
goto v_resetjp_181_;
}
v_resetjp_181_:
{
uint8_t v___x_184_; 
v___x_184_ = lean_name_eq(v_x_159_, v_key_179_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_del_object(v___x_182_);
v___x_185_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_179_, v_val_180_, v_x_159_, v_x_160_);
v___x_186_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
v___y_174_ = v___x_186_;
goto v___jp_173_;
}
else
{
lean_object* v___x_188_; 
lean_dec(v_val_180_);
lean_dec(v_key_179_);
if (v_isShared_183_ == 0)
{
lean_ctor_set(v___x_182_, 1, v_x_160_);
lean_ctor_set(v___x_182_, 0, v_x_159_);
v___x_188_ = v___x_182_;
goto v_reusejp_187_;
}
else
{
lean_object* v_reuseFailAlloc_189_; 
v_reuseFailAlloc_189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_189_, 0, v_x_159_);
lean_ctor_set(v_reuseFailAlloc_189_, 1, v_x_160_);
v___x_188_ = v_reuseFailAlloc_189_;
goto v_reusejp_187_;
}
v_reusejp_187_:
{
v___y_174_ = v___x_188_;
goto v___jp_173_;
}
}
}
}
case 1:
{
lean_object* v_node_191_; lean_object* v___x_193_; uint8_t v_isShared_194_; uint8_t v_isSharedCheck_203_; 
v_node_191_ = lean_ctor_get(v_v_170_, 0);
v_isSharedCheck_203_ = !lean_is_exclusive(v_v_170_);
if (v_isSharedCheck_203_ == 0)
{
v___x_193_ = v_v_170_;
v_isShared_194_ = v_isSharedCheck_203_;
goto v_resetjp_192_;
}
else
{
lean_inc(v_node_191_);
lean_dec(v_v_170_);
v___x_193_ = lean_box(0);
v_isShared_194_ = v_isSharedCheck_203_;
goto v_resetjp_192_;
}
v_resetjp_192_:
{
size_t v___x_195_; size_t v___x_196_; size_t v___x_197_; size_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_201_; 
v___x_195_ = ((size_t)5ULL);
v___x_196_ = lean_usize_shift_right(v_x_157_, v___x_195_);
v___x_197_ = ((size_t)1ULL);
v___x_198_ = lean_usize_add(v_x_158_, v___x_197_);
v___x_199_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_node_191_, v___x_196_, v___x_198_, v_x_159_, v_x_160_);
if (v_isShared_194_ == 0)
{
lean_ctor_set(v___x_193_, 0, v___x_199_);
v___x_201_ = v___x_193_;
goto v_reusejp_200_;
}
else
{
lean_object* v_reuseFailAlloc_202_; 
v_reuseFailAlloc_202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_202_, 0, v___x_199_);
v___x_201_ = v_reuseFailAlloc_202_;
goto v_reusejp_200_;
}
v_reusejp_200_:
{
v___y_174_ = v___x_201_;
goto v___jp_173_;
}
}
}
default: 
{
lean_object* v___x_204_; 
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v_x_159_);
lean_ctor_set(v___x_204_, 1, v_x_160_);
v___y_174_ = v___x_204_;
goto v___jp_173_;
}
}
v___jp_173_:
{
lean_object* v___x_175_; lean_object* v___x_177_; 
v___x_175_ = lean_array_fset(v_xs_x27_172_, v_j_164_, v___y_174_);
lean_dec(v_j_164_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 0, v___x_175_);
v___x_177_ = v___x_168_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v___x_175_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
else
{
lean_object* v_ks_207_; lean_object* v_vs_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_226_; 
v_ks_207_ = lean_ctor_get(v_x_156_, 0);
v_vs_208_ = lean_ctor_get(v_x_156_, 1);
v_isSharedCheck_226_ = !lean_is_exclusive(v_x_156_);
if (v_isSharedCheck_226_ == 0)
{
v___x_210_ = v_x_156_;
v_isShared_211_ = v_isSharedCheck_226_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_vs_208_);
lean_inc(v_ks_207_);
lean_dec(v_x_156_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_226_;
goto v_resetjp_209_;
}
v_resetjp_209_:
{
lean_object* v___x_213_; 
if (v_isShared_211_ == 0)
{
v___x_213_ = v___x_210_;
goto v_reusejp_212_;
}
else
{
lean_object* v_reuseFailAlloc_225_; 
v_reuseFailAlloc_225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_225_, 0, v_ks_207_);
lean_ctor_set(v_reuseFailAlloc_225_, 1, v_vs_208_);
v___x_213_ = v_reuseFailAlloc_225_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v_newNode_214_; size_t v___x_215_; uint8_t v___x_216_; 
v_newNode_214_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9___redArg(v___x_213_, v_x_159_, v_x_160_);
v___x_215_ = ((size_t)7ULL);
v___x_216_ = lean_usize_dec_le(v___x_215_, v_x_158_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___x_218_; uint8_t v___x_219_; 
v___x_217_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_214_);
v___x_218_ = lean_unsigned_to_nat(4u);
v___x_219_ = lean_nat_dec_lt(v___x_217_, v___x_218_);
lean_dec(v___x_217_);
if (v___x_219_ == 0)
{
lean_object* v_ks_220_; lean_object* v_vs_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_ks_220_ = lean_ctor_get(v_newNode_214_, 0);
lean_inc_ref(v_ks_220_);
v_vs_221_ = lean_ctor_get(v_newNode_214_, 1);
lean_inc_ref(v_vs_221_);
lean_dec_ref(v_newNode_214_);
v___x_222_ = lean_unsigned_to_nat(0u);
v___x_223_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0);
v___x_224_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_x_158_, v_ks_220_, v_vs_221_, v___x_222_, v___x_223_);
lean_dec_ref(v_vs_221_);
lean_dec_ref(v_ks_220_);
return v___x_224_;
}
else
{
return v_newNode_214_;
}
}
else
{
return v_newNode_214_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(size_t v_depth_227_, lean_object* v_keys_228_, lean_object* v_vals_229_, lean_object* v_i_230_, lean_object* v_entries_231_){
_start:
{
lean_object* v___x_232_; uint8_t v___x_233_; 
v___x_232_ = lean_array_get_size(v_keys_228_);
v___x_233_ = lean_nat_dec_lt(v_i_230_, v___x_232_);
if (v___x_233_ == 0)
{
lean_dec(v_i_230_);
return v_entries_231_;
}
else
{
lean_object* v_k_234_; lean_object* v_v_235_; uint64_t v___y_237_; 
v_k_234_ = lean_array_fget_borrowed(v_keys_228_, v_i_230_);
v_v_235_ = lean_array_fget_borrowed(v_vals_229_, v_i_230_);
if (lean_obj_tag(v_k_234_) == 0)
{
uint64_t v___x_248_; 
v___x_248_ = 1723ULL;
v___y_237_ = v___x_248_;
goto v___jp_236_;
}
else
{
uint64_t v_hash_249_; 
v_hash_249_ = lean_ctor_get_uint64(v_k_234_, sizeof(void*)*2);
v___y_237_ = v_hash_249_;
goto v___jp_236_;
}
v___jp_236_:
{
size_t v_h_238_; size_t v___x_239_; lean_object* v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v_h_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v_h_238_ = lean_uint64_to_usize(v___y_237_);
v___x_239_ = ((size_t)5ULL);
v___x_240_ = lean_unsigned_to_nat(1u);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_sub(v_depth_227_, v___x_241_);
v___x_243_ = lean_usize_mul(v___x_239_, v___x_242_);
v_h_244_ = lean_usize_shift_right(v_h_238_, v___x_243_);
v___x_245_ = lean_nat_add(v_i_230_, v___x_240_);
lean_dec(v_i_230_);
lean_inc(v_v_235_);
lean_inc(v_k_234_);
v___x_246_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_entries_231_, v_h_244_, v_depth_227_, v_k_234_, v_v_235_);
v_i_230_ = v___x_245_;
v_entries_231_ = v___x_246_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_depth_250_, lean_object* v_keys_251_, lean_object* v_vals_252_, lean_object* v_i_253_, lean_object* v_entries_254_){
_start:
{
size_t v_depth_boxed_255_; lean_object* v_res_256_; 
v_depth_boxed_255_ = lean_unbox_usize(v_depth_250_);
lean_dec(v_depth_250_);
v_res_256_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_depth_boxed_255_, v_keys_251_, v_vals_252_, v_i_253_, v_entries_254_);
lean_dec_ref(v_vals_252_);
lean_dec_ref(v_keys_251_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___boxed(lean_object* v_x_257_, lean_object* v_x_258_, lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_){
_start:
{
size_t v_x_2091__boxed_262_; size_t v_x_2092__boxed_263_; lean_object* v_res_264_; 
v_x_2091__boxed_262_ = lean_unbox_usize(v_x_258_);
lean_dec(v_x_258_);
v_x_2092__boxed_263_ = lean_unbox_usize(v_x_259_);
lean_dec(v_x_259_);
v_res_264_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_257_, v_x_2091__boxed_262_, v_x_2092__boxed_263_, v_x_260_, v_x_261_);
return v_res_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(lean_object* v_x_265_, lean_object* v_x_266_, lean_object* v_x_267_){
_start:
{
uint64_t v___y_269_; 
if (lean_obj_tag(v_x_266_) == 0)
{
uint64_t v___x_273_; 
v___x_273_ = 1723ULL;
v___y_269_ = v___x_273_;
goto v___jp_268_;
}
else
{
uint64_t v_hash_274_; 
v_hash_274_ = lean_ctor_get_uint64(v_x_266_, sizeof(void*)*2);
v___y_269_ = v_hash_274_;
goto v___jp_268_;
}
v___jp_268_:
{
size_t v___x_270_; size_t v___x_271_; lean_object* v___x_272_; 
v___x_270_ = lean_uint64_to_usize(v___y_269_);
v___x_271_ = ((size_t)1ULL);
v___x_272_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_265_, v___x_270_, v___x_271_, v_x_266_, v_x_267_);
return v___x_272_;
}
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_275_; 
v___x_275_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_275_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(lean_object* v_msg_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0);
v___x_278_ = lean_panic_fn_borrowed(v___x_277_, v_msg_276_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(lean_object* v_xs_279_, lean_object* v_v_280_, lean_object* v_i_281_){
_start:
{
lean_object* v___x_282_; uint8_t v___x_283_; 
v___x_282_ = lean_array_get_size(v_xs_279_);
v___x_283_ = lean_nat_dec_lt(v_i_281_, v___x_282_);
if (v___x_283_ == 0)
{
lean_object* v___x_284_; 
lean_dec(v_i_281_);
v___x_284_ = lean_box(0);
return v___x_284_;
}
else
{
lean_object* v___x_285_; uint8_t v___x_286_; 
v___x_285_ = lean_array_fget_borrowed(v_xs_279_, v_i_281_);
v___x_286_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_285_, v_v_280_);
if (v___x_286_ == 0)
{
lean_object* v___x_287_; lean_object* v___x_288_; 
v___x_287_ = lean_unsigned_to_nat(1u);
v___x_288_ = lean_nat_add(v_i_281_, v___x_287_);
lean_dec(v_i_281_);
v_i_281_ = v___x_288_;
goto _start;
}
else
{
lean_object* v___x_290_; 
v___x_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_290_, 0, v_i_281_);
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_xs_291_, lean_object* v_v_292_, lean_object* v_i_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(v_xs_291_, v_v_292_, v_i_293_);
lean_dec(v_v_292_);
lean_dec_ref(v_xs_291_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(lean_object* v_xs_295_, lean_object* v_v_296_){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = lean_unsigned_to_nat(0u);
v___x_298_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(v_xs_295_, v_v_296_, v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4___boxed(lean_object* v_xs_299_, lean_object* v_v_300_){
_start:
{
lean_object* v_res_301_; 
v_res_301_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(v_xs_299_, v_v_300_);
lean_dec(v_v_300_);
lean_dec_ref(v_xs_299_);
return v_res_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(lean_object* v_x_302_, lean_object* v_x_303_, lean_object* v_x_304_, lean_object* v_x_305_){
_start:
{
lean_object* v_ks_306_; lean_object* v_vs_307_; lean_object* v___x_309_; uint8_t v_isShared_310_; uint8_t v_isSharedCheck_331_; 
v_ks_306_ = lean_ctor_get(v_x_302_, 0);
v_vs_307_ = lean_ctor_get(v_x_302_, 1);
v_isSharedCheck_331_ = !lean_is_exclusive(v_x_302_);
if (v_isSharedCheck_331_ == 0)
{
v___x_309_ = v_x_302_;
v_isShared_310_ = v_isSharedCheck_331_;
goto v_resetjp_308_;
}
else
{
lean_inc(v_vs_307_);
lean_inc(v_ks_306_);
lean_dec(v_x_302_);
v___x_309_ = lean_box(0);
v_isShared_310_ = v_isSharedCheck_331_;
goto v_resetjp_308_;
}
v_resetjp_308_:
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = lean_array_get_size(v_ks_306_);
v___x_312_ = lean_nat_dec_lt(v_x_303_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; lean_object* v___x_316_; 
lean_dec(v_x_303_);
v___x_313_ = lean_array_push(v_ks_306_, v_x_304_);
v___x_314_ = lean_array_push(v_vs_307_, v_x_305_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v___x_314_);
lean_ctor_set(v___x_309_, 0, v___x_313_);
v___x_316_ = v___x_309_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v___x_313_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v___x_314_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
else
{
lean_object* v_k_x27_318_; uint8_t v___x_319_; 
v_k_x27_318_ = lean_array_fget_borrowed(v_ks_306_, v_x_303_);
v___x_319_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_304_, v_k_x27_318_);
if (v___x_319_ == 0)
{
lean_object* v___x_321_; 
if (v_isShared_310_ == 0)
{
v___x_321_ = v___x_309_;
goto v_reusejp_320_;
}
else
{
lean_object* v_reuseFailAlloc_325_; 
v_reuseFailAlloc_325_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_325_, 0, v_ks_306_);
lean_ctor_set(v_reuseFailAlloc_325_, 1, v_vs_307_);
v___x_321_ = v_reuseFailAlloc_325_;
goto v_reusejp_320_;
}
v_reusejp_320_:
{
lean_object* v___x_322_; lean_object* v___x_323_; 
v___x_322_ = lean_unsigned_to_nat(1u);
v___x_323_ = lean_nat_add(v_x_303_, v___x_322_);
lean_dec(v_x_303_);
v_x_302_ = v___x_321_;
v_x_303_ = v___x_323_;
goto _start;
}
}
else
{
lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_329_; 
v___x_326_ = lean_array_fset(v_ks_306_, v_x_303_, v_x_304_);
v___x_327_ = lean_array_fset(v_vs_307_, v_x_303_, v_x_305_);
lean_dec(v_x_303_);
if (v_isShared_310_ == 0)
{
lean_ctor_set(v___x_309_, 1, v___x_327_);
lean_ctor_set(v___x_309_, 0, v___x_326_);
v___x_329_ = v___x_309_;
goto v_reusejp_328_;
}
else
{
lean_object* v_reuseFailAlloc_330_; 
v_reuseFailAlloc_330_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_330_, 0, v___x_326_);
lean_ctor_set(v_reuseFailAlloc_330_, 1, v___x_327_);
v___x_329_ = v_reuseFailAlloc_330_;
goto v_reusejp_328_;
}
v_reusejp_328_:
{
return v___x_329_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(lean_object* v_n_332_, lean_object* v_k_333_, lean_object* v_v_334_){
_start:
{
lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(v_n_332_, v___x_335_, v_k_333_, v_v_334_);
return v___x_336_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_337_; 
v___x_337_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_337_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_x_338_, size_t v_x_339_, size_t v_x_340_, lean_object* v_x_341_, lean_object* v_x_342_){
_start:
{
if (lean_obj_tag(v_x_338_) == 0)
{
lean_object* v_es_343_; size_t v___x_344_; size_t v___x_345_; lean_object* v_j_346_; lean_object* v___x_347_; uint8_t v___x_348_; 
v_es_343_ = lean_ctor_get(v_x_338_, 0);
v___x_344_ = ((size_t)31ULL);
v___x_345_ = lean_usize_land(v_x_339_, v___x_344_);
v_j_346_ = lean_usize_to_nat(v___x_345_);
v___x_347_ = lean_array_get_size(v_es_343_);
v___x_348_ = lean_nat_dec_lt(v_j_346_, v___x_347_);
if (v___x_348_ == 0)
{
lean_dec(v_j_346_);
lean_dec(v_x_342_);
lean_dec(v_x_341_);
return v_x_338_;
}
else
{
lean_object* v___x_350_; uint8_t v_isShared_351_; uint8_t v_isSharedCheck_387_; 
lean_inc_ref(v_es_343_);
v_isSharedCheck_387_ = !lean_is_exclusive(v_x_338_);
if (v_isSharedCheck_387_ == 0)
{
lean_object* v_unused_388_; 
v_unused_388_ = lean_ctor_get(v_x_338_, 0);
lean_dec(v_unused_388_);
v___x_350_ = v_x_338_;
v_isShared_351_ = v_isSharedCheck_387_;
goto v_resetjp_349_;
}
else
{
lean_dec(v_x_338_);
v___x_350_ = lean_box(0);
v_isShared_351_ = v_isSharedCheck_387_;
goto v_resetjp_349_;
}
v_resetjp_349_:
{
lean_object* v_v_352_; lean_object* v___x_353_; lean_object* v_xs_x27_354_; lean_object* v___y_356_; 
v_v_352_ = lean_array_fget(v_es_343_, v_j_346_);
v___x_353_ = lean_box(0);
v_xs_x27_354_ = lean_array_fset(v_es_343_, v_j_346_, v___x_353_);
switch(lean_obj_tag(v_v_352_))
{
case 0:
{
lean_object* v_key_361_; lean_object* v_val_362_; lean_object* v___x_364_; uint8_t v_isShared_365_; uint8_t v_isSharedCheck_372_; 
v_key_361_ = lean_ctor_get(v_v_352_, 0);
v_val_362_ = lean_ctor_get(v_v_352_, 1);
v_isSharedCheck_372_ = !lean_is_exclusive(v_v_352_);
if (v_isSharedCheck_372_ == 0)
{
v___x_364_ = v_v_352_;
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
else
{
lean_inc(v_val_362_);
lean_inc(v_key_361_);
lean_dec(v_v_352_);
v___x_364_ = lean_box(0);
v_isShared_365_ = v_isSharedCheck_372_;
goto v_resetjp_363_;
}
v_resetjp_363_:
{
uint8_t v___x_366_; 
v___x_366_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_341_, v_key_361_);
if (v___x_366_ == 0)
{
lean_object* v___x_367_; lean_object* v___x_368_; 
lean_del_object(v___x_364_);
v___x_367_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_361_, v_val_362_, v_x_341_, v_x_342_);
v___x_368_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
v___y_356_ = v___x_368_;
goto v___jp_355_;
}
else
{
lean_object* v___x_370_; 
lean_dec(v_val_362_);
lean_dec(v_key_361_);
if (v_isShared_365_ == 0)
{
lean_ctor_set(v___x_364_, 1, v_x_342_);
lean_ctor_set(v___x_364_, 0, v_x_341_);
v___x_370_ = v___x_364_;
goto v_reusejp_369_;
}
else
{
lean_object* v_reuseFailAlloc_371_; 
v_reuseFailAlloc_371_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_371_, 0, v_x_341_);
lean_ctor_set(v_reuseFailAlloc_371_, 1, v_x_342_);
v___x_370_ = v_reuseFailAlloc_371_;
goto v_reusejp_369_;
}
v_reusejp_369_:
{
v___y_356_ = v___x_370_;
goto v___jp_355_;
}
}
}
}
case 1:
{
lean_object* v_node_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_385_; 
v_node_373_ = lean_ctor_get(v_v_352_, 0);
v_isSharedCheck_385_ = !lean_is_exclusive(v_v_352_);
if (v_isSharedCheck_385_ == 0)
{
v___x_375_ = v_v_352_;
v_isShared_376_ = v_isSharedCheck_385_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_node_373_);
lean_dec(v_v_352_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_385_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
size_t v___x_377_; size_t v___x_378_; size_t v___x_379_; size_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_377_ = ((size_t)5ULL);
v___x_378_ = lean_usize_shift_right(v_x_339_, v___x_377_);
v___x_379_ = ((size_t)1ULL);
v___x_380_ = lean_usize_add(v_x_340_, v___x_379_);
v___x_381_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_node_373_, v___x_378_, v___x_380_, v_x_341_, v_x_342_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 0, v___x_381_);
v___x_383_ = v___x_375_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
v___y_356_ = v___x_383_;
goto v___jp_355_;
}
}
}
default: 
{
lean_object* v___x_386_; 
v___x_386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_386_, 0, v_x_341_);
lean_ctor_set(v___x_386_, 1, v_x_342_);
v___y_356_ = v___x_386_;
goto v___jp_355_;
}
}
v___jp_355_:
{
lean_object* v___x_357_; lean_object* v___x_359_; 
v___x_357_ = lean_array_fset(v_xs_x27_354_, v_j_346_, v___y_356_);
lean_dec(v_j_346_);
if (v_isShared_351_ == 0)
{
lean_ctor_set(v___x_350_, 0, v___x_357_);
v___x_359_ = v___x_350_;
goto v_reusejp_358_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v___x_357_);
v___x_359_ = v_reuseFailAlloc_360_;
goto v_reusejp_358_;
}
v_reusejp_358_:
{
return v___x_359_;
}
}
}
}
}
else
{
lean_object* v_ks_389_; lean_object* v_vs_390_; lean_object* v___x_392_; uint8_t v_isShared_393_; uint8_t v_isSharedCheck_408_; 
v_ks_389_ = lean_ctor_get(v_x_338_, 0);
v_vs_390_ = lean_ctor_get(v_x_338_, 1);
v_isSharedCheck_408_ = !lean_is_exclusive(v_x_338_);
if (v_isSharedCheck_408_ == 0)
{
v___x_392_ = v_x_338_;
v_isShared_393_ = v_isSharedCheck_408_;
goto v_resetjp_391_;
}
else
{
lean_inc(v_vs_390_);
lean_inc(v_ks_389_);
lean_dec(v_x_338_);
v___x_392_ = lean_box(0);
v_isShared_393_ = v_isSharedCheck_408_;
goto v_resetjp_391_;
}
v_resetjp_391_:
{
lean_object* v___x_395_; 
if (v_isShared_393_ == 0)
{
v___x_395_ = v___x_392_;
goto v_reusejp_394_;
}
else
{
lean_object* v_reuseFailAlloc_407_; 
v_reuseFailAlloc_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_407_, 0, v_ks_389_);
lean_ctor_set(v_reuseFailAlloc_407_, 1, v_vs_390_);
v___x_395_ = v_reuseFailAlloc_407_;
goto v_reusejp_394_;
}
v_reusejp_394_:
{
lean_object* v_newNode_396_; size_t v___x_397_; uint8_t v___x_398_; 
v_newNode_396_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(v___x_395_, v_x_341_, v_x_342_);
v___x_397_ = ((size_t)7ULL);
v___x_398_ = lean_usize_dec_le(v___x_397_, v_x_340_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v___x_400_; uint8_t v___x_401_; 
v___x_399_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_396_);
v___x_400_ = lean_unsigned_to_nat(4u);
v___x_401_ = lean_nat_dec_lt(v___x_399_, v___x_400_);
lean_dec(v___x_399_);
if (v___x_401_ == 0)
{
lean_object* v_ks_402_; lean_object* v_vs_403_; lean_object* v___x_404_; lean_object* v___x_405_; lean_object* v___x_406_; 
v_ks_402_ = lean_ctor_get(v_newNode_396_, 0);
lean_inc_ref(v_ks_402_);
v_vs_403_ = lean_ctor_get(v_newNode_396_, 1);
lean_inc_ref(v_vs_403_);
lean_dec_ref(v_newNode_396_);
v___x_404_ = lean_unsigned_to_nat(0u);
v___x_405_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0);
v___x_406_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(v_x_340_, v_ks_402_, v_vs_403_, v___x_404_, v___x_405_);
lean_dec_ref(v_vs_403_);
lean_dec_ref(v_ks_402_);
return v___x_406_;
}
else
{
return v_newNode_396_;
}
}
else
{
return v_newNode_396_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(size_t v_depth_409_, lean_object* v_keys_410_, lean_object* v_vals_411_, lean_object* v_i_412_, lean_object* v_entries_413_){
_start:
{
lean_object* v___x_414_; uint8_t v___x_415_; 
v___x_414_ = lean_array_get_size(v_keys_410_);
v___x_415_ = lean_nat_dec_lt(v_i_412_, v___x_414_);
if (v___x_415_ == 0)
{
lean_dec(v_i_412_);
return v_entries_413_;
}
else
{
lean_object* v_k_416_; lean_object* v_v_417_; uint64_t v___x_418_; size_t v_h_419_; size_t v___x_420_; lean_object* v___x_421_; size_t v___x_422_; size_t v___x_423_; size_t v___x_424_; size_t v_h_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v_k_416_ = lean_array_fget_borrowed(v_keys_410_, v_i_412_);
v_v_417_ = lean_array_fget_borrowed(v_vals_411_, v_i_412_);
v___x_418_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_416_);
v_h_419_ = lean_uint64_to_usize(v___x_418_);
v___x_420_ = ((size_t)5ULL);
v___x_421_ = lean_unsigned_to_nat(1u);
v___x_422_ = ((size_t)1ULL);
v___x_423_ = lean_usize_sub(v_depth_409_, v___x_422_);
v___x_424_ = lean_usize_mul(v___x_420_, v___x_423_);
v_h_425_ = lean_usize_shift_right(v_h_419_, v___x_424_);
v___x_426_ = lean_nat_add(v_i_412_, v___x_421_);
lean_dec(v_i_412_);
lean_inc(v_v_417_);
lean_inc(v_k_416_);
v___x_427_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_entries_413_, v_h_425_, v_depth_409_, v_k_416_, v_v_417_);
v_i_412_ = v___x_426_;
v_entries_413_ = v___x_427_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg___boxed(lean_object* v_depth_429_, lean_object* v_keys_430_, lean_object* v_vals_431_, lean_object* v_i_432_, lean_object* v_entries_433_){
_start:
{
size_t v_depth_boxed_434_; lean_object* v_res_435_; 
v_depth_boxed_434_ = lean_unbox_usize(v_depth_429_);
lean_dec(v_depth_429_);
v_res_435_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(v_depth_boxed_434_, v_keys_430_, v_vals_431_, v_i_432_, v_entries_433_);
lean_dec_ref(v_vals_431_);
lean_dec_ref(v_keys_430_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_x_436_, lean_object* v_x_437_, lean_object* v_x_438_, lean_object* v_x_439_, lean_object* v_x_440_){
_start:
{
size_t v_x_2368__boxed_441_; size_t v_x_2369__boxed_442_; lean_object* v_res_443_; 
v_x_2368__boxed_441_ = lean_unbox_usize(v_x_437_);
lean_dec(v_x_437_);
v_x_2369__boxed_442_ = lean_unbox_usize(v_x_438_);
lean_dec(v_x_438_);
v_res_443_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_x_436_, v_x_2368__boxed_441_, v_x_2369__boxed_442_, v_x_439_, v_x_440_);
return v_res_443_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(lean_object* v_x_444_, lean_object* v_keys_445_, lean_object* v_v_446_, lean_object* v_k_447_, lean_object* v_x_448_){
_start:
{
lean_object* v___x_449_; lean_object* v___x_450_; lean_object* v_c_451_; lean_object* v___x_452_; 
v___x_449_ = lean_unsigned_to_nat(1u);
v___x_450_ = lean_nat_add(v_x_444_, v___x_449_);
v_c_451_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_445_, v_v_446_, v___x_450_);
lean_dec(v___x_450_);
v___x_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_452_, 0, v_k_447_);
lean_ctor_set(v___x_452_, 1, v_c_451_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* v_x_453_, lean_object* v_keys_454_, lean_object* v_v_455_, lean_object* v_k_456_, lean_object* v_x_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_453_, v_keys_454_, v_v_455_, v_k_456_, v_x_457_);
lean_dec_ref(v_keys_454_);
lean_dec(v_x_453_);
return v_res_458_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(lean_object* v_a_459_, lean_object* v_b_460_){
_start:
{
lean_object* v_fst_461_; lean_object* v_fst_462_; uint8_t v___x_463_; 
v_fst_461_ = lean_ctor_get(v_a_459_, 0);
v_fst_462_ = lean_ctor_get(v_b_460_, 0);
v___x_463_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_461_, v_fst_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1___boxed(lean_object* v_a_464_, lean_object* v_b_465_){
_start:
{
uint8_t v_res_466_; lean_object* v_r_467_; 
v_res_466_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_a_464_, v_b_465_);
lean_dec_ref(v_b_465_);
lean_dec_ref(v_a_464_);
v_r_467_ = lean_box(v_res_466_);
return v_r_467_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(lean_object* v_vs_468_, lean_object* v_v_469_, lean_object* v_i_470_){
_start:
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = lean_array_get_size(v_vs_468_);
v___x_472_ = lean_nat_dec_lt(v_i_470_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; 
lean_dec(v_i_470_);
v___x_473_ = lean_array_push(v_vs_468_, v_v_469_);
return v___x_473_;
}
else
{
lean_object* v_val_474_; lean_object* v___x_475_; lean_object* v_val_476_; uint8_t v___x_477_; 
v_val_474_ = lean_ctor_get(v_v_469_, 1);
v___x_475_ = lean_array_fget_borrowed(v_vs_468_, v_i_470_);
v_val_476_ = lean_ctor_get(v___x_475_, 1);
v___x_477_ = lean_expr_eqv(v_val_474_, v_val_476_);
if (v___x_477_ == 0)
{
lean_object* v___x_478_; lean_object* v___x_479_; 
v___x_478_ = lean_unsigned_to_nat(1u);
v___x_479_ = lean_nat_add(v_i_470_, v___x_478_);
lean_dec(v_i_470_);
v_i_470_ = v___x_479_;
goto _start;
}
else
{
lean_object* v___x_481_; 
v___x_481_ = lean_array_fset(v_vs_468_, v_i_470_, v_v_469_);
lean_dec(v_i_470_);
return v___x_481_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(lean_object* v_vs_482_, lean_object* v_v_483_){
_start:
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(0u);
v___x_485_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(v_vs_482_, v_v_483_, v___x_484_);
return v___x_485_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_x_490_, lean_object* v_keys_491_, lean_object* v_v_492_, lean_object* v_k_493_, lean_object* v_as_494_, lean_object* v_k_495_, lean_object* v_x_496_, lean_object* v_x_497_){
_start:
{
lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v_mid_500_; lean_object* v_midVal_501_; uint8_t v___x_502_; 
v___x_498_ = lean_nat_add(v_x_496_, v_x_497_);
v___x_499_ = lean_unsigned_to_nat(1u);
v_mid_500_ = lean_nat_shiftr(v___x_498_, v___x_499_);
lean_dec(v___x_498_);
v_midVal_501_ = lean_array_fget(v_as_494_, v_mid_500_);
v___x_502_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_midVal_501_, v_k_495_);
if (v___x_502_ == 0)
{
uint8_t v___x_503_; 
lean_dec(v_x_497_);
v___x_503_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_495_, v_midVal_501_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; uint8_t v___x_505_; 
lean_dec(v_x_496_);
v___x_504_ = lean_array_get_size(v_as_494_);
v___x_505_ = lean_nat_dec_lt(v_mid_500_, v___x_504_);
if (v___x_505_ == 0)
{
lean_dec(v_midVal_501_);
lean_dec(v_mid_500_);
lean_dec(v_k_493_);
lean_dec_ref(v_v_492_);
return v_as_494_;
}
else
{
lean_object* v_snd_506_; lean_object* v___x_508_; uint8_t v_isShared_509_; uint8_t v_isSharedCheck_518_; 
v_snd_506_ = lean_ctor_get(v_midVal_501_, 1);
v_isSharedCheck_518_ = !lean_is_exclusive(v_midVal_501_);
if (v_isSharedCheck_518_ == 0)
{
lean_object* v_unused_519_; 
v_unused_519_ = lean_ctor_get(v_midVal_501_, 0);
lean_dec(v_unused_519_);
v___x_508_ = v_midVal_501_;
v_isShared_509_ = v_isSharedCheck_518_;
goto v_resetjp_507_;
}
else
{
lean_inc(v_snd_506_);
lean_dec(v_midVal_501_);
v___x_508_ = lean_box(0);
v_isShared_509_ = v_isSharedCheck_518_;
goto v_resetjp_507_;
}
v_resetjp_507_:
{
lean_object* v___x_510_; lean_object* v_xs_x27_511_; lean_object* v___x_512_; lean_object* v_c_513_; lean_object* v___x_515_; 
v___x_510_ = lean_box(0);
v_xs_x27_511_ = lean_array_fset(v_as_494_, v_mid_500_, v___x_510_);
v___x_512_ = lean_nat_add(v_x_490_, v___x_499_);
v_c_513_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_491_, v_v_492_, v___x_512_, v_snd_506_);
lean_dec(v___x_512_);
if (v_isShared_509_ == 0)
{
lean_ctor_set(v___x_508_, 1, v_c_513_);
lean_ctor_set(v___x_508_, 0, v_k_493_);
v___x_515_ = v___x_508_;
goto v_reusejp_514_;
}
else
{
lean_object* v_reuseFailAlloc_517_; 
v_reuseFailAlloc_517_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_517_, 0, v_k_493_);
lean_ctor_set(v_reuseFailAlloc_517_, 1, v_c_513_);
v___x_515_ = v_reuseFailAlloc_517_;
goto v_reusejp_514_;
}
v_reusejp_514_:
{
lean_object* v___x_516_; 
v___x_516_ = lean_array_fset(v_xs_x27_511_, v_mid_500_, v___x_515_);
lean_dec(v_mid_500_);
return v___x_516_;
}
}
}
}
else
{
lean_dec(v_midVal_501_);
v_x_497_ = v_mid_500_;
goto _start;
}
}
else
{
uint8_t v___x_521_; 
lean_dec(v_midVal_501_);
v___x_521_ = lean_nat_dec_eq(v_mid_500_, v_x_496_);
if (v___x_521_ == 0)
{
lean_dec(v_x_496_);
v_x_496_ = v_mid_500_;
goto _start;
}
else
{
lean_object* v___x_523_; lean_object* v_c_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v_j_527_; lean_object* v_as_528_; lean_object* v___x_529_; 
lean_dec(v_mid_500_);
lean_dec(v_x_497_);
v___x_523_ = lean_nat_add(v_x_490_, v___x_499_);
v_c_524_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_491_, v_v_492_, v___x_523_);
lean_dec(v___x_523_);
v___x_525_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_525_, 0, v_k_493_);
lean_ctor_set(v___x_525_, 1, v_c_524_);
v___x_526_ = lean_nat_add(v_x_496_, v___x_499_);
lean_dec(v_x_496_);
v_j_527_ = lean_array_get_size(v_as_494_);
v_as_528_ = lean_array_push(v_as_494_, v___x_525_);
v___x_529_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_526_, v_as_528_, v_j_527_);
lean_dec(v___x_526_);
return v___x_529_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(lean_object* v_x_530_, lean_object* v_keys_531_, lean_object* v_v_532_, lean_object* v_k_533_, lean_object* v_as_534_, lean_object* v_k_535_){
_start:
{
lean_object* v___x_536_; lean_object* v___x_537_; uint8_t v___x_538_; 
v___x_536_ = lean_array_get_size(v_as_534_);
v___x_537_ = lean_unsigned_to_nat(0u);
v___x_538_ = lean_nat_dec_eq(v___x_536_, v___x_537_);
if (v___x_538_ == 0)
{
lean_object* v___x_539_; uint8_t v___x_540_; 
v___x_539_ = lean_array_fget_borrowed(v_as_534_, v___x_537_);
v___x_540_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_535_, v___x_539_);
if (v___x_540_ == 0)
{
uint8_t v___x_541_; 
v___x_541_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v___x_539_, v_k_535_);
if (v___x_541_ == 0)
{
uint8_t v___x_542_; 
v___x_542_ = lean_nat_dec_lt(v___x_537_, v___x_536_);
if (v___x_542_ == 0)
{
lean_dec(v_k_533_);
lean_dec_ref(v_v_532_);
return v_as_534_;
}
else
{
lean_object* v___x_543_; lean_object* v_xs_x27_544_; lean_object* v___x_545_; lean_object* v___x_546_; 
lean_inc(v___x_539_);
v___x_543_ = lean_box(0);
v_xs_x27_544_ = lean_array_fset(v_as_534_, v___x_537_, v___x_543_);
v___x_545_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_530_, v_keys_531_, v_v_532_, v_k_533_, v___x_539_);
v___x_546_ = lean_array_fset(v_xs_x27_544_, v___x_537_, v___x_545_);
return v___x_546_;
}
}
else
{
lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; uint8_t v___x_550_; 
v___x_547_ = lean_unsigned_to_nat(1u);
v___x_548_ = lean_nat_sub(v___x_536_, v___x_547_);
v___x_549_ = lean_array_fget_borrowed(v_as_534_, v___x_548_);
v___x_550_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v___x_549_, v_k_535_);
if (v___x_550_ == 0)
{
uint8_t v___x_551_; 
v___x_551_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_535_, v___x_549_);
if (v___x_551_ == 0)
{
uint8_t v___x_552_; 
v___x_552_ = lean_nat_dec_lt(v___x_548_, v___x_536_);
if (v___x_552_ == 0)
{
lean_dec(v___x_548_);
lean_dec(v_k_533_);
lean_dec_ref(v_v_532_);
return v_as_534_;
}
else
{
lean_object* v___x_553_; lean_object* v_xs_x27_554_; lean_object* v___x_555_; lean_object* v___x_556_; 
lean_inc(v___x_549_);
v___x_553_ = lean_box(0);
v_xs_x27_554_ = lean_array_fset(v_as_534_, v___x_548_, v___x_553_);
v___x_555_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_530_, v_keys_531_, v_v_532_, v_k_533_, v___x_549_);
v___x_556_ = lean_array_fset(v_xs_x27_554_, v___x_548_, v___x_555_);
lean_dec(v___x_548_);
return v___x_556_;
}
}
else
{
lean_object* v___x_557_; 
v___x_557_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_530_, v_keys_531_, v_v_532_, v_k_533_, v_as_534_, v_k_535_, v___x_537_, v___x_548_);
return v___x_557_;
}
}
else
{
lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_dec(v___x_548_);
v___x_558_ = lean_box(0);
v___x_559_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_530_, v_keys_531_, v_v_532_, v_k_533_, v___x_558_);
v___x_560_ = lean_array_push(v_as_534_, v___x_559_);
return v___x_560_;
}
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v_as_563_; lean_object* v___x_564_; 
v___x_561_ = lean_box(0);
v___x_562_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_530_, v_keys_531_, v_v_532_, v_k_533_, v___x_561_);
v_as_563_ = lean_array_push(v_as_534_, v___x_562_);
v___x_564_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_537_, v_as_563_, v___x_536_);
return v___x_564_;
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = lean_box(0);
v___x_566_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_530_, v_keys_531_, v_v_532_, v_k_533_, v___x_565_);
v___x_567_ = lean_array_push(v_as_534_, v___x_566_);
return v___x_567_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object* v_keys_568_, lean_object* v_v_569_, lean_object* v_x_570_, lean_object* v_x_571_){
_start:
{
lean_object* v_vs_572_; lean_object* v_children_573_; lean_object* v___x_575_; uint8_t v_isShared_576_; uint8_t v_isSharedCheck_590_; 
v_vs_572_ = lean_ctor_get(v_x_571_, 0);
v_children_573_ = lean_ctor_get(v_x_571_, 1);
v_isSharedCheck_590_ = !lean_is_exclusive(v_x_571_);
if (v_isSharedCheck_590_ == 0)
{
v___x_575_ = v_x_571_;
v_isShared_576_ = v_isSharedCheck_590_;
goto v_resetjp_574_;
}
else
{
lean_inc(v_children_573_);
lean_inc(v_vs_572_);
lean_dec(v_x_571_);
v___x_575_ = lean_box(0);
v_isShared_576_ = v_isSharedCheck_590_;
goto v_resetjp_574_;
}
v_resetjp_574_:
{
lean_object* v___x_577_; uint8_t v___x_578_; 
v___x_577_ = lean_array_get_size(v_keys_568_);
v___x_578_ = lean_nat_dec_lt(v_x_570_, v___x_577_);
if (v___x_578_ == 0)
{
lean_object* v___x_579_; lean_object* v___x_581_; 
v___x_579_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(v_vs_572_, v_v_569_);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 0, v___x_579_);
v___x_581_ = v___x_575_;
goto v_reusejp_580_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v___x_579_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_children_573_);
v___x_581_ = v_reuseFailAlloc_582_;
goto v_reusejp_580_;
}
v_reusejp_580_:
{
return v___x_581_;
}
}
else
{
lean_object* v_k_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v_c_586_; lean_object* v___x_588_; 
v_k_583_ = lean_array_fget_borrowed(v_keys_568_, v_x_570_);
v___x_584_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__1));
lean_inc_n(v_k_583_, 2);
v___x_585_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_585_, 0, v_k_583_);
lean_ctor_set(v___x_585_, 1, v___x_584_);
v_c_586_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(v_x_570_, v_keys_568_, v_v_569_, v_k_583_, v_children_573_, v___x_585_);
lean_dec_ref_known(v___x_585_, 2);
if (v_isShared_576_ == 0)
{
lean_ctor_set(v___x_575_, 1, v_c_586_);
v___x_588_ = v___x_575_;
goto v_reusejp_587_;
}
else
{
lean_object* v_reuseFailAlloc_589_; 
v_reuseFailAlloc_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_589_, 0, v_vs_572_);
lean_ctor_set(v_reuseFailAlloc_589_, 1, v_c_586_);
v___x_588_ = v_reuseFailAlloc_589_;
goto v_reusejp_587_;
}
v_reusejp_587_:
{
return v___x_588_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(lean_object* v_x_591_, lean_object* v_keys_592_, lean_object* v_v_593_, lean_object* v_k_594_, lean_object* v_x_595_){
_start:
{
lean_object* v_snd_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_606_; 
v_snd_596_ = lean_ctor_get(v_x_595_, 1);
v_isSharedCheck_606_ = !lean_is_exclusive(v_x_595_);
if (v_isSharedCheck_606_ == 0)
{
lean_object* v_unused_607_; 
v_unused_607_ = lean_ctor_get(v_x_595_, 0);
lean_dec(v_unused_607_);
v___x_598_ = v_x_595_;
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_snd_596_);
lean_dec(v_x_595_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_606_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v_c_602_; lean_object* v___x_604_; 
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = lean_nat_add(v_x_591_, v___x_600_);
v_c_602_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_592_, v_v_593_, v___x_601_, v_snd_596_);
lean_dec(v___x_601_);
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v_c_602_);
lean_ctor_set(v___x_598_, 0, v_k_594_);
v___x_604_ = v___x_598_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_605_; 
v_reuseFailAlloc_605_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_605_, 0, v_k_594_);
lean_ctor_set(v_reuseFailAlloc_605_, 1, v_c_602_);
v___x_604_ = v_reuseFailAlloc_605_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
return v___x_604_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* v_x_608_, lean_object* v_keys_609_, lean_object* v_v_610_, lean_object* v_k_611_, lean_object* v_x_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_608_, v_keys_609_, v_v_610_, v_k_611_, v_x_612_);
lean_dec_ref(v_keys_609_);
lean_dec(v_x_608_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object* v_keys_614_, lean_object* v_v_615_, lean_object* v_x_616_, lean_object* v_x_617_){
_start:
{
lean_object* v_res_618_; 
v_res_618_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_614_, v_v_615_, v_x_616_, v_x_617_);
lean_dec(v_x_616_);
lean_dec_ref(v_keys_614_);
return v_res_618_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_x_619_, lean_object* v_keys_620_, lean_object* v_v_621_, lean_object* v_k_622_, lean_object* v_as_623_, lean_object* v_k_624_, lean_object* v_x_625_, lean_object* v_x_626_){
_start:
{
lean_object* v_res_627_; 
v_res_627_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_619_, v_keys_620_, v_v_621_, v_k_622_, v_as_623_, v_k_624_, v_x_625_, v_x_626_);
lean_dec_ref(v_k_624_);
lean_dec_ref(v_keys_620_);
lean_dec(v_x_619_);
return v_res_627_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_x_628_, lean_object* v_keys_629_, lean_object* v_v_630_, lean_object* v_k_631_, lean_object* v_as_632_, lean_object* v_k_633_){
_start:
{
lean_object* v_res_634_; 
v_res_634_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(v_x_628_, v_keys_629_, v_v_630_, v_k_631_, v_as_632_, v_k_633_);
lean_dec_ref(v_k_633_);
lean_dec_ref(v_keys_629_);
lean_dec(v_x_628_);
return v_res_634_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(lean_object* v_keys_635_, lean_object* v_v_636_, lean_object* v_x_637_){
_start:
{
if (lean_obj_tag(v_x_637_) == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; 
v___x_638_ = lean_unsigned_to_nat(1u);
v___x_639_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_635_, v_v_636_, v___x_638_);
v___x_640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_640_, 0, v___x_639_);
return v___x_640_;
}
else
{
lean_object* v_val_641_; lean_object* v___x_643_; uint8_t v_isShared_644_; uint8_t v_isSharedCheck_650_; 
v_val_641_ = lean_ctor_get(v_x_637_, 0);
v_isSharedCheck_650_ = !lean_is_exclusive(v_x_637_);
if (v_isSharedCheck_650_ == 0)
{
v___x_643_ = v_x_637_;
v_isShared_644_ = v_isSharedCheck_650_;
goto v_resetjp_642_;
}
else
{
lean_inc(v_val_641_);
lean_dec(v_x_637_);
v___x_643_ = lean_box(0);
v_isShared_644_ = v_isSharedCheck_650_;
goto v_resetjp_642_;
}
v_resetjp_642_:
{
lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_648_; 
v___x_645_ = lean_unsigned_to_nat(1u);
v___x_646_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_635_, v_v_636_, v___x_645_, v_val_641_);
if (v_isShared_644_ == 0)
{
lean_ctor_set(v___x_643_, 0, v___x_646_);
v___x_648_ = v___x_643_;
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
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0___boxed(lean_object* v_keys_651_, lean_object* v_v_652_, lean_object* v_x_653_){
_start:
{
lean_object* v_res_654_; 
v_res_654_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_651_, v_v_652_, v_x_653_);
lean_dec_ref(v_keys_651_);
return v_res_654_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(lean_object* v_keys_655_, lean_object* v_v_656_, lean_object* v_x_657_, size_t v_x_658_, size_t v_x_659_, lean_object* v_x_660_){
_start:
{
if (lean_obj_tag(v_x_657_) == 0)
{
lean_object* v_es_661_; size_t v___x_662_; size_t v___x_663_; lean_object* v_j_664_; lean_object* v___x_665_; uint8_t v___x_666_; 
v_es_661_ = lean_ctor_get(v_x_657_, 0);
v___x_662_ = ((size_t)31ULL);
v___x_663_ = lean_usize_land(v_x_658_, v___x_662_);
v_j_664_ = lean_usize_to_nat(v___x_663_);
v___x_665_ = lean_array_get_size(v_es_661_);
v___x_666_ = lean_nat_dec_lt(v_j_664_, v___x_665_);
if (v___x_666_ == 0)
{
lean_dec(v_j_664_);
lean_dec(v_x_660_);
lean_dec_ref(v_v_656_);
return v_x_657_;
}
else
{
lean_object* v___x_668_; uint8_t v_isShared_669_; uint8_t v_isSharedCheck_734_; 
lean_inc_ref(v_es_661_);
v_isSharedCheck_734_ = !lean_is_exclusive(v_x_657_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v_x_657_, 0);
lean_dec(v_unused_735_);
v___x_668_ = v_x_657_;
v_isShared_669_ = v_isSharedCheck_734_;
goto v_resetjp_667_;
}
else
{
lean_dec(v_x_657_);
v___x_668_ = lean_box(0);
v_isShared_669_ = v_isSharedCheck_734_;
goto v_resetjp_667_;
}
v_resetjp_667_:
{
lean_object* v_v_670_; lean_object* v___x_671_; lean_object* v_xs_x27_672_; lean_object* v___y_674_; 
v_v_670_ = lean_array_fget(v_es_661_, v_j_664_);
v___x_671_ = lean_box(0);
v_xs_x27_672_ = lean_array_fset(v_es_661_, v_j_664_, v___x_671_);
switch(lean_obj_tag(v_v_670_))
{
case 0:
{
lean_object* v_key_679_; lean_object* v_val_680_; uint8_t v___x_681_; 
v_key_679_ = lean_ctor_get(v_v_670_, 0);
v_val_680_ = lean_ctor_get(v_v_670_, 1);
v___x_681_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_660_, v_key_679_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; lean_object* v___x_683_; 
v___x_682_ = lean_box(0);
v___x_683_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_655_, v_v_656_, v___x_682_);
if (lean_obj_tag(v___x_683_) == 0)
{
lean_dec(v_x_660_);
v___y_674_ = v_v_670_;
goto v___jp_673_;
}
else
{
lean_object* v_val_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_692_; 
lean_inc(v_val_680_);
lean_inc(v_key_679_);
lean_dec_ref_known(v_v_670_, 2);
v_val_684_ = lean_ctor_get(v___x_683_, 0);
v_isSharedCheck_692_ = !lean_is_exclusive(v___x_683_);
if (v_isSharedCheck_692_ == 0)
{
v___x_686_ = v___x_683_;
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_val_684_);
lean_dec(v___x_683_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_692_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
v___x_688_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_679_, v_val_680_, v_x_660_, v_val_684_);
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 0, v___x_688_);
v___x_690_ = v___x_686_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_691_; 
v_reuseFailAlloc_691_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_691_, 0, v___x_688_);
v___x_690_ = v_reuseFailAlloc_691_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
v___y_674_ = v___x_690_;
goto v___jp_673_;
}
}
}
}
else
{
lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_703_; 
lean_inc(v_val_680_);
v_isSharedCheck_703_ = !lean_is_exclusive(v_v_670_);
if (v_isSharedCheck_703_ == 0)
{
lean_object* v_unused_704_; lean_object* v_unused_705_; 
v_unused_704_ = lean_ctor_get(v_v_670_, 1);
lean_dec(v_unused_704_);
v_unused_705_ = lean_ctor_get(v_v_670_, 0);
lean_dec(v_unused_705_);
v___x_694_ = v_v_670_;
v_isShared_695_ = v_isSharedCheck_703_;
goto v_resetjp_693_;
}
else
{
lean_dec(v_v_670_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_703_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_696_, 0, v_val_680_);
v___x_697_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_655_, v_v_656_, v___x_696_);
if (lean_obj_tag(v___x_697_) == 0)
{
lean_object* v___x_698_; 
lean_del_object(v___x_694_);
lean_dec(v_x_660_);
v___x_698_ = lean_box(2);
v___y_674_ = v___x_698_;
goto v___jp_673_;
}
else
{
lean_object* v_val_699_; lean_object* v___x_701_; 
v_val_699_ = lean_ctor_get(v___x_697_, 0);
lean_inc(v_val_699_);
lean_dec_ref_known(v___x_697_, 1);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 1, v_val_699_);
lean_ctor_set(v___x_694_, 0, v_x_660_);
v___x_701_ = v___x_694_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_702_; 
v_reuseFailAlloc_702_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_702_, 0, v_x_660_);
lean_ctor_set(v_reuseFailAlloc_702_, 1, v_val_699_);
v___x_701_ = v_reuseFailAlloc_702_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
v___y_674_ = v___x_701_;
goto v___jp_673_;
}
}
}
}
}
case 1:
{
lean_object* v_node_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_729_; 
v_node_706_ = lean_ctor_get(v_v_670_, 0);
v_isSharedCheck_729_ = !lean_is_exclusive(v_v_670_);
if (v_isSharedCheck_729_ == 0)
{
v___x_708_ = v_v_670_;
v_isShared_709_ = v_isSharedCheck_729_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_node_706_);
lean_dec(v_v_670_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_729_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
size_t v___x_710_; size_t v___x_711_; size_t v___x_712_; size_t v___x_713_; lean_object* v_newNode_714_; lean_object* v___x_715_; 
v___x_710_ = ((size_t)5ULL);
v___x_711_ = lean_usize_shift_right(v_x_658_, v___x_710_);
v___x_712_ = ((size_t)1ULL);
v___x_713_ = lean_usize_add(v_x_659_, v___x_712_);
v_newNode_714_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_655_, v_v_656_, v_node_706_, v___x_711_, v___x_713_, v_x_660_);
lean_inc_ref(v_newNode_714_);
v___x_715_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_714_);
if (lean_obj_tag(v___x_715_) == 0)
{
lean_object* v___x_717_; 
if (v_isShared_709_ == 0)
{
lean_ctor_set(v___x_708_, 0, v_newNode_714_);
v___x_717_ = v___x_708_;
goto v_reusejp_716_;
}
else
{
lean_object* v_reuseFailAlloc_718_; 
v_reuseFailAlloc_718_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_718_, 0, v_newNode_714_);
v___x_717_ = v_reuseFailAlloc_718_;
goto v_reusejp_716_;
}
v_reusejp_716_:
{
v___y_674_ = v___x_717_;
goto v___jp_673_;
}
}
else
{
lean_object* v_val_719_; lean_object* v_fst_720_; lean_object* v_snd_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_728_; 
lean_dec_ref(v_newNode_714_);
lean_del_object(v___x_708_);
v_val_719_ = lean_ctor_get(v___x_715_, 0);
lean_inc(v_val_719_);
lean_dec_ref_known(v___x_715_, 1);
v_fst_720_ = lean_ctor_get(v_val_719_, 0);
v_snd_721_ = lean_ctor_get(v_val_719_, 1);
v_isSharedCheck_728_ = !lean_is_exclusive(v_val_719_);
if (v_isSharedCheck_728_ == 0)
{
v___x_723_ = v_val_719_;
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_snd_721_);
lean_inc(v_fst_720_);
lean_dec(v_val_719_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_728_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_726_; 
if (v_isShared_724_ == 0)
{
v___x_726_ = v___x_723_;
goto v_reusejp_725_;
}
else
{
lean_object* v_reuseFailAlloc_727_; 
v_reuseFailAlloc_727_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_727_, 0, v_fst_720_);
lean_ctor_set(v_reuseFailAlloc_727_, 1, v_snd_721_);
v___x_726_ = v_reuseFailAlloc_727_;
goto v_reusejp_725_;
}
v_reusejp_725_:
{
v___y_674_ = v___x_726_;
goto v___jp_673_;
}
}
}
}
}
default: 
{
lean_object* v___x_730_; lean_object* v___x_731_; 
v___x_730_ = lean_box(0);
v___x_731_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_655_, v_v_656_, v___x_730_);
if (lean_obj_tag(v___x_731_) == 0)
{
lean_dec(v_x_660_);
v___y_674_ = v_v_670_;
goto v___jp_673_;
}
else
{
lean_object* v_val_732_; lean_object* v___x_733_; 
v_val_732_ = lean_ctor_get(v___x_731_, 0);
lean_inc(v_val_732_);
lean_dec_ref_known(v___x_731_, 1);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v_x_660_);
lean_ctor_set(v___x_733_, 1, v_val_732_);
v___y_674_ = v___x_733_;
goto v___jp_673_;
}
}
}
v___jp_673_:
{
lean_object* v___x_675_; lean_object* v___x_677_; 
v___x_675_ = lean_array_fset(v_xs_x27_672_, v_j_664_, v___y_674_);
lean_dec(v_j_664_);
if (v_isShared_669_ == 0)
{
lean_ctor_set(v___x_668_, 0, v___x_675_);
v___x_677_ = v___x_668_;
goto v_reusejp_676_;
}
else
{
lean_object* v_reuseFailAlloc_678_; 
v_reuseFailAlloc_678_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_678_, 0, v___x_675_);
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
}
else
{
lean_object* v_ks_736_; lean_object* v_vs_737_; lean_object* v___x_739_; uint8_t v_isShared_740_; uint8_t v_isSharedCheck_770_; 
v_ks_736_ = lean_ctor_get(v_x_657_, 0);
v_vs_737_ = lean_ctor_get(v_x_657_, 1);
v_isSharedCheck_770_ = !lean_is_exclusive(v_x_657_);
if (v_isSharedCheck_770_ == 0)
{
v___x_739_ = v_x_657_;
v_isShared_740_ = v_isSharedCheck_770_;
goto v_resetjp_738_;
}
else
{
lean_inc(v_vs_737_);
lean_inc(v_ks_736_);
lean_dec(v_x_657_);
v___x_739_ = lean_box(0);
v_isShared_740_ = v_isSharedCheck_770_;
goto v_resetjp_738_;
}
v_resetjp_738_:
{
lean_object* v___x_741_; 
v___x_741_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(v_ks_736_, v_x_660_);
if (lean_obj_tag(v___x_741_) == 0)
{
lean_object* v___x_743_; 
if (v_isShared_740_ == 0)
{
v___x_743_ = v___x_739_;
goto v_reusejp_742_;
}
else
{
lean_object* v_reuseFailAlloc_748_; 
v_reuseFailAlloc_748_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_748_, 0, v_ks_736_);
lean_ctor_set(v_reuseFailAlloc_748_, 1, v_vs_737_);
v___x_743_ = v_reuseFailAlloc_748_;
goto v_reusejp_742_;
}
v_reusejp_742_:
{
lean_object* v___x_744_; lean_object* v___x_745_; 
v___x_744_ = lean_box(0);
v___x_745_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_655_, v_v_656_, v___x_744_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_dec(v_x_660_);
return v___x_743_;
}
else
{
lean_object* v_val_746_; lean_object* v___x_747_; 
v_val_746_ = lean_ctor_get(v___x_745_, 0);
lean_inc(v_val_746_);
lean_dec_ref_known(v___x_745_, 1);
v___x_747_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v___x_743_, v_x_658_, v_x_659_, v_x_660_, v_val_746_);
return v___x_747_;
}
}
}
else
{
lean_object* v_val_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_769_; 
v_val_749_ = lean_ctor_get(v___x_741_, 0);
v_isSharedCheck_769_ = !lean_is_exclusive(v___x_741_);
if (v_isSharedCheck_769_ == 0)
{
v___x_751_ = v___x_741_;
v_isShared_752_ = v_isSharedCheck_769_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_val_749_);
lean_dec(v___x_741_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_769_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v_v_x27_753_; lean_object* v_keys_754_; lean_object* v_vals_755_; lean_object* v___x_757_; 
v_v_x27_753_ = lean_array_fget(v_vs_737_, v_val_749_);
lean_inc(v_val_749_);
v_keys_754_ = l_Array_eraseIdx___redArg(v_ks_736_, v_val_749_);
v_vals_755_ = l_Array_eraseIdx___redArg(v_vs_737_, v_val_749_);
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v_v_x27_753_);
v___x_757_ = v___x_751_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_768_; 
v_reuseFailAlloc_768_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_768_, 0, v_v_x27_753_);
v___x_757_ = v_reuseFailAlloc_768_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
lean_object* v___x_758_; 
v___x_758_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_655_, v_v_656_, v___x_757_);
if (lean_obj_tag(v___x_758_) == 0)
{
lean_object* v___x_760_; 
lean_dec(v_x_660_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v_vals_755_);
lean_ctor_set(v___x_739_, 0, v_keys_754_);
v___x_760_ = v___x_739_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v_keys_754_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_vals_755_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
else
{
lean_object* v_val_762_; lean_object* v_keys_763_; lean_object* v_vals_764_; lean_object* v___x_766_; 
v_val_762_ = lean_ctor_get(v___x_758_, 0);
lean_inc(v_val_762_);
lean_dec_ref_known(v___x_758_, 1);
v_keys_763_ = lean_array_push(v_keys_754_, v_x_660_);
v_vals_764_ = lean_array_push(v_vals_755_, v_val_762_);
if (v_isShared_740_ == 0)
{
lean_ctor_set(v___x_739_, 1, v_vals_764_);
lean_ctor_set(v___x_739_, 0, v_keys_763_);
v___x_766_ = v___x_739_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_keys_763_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_vals_764_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___boxed(lean_object* v_keys_771_, lean_object* v_v_772_, lean_object* v_x_773_, lean_object* v_x_774_, lean_object* v_x_775_, lean_object* v_x_776_){
_start:
{
size_t v_x_2789__boxed_777_; size_t v_x_2790__boxed_778_; lean_object* v_res_779_; 
v_x_2789__boxed_777_ = lean_unbox_usize(v_x_774_);
lean_dec(v_x_774_);
v_x_2790__boxed_778_ = lean_unbox_usize(v_x_775_);
lean_dec(v_x_775_);
v_res_779_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_771_, v_v_772_, v_x_773_, v_x_2789__boxed_777_, v_x_2790__boxed_778_, v_x_776_);
lean_dec_ref(v_keys_771_);
return v_res_779_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; 
v___x_783_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2));
v___x_784_ = lean_unsigned_to_nat(23u);
v___x_785_ = lean_unsigned_to_nat(166u);
v___x_786_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1));
v___x_787_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0));
v___x_788_ = l_mkPanicMessageWithDecl(v___x_787_, v___x_786_, v___x_785_, v___x_784_, v___x_783_);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(lean_object* v_d_789_, lean_object* v_keys_790_, lean_object* v_v_791_){
_start:
{
lean_object* v___x_792_; lean_object* v___x_793_; uint8_t v___x_794_; 
v___x_792_ = lean_array_get_size(v_keys_790_);
v___x_793_ = lean_unsigned_to_nat(0u);
v___x_794_ = lean_nat_dec_eq(v___x_792_, v___x_793_);
if (v___x_794_ == 0)
{
lean_object* v___x_795_; lean_object* v_k_796_; uint64_t v___x_797_; size_t v_h_798_; size_t v___x_799_; lean_object* v___x_800_; 
v___x_795_ = lean_box(0);
v_k_796_ = lean_array_get_borrowed(v___x_795_, v_keys_790_, v___x_793_);
v___x_797_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_796_);
v_h_798_ = lean_uint64_to_usize(v___x_797_);
v___x_799_ = ((size_t)1ULL);
lean_inc(v_k_796_);
v___x_800_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_790_, v_v_791_, v_d_789_, v_h_798_, v___x_799_, v_k_796_);
return v___x_800_;
}
else
{
lean_object* v___x_801_; lean_object* v___x_802_; 
lean_dec_ref(v_v_791_);
lean_dec_ref(v_d_789_);
v___x_801_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3);
v___x_802_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v___x_801_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___boxed(lean_object* v_d_803_, lean_object* v_keys_804_, lean_object* v_v_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_d_803_, v_keys_804_, v_v_805_);
lean_dec_ref(v_keys_804_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(lean_object* v_xs_807_, lean_object* v_v_808_, lean_object* v_i_809_){
_start:
{
lean_object* v___x_810_; uint8_t v___x_811_; 
v___x_810_ = lean_array_get_size(v_xs_807_);
v___x_811_ = lean_nat_dec_lt(v_i_809_, v___x_810_);
if (v___x_811_ == 0)
{
lean_object* v___x_812_; 
lean_dec(v_i_809_);
v___x_812_ = lean_box(0);
return v___x_812_;
}
else
{
lean_object* v___x_813_; uint8_t v___x_814_; 
v___x_813_ = lean_array_fget_borrowed(v_xs_807_, v_i_809_);
v___x_814_ = lean_name_eq(v___x_813_, v_v_808_);
if (v___x_814_ == 0)
{
lean_object* v___x_815_; lean_object* v___x_816_; 
v___x_815_ = lean_unsigned_to_nat(1u);
v___x_816_ = lean_nat_add(v_i_809_, v___x_815_);
lean_dec(v_i_809_);
v_i_809_ = v___x_816_;
goto _start;
}
else
{
lean_object* v___x_818_; 
v___x_818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_818_, 0, v_i_809_);
return v___x_818_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20___boxed(lean_object* v_xs_819_, lean_object* v_v_820_, lean_object* v_i_821_){
_start:
{
lean_object* v_res_822_; 
v_res_822_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(v_xs_819_, v_v_820_, v_i_821_);
lean_dec(v_v_820_);
lean_dec_ref(v_xs_819_);
return v_res_822_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(lean_object* v_xs_823_, lean_object* v_v_824_){
_start:
{
lean_object* v___x_825_; lean_object* v___x_826_; 
v___x_825_ = lean_unsigned_to_nat(0u);
v___x_826_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(v_xs_823_, v_v_824_, v___x_825_);
return v___x_826_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13___boxed(lean_object* v_xs_827_, lean_object* v_v_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(v_xs_827_, v_v_828_);
lean_dec(v_v_828_);
lean_dec_ref(v_xs_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(lean_object* v_x_830_, size_t v_x_831_, lean_object* v_x_832_){
_start:
{
if (lean_obj_tag(v_x_830_) == 0)
{
lean_object* v_es_833_; lean_object* v___x_834_; size_t v___x_835_; size_t v___x_836_; lean_object* v_j_837_; lean_object* v_entry_838_; 
v_es_833_ = lean_ctor_get(v_x_830_, 0);
v___x_834_ = lean_box(2);
v___x_835_ = ((size_t)31ULL);
v___x_836_ = lean_usize_land(v_x_831_, v___x_835_);
v_j_837_ = lean_usize_to_nat(v___x_836_);
v_entry_838_ = lean_array_get(v___x_834_, v_es_833_, v_j_837_);
switch(lean_obj_tag(v_entry_838_))
{
case 0:
{
lean_object* v_key_839_; uint8_t v___x_840_; 
v_key_839_ = lean_ctor_get(v_entry_838_, 0);
lean_inc(v_key_839_);
lean_dec_ref_known(v_entry_838_, 2);
v___x_840_ = lean_name_eq(v_x_832_, v_key_839_);
lean_dec(v_key_839_);
if (v___x_840_ == 0)
{
lean_dec(v_j_837_);
return v_x_830_;
}
else
{
lean_object* v___x_842_; uint8_t v_isShared_843_; uint8_t v_isSharedCheck_848_; 
lean_inc_ref(v_es_833_);
v_isSharedCheck_848_ = !lean_is_exclusive(v_x_830_);
if (v_isSharedCheck_848_ == 0)
{
lean_object* v_unused_849_; 
v_unused_849_ = lean_ctor_get(v_x_830_, 0);
lean_dec(v_unused_849_);
v___x_842_ = v_x_830_;
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
else
{
lean_dec(v_x_830_);
v___x_842_ = lean_box(0);
v_isShared_843_ = v_isSharedCheck_848_;
goto v_resetjp_841_;
}
v_resetjp_841_:
{
lean_object* v___x_844_; lean_object* v___x_846_; 
v___x_844_ = lean_array_set(v_es_833_, v_j_837_, v___x_834_);
lean_dec(v_j_837_);
if (v_isShared_843_ == 0)
{
lean_ctor_set(v___x_842_, 0, v___x_844_);
v___x_846_ = v___x_842_;
goto v_reusejp_845_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_844_);
v___x_846_ = v_reuseFailAlloc_847_;
goto v_reusejp_845_;
}
v_reusejp_845_:
{
return v___x_846_;
}
}
}
}
case 1:
{
lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_884_; 
lean_inc_ref(v_es_833_);
v_isSharedCheck_884_ = !lean_is_exclusive(v_x_830_);
if (v_isSharedCheck_884_ == 0)
{
lean_object* v_unused_885_; 
v_unused_885_ = lean_ctor_get(v_x_830_, 0);
lean_dec(v_unused_885_);
v___x_851_ = v_x_830_;
v_isShared_852_ = v_isSharedCheck_884_;
goto v_resetjp_850_;
}
else
{
lean_dec(v_x_830_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_884_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v_node_853_; lean_object* v___x_855_; uint8_t v_isShared_856_; uint8_t v_isSharedCheck_883_; 
v_node_853_ = lean_ctor_get(v_entry_838_, 0);
v_isSharedCheck_883_ = !lean_is_exclusive(v_entry_838_);
if (v_isSharedCheck_883_ == 0)
{
v___x_855_ = v_entry_838_;
v_isShared_856_ = v_isSharedCheck_883_;
goto v_resetjp_854_;
}
else
{
lean_inc(v_node_853_);
lean_dec(v_entry_838_);
v___x_855_ = lean_box(0);
v_isShared_856_ = v_isSharedCheck_883_;
goto v_resetjp_854_;
}
v_resetjp_854_:
{
size_t v___x_857_; lean_object* v_entries_858_; size_t v___x_859_; lean_object* v_newNode_860_; lean_object* v___x_861_; 
v___x_857_ = ((size_t)5ULL);
v_entries_858_ = lean_array_set(v_es_833_, v_j_837_, v___x_834_);
v___x_859_ = lean_usize_shift_right(v_x_831_, v___x_857_);
v_newNode_860_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_node_853_, v___x_859_, v_x_832_);
lean_inc_ref(v_newNode_860_);
v___x_861_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_860_);
if (lean_obj_tag(v___x_861_) == 0)
{
lean_object* v___x_863_; 
if (v_isShared_856_ == 0)
{
lean_ctor_set(v___x_855_, 0, v_newNode_860_);
v___x_863_ = v___x_855_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_newNode_860_);
v___x_863_ = v_reuseFailAlloc_868_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
lean_object* v___x_864_; lean_object* v___x_866_; 
v___x_864_ = lean_array_set(v_entries_858_, v_j_837_, v___x_863_);
lean_dec(v_j_837_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_864_);
v___x_866_ = v___x_851_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
else
{
lean_object* v_val_869_; lean_object* v_fst_870_; lean_object* v_snd_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_882_; 
lean_dec_ref(v_newNode_860_);
lean_del_object(v___x_855_);
v_val_869_ = lean_ctor_get(v___x_861_, 0);
lean_inc(v_val_869_);
lean_dec_ref_known(v___x_861_, 1);
v_fst_870_ = lean_ctor_get(v_val_869_, 0);
v_snd_871_ = lean_ctor_get(v_val_869_, 1);
v_isSharedCheck_882_ = !lean_is_exclusive(v_val_869_);
if (v_isSharedCheck_882_ == 0)
{
v___x_873_ = v_val_869_;
v_isShared_874_ = v_isSharedCheck_882_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_snd_871_);
lean_inc(v_fst_870_);
lean_dec(v_val_869_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_882_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v___x_876_; 
if (v_isShared_874_ == 0)
{
v___x_876_ = v___x_873_;
goto v_reusejp_875_;
}
else
{
lean_object* v_reuseFailAlloc_881_; 
v_reuseFailAlloc_881_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_881_, 0, v_fst_870_);
lean_ctor_set(v_reuseFailAlloc_881_, 1, v_snd_871_);
v___x_876_ = v_reuseFailAlloc_881_;
goto v_reusejp_875_;
}
v_reusejp_875_:
{
lean_object* v___x_877_; lean_object* v___x_879_; 
v___x_877_ = lean_array_set(v_entries_858_, v_j_837_, v___x_876_);
lean_dec(v_j_837_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 0, v___x_877_);
v___x_879_ = v___x_851_;
goto v_reusejp_878_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v___x_877_);
v___x_879_ = v_reuseFailAlloc_880_;
goto v_reusejp_878_;
}
v_reusejp_878_:
{
return v___x_879_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_837_);
return v_x_830_;
}
}
}
else
{
lean_object* v_ks_886_; lean_object* v_vs_887_; lean_object* v___x_889_; uint8_t v_isShared_890_; uint8_t v_isSharedCheck_901_; 
v_ks_886_ = lean_ctor_get(v_x_830_, 0);
v_vs_887_ = lean_ctor_get(v_x_830_, 1);
v_isSharedCheck_901_ = !lean_is_exclusive(v_x_830_);
if (v_isSharedCheck_901_ == 0)
{
v___x_889_ = v_x_830_;
v_isShared_890_ = v_isSharedCheck_901_;
goto v_resetjp_888_;
}
else
{
lean_inc(v_vs_887_);
lean_inc(v_ks_886_);
lean_dec(v_x_830_);
v___x_889_ = lean_box(0);
v_isShared_890_ = v_isSharedCheck_901_;
goto v_resetjp_888_;
}
v_resetjp_888_:
{
lean_object* v___x_891_; 
v___x_891_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(v_ks_886_, v_x_832_);
if (lean_obj_tag(v___x_891_) == 0)
{
lean_object* v___x_893_; 
if (v_isShared_890_ == 0)
{
v___x_893_ = v___x_889_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_894_; 
v_reuseFailAlloc_894_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_894_, 0, v_ks_886_);
lean_ctor_set(v_reuseFailAlloc_894_, 1, v_vs_887_);
v___x_893_ = v_reuseFailAlloc_894_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
return v___x_893_;
}
}
else
{
lean_object* v_val_895_; lean_object* v_keys_x27_896_; lean_object* v_vals_x27_897_; lean_object* v___x_899_; 
v_val_895_ = lean_ctor_get(v___x_891_, 0);
lean_inc_n(v_val_895_, 2);
lean_dec_ref_known(v___x_891_, 1);
v_keys_x27_896_ = l_Array_eraseIdx___redArg(v_ks_886_, v_val_895_);
v_vals_x27_897_ = l_Array_eraseIdx___redArg(v_vs_887_, v_val_895_);
if (v_isShared_890_ == 0)
{
lean_ctor_set(v___x_889_, 1, v_vals_x27_897_);
lean_ctor_set(v___x_889_, 0, v_keys_x27_896_);
v___x_899_ = v___x_889_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_keys_x27_896_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_vals_x27_897_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg___boxed(lean_object* v_x_902_, lean_object* v_x_903_, lean_object* v_x_904_){
_start:
{
size_t v_x_3070__boxed_905_; lean_object* v_res_906_; 
v_x_3070__boxed_905_ = lean_unbox_usize(v_x_903_);
lean_dec(v_x_903_);
v_res_906_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_902_, v_x_3070__boxed_905_, v_x_904_);
lean_dec(v_x_904_);
return v_res_906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(lean_object* v_x_907_, lean_object* v_x_908_){
_start:
{
uint64_t v___y_910_; 
if (lean_obj_tag(v_x_908_) == 0)
{
uint64_t v___x_913_; 
v___x_913_ = 1723ULL;
v___y_910_ = v___x_913_;
goto v___jp_909_;
}
else
{
uint64_t v_hash_914_; 
v_hash_914_ = lean_ctor_get_uint64(v_x_908_, sizeof(void*)*2);
v___y_910_ = v_hash_914_;
goto v___jp_909_;
}
v___jp_909_:
{
size_t v_h_911_; lean_object* v___x_912_; 
v_h_911_ = lean_uint64_to_usize(v___y_910_);
v___x_912_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_907_, v_h_911_, v_x_908_);
return v___x_912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg___boxed(lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
lean_object* v_res_917_; 
v_res_917_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_915_, v_x_916_);
lean_dec(v_x_916_);
return v_res_917_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object* v_d_918_, lean_object* v_e_919_){
_start:
{
lean_object* v_globalName_x3f_920_; 
v_globalName_x3f_920_ = lean_ctor_get(v_e_919_, 3);
if (lean_obj_tag(v_globalName_x3f_920_) == 0)
{
lean_object* v_keys_921_; lean_object* v_discrTree_922_; lean_object* v_instanceNames_923_; lean_object* v_erased_924_; lean_object* v___x_926_; uint8_t v_isShared_927_; uint8_t v_isSharedCheck_932_; 
v_keys_921_ = lean_ctor_get(v_e_919_, 0);
lean_inc_ref(v_keys_921_);
v_discrTree_922_ = lean_ctor_get(v_d_918_, 0);
v_instanceNames_923_ = lean_ctor_get(v_d_918_, 1);
v_erased_924_ = lean_ctor_get(v_d_918_, 2);
v_isSharedCheck_932_ = !lean_is_exclusive(v_d_918_);
if (v_isSharedCheck_932_ == 0)
{
v___x_926_ = v_d_918_;
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
else
{
lean_inc(v_erased_924_);
lean_inc(v_instanceNames_923_);
lean_inc(v_discrTree_922_);
lean_dec(v_d_918_);
v___x_926_ = lean_box(0);
v_isShared_927_ = v_isSharedCheck_932_;
goto v_resetjp_925_;
}
v_resetjp_925_:
{
lean_object* v___x_928_; lean_object* v___x_930_; 
v___x_928_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_922_, v_keys_921_, v_e_919_);
lean_dec_ref(v_keys_921_);
if (v_isShared_927_ == 0)
{
lean_ctor_set(v___x_926_, 0, v___x_928_);
v___x_930_ = v___x_926_;
goto v_reusejp_929_;
}
else
{
lean_object* v_reuseFailAlloc_931_; 
v_reuseFailAlloc_931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_931_, 0, v___x_928_);
lean_ctor_set(v_reuseFailAlloc_931_, 1, v_instanceNames_923_);
lean_ctor_set(v_reuseFailAlloc_931_, 2, v_erased_924_);
v___x_930_ = v_reuseFailAlloc_931_;
goto v_reusejp_929_;
}
v_reusejp_929_:
{
return v___x_930_;
}
}
}
else
{
lean_object* v_keys_933_; lean_object* v_val_934_; lean_object* v_discrTree_935_; lean_object* v_instanceNames_936_; lean_object* v_erased_937_; lean_object* v___x_939_; uint8_t v_isShared_940_; uint8_t v_isSharedCheck_947_; 
v_keys_933_ = lean_ctor_get(v_e_919_, 0);
v_val_934_ = lean_ctor_get(v_globalName_x3f_920_, 0);
lean_inc(v_val_934_);
v_discrTree_935_ = lean_ctor_get(v_d_918_, 0);
v_instanceNames_936_ = lean_ctor_get(v_d_918_, 1);
v_erased_937_ = lean_ctor_get(v_d_918_, 2);
v_isSharedCheck_947_ = !lean_is_exclusive(v_d_918_);
if (v_isSharedCheck_947_ == 0)
{
v___x_939_ = v_d_918_;
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
else
{
lean_inc(v_erased_937_);
lean_inc(v_instanceNames_936_);
lean_inc(v_discrTree_935_);
lean_dec(v_d_918_);
v___x_939_ = lean_box(0);
v_isShared_940_ = v_isSharedCheck_947_;
goto v_resetjp_938_;
}
v_resetjp_938_:
{
lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_945_; 
lean_inc_ref(v_e_919_);
v___x_941_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_935_, v_keys_933_, v_e_919_);
lean_inc(v_val_934_);
v___x_942_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_instanceNames_936_, v_val_934_, v_e_919_);
v___x_943_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_erased_937_, v_val_934_);
lean_dec(v_val_934_);
if (v_isShared_940_ == 0)
{
lean_ctor_set(v___x_939_, 2, v___x_943_);
lean_ctor_set(v___x_939_, 1, v___x_942_);
lean_ctor_set(v___x_939_, 0, v___x_941_);
v___x_945_ = v___x_939_;
goto v_reusejp_944_;
}
else
{
lean_object* v_reuseFailAlloc_946_; 
v_reuseFailAlloc_946_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_946_, 0, v___x_941_);
lean_ctor_set(v_reuseFailAlloc_946_, 1, v___x_942_);
lean_ctor_set(v_reuseFailAlloc_946_, 2, v___x_943_);
v___x_945_ = v_reuseFailAlloc_946_;
goto v_reusejp_944_;
}
v_reusejp_944_:
{
return v___x_945_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1(lean_object* v_00_u03b2_948_, lean_object* v_x_949_, lean_object* v_x_950_, lean_object* v_x_951_){
_start:
{
lean_object* v___x_952_; 
v___x_952_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_x_949_, v_x_950_, v_x_951_);
return v___x_952_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(lean_object* v_00_u03b2_953_, lean_object* v_x_954_, lean_object* v_x_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_954_, v_x_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___boxed(lean_object* v_00_u03b2_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v_res_960_; 
v_res_960_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(v_00_u03b2_957_, v_x_958_, v_x_959_);
lean_dec(v_x_959_);
return v_res_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4(lean_object* v_00_u03b2_961_, lean_object* v_x_962_, size_t v_x_963_, size_t v_x_964_, lean_object* v_x_965_, lean_object* v_x_966_){
_start:
{
lean_object* v___x_967_; 
v___x_967_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_962_, v_x_963_, v_x_964_, v_x_965_, v_x_966_);
return v___x_967_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___boxed(lean_object* v_00_u03b2_968_, lean_object* v_x_969_, lean_object* v_x_970_, lean_object* v_x_971_, lean_object* v_x_972_, lean_object* v_x_973_){
_start:
{
size_t v_x_3274__boxed_974_; size_t v_x_3275__boxed_975_; lean_object* v_res_976_; 
v_x_3274__boxed_974_ = lean_unbox_usize(v_x_970_);
lean_dec(v_x_970_);
v_x_3275__boxed_975_ = lean_unbox_usize(v_x_971_);
lean_dec(v_x_971_);
v_res_976_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4(v_00_u03b2_968_, v_x_969_, v_x_3274__boxed_974_, v_x_3275__boxed_975_, v_x_972_, v_x_973_);
return v_res_976_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6(lean_object* v_00_u03b2_977_, lean_object* v_x_978_, size_t v_x_979_, lean_object* v_x_980_){
_start:
{
lean_object* v___x_981_; 
v___x_981_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_978_, v_x_979_, v_x_980_);
return v___x_981_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___boxed(lean_object* v_00_u03b2_982_, lean_object* v_x_983_, lean_object* v_x_984_, lean_object* v_x_985_){
_start:
{
size_t v_x_3291__boxed_986_; lean_object* v_res_987_; 
v_x_3291__boxed_986_ = lean_unbox_usize(v_x_984_);
lean_dec(v_x_984_);
v_res_987_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6(v_00_u03b2_982_, v_x_983_, v_x_3291__boxed_986_, v_x_985_);
lean_dec(v_x_985_);
return v_res_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_988_, lean_object* v_x_989_, size_t v_x_990_, size_t v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
lean_object* v___x_994_; 
v___x_994_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_x_989_, v_x_990_, v_x_991_, v_x_992_, v_x_993_);
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_995_, lean_object* v_x_996_, lean_object* v_x_997_, lean_object* v_x_998_, lean_object* v_x_999_, lean_object* v_x_1000_){
_start:
{
size_t v_x_3302__boxed_1001_; size_t v_x_3303__boxed_1002_; lean_object* v_res_1003_; 
v_x_3302__boxed_1001_ = lean_unbox_usize(v_x_997_);
lean_dec(v_x_997_);
v_x_3303__boxed_1002_ = lean_unbox_usize(v_x_998_);
lean_dec(v_x_998_);
v_res_1003_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(v_00_u03b2_995_, v_x_996_, v_x_3302__boxed_1001_, v_x_3303__boxed_1002_, v_x_999_, v_x_1000_);
return v_res_1003_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_1004_, lean_object* v_n_1005_, lean_object* v_k_1006_, lean_object* v_v_1007_){
_start:
{
lean_object* v___x_1008_; 
v___x_1008_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9___redArg(v_n_1005_, v_k_1006_, v_v_1007_);
return v___x_1008_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_1009_, size_t v_depth_1010_, lean_object* v_keys_1011_, lean_object* v_vals_1012_, lean_object* v_heq_1013_, lean_object* v_i_1014_, lean_object* v_entries_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_depth_1010_, v_keys_1011_, v_vals_1012_, v_i_1014_, v_entries_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___boxed(lean_object* v_00_u03b2_1017_, lean_object* v_depth_1018_, lean_object* v_keys_1019_, lean_object* v_vals_1020_, lean_object* v_heq_1021_, lean_object* v_i_1022_, lean_object* v_entries_1023_){
_start:
{
size_t v_depth_boxed_1024_; lean_object* v_res_1025_; 
v_depth_boxed_1024_ = lean_unbox_usize(v_depth_1018_);
lean_dec(v_depth_1018_);
v_res_1025_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10(v_00_u03b2_1017_, v_depth_boxed_1024_, v_keys_1019_, v_vals_1020_, v_heq_1021_, v_i_1022_, v_entries_1023_);
lean_dec_ref(v_vals_1020_);
lean_dec_ref(v_keys_1019_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7(lean_object* v_x_1026_, lean_object* v_keys_1027_, lean_object* v_v_1028_, lean_object* v_k_1029_, lean_object* v_as_1030_, lean_object* v_k_1031_, lean_object* v_x_1032_, lean_object* v_x_1033_, lean_object* v_x_1034_, lean_object* v_x_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_1026_, v_keys_1027_, v_v_1028_, v_k_1029_, v_as_1030_, v_k_1031_, v_x_1032_, v_x_1033_);
return v___x_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_x_1037_, lean_object* v_keys_1038_, lean_object* v_v_1039_, lean_object* v_k_1040_, lean_object* v_as_1041_, lean_object* v_k_1042_, lean_object* v_x_1043_, lean_object* v_x_1044_, lean_object* v_x_1045_, lean_object* v_x_1046_){
_start:
{
lean_object* v_res_1047_; 
v_res_1047_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7(v_x_1037_, v_keys_1038_, v_v_1039_, v_k_1040_, v_as_1041_, v_k_1042_, v_x_1043_, v_x_1044_, v_x_1045_, v_x_1046_);
lean_dec_ref(v_k_1042_);
lean_dec_ref(v_keys_1038_);
lean_dec(v_x_1037_);
return v_res_1047_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12(lean_object* v_00_u03b2_1048_, lean_object* v_n_1049_, lean_object* v_k_1050_, lean_object* v_v_1051_){
_start:
{
lean_object* v___x_1052_; 
v___x_1052_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(v_n_1049_, v_k_1050_, v_v_1051_);
return v___x_1052_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13(lean_object* v_00_u03b2_1053_, size_t v_depth_1054_, lean_object* v_keys_1055_, lean_object* v_vals_1056_, lean_object* v_heq_1057_, lean_object* v_i_1058_, lean_object* v_entries_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(v_depth_1054_, v_keys_1055_, v_vals_1056_, v_i_1058_, v_entries_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___boxed(lean_object* v_00_u03b2_1061_, lean_object* v_depth_1062_, lean_object* v_keys_1063_, lean_object* v_vals_1064_, lean_object* v_heq_1065_, lean_object* v_i_1066_, lean_object* v_entries_1067_){
_start:
{
size_t v_depth_boxed_1068_; lean_object* v_res_1069_; 
v_depth_boxed_1068_ = lean_unbox_usize(v_depth_1062_);
lean_dec(v_depth_1062_);
v_res_1069_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13(v_00_u03b2_1061_, v_depth_boxed_1068_, v_keys_1063_, v_vals_1064_, v_heq_1065_, v_i_1066_, v_entries_1067_);
lean_dec_ref(v_vals_1064_);
lean_dec_ref(v_keys_1063_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16(lean_object* v_00_u03b2_1070_, lean_object* v_x_1071_, lean_object* v_x_1072_, lean_object* v_x_1073_, lean_object* v_x_1074_){
_start:
{
lean_object* v___x_1075_; 
v___x_1075_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16___redArg(v_x_1071_, v_x_1072_, v_x_1073_, v_x_1074_);
return v___x_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(v_x_1077_, v_x_1078_, v_x_1079_, v_x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_eraseCore(lean_object* v_d_1082_, lean_object* v_declName_1083_){
_start:
{
lean_object* v_discrTree_1084_; lean_object* v_instanceNames_1085_; lean_object* v_erased_1086_; lean_object* v___x_1088_; uint8_t v_isShared_1089_; uint8_t v_isSharedCheck_1096_; 
v_discrTree_1084_ = lean_ctor_get(v_d_1082_, 0);
v_instanceNames_1085_ = lean_ctor_get(v_d_1082_, 1);
v_erased_1086_ = lean_ctor_get(v_d_1082_, 2);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_d_1082_);
if (v_isSharedCheck_1096_ == 0)
{
v___x_1088_ = v_d_1082_;
v_isShared_1089_ = v_isSharedCheck_1096_;
goto v_resetjp_1087_;
}
else
{
lean_inc(v_erased_1086_);
lean_inc(v_instanceNames_1085_);
lean_inc(v_discrTree_1084_);
lean_dec(v_d_1082_);
v___x_1088_ = lean_box(0);
v_isShared_1089_ = v_isSharedCheck_1096_;
goto v_resetjp_1087_;
}
v_resetjp_1087_:
{
lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1094_; 
v___x_1090_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_instanceNames_1085_, v_declName_1083_);
v___x_1091_ = lean_box(0);
v___x_1092_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_erased_1086_, v_declName_1083_, v___x_1091_);
if (v_isShared_1089_ == 0)
{
lean_ctor_set(v___x_1088_, 2, v___x_1092_);
lean_ctor_set(v___x_1088_, 1, v___x_1090_);
v___x_1094_ = v___x_1088_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v_discrTree_1084_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v___x_1090_);
lean_ctor_set(v_reuseFailAlloc_1095_, 2, v___x_1092_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__0(lean_object* v_d_1097_, lean_object* v_declName_1098_, lean_object* v_toPure_1099_, lean_object* v_____r_1100_){
_start:
{
lean_object* v___x_1101_; lean_object* v___x_1102_; 
v___x_1101_ = l_Lean_Meta_Instances_eraseCore(v_d_1097_, v_declName_1098_);
v___x_1102_ = lean_apply_2(v_toPure_1099_, lean_box(0), v___x_1101_);
return v___x_1102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__1(lean_object* v___f_1103_, lean_object* v_____r_1104_){
_start:
{
lean_object* v___x_1105_; 
v___x_1105_ = lean_apply_1(v___f_1103_, v_____r_1104_);
return v___x_1105_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__2));
v___x_1110_ = l_Lean_stringToMessageData(v___x_1109_);
return v___x_1110_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__5(void){
_start:
{
lean_object* v___x_1112_; lean_object* v___x_1113_; 
v___x_1112_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__4));
v___x_1113_ = l_Lean_stringToMessageData(v___x_1112_);
return v___x_1113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg(lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_d_1116_, lean_object* v_declName_1117_){
_start:
{
lean_object* v_toApplicative_1118_; lean_object* v_toBind_1119_; lean_object* v_toPure_1120_; lean_object* v_instanceNames_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___f_1124_; uint8_t v___x_1125_; 
v_toApplicative_1118_ = lean_ctor_get(v_inst_1114_, 0);
v_toBind_1119_ = lean_ctor_get(v_inst_1114_, 1);
lean_inc(v_toBind_1119_);
v_toPure_1120_ = lean_ctor_get(v_toApplicative_1118_, 1);
v_instanceNames_1121_ = lean_ctor_get(v_d_1116_, 1);
v___x_1122_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__0));
v___x_1123_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__1));
lean_inc(v_toPure_1120_);
lean_inc_n(v_declName_1117_, 2);
lean_inc_ref(v_d_1116_);
v___f_1124_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1124_, 0, v_d_1116_);
lean_closure_set(v___f_1124_, 1, v_declName_1117_);
lean_closure_set(v___f_1124_, 2, v_toPure_1120_);
lean_inc_ref(v_instanceNames_1121_);
v___x_1125_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1122_, v___x_1123_, v_instanceNames_1121_, v_declName_1117_);
if (v___x_1125_ == 0)
{
lean_object* v___f_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; 
lean_dec_ref(v_d_1116_);
v___f_1126_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1126_, 0, v___f_1124_);
v___x_1127_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_1128_ = l_Lean_MessageData_ofConstName(v_declName_1117_, v___x_1125_);
v___x_1129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1127_);
lean_ctor_set(v___x_1129_, 1, v___x_1128_);
v___x_1130_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_1131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1131_, 0, v___x_1129_);
lean_ctor_set(v___x_1131_, 1, v___x_1130_);
v___x_1132_ = l_Lean_throwError___redArg(v_inst_1114_, v_inst_1115_, v___x_1131_);
v___x_1133_ = lean_apply_4(v_toBind_1119_, lean_box(0), lean_box(0), v___x_1132_, v___f_1126_);
return v___x_1133_;
}
else
{
lean_object* v___x_1134_; lean_object* v___x_1135_; 
lean_inc(v_toPure_1120_);
lean_dec_ref(v___f_1124_);
lean_dec(v_toBind_1119_);
lean_dec_ref(v_inst_1115_);
lean_dec_ref(v_inst_1114_);
v___x_1134_ = lean_box(0);
v___x_1135_ = l_Lean_Meta_Instances_erase___redArg___lam__0(v_d_1116_, v_declName_1117_, v_toPure_1120_, v___x_1134_);
return v___x_1135_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase(lean_object* v_m_1136_, lean_object* v_inst_1137_, lean_object* v_inst_1138_, lean_object* v_d_1139_, lean_object* v_declName_1140_){
_start:
{
lean_object* v___x_1141_; 
v___x_1141_ = l_Lean_Meta_Instances_erase___redArg(v_inst_1137_, v_inst_1138_, v_d_1139_, v_declName_1140_);
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(lean_object* v_x_1142_, lean_object* v_e_1143_){
_start:
{
lean_object* v_globalName_x3f_1148_; 
v_globalName_x3f_1148_ = lean_ctor_get(v_e_1143_, 3);
lean_inc(v_globalName_x3f_1148_);
if (lean_obj_tag(v_globalName_x3f_1148_) == 0)
{
goto v___jp_1144_;
}
else
{
lean_object* v_val_1149_; lean_object* v___x_1151_; uint8_t v_isShared_1152_; uint8_t v_isSharedCheck_1158_; 
v_val_1149_ = lean_ctor_get(v_globalName_x3f_1148_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v_globalName_x3f_1148_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1151_ = v_globalName_x3f_1148_;
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
else
{
lean_inc(v_val_1149_);
lean_dec(v_globalName_x3f_1148_);
v___x_1151_ = lean_box(0);
v_isShared_1152_ = v_isSharedCheck_1158_;
goto v_resetjp_1150_;
}
v_resetjp_1150_:
{
uint8_t v___x_1153_; 
v___x_1153_ = l_Lean_isPrivateName(v_val_1149_);
lean_dec(v_val_1149_);
if (v___x_1153_ == 0)
{
lean_object* v___x_1155_; 
if (v_isShared_1152_ == 0)
{
lean_ctor_set(v___x_1151_, 0, v_e_1143_);
v___x_1155_ = v___x_1151_;
goto v_reusejp_1154_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_e_1143_);
v___x_1155_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1154_;
}
v_reusejp_1154_:
{
lean_object* v___x_1156_; 
lean_inc_ref_n(v___x_1155_, 2);
v___x_1156_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1156_, 0, v___x_1155_);
lean_ctor_set(v___x_1156_, 1, v___x_1155_);
lean_ctor_set(v___x_1156_, 2, v___x_1155_);
return v___x_1156_;
}
}
else
{
lean_del_object(v___x_1151_);
goto v___jp_1144_;
}
}
}
v___jp_1144_:
{
lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; 
v___x_1145_ = lean_box(0);
v___x_1146_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1146_, 0, v_e_1143_);
v___x_1147_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1147_, 0, v___x_1145_);
lean_ctor_set(v___x_1147_, 1, v___x_1145_);
lean_ctor_set(v___x_1147_, 2, v___x_1146_);
return v___x_1147_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v_x_1159_, lean_object* v_e_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(v_x_1159_, v_e_1160_);
lean_dec_ref(v_x_1159_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(lean_object* v___y_1162_){
_start:
{
lean_inc_ref(v___y_1162_);
return v___y_1162_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v___y_1163_){
_start:
{
lean_object* v_res_1164_; 
v_res_1164_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(v___y_1163_);
lean_dec_ref(v___y_1163_);
return v_res_1164_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1173_; lean_object* v___f_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; 
v___f_1173_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___f_1174_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1175_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__4, &l_Lean_Meta_instInhabitedInstances_default___closed__4_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__4);
v___x_1176_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1177_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1178_, 0, v___x_1177_);
lean_ctor_set(v___x_1178_, 1, v___x_1176_);
lean_ctor_set(v___x_1178_, 2, v___x_1175_);
lean_ctor_set(v___x_1178_, 3, v___f_1174_);
lean_ctor_set(v___x_1178_, 4, v___f_1173_);
return v___x_1178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1180_; lean_object* v___x_1181_; 
v___x_1180_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_);
v___x_1181_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1180_);
return v___x_1181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v_a_1182_){
_start:
{
lean_object* v_res_1183_; 
v_res_1183_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_();
return v_res_1183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object* v_k_1184_, uint8_t v_allowLevelAssignments_1185_, lean_object* v___y_1186_, lean_object* v___y_1187_, lean_object* v___y_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v___x_1191_; 
v___x_1191_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1185_, v_k_1184_, v___y_1186_, v___y_1187_, v___y_1188_, v___y_1189_);
if (lean_obj_tag(v___x_1191_) == 0)
{
lean_object* v_a_1192_; lean_object* v___x_1194_; uint8_t v_isShared_1195_; uint8_t v_isSharedCheck_1199_; 
v_a_1192_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1199_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1194_ = v___x_1191_;
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
else
{
lean_inc(v_a_1192_);
lean_dec(v___x_1191_);
v___x_1194_ = lean_box(0);
v_isShared_1195_ = v_isSharedCheck_1199_;
goto v_resetjp_1193_;
}
v_resetjp_1193_:
{
lean_object* v___x_1197_; 
if (v_isShared_1195_ == 0)
{
v___x_1197_ = v___x_1194_;
goto v_reusejp_1196_;
}
else
{
lean_object* v_reuseFailAlloc_1198_; 
v_reuseFailAlloc_1198_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1198_, 0, v_a_1192_);
v___x_1197_ = v_reuseFailAlloc_1198_;
goto v_reusejp_1196_;
}
v_reusejp_1196_:
{
return v___x_1197_;
}
}
}
else
{
lean_object* v_a_1200_; lean_object* v___x_1202_; uint8_t v_isShared_1203_; uint8_t v_isSharedCheck_1207_; 
v_a_1200_ = lean_ctor_get(v___x_1191_, 0);
v_isSharedCheck_1207_ = !lean_is_exclusive(v___x_1191_);
if (v_isSharedCheck_1207_ == 0)
{
v___x_1202_ = v___x_1191_;
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
else
{
lean_inc(v_a_1200_);
lean_dec(v___x_1191_);
v___x_1202_ = lean_box(0);
v_isShared_1203_ = v_isSharedCheck_1207_;
goto v_resetjp_1201_;
}
v_resetjp_1201_:
{
lean_object* v___x_1205_; 
if (v_isShared_1203_ == 0)
{
v___x_1205_ = v___x_1202_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1206_; 
v_reuseFailAlloc_1206_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1206_, 0, v_a_1200_);
v___x_1205_ = v_reuseFailAlloc_1206_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
return v___x_1205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object* v_k_1208_, lean_object* v_allowLevelAssignments_1209_, lean_object* v___y_1210_, lean_object* v___y_1211_, lean_object* v___y_1212_, lean_object* v___y_1213_, lean_object* v___y_1214_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1215_; lean_object* v_res_1216_; 
v_allowLevelAssignments_boxed_1215_ = lean_unbox(v_allowLevelAssignments_1209_);
v_res_1216_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1208_, v_allowLevelAssignments_boxed_1215_, v___y_1210_, v___y_1211_, v___y_1212_, v___y_1213_);
lean_dec(v___y_1213_);
lean_dec_ref(v___y_1212_);
lean_dec(v___y_1211_);
lean_dec_ref(v___y_1210_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object* v_00_u03b1_1217_, lean_object* v_k_1218_, uint8_t v_allowLevelAssignments_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1218_, v_allowLevelAssignments_1219_, v___y_1220_, v___y_1221_, v___y_1222_, v___y_1223_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object* v_00_u03b1_1226_, lean_object* v_k_1227_, lean_object* v_allowLevelAssignments_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_, lean_object* v___y_1233_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1234_; lean_object* v_res_1235_; 
v_allowLevelAssignments_boxed_1234_ = lean_unbox(v_allowLevelAssignments_1228_);
v_res_1235_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(v_00_u03b1_1226_, v_k_1227_, v_allowLevelAssignments_boxed_1234_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
lean_dec(v___y_1232_);
lean_dec_ref(v___y_1231_);
lean_dec(v___y_1230_);
lean_dec_ref(v___y_1229_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1236_, lean_object* v___x_1237_, uint8_t v___x_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
lean_object* v___x_1244_; 
v___x_1244_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1236_, v___x_1237_, v___x_1238_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
if (lean_obj_tag(v___x_1244_) == 0)
{
lean_object* v_a_1245_; lean_object* v_snd_1246_; lean_object* v_snd_1247_; uint8_t v___x_1248_; lean_object* v___x_1249_; 
v_a_1245_ = lean_ctor_get(v___x_1244_, 0);
lean_inc(v_a_1245_);
lean_dec_ref_known(v___x_1244_, 1);
v_snd_1246_ = lean_ctor_get(v_a_1245_, 1);
lean_inc(v_snd_1246_);
lean_dec(v_a_1245_);
v_snd_1247_ = lean_ctor_get(v_snd_1246_, 1);
lean_inc(v_snd_1247_);
lean_dec(v_snd_1246_);
v___x_1248_ = 0;
v___x_1249_ = l_Lean_Meta_DiscrTree_mkPath(v_snd_1247_, v___x_1248_, v___y_1239_, v___y_1240_, v___y_1241_, v___y_1242_);
return v___x_1249_;
}
else
{
lean_object* v_a_1250_; lean_object* v___x_1252_; uint8_t v_isShared_1253_; uint8_t v_isSharedCheck_1257_; 
v_a_1250_ = lean_ctor_get(v___x_1244_, 0);
v_isSharedCheck_1257_ = !lean_is_exclusive(v___x_1244_);
if (v_isSharedCheck_1257_ == 0)
{
v___x_1252_ = v___x_1244_;
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
else
{
lean_inc(v_a_1250_);
lean_dec(v___x_1244_);
v___x_1252_ = lean_box(0);
v_isShared_1253_ = v_isSharedCheck_1257_;
goto v_resetjp_1251_;
}
v_resetjp_1251_:
{
lean_object* v___x_1255_; 
if (v_isShared_1253_ == 0)
{
v___x_1255_ = v___x_1252_;
goto v_reusejp_1254_;
}
else
{
lean_object* v_reuseFailAlloc_1256_; 
v_reuseFailAlloc_1256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1256_, 0, v_a_1250_);
v___x_1255_ = v_reuseFailAlloc_1256_;
goto v_reusejp_1254_;
}
v_reusejp_1254_:
{
return v___x_1255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object* v_a_1258_, lean_object* v___x_1259_, lean_object* v___x_1260_, lean_object* v___y_1261_, lean_object* v___y_1262_, lean_object* v___y_1263_, lean_object* v___y_1264_, lean_object* v___y_1265_){
_start:
{
uint8_t v___x_497__boxed_1266_; lean_object* v_res_1267_; 
v___x_497__boxed_1266_ = lean_unbox(v___x_1260_);
v_res_1267_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1258_, v___x_1259_, v___x_497__boxed_1266_, v___y_1261_, v___y_1262_, v___y_1263_, v___y_1264_);
lean_dec(v___y_1264_);
lean_dec_ref(v___y_1263_);
lean_dec(v___y_1262_);
lean_dec_ref(v___y_1261_);
return v_res_1267_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object* v_e_1268_, lean_object* v_a_1269_, lean_object* v_a_1270_, lean_object* v_a_1271_, lean_object* v_a_1272_){
_start:
{
lean_object* v___x_1274_; 
lean_inc(v_a_1272_);
lean_inc_ref(v_a_1271_);
lean_inc(v_a_1270_);
lean_inc_ref(v_a_1269_);
v___x_1274_ = lean_infer_type(v_e_1268_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
if (lean_obj_tag(v___x_1274_) == 0)
{
lean_object* v_a_1275_; lean_object* v___x_1276_; uint8_t v___x_1277_; lean_object* v___x_1278_; lean_object* v___f_1279_; uint8_t v___x_1280_; lean_object* v___x_1281_; 
v_a_1275_ = lean_ctor_get(v___x_1274_, 0);
lean_inc(v_a_1275_);
lean_dec_ref_known(v___x_1274_, 1);
v___x_1276_ = lean_box(0);
v___x_1277_ = 0;
v___x_1278_ = lean_box(v___x_1277_);
v___f_1279_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1279_, 0, v_a_1275_);
lean_closure_set(v___f_1279_, 1, v___x_1276_);
lean_closure_set(v___f_1279_, 2, v___x_1278_);
v___x_1280_ = 0;
v___x_1281_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v___f_1279_, v___x_1280_, v_a_1269_, v_a_1270_, v_a_1271_, v_a_1272_);
return v___x_1281_;
}
else
{
lean_object* v_a_1282_; lean_object* v___x_1284_; uint8_t v_isShared_1285_; uint8_t v_isSharedCheck_1289_; 
v_a_1282_ = lean_ctor_get(v___x_1274_, 0);
v_isSharedCheck_1289_ = !lean_is_exclusive(v___x_1274_);
if (v_isSharedCheck_1289_ == 0)
{
v___x_1284_ = v___x_1274_;
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
else
{
lean_inc(v_a_1282_);
lean_dec(v___x_1274_);
v___x_1284_ = lean_box(0);
v_isShared_1285_ = v_isSharedCheck_1289_;
goto v_resetjp_1283_;
}
v_resetjp_1283_:
{
lean_object* v___x_1287_; 
if (v_isShared_1285_ == 0)
{
v___x_1287_ = v___x_1284_;
goto v_reusejp_1286_;
}
else
{
lean_object* v_reuseFailAlloc_1288_; 
v_reuseFailAlloc_1288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1288_, 0, v_a_1282_);
v___x_1287_ = v_reuseFailAlloc_1288_;
goto v_reusejp_1286_;
}
v_reusejp_1286_:
{
return v___x_1287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object* v_e_1290_, lean_object* v_a_1291_, lean_object* v_a_1292_, lean_object* v_a_1293_, lean_object* v_a_1294_, lean_object* v_a_1295_){
_start:
{
lean_object* v_res_1296_; 
v_res_1296_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_e_1290_, v_a_1291_, v_a_1292_, v_a_1293_, v_a_1294_);
lean_dec(v_a_1294_);
lean_dec_ref(v_a_1293_);
lean_dec(v_a_1292_);
lean_dec_ref(v_a_1291_);
return v_res_1296_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1297_, lean_object* v_b_1298_, lean_object* v_c_1299_, lean_object* v___y_1300_, lean_object* v___y_1301_, lean_object* v___y_1302_, lean_object* v___y_1303_){
_start:
{
lean_object* v___x_1305_; 
lean_inc(v___y_1303_);
lean_inc_ref(v___y_1302_);
lean_inc(v___y_1301_);
lean_inc_ref(v___y_1300_);
v___x_1305_ = lean_apply_7(v_k_1297_, v_b_1298_, v_c_1299_, v___y_1300_, v___y_1301_, v___y_1302_, v___y_1303_, lean_box(0));
return v___x_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1306_, lean_object* v_b_1307_, lean_object* v_c_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_, lean_object* v___y_1313_){
_start:
{
lean_object* v_res_1314_; 
v_res_1314_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1306_, v_b_1307_, v_c_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_);
lean_dec(v___y_1312_);
lean_dec_ref(v___y_1311_);
lean_dec(v___y_1310_);
lean_dec_ref(v___y_1309_);
return v_res_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object* v_type_1315_, lean_object* v_k_1316_, uint8_t v_cleanupAnnotations_1317_, uint8_t v_whnfType_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v___f_1324_; lean_object* v___x_1325_; 
v___f_1324_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1324_, 0, v_k_1316_);
v___x_1325_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1315_, v___f_1324_, v_cleanupAnnotations_1317_, v_whnfType_1318_, v___y_1319_, v___y_1320_, v___y_1321_, v___y_1322_);
if (lean_obj_tag(v___x_1325_) == 0)
{
lean_object* v_a_1326_; lean_object* v___x_1328_; uint8_t v_isShared_1329_; uint8_t v_isSharedCheck_1333_; 
v_a_1326_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1333_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1328_ = v___x_1325_;
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
else
{
lean_inc(v_a_1326_);
lean_dec(v___x_1325_);
v___x_1328_ = lean_box(0);
v_isShared_1329_ = v_isSharedCheck_1333_;
goto v_resetjp_1327_;
}
v_resetjp_1327_:
{
lean_object* v___x_1331_; 
if (v_isShared_1329_ == 0)
{
v___x_1331_ = v___x_1328_;
goto v_reusejp_1330_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_a_1326_);
v___x_1331_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1330_;
}
v_reusejp_1330_:
{
return v___x_1331_;
}
}
}
else
{
lean_object* v_a_1334_; lean_object* v___x_1336_; uint8_t v_isShared_1337_; uint8_t v_isSharedCheck_1341_; 
v_a_1334_ = lean_ctor_get(v___x_1325_, 0);
v_isSharedCheck_1341_ = !lean_is_exclusive(v___x_1325_);
if (v_isSharedCheck_1341_ == 0)
{
v___x_1336_ = v___x_1325_;
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
else
{
lean_inc(v_a_1334_);
lean_dec(v___x_1325_);
v___x_1336_ = lean_box(0);
v_isShared_1337_ = v_isSharedCheck_1341_;
goto v_resetjp_1335_;
}
v_resetjp_1335_:
{
lean_object* v___x_1339_; 
if (v_isShared_1337_ == 0)
{
v___x_1339_ = v___x_1336_;
goto v_reusejp_1338_;
}
else
{
lean_object* v_reuseFailAlloc_1340_; 
v_reuseFailAlloc_1340_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1340_, 0, v_a_1334_);
v___x_1339_ = v_reuseFailAlloc_1340_;
goto v_reusejp_1338_;
}
v_reusejp_1338_:
{
return v___x_1339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object* v_type_1342_, lean_object* v_k_1343_, lean_object* v_cleanupAnnotations_1344_, lean_object* v_whnfType_1345_, lean_object* v___y_1346_, lean_object* v___y_1347_, lean_object* v___y_1348_, lean_object* v___y_1349_, lean_object* v___y_1350_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1351_; uint8_t v_whnfType_boxed_1352_; lean_object* v_res_1353_; 
v_cleanupAnnotations_boxed_1351_ = lean_unbox(v_cleanupAnnotations_1344_);
v_whnfType_boxed_1352_ = lean_unbox(v_whnfType_1345_);
v_res_1353_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1342_, v_k_1343_, v_cleanupAnnotations_boxed_1351_, v_whnfType_boxed_1352_, v___y_1346_, v___y_1347_, v___y_1348_, v___y_1349_);
lean_dec(v___y_1349_);
lean_dec_ref(v___y_1348_);
lean_dec(v___y_1347_);
lean_dec_ref(v___y_1346_);
return v_res_1353_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object* v_00_u03b1_1354_, lean_object* v_type_1355_, lean_object* v_k_1356_, uint8_t v_cleanupAnnotations_1357_, uint8_t v_whnfType_1358_, lean_object* v___y_1359_, lean_object* v___y_1360_, lean_object* v___y_1361_, lean_object* v___y_1362_){
_start:
{
lean_object* v___x_1364_; 
v___x_1364_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1355_, v_k_1356_, v_cleanupAnnotations_1357_, v_whnfType_1358_, v___y_1359_, v___y_1360_, v___y_1361_, v___y_1362_);
return v___x_1364_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object* v_00_u03b1_1365_, lean_object* v_type_1366_, lean_object* v_k_1367_, lean_object* v_cleanupAnnotations_1368_, lean_object* v_whnfType_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_, lean_object* v___y_1372_, lean_object* v___y_1373_, lean_object* v___y_1374_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1375_; uint8_t v_whnfType_boxed_1376_; lean_object* v_res_1377_; 
v_cleanupAnnotations_boxed_1375_ = lean_unbox(v_cleanupAnnotations_1368_);
v_whnfType_boxed_1376_ = lean_unbox(v_whnfType_1369_);
v_res_1377_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(v_00_u03b1_1365_, v_type_1366_, v_k_1367_, v_cleanupAnnotations_boxed_1375_, v_whnfType_boxed_1376_, v___y_1370_, v___y_1371_, v___y_1372_, v___y_1373_);
lean_dec(v___y_1373_);
lean_dec_ref(v___y_1372_);
lean_dec(v___y_1371_);
lean_dec_ref(v___y_1370_);
return v_res_1377_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object* v_as_1381_, size_t v_sz_1382_, size_t v_i_1383_, lean_object* v_b_1384_, lean_object* v___y_1385_, lean_object* v___y_1386_, lean_object* v___y_1387_, lean_object* v___y_1388_){
_start:
{
uint8_t v___x_1390_; 
v___x_1390_ = lean_usize_dec_lt(v_i_1383_, v_sz_1382_);
if (v___x_1390_ == 0)
{
lean_object* v___x_1391_; 
v___x_1391_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1391_, 0, v_b_1384_);
return v___x_1391_;
}
else
{
lean_object* v_fst_1392_; lean_object* v_snd_1393_; lean_object* v___x_1395_; uint8_t v_isShared_1396_; uint8_t v_isSharedCheck_1445_; 
v_fst_1392_ = lean_ctor_get(v_b_1384_, 0);
v_snd_1393_ = lean_ctor_get(v_b_1384_, 1);
v_isSharedCheck_1445_ = !lean_is_exclusive(v_b_1384_);
if (v_isSharedCheck_1445_ == 0)
{
v___x_1395_ = v_b_1384_;
v_isShared_1396_ = v_isSharedCheck_1445_;
goto v_resetjp_1394_;
}
else
{
lean_inc(v_snd_1393_);
lean_inc(v_fst_1392_);
lean_dec(v_b_1384_);
v___x_1395_ = lean_box(0);
v_isShared_1396_ = v_isSharedCheck_1445_;
goto v_resetjp_1394_;
}
v_resetjp_1394_:
{
lean_object* v_next_1402_; 
v_next_1402_ = lean_ctor_get(v_snd_1393_, 0);
lean_inc(v_next_1402_);
if (lean_obj_tag(v_next_1402_) == 0)
{
goto v___jp_1397_;
}
else
{
lean_object* v_upperBound_1403_; lean_object* v_val_1404_; lean_object* v___x_1406_; uint8_t v_isShared_1407_; uint8_t v_isSharedCheck_1444_; 
v_upperBound_1403_ = lean_ctor_get(v_snd_1393_, 1);
v_val_1404_ = lean_ctor_get(v_next_1402_, 0);
v_isSharedCheck_1444_ = !lean_is_exclusive(v_next_1402_);
if (v_isSharedCheck_1444_ == 0)
{
v___x_1406_ = v_next_1402_;
v_isShared_1407_ = v_isSharedCheck_1444_;
goto v_resetjp_1405_;
}
else
{
lean_inc(v_val_1404_);
lean_dec(v_next_1402_);
v___x_1406_ = lean_box(0);
v_isShared_1407_ = v_isSharedCheck_1444_;
goto v_resetjp_1405_;
}
v_resetjp_1405_:
{
uint8_t v___x_1408_; 
v___x_1408_ = lean_nat_dec_lt(v_val_1404_, v_upperBound_1403_);
if (v___x_1408_ == 0)
{
lean_del_object(v___x_1406_);
lean_dec(v_val_1404_);
goto v___jp_1397_;
}
else
{
lean_object* v___x_1410_; uint8_t v_isShared_1411_; uint8_t v_isSharedCheck_1441_; 
lean_inc(v_upperBound_1403_);
lean_del_object(v___x_1395_);
v_isSharedCheck_1441_ = !lean_is_exclusive(v_snd_1393_);
if (v_isSharedCheck_1441_ == 0)
{
lean_object* v_unused_1442_; lean_object* v_unused_1443_; 
v_unused_1442_ = lean_ctor_get(v_snd_1393_, 1);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_snd_1393_, 0);
lean_dec(v_unused_1443_);
v___x_1410_ = v_snd_1393_;
v_isShared_1411_ = v_isSharedCheck_1441_;
goto v_resetjp_1409_;
}
else
{
lean_dec(v_snd_1393_);
v___x_1410_ = lean_box(0);
v_isShared_1411_ = v_isSharedCheck_1441_;
goto v_resetjp_1409_;
}
v_resetjp_1409_:
{
lean_object* v_a_1412_; lean_object* v___x_1413_; 
v_a_1412_ = lean_array_uget_borrowed(v_as_1381_, v_i_1383_);
lean_inc(v___y_1388_);
lean_inc_ref(v___y_1387_);
lean_inc(v___y_1386_);
lean_inc_ref(v___y_1385_);
lean_inc(v_a_1412_);
v___x_1413_ = lean_infer_type(v_a_1412_, v___y_1385_, v___y_1386_, v___y_1387_, v___y_1388_);
if (lean_obj_tag(v___x_1413_) == 0)
{
lean_object* v_a_1414_; lean_object* v_a_1416_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; 
v_a_1414_ = lean_ctor_get(v___x_1413_, 0);
lean_inc(v_a_1414_);
lean_dec_ref_known(v___x_1413_, 1);
v___x_1420_ = lean_unsigned_to_nat(1u);
v___x_1421_ = lean_nat_add(v_val_1404_, v___x_1420_);
if (v_isShared_1407_ == 0)
{
lean_ctor_set(v___x_1406_, 0, v___x_1421_);
v___x_1423_ = v___x_1406_;
goto v_reusejp_1422_;
}
else
{
lean_object* v_reuseFailAlloc_1432_; 
v_reuseFailAlloc_1432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1432_, 0, v___x_1421_);
v___x_1423_ = v_reuseFailAlloc_1432_;
goto v_reusejp_1422_;
}
v___jp_1415_:
{
size_t v___x_1417_; size_t v___x_1418_; 
v___x_1417_ = ((size_t)1ULL);
v___x_1418_ = lean_usize_add(v_i_1383_, v___x_1417_);
v_i_1383_ = v___x_1418_;
v_b_1384_ = v_a_1416_;
goto _start;
}
v_reusejp_1422_:
{
lean_object* v___x_1425_; 
if (v_isShared_1411_ == 0)
{
lean_ctor_set(v___x_1410_, 0, v___x_1423_);
v___x_1425_ = v___x_1410_;
goto v_reusejp_1424_;
}
else
{
lean_object* v_reuseFailAlloc_1431_; 
v_reuseFailAlloc_1431_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1431_, 0, v___x_1423_);
lean_ctor_set(v_reuseFailAlloc_1431_, 1, v_upperBound_1403_);
v___x_1425_ = v_reuseFailAlloc_1431_;
goto v_reusejp_1424_;
}
v_reusejp_1424_:
{
lean_object* v___x_1426_; uint8_t v___x_1427_; 
v___x_1426_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1));
v___x_1427_ = l_Lean_Expr_isAppOf(v_a_1414_, v___x_1426_);
lean_dec(v_a_1414_);
if (v___x_1427_ == 0)
{
lean_object* v___x_1428_; 
lean_dec(v_val_1404_);
v___x_1428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1428_, 0, v_fst_1392_);
lean_ctor_set(v___x_1428_, 1, v___x_1425_);
v_a_1416_ = v___x_1428_;
goto v___jp_1415_;
}
else
{
lean_object* v___x_1429_; lean_object* v___x_1430_; 
v___x_1429_ = lean_array_push(v_fst_1392_, v_val_1404_);
v___x_1430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1430_, 0, v___x_1429_);
lean_ctor_set(v___x_1430_, 1, v___x_1425_);
v_a_1416_ = v___x_1430_;
goto v___jp_1415_;
}
}
}
}
else
{
lean_object* v_a_1433_; lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_del_object(v___x_1410_);
lean_del_object(v___x_1406_);
lean_dec(v_val_1404_);
lean_dec(v_upperBound_1403_);
lean_dec(v_fst_1392_);
v_a_1433_ = lean_ctor_get(v___x_1413_, 0);
v_isSharedCheck_1440_ = !lean_is_exclusive(v___x_1413_);
if (v_isSharedCheck_1440_ == 0)
{
v___x_1435_ = v___x_1413_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_inc(v_a_1433_);
lean_dec(v___x_1413_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_a_1433_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
}
}
v___jp_1397_:
{
lean_object* v___x_1399_; 
if (v_isShared_1396_ == 0)
{
v___x_1399_ = v___x_1395_;
goto v_reusejp_1398_;
}
else
{
lean_object* v_reuseFailAlloc_1401_; 
v_reuseFailAlloc_1401_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1401_, 0, v_fst_1392_);
lean_ctor_set(v_reuseFailAlloc_1401_, 1, v_snd_1393_);
v___x_1399_ = v_reuseFailAlloc_1401_;
goto v_reusejp_1398_;
}
v_reusejp_1398_:
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v___x_1399_);
return v___x_1400_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object* v_as_1446_, lean_object* v_sz_1447_, lean_object* v_i_1448_, lean_object* v_b_1449_, lean_object* v___y_1450_, lean_object* v___y_1451_, lean_object* v___y_1452_, lean_object* v___y_1453_, lean_object* v___y_1454_){
_start:
{
size_t v_sz_boxed_1455_; size_t v_i_boxed_1456_; lean_object* v_res_1457_; 
v_sz_boxed_1455_ = lean_unbox_usize(v_sz_1447_);
lean_dec(v_sz_1447_);
v_i_boxed_1456_ = lean_unbox_usize(v_i_1448_);
lean_dec(v_i_1448_);
v_res_1457_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_as_1446_, v_sz_boxed_1455_, v_i_boxed_1456_, v_b_1449_, v___y_1450_, v___y_1451_, v___y_1452_, v___y_1453_);
lean_dec(v___y_1453_);
lean_dec_ref(v___y_1452_);
lean_dec(v___y_1451_);
lean_dec_ref(v___y_1450_);
lean_dec_ref(v_as_1446_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object* v_declName_1462_, lean_object* v_args_1463_, lean_object* v_x_1464_, lean_object* v___y_1465_, lean_object* v___y_1466_, lean_object* v___y_1467_, lean_object* v___y_1468_){
_start:
{
lean_object* v___x_1470_; lean_object* v___y_1472_; lean_object* v_env_1497_; lean_object* v___x_1498_; 
v___x_1470_ = lean_st_ref_get(v___y_1468_);
v_env_1497_ = lean_ctor_get(v___x_1470_, 0);
lean_inc_ref(v_env_1497_);
lean_dec(v___x_1470_);
v___x_1498_ = l_Lean_getOutParamPositions_x3f(v_env_1497_, v_declName_1462_);
if (lean_obj_tag(v___x_1498_) == 0)
{
lean_object* v___x_1499_; 
v___x_1499_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___y_1472_ = v___x_1499_;
goto v___jp_1471_;
}
else
{
lean_object* v_val_1500_; 
v_val_1500_ = lean_ctor_get(v___x_1498_, 0);
lean_inc(v_val_1500_);
lean_dec_ref_known(v___x_1498_, 1);
v___y_1472_ = v_val_1500_;
goto v___jp_1471_;
}
v___jp_1471_:
{
lean_object* v___x_1473_; lean_object* v___x_1474_; lean_object* v___x_1475_; lean_object* v___x_1476_; size_t v_sz_1477_; size_t v___x_1478_; lean_object* v___x_1479_; 
v___x_1473_ = lean_array_get_size(v_args_1463_);
v___x_1474_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_1475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1474_);
lean_ctor_set(v___x_1475_, 1, v___x_1473_);
v___x_1476_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1476_, 0, v___y_1472_);
lean_ctor_set(v___x_1476_, 1, v___x_1475_);
v_sz_1477_ = lean_array_size(v_args_1463_);
v___x_1478_ = ((size_t)0ULL);
v___x_1479_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_args_1463_, v_sz_1477_, v___x_1478_, v___x_1476_, v___y_1465_, v___y_1466_, v___y_1467_, v___y_1468_);
if (lean_obj_tag(v___x_1479_) == 0)
{
lean_object* v_a_1480_; lean_object* v___x_1482_; uint8_t v_isShared_1483_; uint8_t v_isSharedCheck_1488_; 
v_a_1480_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1488_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1488_ == 0)
{
v___x_1482_ = v___x_1479_;
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
else
{
lean_inc(v_a_1480_);
lean_dec(v___x_1479_);
v___x_1482_ = lean_box(0);
v_isShared_1483_ = v_isSharedCheck_1488_;
goto v_resetjp_1481_;
}
v_resetjp_1481_:
{
lean_object* v_fst_1484_; lean_object* v___x_1486_; 
v_fst_1484_ = lean_ctor_get(v_a_1480_, 0);
lean_inc(v_fst_1484_);
lean_dec(v_a_1480_);
if (v_isShared_1483_ == 0)
{
lean_ctor_set(v___x_1482_, 0, v_fst_1484_);
v___x_1486_ = v___x_1482_;
goto v_reusejp_1485_;
}
else
{
lean_object* v_reuseFailAlloc_1487_; 
v_reuseFailAlloc_1487_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1487_, 0, v_fst_1484_);
v___x_1486_ = v_reuseFailAlloc_1487_;
goto v_reusejp_1485_;
}
v_reusejp_1485_:
{
return v___x_1486_;
}
}
}
else
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1496_; 
v_a_1489_ = lean_ctor_get(v___x_1479_, 0);
v_isSharedCheck_1496_ = !lean_is_exclusive(v___x_1479_);
if (v_isSharedCheck_1496_ == 0)
{
v___x_1491_ = v___x_1479_;
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1479_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1496_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v___x_1494_; 
if (v_isShared_1492_ == 0)
{
v___x_1494_ = v___x_1491_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_a_1489_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object* v_declName_1501_, lean_object* v_args_1502_, lean_object* v_x_1503_, lean_object* v___y_1504_, lean_object* v___y_1505_, lean_object* v___y_1506_, lean_object* v___y_1507_, lean_object* v___y_1508_){
_start:
{
lean_object* v_res_1509_; 
v_res_1509_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(v_declName_1501_, v_args_1502_, v_x_1503_, v___y_1504_, v___y_1505_, v___y_1506_, v___y_1507_);
lean_dec(v___y_1507_);
lean_dec_ref(v___y_1506_);
lean_dec(v___y_1505_);
lean_dec_ref(v___y_1504_);
lean_dec_ref(v_x_1503_);
lean_dec_ref(v_args_1502_);
lean_dec(v_declName_1501_);
return v_res_1509_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object* v_classTy_1510_, lean_object* v_a_1511_, lean_object* v_a_1512_, lean_object* v_a_1513_, lean_object* v_a_1514_){
_start:
{
lean_object* v___x_1516_; 
v___x_1516_ = l_Lean_Expr_getAppFn(v_classTy_1510_);
if (lean_obj_tag(v___x_1516_) == 4)
{
lean_object* v_declName_1517_; lean_object* v___x_1518_; 
v_declName_1517_ = lean_ctor_get(v___x_1516_, 0);
lean_inc(v_declName_1517_);
lean_inc(v_a_1514_);
lean_inc_ref(v_a_1513_);
lean_inc(v_a_1512_);
lean_inc_ref(v_a_1511_);
v___x_1518_ = lean_infer_type(v___x_1516_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
if (lean_obj_tag(v___x_1518_) == 0)
{
lean_object* v_a_1519_; lean_object* v___f_1520_; uint8_t v___x_1521_; lean_object* v___x_1522_; 
v_a_1519_ = lean_ctor_get(v___x_1518_, 0);
lean_inc(v_a_1519_);
lean_dec_ref_known(v___x_1518_, 1);
v___f_1520_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1520_, 0, v_declName_1517_);
v___x_1521_ = 0;
v___x_1522_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_1519_, v___f_1520_, v___x_1521_, v___x_1521_, v_a_1511_, v_a_1512_, v_a_1513_, v_a_1514_);
return v___x_1522_;
}
else
{
lean_object* v_a_1523_; lean_object* v___x_1525_; uint8_t v_isShared_1526_; uint8_t v_isSharedCheck_1530_; 
lean_dec(v_declName_1517_);
v_a_1523_ = lean_ctor_get(v___x_1518_, 0);
v_isSharedCheck_1530_ = !lean_is_exclusive(v___x_1518_);
if (v_isSharedCheck_1530_ == 0)
{
v___x_1525_ = v___x_1518_;
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
else
{
lean_inc(v_a_1523_);
lean_dec(v___x_1518_);
v___x_1525_ = lean_box(0);
v_isShared_1526_ = v_isSharedCheck_1530_;
goto v_resetjp_1524_;
}
v_resetjp_1524_:
{
lean_object* v___x_1528_; 
if (v_isShared_1526_ == 0)
{
v___x_1528_ = v___x_1525_;
goto v_reusejp_1527_;
}
else
{
lean_object* v_reuseFailAlloc_1529_; 
v_reuseFailAlloc_1529_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1529_, 0, v_a_1523_);
v___x_1528_ = v_reuseFailAlloc_1529_;
goto v_reusejp_1527_;
}
v_reusejp_1527_:
{
return v___x_1528_;
}
}
}
}
else
{
lean_object* v___x_1531_; lean_object* v___x_1532_; 
lean_dec_ref(v___x_1516_);
v___x_1531_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_1532_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1532_, 0, v___x_1531_);
return v___x_1532_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object* v_classTy_1533_, lean_object* v_a_1534_, lean_object* v_a_1535_, lean_object* v_a_1536_, lean_object* v_a_1537_, lean_object* v_a_1538_){
_start:
{
lean_object* v_res_1539_; 
v_res_1539_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_classTy_1533_, v_a_1534_, v_a_1535_, v_a_1536_, v_a_1537_);
lean_dec(v_a_1537_);
lean_dec_ref(v_a_1536_);
lean_dec(v_a_1535_);
lean_dec_ref(v_a_1534_);
lean_dec_ref(v_classTy_1533_);
return v_res_1539_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_a_1540_, lean_object* v_as_1541_, lean_object* v_j_1542_){
_start:
{
lean_object* v___x_1543_; uint8_t v___x_1544_; 
v___x_1543_ = lean_array_get_size(v_as_1541_);
v___x_1544_ = lean_nat_dec_lt(v_j_1542_, v___x_1543_);
if (v___x_1544_ == 0)
{
lean_object* v___x_1545_; 
lean_dec(v_j_1542_);
v___x_1545_ = lean_box(0);
return v___x_1545_;
}
else
{
lean_object* v___x_1546_; lean_object* v___x_1547_; uint8_t v___x_1548_; 
v___x_1546_ = lean_array_fget_borrowed(v_as_1541_, v_j_1542_);
v___x_1547_ = l_Lean_Expr_mvarId_x21(v___x_1546_);
v___x_1548_ = l_Lean_instBEqMVarId_beq(v___x_1547_, v_a_1540_);
lean_dec(v___x_1547_);
if (v___x_1548_ == 0)
{
lean_object* v___x_1549_; lean_object* v___x_1550_; 
v___x_1549_ = lean_unsigned_to_nat(1u);
v___x_1550_ = lean_nat_add(v_j_1542_, v___x_1549_);
lean_dec(v_j_1542_);
v_j_1542_ = v___x_1550_;
goto _start;
}
else
{
lean_object* v___x_1552_; 
v___x_1552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1552_, 0, v_j_1542_);
return v___x_1552_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_a_1553_, lean_object* v_as_1554_, lean_object* v_j_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1553_, v_as_1554_, v_j_1555_);
lean_dec_ref(v_as_1554_);
lean_dec(v_a_1553_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1557_, lean_object* v_x_1558_, lean_object* v_x_1559_, lean_object* v_x_1560_){
_start:
{
lean_object* v_ks_1561_; lean_object* v_vs_1562_; lean_object* v___x_1564_; uint8_t v_isShared_1565_; uint8_t v_isSharedCheck_1586_; 
v_ks_1561_ = lean_ctor_get(v_x_1557_, 0);
v_vs_1562_ = lean_ctor_get(v_x_1557_, 1);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_x_1557_);
if (v_isSharedCheck_1586_ == 0)
{
v___x_1564_ = v_x_1557_;
v_isShared_1565_ = v_isSharedCheck_1586_;
goto v_resetjp_1563_;
}
else
{
lean_inc(v_vs_1562_);
lean_inc(v_ks_1561_);
lean_dec(v_x_1557_);
v___x_1564_ = lean_box(0);
v_isShared_1565_ = v_isSharedCheck_1586_;
goto v_resetjp_1563_;
}
v_resetjp_1563_:
{
lean_object* v___x_1566_; uint8_t v___x_1567_; 
v___x_1566_ = lean_array_get_size(v_ks_1561_);
v___x_1567_ = lean_nat_dec_lt(v_x_1558_, v___x_1566_);
if (v___x_1567_ == 0)
{
lean_object* v___x_1568_; lean_object* v___x_1569_; lean_object* v___x_1571_; 
lean_dec(v_x_1558_);
v___x_1568_ = lean_array_push(v_ks_1561_, v_x_1559_);
v___x_1569_ = lean_array_push(v_vs_1562_, v_x_1560_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 1, v___x_1569_);
lean_ctor_set(v___x_1564_, 0, v___x_1568_);
v___x_1571_ = v___x_1564_;
goto v_reusejp_1570_;
}
else
{
lean_object* v_reuseFailAlloc_1572_; 
v_reuseFailAlloc_1572_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1572_, 0, v___x_1568_);
lean_ctor_set(v_reuseFailAlloc_1572_, 1, v___x_1569_);
v___x_1571_ = v_reuseFailAlloc_1572_;
goto v_reusejp_1570_;
}
v_reusejp_1570_:
{
return v___x_1571_;
}
}
else
{
lean_object* v_k_x27_1573_; uint8_t v___x_1574_; 
v_k_x27_1573_ = lean_array_fget_borrowed(v_ks_1561_, v_x_1558_);
v___x_1574_ = l_Lean_instBEqMVarId_beq(v_x_1559_, v_k_x27_1573_);
if (v___x_1574_ == 0)
{
lean_object* v___x_1576_; 
if (v_isShared_1565_ == 0)
{
v___x_1576_ = v___x_1564_;
goto v_reusejp_1575_;
}
else
{
lean_object* v_reuseFailAlloc_1580_; 
v_reuseFailAlloc_1580_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1580_, 0, v_ks_1561_);
lean_ctor_set(v_reuseFailAlloc_1580_, 1, v_vs_1562_);
v___x_1576_ = v_reuseFailAlloc_1580_;
goto v_reusejp_1575_;
}
v_reusejp_1575_:
{
lean_object* v___x_1577_; lean_object* v___x_1578_; 
v___x_1577_ = lean_unsigned_to_nat(1u);
v___x_1578_ = lean_nat_add(v_x_1558_, v___x_1577_);
lean_dec(v_x_1558_);
v_x_1557_ = v___x_1576_;
v_x_1558_ = v___x_1578_;
goto _start;
}
}
else
{
lean_object* v___x_1581_; lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1581_ = lean_array_fset(v_ks_1561_, v_x_1558_, v_x_1559_);
v___x_1582_ = lean_array_fset(v_vs_1562_, v_x_1558_, v_x_1560_);
lean_dec(v_x_1558_);
if (v_isShared_1565_ == 0)
{
lean_ctor_set(v___x_1564_, 1, v___x_1582_);
lean_ctor_set(v___x_1564_, 0, v___x_1581_);
v___x_1584_ = v___x_1564_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v___x_1581_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v___x_1582_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1587_, lean_object* v_k_1588_, lean_object* v_v_1589_){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = lean_unsigned_to_nat(0u);
v___x_1591_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1587_, v___x_1590_, v_k_1588_, v_v_1589_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1592_, size_t v_x_1593_, size_t v_x_1594_, lean_object* v_x_1595_, lean_object* v_x_1596_){
_start:
{
if (lean_obj_tag(v_x_1592_) == 0)
{
lean_object* v_es_1597_; size_t v___x_1598_; size_t v___x_1599_; lean_object* v_j_1600_; lean_object* v___x_1601_; uint8_t v___x_1602_; 
v_es_1597_ = lean_ctor_get(v_x_1592_, 0);
v___x_1598_ = ((size_t)31ULL);
v___x_1599_ = lean_usize_land(v_x_1593_, v___x_1598_);
v_j_1600_ = lean_usize_to_nat(v___x_1599_);
v___x_1601_ = lean_array_get_size(v_es_1597_);
v___x_1602_ = lean_nat_dec_lt(v_j_1600_, v___x_1601_);
if (v___x_1602_ == 0)
{
lean_dec(v_j_1600_);
lean_dec(v_x_1596_);
lean_dec(v_x_1595_);
return v_x_1592_;
}
else
{
lean_object* v___x_1604_; uint8_t v_isShared_1605_; uint8_t v_isSharedCheck_1641_; 
lean_inc_ref(v_es_1597_);
v_isSharedCheck_1641_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1641_ == 0)
{
lean_object* v_unused_1642_; 
v_unused_1642_ = lean_ctor_get(v_x_1592_, 0);
lean_dec(v_unused_1642_);
v___x_1604_ = v_x_1592_;
v_isShared_1605_ = v_isSharedCheck_1641_;
goto v_resetjp_1603_;
}
else
{
lean_dec(v_x_1592_);
v___x_1604_ = lean_box(0);
v_isShared_1605_ = v_isSharedCheck_1641_;
goto v_resetjp_1603_;
}
v_resetjp_1603_:
{
lean_object* v_v_1606_; lean_object* v___x_1607_; lean_object* v_xs_x27_1608_; lean_object* v___y_1610_; 
v_v_1606_ = lean_array_fget(v_es_1597_, v_j_1600_);
v___x_1607_ = lean_box(0);
v_xs_x27_1608_ = lean_array_fset(v_es_1597_, v_j_1600_, v___x_1607_);
switch(lean_obj_tag(v_v_1606_))
{
case 0:
{
lean_object* v_key_1615_; lean_object* v_val_1616_; lean_object* v___x_1618_; uint8_t v_isShared_1619_; uint8_t v_isSharedCheck_1626_; 
v_key_1615_ = lean_ctor_get(v_v_1606_, 0);
v_val_1616_ = lean_ctor_get(v_v_1606_, 1);
v_isSharedCheck_1626_ = !lean_is_exclusive(v_v_1606_);
if (v_isSharedCheck_1626_ == 0)
{
v___x_1618_ = v_v_1606_;
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
else
{
lean_inc(v_val_1616_);
lean_inc(v_key_1615_);
lean_dec(v_v_1606_);
v___x_1618_ = lean_box(0);
v_isShared_1619_ = v_isSharedCheck_1626_;
goto v_resetjp_1617_;
}
v_resetjp_1617_:
{
uint8_t v___x_1620_; 
v___x_1620_ = l_Lean_instBEqMVarId_beq(v_x_1595_, v_key_1615_);
if (v___x_1620_ == 0)
{
lean_object* v___x_1621_; lean_object* v___x_1622_; 
lean_del_object(v___x_1618_);
v___x_1621_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1615_, v_val_1616_, v_x_1595_, v_x_1596_);
v___x_1622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1622_, 0, v___x_1621_);
v___y_1610_ = v___x_1622_;
goto v___jp_1609_;
}
else
{
lean_object* v___x_1624_; 
lean_dec(v_val_1616_);
lean_dec(v_key_1615_);
if (v_isShared_1619_ == 0)
{
lean_ctor_set(v___x_1618_, 1, v_x_1596_);
lean_ctor_set(v___x_1618_, 0, v_x_1595_);
v___x_1624_ = v___x_1618_;
goto v_reusejp_1623_;
}
else
{
lean_object* v_reuseFailAlloc_1625_; 
v_reuseFailAlloc_1625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1625_, 0, v_x_1595_);
lean_ctor_set(v_reuseFailAlloc_1625_, 1, v_x_1596_);
v___x_1624_ = v_reuseFailAlloc_1625_;
goto v_reusejp_1623_;
}
v_reusejp_1623_:
{
v___y_1610_ = v___x_1624_;
goto v___jp_1609_;
}
}
}
}
case 1:
{
lean_object* v_node_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1639_; 
v_node_1627_ = lean_ctor_get(v_v_1606_, 0);
v_isSharedCheck_1639_ = !lean_is_exclusive(v_v_1606_);
if (v_isSharedCheck_1639_ == 0)
{
v___x_1629_ = v_v_1606_;
v_isShared_1630_ = v_isSharedCheck_1639_;
goto v_resetjp_1628_;
}
else
{
lean_inc(v_node_1627_);
lean_dec(v_v_1606_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1639_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
size_t v___x_1631_; size_t v___x_1632_; size_t v___x_1633_; size_t v___x_1634_; lean_object* v___x_1635_; lean_object* v___x_1637_; 
v___x_1631_ = ((size_t)5ULL);
v___x_1632_ = lean_usize_shift_right(v_x_1593_, v___x_1631_);
v___x_1633_ = ((size_t)1ULL);
v___x_1634_ = lean_usize_add(v_x_1594_, v___x_1633_);
v___x_1635_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_node_1627_, v___x_1632_, v___x_1634_, v_x_1595_, v_x_1596_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 0, v___x_1635_);
v___x_1637_ = v___x_1629_;
goto v_reusejp_1636_;
}
else
{
lean_object* v_reuseFailAlloc_1638_; 
v_reuseFailAlloc_1638_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1638_, 0, v___x_1635_);
v___x_1637_ = v_reuseFailAlloc_1638_;
goto v_reusejp_1636_;
}
v_reusejp_1636_:
{
v___y_1610_ = v___x_1637_;
goto v___jp_1609_;
}
}
}
default: 
{
lean_object* v___x_1640_; 
v___x_1640_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1640_, 0, v_x_1595_);
lean_ctor_set(v___x_1640_, 1, v_x_1596_);
v___y_1610_ = v___x_1640_;
goto v___jp_1609_;
}
}
v___jp_1609_:
{
lean_object* v___x_1611_; lean_object* v___x_1613_; 
v___x_1611_ = lean_array_fset(v_xs_x27_1608_, v_j_1600_, v___y_1610_);
lean_dec(v_j_1600_);
if (v_isShared_1605_ == 0)
{
lean_ctor_set(v___x_1604_, 0, v___x_1611_);
v___x_1613_ = v___x_1604_;
goto v_reusejp_1612_;
}
else
{
lean_object* v_reuseFailAlloc_1614_; 
v_reuseFailAlloc_1614_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1614_, 0, v___x_1611_);
v___x_1613_ = v_reuseFailAlloc_1614_;
goto v_reusejp_1612_;
}
v_reusejp_1612_:
{
return v___x_1613_;
}
}
}
}
}
else
{
lean_object* v_ks_1643_; lean_object* v_vs_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1662_; 
v_ks_1643_ = lean_ctor_get(v_x_1592_, 0);
v_vs_1644_ = lean_ctor_get(v_x_1592_, 1);
v_isSharedCheck_1662_ = !lean_is_exclusive(v_x_1592_);
if (v_isSharedCheck_1662_ == 0)
{
v___x_1646_ = v_x_1592_;
v_isShared_1647_ = v_isSharedCheck_1662_;
goto v_resetjp_1645_;
}
else
{
lean_inc(v_vs_1644_);
lean_inc(v_ks_1643_);
lean_dec(v_x_1592_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1662_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1649_; 
if (v_isShared_1647_ == 0)
{
v___x_1649_ = v___x_1646_;
goto v_reusejp_1648_;
}
else
{
lean_object* v_reuseFailAlloc_1661_; 
v_reuseFailAlloc_1661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1661_, 0, v_ks_1643_);
lean_ctor_set(v_reuseFailAlloc_1661_, 1, v_vs_1644_);
v___x_1649_ = v_reuseFailAlloc_1661_;
goto v_reusejp_1648_;
}
v_reusejp_1648_:
{
lean_object* v_newNode_1650_; size_t v___x_1651_; uint8_t v___x_1652_; 
v_newNode_1650_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v___x_1649_, v_x_1595_, v_x_1596_);
v___x_1651_ = ((size_t)7ULL);
v___x_1652_ = lean_usize_dec_le(v___x_1651_, v_x_1594_);
if (v___x_1652_ == 0)
{
lean_object* v___x_1653_; lean_object* v___x_1654_; uint8_t v___x_1655_; 
v___x_1653_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1650_);
v___x_1654_ = lean_unsigned_to_nat(4u);
v___x_1655_ = lean_nat_dec_lt(v___x_1653_, v___x_1654_);
lean_dec(v___x_1653_);
if (v___x_1655_ == 0)
{
lean_object* v_ks_1656_; lean_object* v_vs_1657_; lean_object* v___x_1658_; lean_object* v___x_1659_; lean_object* v___x_1660_; 
v_ks_1656_ = lean_ctor_get(v_newNode_1650_, 0);
lean_inc_ref(v_ks_1656_);
v_vs_1657_ = lean_ctor_get(v_newNode_1650_, 1);
lean_inc_ref(v_vs_1657_);
lean_dec_ref(v_newNode_1650_);
v___x_1658_ = lean_unsigned_to_nat(0u);
v___x_1659_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0);
v___x_1660_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_x_1594_, v_ks_1656_, v_vs_1657_, v___x_1658_, v___x_1659_);
lean_dec_ref(v_vs_1657_);
lean_dec_ref(v_ks_1656_);
return v___x_1660_;
}
else
{
return v_newNode_1650_;
}
}
else
{
return v_newNode_1650_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(size_t v_depth_1663_, lean_object* v_keys_1664_, lean_object* v_vals_1665_, lean_object* v_i_1666_, lean_object* v_entries_1667_){
_start:
{
lean_object* v___x_1668_; uint8_t v___x_1669_; 
v___x_1668_ = lean_array_get_size(v_keys_1664_);
v___x_1669_ = lean_nat_dec_lt(v_i_1666_, v___x_1668_);
if (v___x_1669_ == 0)
{
lean_dec(v_i_1666_);
return v_entries_1667_;
}
else
{
lean_object* v_k_1670_; lean_object* v_v_1671_; uint64_t v___x_1672_; size_t v_h_1673_; size_t v___x_1674_; lean_object* v___x_1675_; size_t v___x_1676_; size_t v___x_1677_; size_t v___x_1678_; size_t v_h_1679_; lean_object* v___x_1680_; lean_object* v___x_1681_; 
v_k_1670_ = lean_array_fget_borrowed(v_keys_1664_, v_i_1666_);
v_v_1671_ = lean_array_fget_borrowed(v_vals_1665_, v_i_1666_);
v___x_1672_ = l_Lean_instHashableMVarId_hash(v_k_1670_);
v_h_1673_ = lean_uint64_to_usize(v___x_1672_);
v___x_1674_ = ((size_t)5ULL);
v___x_1675_ = lean_unsigned_to_nat(1u);
v___x_1676_ = ((size_t)1ULL);
v___x_1677_ = lean_usize_sub(v_depth_1663_, v___x_1676_);
v___x_1678_ = lean_usize_mul(v___x_1674_, v___x_1677_);
v_h_1679_ = lean_usize_shift_right(v_h_1673_, v___x_1678_);
v___x_1680_ = lean_nat_add(v_i_1666_, v___x_1675_);
lean_dec(v_i_1666_);
lean_inc(v_v_1671_);
lean_inc(v_k_1670_);
v___x_1681_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_entries_1667_, v_h_1679_, v_depth_1663_, v_k_1670_, v_v_1671_);
v_i_1666_ = v___x_1680_;
v_entries_1667_ = v___x_1681_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1683_, lean_object* v_keys_1684_, lean_object* v_vals_1685_, lean_object* v_i_1686_, lean_object* v_entries_1687_){
_start:
{
size_t v_depth_boxed_1688_; lean_object* v_res_1689_; 
v_depth_boxed_1688_ = lean_unbox_usize(v_depth_1683_);
lean_dec(v_depth_1683_);
v_res_1689_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1688_, v_keys_1684_, v_vals_1685_, v_i_1686_, v_entries_1687_);
lean_dec_ref(v_vals_1685_);
lean_dec_ref(v_keys_1684_);
return v_res_1689_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1690_, lean_object* v_x_1691_, lean_object* v_x_1692_, lean_object* v_x_1693_, lean_object* v_x_1694_){
_start:
{
size_t v_x_1604__boxed_1695_; size_t v_x_1605__boxed_1696_; lean_object* v_res_1697_; 
v_x_1604__boxed_1695_ = lean_unbox_usize(v_x_1691_);
lean_dec(v_x_1691_);
v_x_1605__boxed_1696_ = lean_unbox_usize(v_x_1692_);
lean_dec(v_x_1692_);
v_res_1697_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1690_, v_x_1604__boxed_1695_, v_x_1605__boxed_1696_, v_x_1693_, v_x_1694_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(lean_object* v_x_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_){
_start:
{
uint64_t v___x_1701_; size_t v___x_1702_; size_t v___x_1703_; lean_object* v___x_1704_; 
v___x_1701_ = l_Lean_instHashableMVarId_hash(v_x_1699_);
v___x_1702_ = lean_uint64_to_usize(v___x_1701_);
v___x_1703_ = ((size_t)1ULL);
v___x_1704_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1698_, v___x_1702_, v___x_1703_, v_x_1699_, v_x_1700_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(lean_object* v_mvarId_1705_, lean_object* v_val_1706_, lean_object* v___y_1707_){
_start:
{
lean_object* v___x_1709_; lean_object* v_mctx_1710_; lean_object* v_cache_1711_; lean_object* v_zetaDeltaFVarIds_1712_; lean_object* v_postponed_1713_; lean_object* v_diag_1714_; lean_object* v___x_1716_; uint8_t v_isShared_1717_; uint8_t v_isSharedCheck_1743_; 
v___x_1709_ = lean_st_ref_take(v___y_1707_);
v_mctx_1710_ = lean_ctor_get(v___x_1709_, 0);
v_cache_1711_ = lean_ctor_get(v___x_1709_, 1);
v_zetaDeltaFVarIds_1712_ = lean_ctor_get(v___x_1709_, 2);
v_postponed_1713_ = lean_ctor_get(v___x_1709_, 3);
v_diag_1714_ = lean_ctor_get(v___x_1709_, 4);
v_isSharedCheck_1743_ = !lean_is_exclusive(v___x_1709_);
if (v_isSharedCheck_1743_ == 0)
{
v___x_1716_ = v___x_1709_;
v_isShared_1717_ = v_isSharedCheck_1743_;
goto v_resetjp_1715_;
}
else
{
lean_inc(v_diag_1714_);
lean_inc(v_postponed_1713_);
lean_inc(v_zetaDeltaFVarIds_1712_);
lean_inc(v_cache_1711_);
lean_inc(v_mctx_1710_);
lean_dec(v___x_1709_);
v___x_1716_ = lean_box(0);
v_isShared_1717_ = v_isSharedCheck_1743_;
goto v_resetjp_1715_;
}
v_resetjp_1715_:
{
lean_object* v_depth_1718_; lean_object* v_levelAssignDepth_1719_; lean_object* v_lmvarCounter_1720_; lean_object* v_mvarCounter_1721_; lean_object* v_lDecls_1722_; lean_object* v_decls_1723_; lean_object* v_userNames_1724_; lean_object* v_lAssignment_1725_; lean_object* v_eAssignment_1726_; lean_object* v_dAssignment_1727_; lean_object* v_instanceTypedMVars_1728_; lean_object* v___x_1730_; uint8_t v_isShared_1731_; uint8_t v_isSharedCheck_1742_; 
v_depth_1718_ = lean_ctor_get(v_mctx_1710_, 0);
v_levelAssignDepth_1719_ = lean_ctor_get(v_mctx_1710_, 1);
v_lmvarCounter_1720_ = lean_ctor_get(v_mctx_1710_, 2);
v_mvarCounter_1721_ = lean_ctor_get(v_mctx_1710_, 3);
v_lDecls_1722_ = lean_ctor_get(v_mctx_1710_, 4);
v_decls_1723_ = lean_ctor_get(v_mctx_1710_, 5);
v_userNames_1724_ = lean_ctor_get(v_mctx_1710_, 6);
v_lAssignment_1725_ = lean_ctor_get(v_mctx_1710_, 7);
v_eAssignment_1726_ = lean_ctor_get(v_mctx_1710_, 8);
v_dAssignment_1727_ = lean_ctor_get(v_mctx_1710_, 9);
v_instanceTypedMVars_1728_ = lean_ctor_get(v_mctx_1710_, 10);
v_isSharedCheck_1742_ = !lean_is_exclusive(v_mctx_1710_);
if (v_isSharedCheck_1742_ == 0)
{
v___x_1730_ = v_mctx_1710_;
v_isShared_1731_ = v_isSharedCheck_1742_;
goto v_resetjp_1729_;
}
else
{
lean_inc(v_instanceTypedMVars_1728_);
lean_inc(v_dAssignment_1727_);
lean_inc(v_eAssignment_1726_);
lean_inc(v_lAssignment_1725_);
lean_inc(v_userNames_1724_);
lean_inc(v_decls_1723_);
lean_inc(v_lDecls_1722_);
lean_inc(v_mvarCounter_1721_);
lean_inc(v_lmvarCounter_1720_);
lean_inc(v_levelAssignDepth_1719_);
lean_inc(v_depth_1718_);
lean_dec(v_mctx_1710_);
v___x_1730_ = lean_box(0);
v_isShared_1731_ = v_isSharedCheck_1742_;
goto v_resetjp_1729_;
}
v_resetjp_1729_:
{
lean_object* v___x_1732_; lean_object* v___x_1734_; 
v___x_1732_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_eAssignment_1726_, v_mvarId_1705_, v_val_1706_);
if (v_isShared_1731_ == 0)
{
lean_ctor_set(v___x_1730_, 8, v___x_1732_);
v___x_1734_ = v___x_1730_;
goto v_reusejp_1733_;
}
else
{
lean_object* v_reuseFailAlloc_1741_; 
v_reuseFailAlloc_1741_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v_reuseFailAlloc_1741_, 0, v_depth_1718_);
lean_ctor_set(v_reuseFailAlloc_1741_, 1, v_levelAssignDepth_1719_);
lean_ctor_set(v_reuseFailAlloc_1741_, 2, v_lmvarCounter_1720_);
lean_ctor_set(v_reuseFailAlloc_1741_, 3, v_mvarCounter_1721_);
lean_ctor_set(v_reuseFailAlloc_1741_, 4, v_lDecls_1722_);
lean_ctor_set(v_reuseFailAlloc_1741_, 5, v_decls_1723_);
lean_ctor_set(v_reuseFailAlloc_1741_, 6, v_userNames_1724_);
lean_ctor_set(v_reuseFailAlloc_1741_, 7, v_lAssignment_1725_);
lean_ctor_set(v_reuseFailAlloc_1741_, 8, v___x_1732_);
lean_ctor_set(v_reuseFailAlloc_1741_, 9, v_dAssignment_1727_);
lean_ctor_set(v_reuseFailAlloc_1741_, 10, v_instanceTypedMVars_1728_);
v___x_1734_ = v_reuseFailAlloc_1741_;
goto v_reusejp_1733_;
}
v_reusejp_1733_:
{
lean_object* v___x_1736_; 
if (v_isShared_1717_ == 0)
{
lean_ctor_set(v___x_1716_, 0, v___x_1734_);
v___x_1736_ = v___x_1716_;
goto v_reusejp_1735_;
}
else
{
lean_object* v_reuseFailAlloc_1740_; 
v_reuseFailAlloc_1740_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1740_, 0, v___x_1734_);
lean_ctor_set(v_reuseFailAlloc_1740_, 1, v_cache_1711_);
lean_ctor_set(v_reuseFailAlloc_1740_, 2, v_zetaDeltaFVarIds_1712_);
lean_ctor_set(v_reuseFailAlloc_1740_, 3, v_postponed_1713_);
lean_ctor_set(v_reuseFailAlloc_1740_, 4, v_diag_1714_);
v___x_1736_ = v_reuseFailAlloc_1740_;
goto v_reusejp_1735_;
}
v_reusejp_1735_:
{
lean_object* v___x_1737_; lean_object* v___x_1738_; lean_object* v___x_1739_; 
v___x_1737_ = lean_st_ref_put(v___y_1707_, v___x_1736_);
v___x_1738_ = lean_box(0);
v___x_1739_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1739_, 0, v___x_1738_);
return v___x_1739_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg___boxed(lean_object* v_mvarId_1744_, lean_object* v_val_1745_, lean_object* v___y_1746_, lean_object* v___y_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1744_, v_val_1745_, v___y_1746_);
lean_dec(v___y_1746_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(lean_object* v_argMVars_1749_, lean_object* v_argVars_1750_, lean_object* v_as_1751_, size_t v_sz_1752_, size_t v_i_1753_, lean_object* v_b_1754_, lean_object* v___y_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_, lean_object* v___y_1758_){
_start:
{
uint8_t v___x_1760_; 
v___x_1760_ = lean_usize_dec_lt(v_i_1753_, v_sz_1752_);
if (v___x_1760_ == 0)
{
lean_object* v___x_1761_; 
v___x_1761_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1761_, 0, v_b_1754_);
return v___x_1761_;
}
else
{
lean_object* v___x_1762_; lean_object* v_a_1763_; lean_object* v___y_1765_; lean_object* v___y_1766_; lean_object* v___y_1767_; lean_object* v___y_1768_; lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1762_ = lean_box(0);
v_a_1763_ = lean_array_uget_borrowed(v_as_1751_, v_i_1753_);
v___x_1784_ = lean_unsigned_to_nat(0u);
v___x_1785_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1763_, v_argMVars_1749_, v___x_1784_);
if (lean_obj_tag(v___x_1785_) == 1)
{
lean_object* v_val_1786_; lean_object* v___x_1787_; lean_object* v___x_1788_; lean_object* v___x_1789_; 
v_val_1786_ = lean_ctor_get(v___x_1785_, 0);
lean_inc(v_val_1786_);
lean_dec_ref_known(v___x_1785_, 1);
v___x_1787_ = l_Lean_instInhabitedExpr;
v___x_1788_ = lean_array_get_borrowed(v___x_1787_, v_argVars_1750_, v_val_1786_);
lean_dec(v_val_1786_);
lean_inc(v___x_1788_);
lean_inc(v_a_1763_);
v___x_1789_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_a_1763_, v___x_1788_, v___y_1756_);
if (lean_obj_tag(v___x_1789_) == 0)
{
lean_dec_ref_known(v___x_1789_, 1);
v___y_1765_ = v___y_1755_;
v___y_1766_ = v___y_1756_;
v___y_1767_ = v___y_1757_;
v___y_1768_ = v___y_1758_;
goto v___jp_1764_;
}
else
{
return v___x_1789_;
}
}
else
{
lean_dec(v___x_1785_);
v___y_1765_ = v___y_1755_;
v___y_1766_ = v___y_1756_;
v___y_1767_ = v___y_1757_;
v___y_1768_ = v___y_1758_;
goto v___jp_1764_;
}
v___jp_1764_:
{
lean_object* v___x_1769_; lean_object* v___x_1770_; 
lean_inc(v_a_1763_);
v___x_1769_ = l_Lean_Expr_mvar___override(v_a_1763_);
lean_inc(v___y_1768_);
lean_inc_ref(v___y_1767_);
lean_inc(v___y_1766_);
lean_inc_ref(v___y_1765_);
v___x_1770_ = lean_infer_type(v___x_1769_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1770_) == 0)
{
lean_object* v_a_1771_; lean_object* v___x_1772_; 
v_a_1771_ = lean_ctor_get(v___x_1770_, 0);
lean_inc(v_a_1771_);
lean_dec_ref_known(v___x_1770_, 1);
v___x_1772_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1749_, v_argVars_1750_, v_a_1771_, v___y_1765_, v___y_1766_, v___y_1767_, v___y_1768_);
if (lean_obj_tag(v___x_1772_) == 0)
{
size_t v___x_1773_; size_t v___x_1774_; 
lean_dec_ref_known(v___x_1772_, 1);
v___x_1773_ = ((size_t)1ULL);
v___x_1774_ = lean_usize_add(v_i_1753_, v___x_1773_);
v_i_1753_ = v___x_1774_;
v_b_1754_ = v___x_1762_;
goto _start;
}
else
{
return v___x_1772_;
}
}
else
{
lean_object* v_a_1776_; lean_object* v___x_1778_; uint8_t v_isShared_1779_; uint8_t v_isSharedCheck_1783_; 
v_a_1776_ = lean_ctor_get(v___x_1770_, 0);
v_isSharedCheck_1783_ = !lean_is_exclusive(v___x_1770_);
if (v_isSharedCheck_1783_ == 0)
{
v___x_1778_ = v___x_1770_;
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
else
{
lean_inc(v_a_1776_);
lean_dec(v___x_1770_);
v___x_1778_ = lean_box(0);
v_isShared_1779_ = v_isSharedCheck_1783_;
goto v_resetjp_1777_;
}
v_resetjp_1777_:
{
lean_object* v___x_1781_; 
if (v_isShared_1779_ == 0)
{
v___x_1781_ = v___x_1778_;
goto v_reusejp_1780_;
}
else
{
lean_object* v_reuseFailAlloc_1782_; 
v_reuseFailAlloc_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1782_, 0, v_a_1776_);
v___x_1781_ = v_reuseFailAlloc_1782_;
goto v_reusejp_1780_;
}
v_reusejp_1780_:
{
return v___x_1781_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1790_, lean_object* v_argVars_1791_, lean_object* v_e_1792_, lean_object* v_a_1793_, lean_object* v_a_1794_, lean_object* v_a_1795_, lean_object* v_a_1796_){
_start:
{
lean_object* v___x_1798_; 
v___x_1798_ = l_Lean_Meta_getMVars(v_e_1792_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
if (lean_obj_tag(v___x_1798_) == 0)
{
lean_object* v_a_1799_; lean_object* v___x_1800_; size_t v_sz_1801_; size_t v___x_1802_; lean_object* v___x_1803_; 
v_a_1799_ = lean_ctor_get(v___x_1798_, 0);
lean_inc(v_a_1799_);
lean_dec_ref_known(v___x_1798_, 1);
v___x_1800_ = lean_box(0);
v_sz_1801_ = lean_array_size(v_a_1799_);
v___x_1802_ = ((size_t)0ULL);
v___x_1803_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1790_, v_argVars_1791_, v_a_1799_, v_sz_1801_, v___x_1802_, v___x_1800_, v_a_1793_, v_a_1794_, v_a_1795_, v_a_1796_);
lean_dec(v_a_1799_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v___x_1805_; uint8_t v_isShared_1806_; uint8_t v_isSharedCheck_1810_; 
v_isSharedCheck_1810_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1810_ == 0)
{
lean_object* v_unused_1811_; 
v_unused_1811_ = lean_ctor_get(v___x_1803_, 0);
lean_dec(v_unused_1811_);
v___x_1805_ = v___x_1803_;
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
else
{
lean_dec(v___x_1803_);
v___x_1805_ = lean_box(0);
v_isShared_1806_ = v_isSharedCheck_1810_;
goto v_resetjp_1804_;
}
v_resetjp_1804_:
{
lean_object* v___x_1808_; 
if (v_isShared_1806_ == 0)
{
lean_ctor_set(v___x_1805_, 0, v___x_1800_);
v___x_1808_ = v___x_1805_;
goto v_reusejp_1807_;
}
else
{
lean_object* v_reuseFailAlloc_1809_; 
v_reuseFailAlloc_1809_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1809_, 0, v___x_1800_);
v___x_1808_ = v_reuseFailAlloc_1809_;
goto v_reusejp_1807_;
}
v_reusejp_1807_:
{
return v___x_1808_;
}
}
}
else
{
return v___x_1803_;
}
}
else
{
lean_object* v_a_1812_; lean_object* v___x_1814_; uint8_t v_isShared_1815_; uint8_t v_isSharedCheck_1819_; 
v_a_1812_ = lean_ctor_get(v___x_1798_, 0);
v_isSharedCheck_1819_ = !lean_is_exclusive(v___x_1798_);
if (v_isSharedCheck_1819_ == 0)
{
v___x_1814_ = v___x_1798_;
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
else
{
lean_inc(v_a_1812_);
lean_dec(v___x_1798_);
v___x_1814_ = lean_box(0);
v_isShared_1815_ = v_isSharedCheck_1819_;
goto v_resetjp_1813_;
}
v_resetjp_1813_:
{
lean_object* v___x_1817_; 
if (v_isShared_1815_ == 0)
{
v___x_1817_ = v___x_1814_;
goto v_reusejp_1816_;
}
else
{
lean_object* v_reuseFailAlloc_1818_; 
v_reuseFailAlloc_1818_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1818_, 0, v_a_1812_);
v___x_1817_ = v_reuseFailAlloc_1818_;
goto v_reusejp_1816_;
}
v_reusejp_1816_:
{
return v___x_1817_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1820_, lean_object* v_argVars_1821_, lean_object* v_e_1822_, lean_object* v_a_1823_, lean_object* v_a_1824_, lean_object* v_a_1825_, lean_object* v_a_1826_, lean_object* v_a_1827_){
_start:
{
lean_object* v_res_1828_; 
v_res_1828_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1820_, v_argVars_1821_, v_e_1822_, v_a_1823_, v_a_1824_, v_a_1825_, v_a_1826_);
lean_dec(v_a_1826_);
lean_dec_ref(v_a_1825_);
lean_dec(v_a_1824_);
lean_dec_ref(v_a_1823_);
lean_dec_ref(v_argVars_1821_);
lean_dec_ref(v_argMVars_1820_);
return v_res_1828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2___boxed(lean_object* v_argMVars_1829_, lean_object* v_argVars_1830_, lean_object* v_as_1831_, lean_object* v_sz_1832_, lean_object* v_i_1833_, lean_object* v_b_1834_, lean_object* v___y_1835_, lean_object* v___y_1836_, lean_object* v___y_1837_, lean_object* v___y_1838_, lean_object* v___y_1839_){
_start:
{
size_t v_sz_boxed_1840_; size_t v_i_boxed_1841_; lean_object* v_res_1842_; 
v_sz_boxed_1840_ = lean_unbox_usize(v_sz_1832_);
lean_dec(v_sz_1832_);
v_i_boxed_1841_ = lean_unbox_usize(v_i_1833_);
lean_dec(v_i_1833_);
v_res_1842_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1829_, v_argVars_1830_, v_as_1831_, v_sz_boxed_1840_, v_i_boxed_1841_, v_b_1834_, v___y_1835_, v___y_1836_, v___y_1837_, v___y_1838_);
lean_dec(v___y_1838_);
lean_dec_ref(v___y_1837_);
lean_dec(v___y_1836_);
lean_dec_ref(v___y_1835_);
lean_dec_ref(v_as_1831_);
lean_dec_ref(v_argVars_1830_);
lean_dec_ref(v_argMVars_1829_);
return v_res_1842_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_mvarId_1843_, lean_object* v_val_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1843_, v_val_1844_, v___y_1846_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_mvarId_1851_, lean_object* v_val_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_mvarId_1851_, v_val_1852_, v___y_1853_, v___y_1854_, v___y_1855_, v___y_1856_);
lean_dec(v___y_1856_);
lean_dec_ref(v___y_1855_);
lean_dec(v___y_1854_);
lean_dec_ref(v___y_1853_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1(lean_object* v_00_u03b2_1859_, lean_object* v_x_1860_, lean_object* v_x_1861_, lean_object* v_x_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_x_1860_, v_x_1861_, v_x_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1864_, lean_object* v_x_1865_, size_t v_x_1866_, size_t v_x_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1865_, v_x_1866_, v_x_1867_, v_x_1868_, v_x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1871_, lean_object* v_x_1872_, lean_object* v_x_1873_, lean_object* v_x_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
size_t v_x_1962__boxed_1877_; size_t v_x_1963__boxed_1878_; lean_object* v_res_1879_; 
v_x_1962__boxed_1877_ = lean_unbox_usize(v_x_1873_);
lean_dec(v_x_1873_);
v_x_1963__boxed_1878_ = lean_unbox_usize(v_x_1874_);
lean_dec(v_x_1874_);
v_res_1879_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(v_00_u03b2_1871_, v_x_1872_, v_x_1962__boxed_1877_, v_x_1963__boxed_1878_, v_x_1875_, v_x_1876_);
return v_res_1879_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1880_, lean_object* v_n_1881_, lean_object* v_k_1882_, lean_object* v_v_1883_){
_start:
{
lean_object* v___x_1884_; 
v___x_1884_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v_n_1881_, v_k_1882_, v_v_1883_);
return v___x_1884_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1885_, size_t v_depth_1886_, lean_object* v_keys_1887_, lean_object* v_vals_1888_, lean_object* v_heq_1889_, lean_object* v_i_1890_, lean_object* v_entries_1891_){
_start:
{
lean_object* v___x_1892_; 
v___x_1892_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_1886_, v_keys_1887_, v_vals_1888_, v_i_1890_, v_entries_1891_);
return v___x_1892_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1893_, lean_object* v_depth_1894_, lean_object* v_keys_1895_, lean_object* v_vals_1896_, lean_object* v_heq_1897_, lean_object* v_i_1898_, lean_object* v_entries_1899_){
_start:
{
size_t v_depth_boxed_1900_; lean_object* v_res_1901_; 
v_depth_boxed_1900_ = lean_unbox_usize(v_depth_1894_);
lean_dec(v_depth_1894_);
v_res_1901_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_1893_, v_depth_boxed_1900_, v_keys_1895_, v_vals_1896_, v_heq_1897_, v_i_1898_, v_entries_1899_);
lean_dec_ref(v_vals_1896_);
lean_dec_ref(v_keys_1895_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1902_, lean_object* v_x_1903_, lean_object* v_x_1904_, lean_object* v_x_1905_, lean_object* v_x_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1903_, v_x_1904_, v_x_1905_, v_x_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_1908_, lean_object* v___y_1909_){
_start:
{
uint8_t v___x_1911_; 
v___x_1911_ = l_Lean_Expr_hasMVar(v_e_1908_);
if (v___x_1911_ == 0)
{
lean_object* v___x_1912_; 
v___x_1912_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1912_, 0, v_e_1908_);
return v___x_1912_;
}
else
{
lean_object* v___x_1913_; lean_object* v_mctx_1914_; lean_object* v___x_1915_; lean_object* v_fst_1916_; lean_object* v_snd_1917_; lean_object* v___x_1918_; lean_object* v_cache_1919_; lean_object* v_zetaDeltaFVarIds_1920_; lean_object* v_postponed_1921_; lean_object* v_diag_1922_; lean_object* v___x_1924_; uint8_t v_isShared_1925_; uint8_t v_isSharedCheck_1931_; 
v___x_1913_ = lean_st_ref_get(v___y_1909_);
v_mctx_1914_ = lean_ctor_get(v___x_1913_, 0);
lean_inc_ref(v_mctx_1914_);
lean_dec(v___x_1913_);
v___x_1915_ = l_Lean_instantiateMVarsCore(v_mctx_1914_, v_e_1908_);
v_fst_1916_ = lean_ctor_get(v___x_1915_, 0);
lean_inc(v_fst_1916_);
v_snd_1917_ = lean_ctor_get(v___x_1915_, 1);
lean_inc(v_snd_1917_);
lean_dec_ref(v___x_1915_);
v___x_1918_ = lean_st_ref_take(v___y_1909_);
v_cache_1919_ = lean_ctor_get(v___x_1918_, 1);
v_zetaDeltaFVarIds_1920_ = lean_ctor_get(v___x_1918_, 2);
v_postponed_1921_ = lean_ctor_get(v___x_1918_, 3);
v_diag_1922_ = lean_ctor_get(v___x_1918_, 4);
v_isSharedCheck_1931_ = !lean_is_exclusive(v___x_1918_);
if (v_isSharedCheck_1931_ == 0)
{
lean_object* v_unused_1932_; 
v_unused_1932_ = lean_ctor_get(v___x_1918_, 0);
lean_dec(v_unused_1932_);
v___x_1924_ = v___x_1918_;
v_isShared_1925_ = v_isSharedCheck_1931_;
goto v_resetjp_1923_;
}
else
{
lean_inc(v_diag_1922_);
lean_inc(v_postponed_1921_);
lean_inc(v_zetaDeltaFVarIds_1920_);
lean_inc(v_cache_1919_);
lean_dec(v___x_1918_);
v___x_1924_ = lean_box(0);
v_isShared_1925_ = v_isSharedCheck_1931_;
goto v_resetjp_1923_;
}
v_resetjp_1923_:
{
lean_object* v___x_1927_; 
if (v_isShared_1925_ == 0)
{
lean_ctor_set(v___x_1924_, 0, v_snd_1917_);
v___x_1927_ = v___x_1924_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_snd_1917_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_cache_1919_);
lean_ctor_set(v_reuseFailAlloc_1930_, 2, v_zetaDeltaFVarIds_1920_);
lean_ctor_set(v_reuseFailAlloc_1930_, 3, v_postponed_1921_);
lean_ctor_set(v_reuseFailAlloc_1930_, 4, v_diag_1922_);
v___x_1927_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_st_ref_put(v___y_1909_, v___x_1927_);
v___x_1929_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1929_, 0, v_fst_1916_);
return v___x_1929_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_1933_, lean_object* v___y_1934_, lean_object* v___y_1935_){
_start:
{
lean_object* v_res_1936_; 
v_res_1936_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1933_, v___y_1934_);
lean_dec(v___y_1934_);
return v_res_1936_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_1937_, lean_object* v___y_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_, lean_object* v___y_1941_){
_start:
{
lean_object* v___x_1943_; 
v___x_1943_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1937_, v___y_1939_);
return v___x_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_, lean_object* v___y_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_1944_, v___y_1945_, v___y_1946_, v___y_1947_, v___y_1948_);
lean_dec(v___y_1948_);
lean_dec_ref(v___y_1947_);
lean_dec(v___y_1946_);
lean_dec_ref(v___y_1945_);
return v_res_1950_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_1951_, lean_object* v_opt_1952_){
_start:
{
lean_object* v_name_1953_; lean_object* v_defValue_1954_; lean_object* v_map_1955_; lean_object* v___x_1956_; 
v_name_1953_ = lean_ctor_get(v_opt_1952_, 0);
v_defValue_1954_ = lean_ctor_get(v_opt_1952_, 1);
v_map_1955_ = lean_ctor_get(v_opts_1951_, 0);
v___x_1956_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1955_, v_name_1953_);
if (lean_obj_tag(v___x_1956_) == 0)
{
uint8_t v___x_1957_; 
v___x_1957_ = lean_unbox(v_defValue_1954_);
return v___x_1957_;
}
else
{
lean_object* v_val_1958_; 
v_val_1958_ = lean_ctor_get(v___x_1956_, 0);
lean_inc(v_val_1958_);
lean_dec_ref_known(v___x_1956_, 1);
if (lean_obj_tag(v_val_1958_) == 1)
{
uint8_t v_v_1959_; 
v_v_1959_ = lean_ctor_get_uint8(v_val_1958_, 0);
lean_dec_ref_known(v_val_1958_, 0);
return v_v_1959_;
}
else
{
uint8_t v___x_1960_; 
lean_dec(v_val_1958_);
v___x_1960_ = lean_unbox(v_defValue_1954_);
return v___x_1960_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_1961_, lean_object* v_opt_1962_){
_start:
{
uint8_t v_res_1963_; lean_object* v_r_1964_; 
v_res_1963_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_1961_, v_opt_1962_);
lean_dec_ref(v_opt_1962_);
lean_dec_ref(v_opts_1961_);
v_r_1964_ = lean_box(v_res_1963_);
return v_r_1964_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_1965_, lean_object* v_as_1966_, size_t v_i_1967_, size_t v_stop_1968_){
_start:
{
uint8_t v___x_1969_; 
v___x_1969_ = lean_usize_dec_eq(v_i_1967_, v_stop_1968_);
if (v___x_1969_ == 0)
{
lean_object* v___x_1970_; uint8_t v___x_1971_; 
v___x_1970_ = lean_array_uget_borrowed(v_as_1966_, v_i_1967_);
v___x_1971_ = lean_nat_dec_eq(v_a_1965_, v___x_1970_);
if (v___x_1971_ == 0)
{
size_t v___x_1972_; size_t v___x_1973_; 
v___x_1972_ = ((size_t)1ULL);
v___x_1973_ = lean_usize_add(v_i_1967_, v___x_1972_);
v_i_1967_ = v___x_1973_;
goto _start;
}
else
{
return v___x_1971_;
}
}
else
{
uint8_t v___x_1975_; 
v___x_1975_ = 0;
return v___x_1975_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_1976_, lean_object* v_as_1977_, lean_object* v_i_1978_, lean_object* v_stop_1979_){
_start:
{
size_t v_i_boxed_1980_; size_t v_stop_boxed_1981_; uint8_t v_res_1982_; lean_object* v_r_1983_; 
v_i_boxed_1980_ = lean_unbox_usize(v_i_1978_);
lean_dec(v_i_1978_);
v_stop_boxed_1981_ = lean_unbox_usize(v_stop_1979_);
lean_dec(v_stop_1979_);
v_res_1982_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1976_, v_as_1977_, v_i_boxed_1980_, v_stop_boxed_1981_);
lean_dec_ref(v_as_1977_);
lean_dec(v_a_1976_);
v_r_1983_ = lean_box(v_res_1982_);
return v_r_1983_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v___x_1986_; lean_object* v___x_1987_; uint8_t v___x_1988_; 
v___x_1986_ = lean_unsigned_to_nat(0u);
v___x_1987_ = lean_array_get_size(v_as_1984_);
v___x_1988_ = lean_nat_dec_lt(v___x_1986_, v___x_1987_);
if (v___x_1988_ == 0)
{
return v___x_1988_;
}
else
{
if (v___x_1988_ == 0)
{
return v___x_1988_;
}
else
{
size_t v___x_1989_; size_t v___x_1990_; uint8_t v___x_1991_; 
v___x_1989_ = ((size_t)0ULL);
v___x_1990_ = lean_usize_of_nat(v___x_1987_);
v___x_1991_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1985_, v_as_1984_, v___x_1989_, v___x_1990_);
return v___x_1991_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_1992_, lean_object* v_a_1993_){
_start:
{
uint8_t v_res_1994_; lean_object* v_r_1995_; 
v_res_1994_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_1992_, v_a_1993_);
lean_dec(v_a_1993_);
lean_dec_ref(v_as_1992_);
v_r_1995_ = lean_box(v_res_1994_);
return v_r_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_1996_, lean_object* v_fst_1997_, lean_object* v_argVars_1998_, lean_object* v_as_1999_, size_t v_sz_2000_, size_t v_i_2001_, lean_object* v_b_2002_, lean_object* v___y_2003_, lean_object* v___y_2004_, lean_object* v___y_2005_, lean_object* v___y_2006_){
_start:
{
lean_object* v_a_2009_; uint8_t v___x_2013_; 
v___x_2013_ = lean_usize_dec_lt(v_i_2001_, v_sz_2000_);
if (v___x_2013_ == 0)
{
lean_object* v___x_2014_; 
v___x_2014_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2014_, 0, v_b_2002_);
return v___x_2014_;
}
else
{
lean_object* v_next_2015_; 
v_next_2015_ = lean_ctor_get(v_b_2002_, 0);
lean_inc(v_next_2015_);
if (lean_obj_tag(v_next_2015_) == 0)
{
lean_object* v___x_2016_; 
v___x_2016_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2016_, 0, v_b_2002_);
return v___x_2016_;
}
else
{
lean_object* v_upperBound_2017_; lean_object* v_val_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2049_; 
v_upperBound_2017_ = lean_ctor_get(v_b_2002_, 1);
v_val_2018_ = lean_ctor_get(v_next_2015_, 0);
v_isSharedCheck_2049_ = !lean_is_exclusive(v_next_2015_);
if (v_isSharedCheck_2049_ == 0)
{
v___x_2020_ = v_next_2015_;
v_isShared_2021_ = v_isSharedCheck_2049_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_val_2018_);
lean_dec(v_next_2015_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2049_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
uint8_t v___x_2022_; 
v___x_2022_ = lean_nat_dec_lt(v_val_2018_, v_upperBound_2017_);
if (v___x_2022_ == 0)
{
lean_object* v___x_2023_; 
lean_del_object(v___x_2020_);
lean_dec(v_val_2018_);
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v_b_2002_);
return v___x_2023_;
}
else
{
lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2046_; 
lean_inc(v_upperBound_2017_);
v_isSharedCheck_2046_ = !lean_is_exclusive(v_b_2002_);
if (v_isSharedCheck_2046_ == 0)
{
lean_object* v_unused_2047_; lean_object* v_unused_2048_; 
v_unused_2047_ = lean_ctor_get(v_b_2002_, 1);
lean_dec(v_unused_2047_);
v_unused_2048_ = lean_ctor_get(v_b_2002_, 0);
lean_dec(v_unused_2048_);
v___x_2025_ = v_b_2002_;
v_isShared_2026_ = v_isSharedCheck_2046_;
goto v_resetjp_2024_;
}
else
{
lean_dec(v_b_2002_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2046_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
lean_object* v___x_2027_; lean_object* v___x_2028_; lean_object* v___x_2030_; 
v___x_2027_ = lean_unsigned_to_nat(1u);
v___x_2028_ = lean_nat_add(v_val_2018_, v___x_2027_);
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2028_);
v___x_2030_ = v___x_2020_;
goto v_reusejp_2029_;
}
else
{
lean_object* v_reuseFailAlloc_2045_; 
v_reuseFailAlloc_2045_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2045_, 0, v___x_2028_);
v___x_2030_ = v_reuseFailAlloc_2045_;
goto v_reusejp_2029_;
}
v_reusejp_2029_:
{
lean_object* v___x_2032_; 
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2030_);
v___x_2032_ = v___x_2025_;
goto v_reusejp_2031_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v___x_2030_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_upperBound_2017_);
v___x_2032_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2031_;
}
v_reusejp_2031_:
{
uint8_t v___x_2033_; 
v___x_2033_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_1996_, v_val_2018_);
lean_dec(v_val_2018_);
if (v___x_2033_ == 0)
{
lean_object* v_a_2034_; lean_object* v___x_2035_; 
v_a_2034_ = lean_array_uget_borrowed(v_as_1999_, v_i_2001_);
lean_inc(v_a_2034_);
v___x_2035_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_1997_, v_argVars_1998_, v_a_2034_, v___y_2003_, v___y_2004_, v___y_2005_, v___y_2006_);
if (lean_obj_tag(v___x_2035_) == 0)
{
lean_dec_ref_known(v___x_2035_, 1);
v_a_2009_ = v___x_2032_;
goto v___jp_2008_;
}
else
{
lean_object* v_a_2036_; lean_object* v___x_2038_; uint8_t v_isShared_2039_; uint8_t v_isSharedCheck_2043_; 
lean_dec_ref(v___x_2032_);
v_a_2036_ = lean_ctor_get(v___x_2035_, 0);
v_isSharedCheck_2043_ = !lean_is_exclusive(v___x_2035_);
if (v_isSharedCheck_2043_ == 0)
{
v___x_2038_ = v___x_2035_;
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
else
{
lean_inc(v_a_2036_);
lean_dec(v___x_2035_);
v___x_2038_ = lean_box(0);
v_isShared_2039_ = v_isSharedCheck_2043_;
goto v_resetjp_2037_;
}
v_resetjp_2037_:
{
lean_object* v___x_2041_; 
if (v_isShared_2039_ == 0)
{
v___x_2041_ = v___x_2038_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2042_; 
v_reuseFailAlloc_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2042_, 0, v_a_2036_);
v___x_2041_ = v_reuseFailAlloc_2042_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
return v___x_2041_;
}
}
}
}
else
{
v_a_2009_ = v___x_2032_;
goto v___jp_2008_;
}
}
}
}
}
}
}
}
v___jp_2008_:
{
size_t v___x_2010_; size_t v___x_2011_; 
v___x_2010_ = ((size_t)1ULL);
v___x_2011_ = lean_usize_add(v_i_2001_, v___x_2010_);
v_i_2001_ = v___x_2011_;
v_b_2002_ = v_a_2009_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2050_, lean_object* v_fst_2051_, lean_object* v_argVars_2052_, lean_object* v_as_2053_, lean_object* v_sz_2054_, lean_object* v_i_2055_, lean_object* v_b_2056_, lean_object* v___y_2057_, lean_object* v___y_2058_, lean_object* v___y_2059_, lean_object* v___y_2060_, lean_object* v___y_2061_){
_start:
{
size_t v_sz_boxed_2062_; size_t v_i_boxed_2063_; lean_object* v_res_2064_; 
v_sz_boxed_2062_ = lean_unbox_usize(v_sz_2054_);
lean_dec(v_sz_2054_);
v_i_boxed_2063_ = lean_unbox_usize(v_i_2055_);
lean_dec(v_i_2055_);
v_res_2064_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2050_, v_fst_2051_, v_argVars_2052_, v_as_2053_, v_sz_boxed_2062_, v_i_boxed_2063_, v_b_2056_, v___y_2057_, v___y_2058_, v___y_2059_, v___y_2060_);
lean_dec(v___y_2060_);
lean_dec_ref(v___y_2059_);
lean_dec(v___y_2058_);
lean_dec_ref(v___y_2057_);
lean_dec_ref(v_as_2053_);
lean_dec_ref(v_argVars_2052_);
lean_dec_ref(v_fst_2051_);
lean_dec_ref(v_a_2050_);
return v_res_2064_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2065_, lean_object* v_as_2066_, size_t v_i_2067_, size_t v_stop_2068_, lean_object* v_b_2069_){
_start:
{
lean_object* v___y_2071_; uint8_t v___x_2075_; 
v___x_2075_ = lean_usize_dec_eq(v_i_2067_, v_stop_2068_);
if (v___x_2075_ == 0)
{
lean_object* v___x_2076_; uint8_t v___x_2077_; 
v___x_2076_ = lean_array_uget_borrowed(v_as_2066_, v_i_2067_);
v___x_2077_ = lean_nat_dec_eq(v___x_2076_, v_next_2065_);
if (v___x_2077_ == 0)
{
lean_object* v___x_2078_; 
lean_inc(v___x_2076_);
v___x_2078_ = lean_array_push(v_b_2069_, v___x_2076_);
v___y_2071_ = v___x_2078_;
goto v___jp_2070_;
}
else
{
v___y_2071_ = v_b_2069_;
goto v___jp_2070_;
}
}
else
{
return v_b_2069_;
}
v___jp_2070_:
{
size_t v___x_2072_; size_t v___x_2073_; 
v___x_2072_ = ((size_t)1ULL);
v___x_2073_ = lean_usize_add(v_i_2067_, v___x_2072_);
v_i_2067_ = v___x_2073_;
v_b_2069_ = v___y_2071_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2079_, lean_object* v_as_2080_, lean_object* v_i_2081_, lean_object* v_stop_2082_, lean_object* v_b_2083_){
_start:
{
size_t v_i_boxed_2084_; size_t v_stop_boxed_2085_; lean_object* v_res_2086_; 
v_i_boxed_2084_ = lean_unbox_usize(v_i_2081_);
lean_dec(v_i_2081_);
v_stop_boxed_2085_ = lean_unbox_usize(v_stop_2082_);
lean_dec(v_stop_2082_);
v_res_2086_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2079_, v_as_2080_, v_i_boxed_2084_, v_stop_boxed_2085_, v_b_2083_);
lean_dec_ref(v_as_2080_);
lean_dec(v_next_2079_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object* v_fst_2087_, lean_object* v___x_2088_, lean_object* v_fst_2089_, lean_object* v_argVars_2090_, lean_object* v_snd_2091_, lean_object* v_next_2092_, lean_object* v___y_2093_, lean_object* v___y_2094_, lean_object* v___y_2095_, lean_object* v___y_2096_){
_start:
{
lean_object* v___x_2098_; lean_object* v___y_2100_; lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; uint8_t v___x_2143_; 
lean_inc(v_next_2092_);
v___x_2098_ = lean_array_push(v_fst_2087_, v_next_2092_);
v___x_2140_ = lean_unsigned_to_nat(0u);
v___x_2141_ = lean_array_get_size(v_snd_2091_);
v___x_2142_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2143_ = lean_nat_dec_lt(v___x_2140_, v___x_2141_);
if (v___x_2143_ == 0)
{
v___y_2100_ = v___x_2142_;
goto v___jp_2099_;
}
else
{
uint8_t v___x_2144_; 
v___x_2144_ = lean_nat_dec_le(v___x_2141_, v___x_2141_);
if (v___x_2144_ == 0)
{
if (v___x_2143_ == 0)
{
v___y_2100_ = v___x_2142_;
goto v___jp_2099_;
}
else
{
size_t v___x_2145_; size_t v___x_2146_; lean_object* v___x_2147_; 
v___x_2145_ = ((size_t)0ULL);
v___x_2146_ = lean_usize_of_nat(v___x_2141_);
v___x_2147_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2092_, v_snd_2091_, v___x_2145_, v___x_2146_, v___x_2142_);
v___y_2100_ = v___x_2147_;
goto v___jp_2099_;
}
}
else
{
size_t v___x_2148_; size_t v___x_2149_; lean_object* v___x_2150_; 
v___x_2148_ = ((size_t)0ULL);
v___x_2149_ = lean_usize_of_nat(v___x_2141_);
v___x_2150_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2092_, v_snd_2091_, v___x_2148_, v___x_2149_, v___x_2142_);
v___y_2100_ = v___x_2150_;
goto v___jp_2099_;
}
}
v___jp_2099_:
{
lean_object* v___x_2101_; lean_object* v___x_2102_; 
v___x_2101_ = lean_array_get_borrowed(v___x_2088_, v_fst_2089_, v_next_2092_);
lean_dec(v_next_2092_);
lean_inc(v___y_2096_);
lean_inc_ref(v___y_2095_);
lean_inc(v___y_2094_);
lean_inc_ref(v___y_2093_);
lean_inc(v___x_2101_);
v___x_2102_ = lean_infer_type(v___x_2101_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2102_) == 0)
{
lean_object* v_a_2103_; lean_object* v___x_2104_; 
v_a_2103_ = lean_ctor_get(v___x_2102_, 0);
lean_inc(v_a_2103_);
lean_dec_ref_known(v___x_2102_, 1);
v___x_2104_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2089_, v_argVars_2090_, v_a_2103_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2104_) == 0)
{
lean_object* v___x_2105_; 
lean_dec_ref_known(v___x_2104_, 1);
lean_inc(v___x_2101_);
v___x_2105_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2089_, v_argVars_2090_, v___x_2101_, v___y_2093_, v___y_2094_, v___y_2095_, v___y_2096_);
if (lean_obj_tag(v___x_2105_) == 0)
{
lean_object* v___x_2107_; uint8_t v_isShared_2108_; uint8_t v_isSharedCheck_2114_; 
v_isSharedCheck_2114_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2114_ == 0)
{
lean_object* v_unused_2115_; 
v_unused_2115_ = lean_ctor_get(v___x_2105_, 0);
lean_dec(v_unused_2115_);
v___x_2107_ = v___x_2105_;
v_isShared_2108_ = v_isSharedCheck_2114_;
goto v_resetjp_2106_;
}
else
{
lean_dec(v___x_2105_);
v___x_2107_ = lean_box(0);
v_isShared_2108_ = v_isSharedCheck_2114_;
goto v_resetjp_2106_;
}
v_resetjp_2106_:
{
lean_object* v___x_2109_; lean_object* v___x_2110_; lean_object* v___x_2112_; 
v___x_2109_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2109_, 0, v___x_2098_);
lean_ctor_set(v___x_2109_, 1, v___y_2100_);
v___x_2110_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2110_, 0, v___x_2109_);
if (v_isShared_2108_ == 0)
{
lean_ctor_set(v___x_2107_, 0, v___x_2110_);
v___x_2112_ = v___x_2107_;
goto v_reusejp_2111_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v___x_2110_);
v___x_2112_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2111_;
}
v_reusejp_2111_:
{
return v___x_2112_;
}
}
}
else
{
lean_object* v_a_2116_; lean_object* v___x_2118_; uint8_t v_isShared_2119_; uint8_t v_isSharedCheck_2123_; 
lean_dec_ref(v___y_2100_);
lean_dec_ref(v___x_2098_);
v_a_2116_ = lean_ctor_get(v___x_2105_, 0);
v_isSharedCheck_2123_ = !lean_is_exclusive(v___x_2105_);
if (v_isSharedCheck_2123_ == 0)
{
v___x_2118_ = v___x_2105_;
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
else
{
lean_inc(v_a_2116_);
lean_dec(v___x_2105_);
v___x_2118_ = lean_box(0);
v_isShared_2119_ = v_isSharedCheck_2123_;
goto v_resetjp_2117_;
}
v_resetjp_2117_:
{
lean_object* v___x_2121_; 
if (v_isShared_2119_ == 0)
{
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
}
else
{
lean_object* v_a_2124_; lean_object* v___x_2126_; uint8_t v_isShared_2127_; uint8_t v_isSharedCheck_2131_; 
lean_dec_ref(v___y_2100_);
lean_dec_ref(v___x_2098_);
v_a_2124_ = lean_ctor_get(v___x_2104_, 0);
v_isSharedCheck_2131_ = !lean_is_exclusive(v___x_2104_);
if (v_isSharedCheck_2131_ == 0)
{
v___x_2126_ = v___x_2104_;
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
else
{
lean_inc(v_a_2124_);
lean_dec(v___x_2104_);
v___x_2126_ = lean_box(0);
v_isShared_2127_ = v_isSharedCheck_2131_;
goto v_resetjp_2125_;
}
v_resetjp_2125_:
{
lean_object* v___x_2129_; 
if (v_isShared_2127_ == 0)
{
v___x_2129_ = v___x_2126_;
goto v_reusejp_2128_;
}
else
{
lean_object* v_reuseFailAlloc_2130_; 
v_reuseFailAlloc_2130_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2130_, 0, v_a_2124_);
v___x_2129_ = v_reuseFailAlloc_2130_;
goto v_reusejp_2128_;
}
v_reusejp_2128_:
{
return v___x_2129_;
}
}
}
}
else
{
lean_object* v_a_2132_; lean_object* v___x_2134_; uint8_t v_isShared_2135_; uint8_t v_isSharedCheck_2139_; 
lean_dec_ref(v___y_2100_);
lean_dec_ref(v___x_2098_);
v_a_2132_ = lean_ctor_get(v___x_2102_, 0);
v_isSharedCheck_2139_ = !lean_is_exclusive(v___x_2102_);
if (v_isSharedCheck_2139_ == 0)
{
v___x_2134_ = v___x_2102_;
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
else
{
lean_inc(v_a_2132_);
lean_dec(v___x_2102_);
v___x_2134_ = lean_box(0);
v_isShared_2135_ = v_isSharedCheck_2139_;
goto v_resetjp_2133_;
}
v_resetjp_2133_:
{
lean_object* v___x_2137_; 
if (v_isShared_2135_ == 0)
{
v___x_2137_ = v___x_2134_;
goto v_reusejp_2136_;
}
else
{
lean_object* v_reuseFailAlloc_2138_; 
v_reuseFailAlloc_2138_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2138_, 0, v_a_2132_);
v___x_2137_ = v_reuseFailAlloc_2138_;
goto v_reusejp_2136_;
}
v_reusejp_2136_:
{
return v___x_2137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object* v_fst_2151_, lean_object* v___x_2152_, lean_object* v_fst_2153_, lean_object* v_argVars_2154_, lean_object* v_snd_2155_, lean_object* v_next_2156_, lean_object* v___y_2157_, lean_object* v___y_2158_, lean_object* v___y_2159_, lean_object* v___y_2160_, lean_object* v___y_2161_){
_start:
{
lean_object* v_res_2162_; 
v_res_2162_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2151_, v___x_2152_, v_fst_2153_, v_argVars_2154_, v_snd_2155_, v_next_2156_, v___y_2157_, v___y_2158_, v___y_2159_, v___y_2160_);
lean_dec(v___y_2160_);
lean_dec_ref(v___y_2159_);
lean_dec(v___y_2158_);
lean_dec_ref(v___y_2157_);
lean_dec(v_snd_2155_);
lean_dec_ref(v_argVars_2154_);
lean_dec_ref(v_fst_2153_);
lean_dec_ref(v___x_2152_);
return v_res_2162_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2163_, lean_object* v_a_2164_, lean_object* v___x_2165_, lean_object* v_a_2166_, lean_object* v_b_2167_){
_start:
{
uint8_t v___x_2169_; 
v___x_2169_ = lean_nat_dec_lt(v_a_2166_, v_upperBound_2163_);
if (v___x_2169_ == 0)
{
lean_object* v___x_2170_; 
lean_dec(v_a_2166_);
v___x_2170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2170_, 0, v_b_2167_);
return v___x_2170_;
}
else
{
lean_object* v_snd_2171_; lean_object* v___x_2173_; uint8_t v_isShared_2174_; uint8_t v_isSharedCheck_2211_; 
v_snd_2171_ = lean_ctor_get(v_b_2167_, 1);
v_isSharedCheck_2211_ = !lean_is_exclusive(v_b_2167_);
if (v_isSharedCheck_2211_ == 0)
{
lean_object* v_unused_2212_; 
v_unused_2212_ = lean_ctor_get(v_b_2167_, 0);
lean_dec(v_unused_2212_);
v___x_2173_ = v_b_2167_;
v_isShared_2174_ = v_isSharedCheck_2211_;
goto v_resetjp_2172_;
}
else
{
lean_inc(v_snd_2171_);
lean_dec(v_b_2167_);
v___x_2173_ = lean_box(0);
v_isShared_2174_ = v_isSharedCheck_2211_;
goto v_resetjp_2172_;
}
v_resetjp_2172_:
{
lean_object* v_array_2175_; lean_object* v_start_2176_; lean_object* v_stop_2177_; lean_object* v___x_2178_; uint8_t v___x_2179_; 
v_array_2175_ = lean_ctor_get(v_snd_2171_, 0);
v_start_2176_ = lean_ctor_get(v_snd_2171_, 1);
v_stop_2177_ = lean_ctor_get(v_snd_2171_, 2);
v___x_2178_ = lean_box(0);
v___x_2179_ = lean_nat_dec_lt(v_start_2176_, v_stop_2177_);
if (v___x_2179_ == 0)
{
lean_object* v___x_2181_; 
lean_dec(v_a_2166_);
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 0, v___x_2178_);
v___x_2181_ = v___x_2173_;
goto v_reusejp_2180_;
}
else
{
lean_object* v_reuseFailAlloc_2183_; 
v_reuseFailAlloc_2183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2183_, 0, v___x_2178_);
lean_ctor_set(v_reuseFailAlloc_2183_, 1, v_snd_2171_);
v___x_2181_ = v_reuseFailAlloc_2183_;
goto v_reusejp_2180_;
}
v_reusejp_2180_:
{
lean_object* v___x_2182_; 
v___x_2182_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2182_, 0, v___x_2181_);
return v___x_2182_;
}
}
else
{
lean_object* v___x_2185_; uint8_t v_isShared_2186_; uint8_t v_isSharedCheck_2207_; 
lean_inc(v_stop_2177_);
lean_inc(v_start_2176_);
lean_inc_ref(v_array_2175_);
v_isSharedCheck_2207_ = !lean_is_exclusive(v_snd_2171_);
if (v_isSharedCheck_2207_ == 0)
{
lean_object* v_unused_2208_; lean_object* v_unused_2209_; lean_object* v_unused_2210_; 
v_unused_2208_ = lean_ctor_get(v_snd_2171_, 2);
lean_dec(v_unused_2208_);
v_unused_2209_ = lean_ctor_get(v_snd_2171_, 1);
lean_dec(v_unused_2209_);
v_unused_2210_ = lean_ctor_get(v_snd_2171_, 0);
lean_dec(v_unused_2210_);
v___x_2185_ = v_snd_2171_;
v_isShared_2186_ = v_isSharedCheck_2207_;
goto v_resetjp_2184_;
}
else
{
lean_dec(v_snd_2171_);
v___x_2185_ = lean_box(0);
v_isShared_2186_ = v_isSharedCheck_2207_;
goto v_resetjp_2184_;
}
v_resetjp_2184_:
{
lean_object* v___x_2187_; lean_object* v___x_2188_; lean_object* v___x_2189_; lean_object* v___x_2191_; 
v___x_2187_ = lean_array_fget(v_array_2175_, v_start_2176_);
v___x_2188_ = lean_unsigned_to_nat(1u);
v___x_2189_ = lean_nat_add(v_start_2176_, v___x_2188_);
lean_dec(v_start_2176_);
if (v_isShared_2186_ == 0)
{
lean_ctor_set(v___x_2185_, 1, v___x_2189_);
v___x_2191_ = v___x_2185_;
goto v_reusejp_2190_;
}
else
{
lean_object* v_reuseFailAlloc_2206_; 
v_reuseFailAlloc_2206_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2206_, 0, v_array_2175_);
lean_ctor_set(v_reuseFailAlloc_2206_, 1, v___x_2189_);
lean_ctor_set(v_reuseFailAlloc_2206_, 2, v_stop_2177_);
v___x_2191_ = v_reuseFailAlloc_2206_;
goto v_reusejp_2190_;
}
v_reusejp_2190_:
{
uint8_t v___x_2198_; 
v___x_2198_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2164_, v_a_2166_);
if (v___x_2198_ == 0)
{
uint8_t v___x_2199_; 
v___x_2199_ = l_Lean_Expr_hasExprMVar(v___x_2187_);
lean_dec(v___x_2187_);
if (v___x_2199_ == 0)
{
goto v___jp_2192_;
}
else
{
lean_object* v___x_2200_; uint8_t v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_del_object(v___x_2173_);
lean_dec(v_a_2166_);
v___x_2200_ = lean_unsigned_to_nat(0u);
v___x_2201_ = lean_nat_dec_eq(v___x_2165_, v___x_2200_);
v___x_2202_ = lean_box(v___x_2201_);
v___x_2203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2203_, 0, v___x_2202_);
v___x_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2203_);
lean_ctor_set(v___x_2204_, 1, v___x_2191_);
v___x_2205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2205_, 0, v___x_2204_);
return v___x_2205_;
}
}
else
{
lean_dec(v___x_2187_);
goto v___jp_2192_;
}
v___jp_2192_:
{
lean_object* v___x_2194_; 
if (v_isShared_2174_ == 0)
{
lean_ctor_set(v___x_2173_, 1, v___x_2191_);
lean_ctor_set(v___x_2173_, 0, v___x_2178_);
v___x_2194_ = v___x_2173_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2197_; 
v_reuseFailAlloc_2197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2197_, 0, v___x_2178_);
lean_ctor_set(v_reuseFailAlloc_2197_, 1, v___x_2191_);
v___x_2194_ = v_reuseFailAlloc_2197_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_nat_add(v_a_2166_, v___x_2188_);
lean_dec(v_a_2166_);
v_a_2166_ = v___x_2195_;
v_b_2167_ = v___x_2194_;
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2213_, lean_object* v_a_2214_, lean_object* v___x_2215_, lean_object* v_a_2216_, lean_object* v_b_2217_, lean_object* v___y_2218_){
_start:
{
lean_object* v_res_2219_; 
v_res_2219_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2213_, v_a_2214_, v___x_2215_, v_a_2216_, v_b_2217_);
lean_dec(v___x_2215_);
lean_dec_ref(v_a_2214_);
lean_dec(v_upperBound_2213_);
return v_res_2219_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2220_; lean_object* v_dummy_2221_; 
v___x_2220_ = lean_box(0);
v_dummy_2221_ = l_Lean_Expr_sort___override(v___x_2220_);
return v_dummy_2221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2222_, lean_object* v___x_2223_, uint8_t v___x_2224_, lean_object* v_x_2225_, lean_object* v_argTy_2226_, lean_object* v___y_2227_, lean_object* v___y_2228_, lean_object* v___y_2229_, lean_object* v___y_2230_){
_start:
{
lean_object* v___x_2232_; 
lean_inc(v___y_2230_);
lean_inc_ref(v___y_2229_);
lean_inc(v___y_2228_);
lean_inc_ref(v___y_2227_);
v___x_2232_ = lean_whnf(v_argTy_2226_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
if (lean_obj_tag(v___x_2232_) == 0)
{
lean_object* v_a_2233_; lean_object* v___x_2234_; 
v_a_2233_ = lean_ctor_get(v___x_2232_, 0);
lean_inc(v_a_2233_);
lean_dec_ref_known(v___x_2232_, 1);
v___x_2234_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2233_, v___y_2227_, v___y_2228_, v___y_2229_, v___y_2230_);
if (lean_obj_tag(v___x_2234_) == 0)
{
lean_object* v_a_2235_; lean_object* v_dummy_2236_; lean_object* v_nargs_2237_; lean_object* v___x_2238_; lean_object* v___x_2239_; lean_object* v___x_2240_; lean_object* v___x_2241_; lean_object* v___x_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; 
v_a_2235_ = lean_ctor_get(v___x_2234_, 0);
lean_inc(v_a_2235_);
lean_dec_ref_known(v___x_2234_, 1);
v_dummy_2236_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2237_ = l_Lean_Expr_getAppNumArgs(v_a_2233_);
lean_inc(v_nargs_2237_);
v___x_2238_ = lean_mk_array(v_nargs_2237_, v_dummy_2236_);
v___x_2239_ = lean_unsigned_to_nat(1u);
v___x_2240_ = lean_nat_sub(v_nargs_2237_, v___x_2239_);
lean_dec(v_nargs_2237_);
v___x_2241_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2233_, v___x_2238_, v___x_2240_);
v___x_2242_ = lean_array_get_size(v___x_2241_);
lean_inc(v___x_2222_);
v___x_2243_ = l_Array_toSubarray___redArg(v___x_2241_, v___x_2222_, v___x_2242_);
v___x_2244_ = lean_box(0);
v___x_2245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2245_, 0, v___x_2244_);
lean_ctor_set(v___x_2245_, 1, v___x_2243_);
v___x_2246_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2242_, v_a_2235_, v___x_2223_, v___x_2222_, v___x_2245_);
lean_dec(v_a_2235_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2260_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2260_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2260_ == 0)
{
v___x_2249_ = v___x_2246_;
v_isShared_2250_ = v_isSharedCheck_2260_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_a_2247_);
lean_dec(v___x_2246_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2260_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v_fst_2251_; 
v_fst_2251_ = lean_ctor_get(v_a_2247_, 0);
lean_inc(v_fst_2251_);
lean_dec(v_a_2247_);
if (lean_obj_tag(v_fst_2251_) == 0)
{
lean_object* v___x_2252_; lean_object* v___x_2254_; 
v___x_2252_ = lean_box(v___x_2224_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v___x_2252_);
v___x_2254_ = v___x_2249_;
goto v_reusejp_2253_;
}
else
{
lean_object* v_reuseFailAlloc_2255_; 
v_reuseFailAlloc_2255_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2255_, 0, v___x_2252_);
v___x_2254_ = v_reuseFailAlloc_2255_;
goto v_reusejp_2253_;
}
v_reusejp_2253_:
{
return v___x_2254_;
}
}
else
{
lean_object* v_val_2256_; lean_object* v___x_2258_; 
v_val_2256_ = lean_ctor_get(v_fst_2251_, 0);
lean_inc(v_val_2256_);
lean_dec_ref_known(v_fst_2251_, 1);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 0, v_val_2256_);
v___x_2258_ = v___x_2249_;
goto v_reusejp_2257_;
}
else
{
lean_object* v_reuseFailAlloc_2259_; 
v_reuseFailAlloc_2259_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2259_, 0, v_val_2256_);
v___x_2258_ = v_reuseFailAlloc_2259_;
goto v_reusejp_2257_;
}
v_reusejp_2257_:
{
return v___x_2258_;
}
}
}
}
else
{
lean_object* v_a_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2268_; 
v_a_2261_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2268_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2268_ == 0)
{
v___x_2263_ = v___x_2246_;
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_a_2261_);
lean_dec(v___x_2246_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2268_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v___x_2266_; 
if (v_isShared_2264_ == 0)
{
v___x_2266_ = v___x_2263_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v_a_2261_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
}
}
else
{
lean_object* v_a_2269_; lean_object* v___x_2271_; uint8_t v_isShared_2272_; uint8_t v_isSharedCheck_2276_; 
lean_dec(v_a_2233_);
lean_dec(v___x_2222_);
v_a_2269_ = lean_ctor_get(v___x_2234_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2234_);
if (v_isSharedCheck_2276_ == 0)
{
v___x_2271_ = v___x_2234_;
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
else
{
lean_inc(v_a_2269_);
lean_dec(v___x_2234_);
v___x_2271_ = lean_box(0);
v_isShared_2272_ = v_isSharedCheck_2276_;
goto v_resetjp_2270_;
}
v_resetjp_2270_:
{
lean_object* v___x_2274_; 
if (v_isShared_2272_ == 0)
{
v___x_2274_ = v___x_2271_;
goto v_reusejp_2273_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_a_2269_);
v___x_2274_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2273_;
}
v_reusejp_2273_:
{
return v___x_2274_;
}
}
}
}
else
{
lean_object* v_a_2277_; lean_object* v___x_2279_; uint8_t v_isShared_2280_; uint8_t v_isSharedCheck_2284_; 
lean_dec(v___x_2222_);
v_a_2277_ = lean_ctor_get(v___x_2232_, 0);
v_isSharedCheck_2284_ = !lean_is_exclusive(v___x_2232_);
if (v_isSharedCheck_2284_ == 0)
{
v___x_2279_ = v___x_2232_;
v_isShared_2280_ = v_isSharedCheck_2284_;
goto v_resetjp_2278_;
}
else
{
lean_inc(v_a_2277_);
lean_dec(v___x_2232_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2285_, lean_object* v___x_2286_, lean_object* v___x_2287_, lean_object* v_x_2288_, lean_object* v_argTy_2289_, lean_object* v___y_2290_, lean_object* v___y_2291_, lean_object* v___y_2292_, lean_object* v___y_2293_, lean_object* v___y_2294_){
_start:
{
uint8_t v___x_22758__boxed_2295_; lean_object* v_res_2296_; 
v___x_22758__boxed_2295_ = lean_unbox(v___x_2287_);
v_res_2296_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2285_, v___x_2286_, v___x_22758__boxed_2295_, v_x_2288_, v_argTy_2289_, v___y_2290_, v___y_2291_, v___y_2292_, v___y_2293_);
lean_dec(v___y_2293_);
lean_dec_ref(v___y_2292_);
lean_dec(v___y_2291_);
lean_dec_ref(v___y_2290_);
lean_dec_ref(v_x_2288_);
lean_dec(v___x_2286_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2300_, lean_object* v_projInfo_x3f_2301_, lean_object* v___x_2302_, lean_object* v_argVars_2303_, lean_object* v_as_2304_, size_t v_sz_2305_, size_t v_i_2306_, lean_object* v_b_2307_, lean_object* v___y_2308_, lean_object* v___y_2309_, lean_object* v___y_2310_, lean_object* v___y_2311_){
_start:
{
uint8_t v___x_2313_; 
v___x_2313_ = lean_usize_dec_lt(v_i_2306_, v_sz_2305_);
if (v___x_2313_ == 0)
{
lean_object* v___x_2314_; 
lean_dec(v___x_2302_);
v___x_2314_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2314_, 0, v_b_2307_);
return v___x_2314_;
}
else
{
lean_object* v___x_2315_; lean_object* v_a_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
lean_dec_ref(v_b_2307_);
v___x_2315_ = l_Lean_instInhabitedExpr;
v_a_2316_ = lean_array_uget_borrowed(v_as_2304_, v_i_2306_);
v___x_2317_ = lean_array_get_borrowed(v___x_2315_, v_fst_2300_, v_a_2316_);
lean_inc(v___y_2311_);
lean_inc_ref(v___y_2310_);
lean_inc(v___y_2309_);
lean_inc_ref(v___y_2308_);
lean_inc(v___x_2317_);
v___x_2318_ = lean_infer_type(v___x_2317_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2318_) == 0)
{
lean_object* v_a_2319_; lean_object* v___x_2320_; 
v_a_2319_ = lean_ctor_get(v___x_2318_, 0);
lean_inc(v_a_2319_);
lean_dec_ref_known(v___x_2318_, 1);
v___x_2320_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2319_, v___y_2309_);
if (lean_obj_tag(v___x_2320_) == 0)
{
lean_object* v_a_2321_; lean_object* v___x_2323_; uint8_t v_isShared_2324_; uint8_t v_isSharedCheck_2367_; 
v_a_2321_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2367_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2367_ == 0)
{
v___x_2323_ = v___x_2320_;
v_isShared_2324_ = v_isSharedCheck_2367_;
goto v_resetjp_2322_;
}
else
{
lean_inc(v_a_2321_);
lean_dec(v___x_2320_);
v___x_2323_ = lean_box(0);
v_isShared_2324_ = v_isSharedCheck_2367_;
goto v_resetjp_2322_;
}
v_resetjp_2322_:
{
lean_object* v___x_2325_; lean_object* v___x_2333_; lean_object* v___y_2335_; lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___f_2351_; uint8_t v___x_2352_; 
v___x_2325_ = lean_box(0);
v___x_2333_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2349_ = lean_unsigned_to_nat(0u);
v___x_2350_ = lean_box(v___x_2313_);
lean_inc(v___x_2302_);
v___f_2351_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2351_, 0, v___x_2349_);
lean_closure_set(v___f_2351_, 1, v___x_2302_);
lean_closure_set(v___f_2351_, 2, v___x_2350_);
v___x_2352_ = lean_nat_dec_eq(v___x_2302_, v___x_2349_);
if (lean_obj_tag(v_projInfo_x3f_2301_) == 1)
{
lean_object* v_val_2353_; lean_object* v_numParams_2354_; uint8_t v___x_2355_; 
v_val_2353_ = lean_ctor_get(v_projInfo_x3f_2301_, 0);
v_numParams_2354_ = lean_ctor_get(v_val_2353_, 1);
v___x_2355_ = lean_nat_dec_eq(v_numParams_2354_, v_a_2316_);
if (v___x_2355_ == 0)
{
lean_object* v___x_2356_; 
v___x_2356_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2321_, v___f_2351_, v___x_2352_, v___x_2352_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
v___y_2335_ = v___x_2356_;
goto v___jp_2334_;
}
else
{
lean_object* v___x_2357_; 
lean_dec_ref(v___f_2351_);
lean_dec(v___x_2302_);
v___x_2357_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2300_, v_argVars_2303_, v_a_2321_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
if (lean_obj_tag(v___x_2357_) == 0)
{
lean_dec_ref_known(v___x_2357_, 1);
goto v___jp_2326_;
}
else
{
lean_object* v_a_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2365_; 
lean_del_object(v___x_2323_);
v_a_2358_ = lean_ctor_get(v___x_2357_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2357_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2360_ = v___x_2357_;
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_a_2358_);
lean_dec(v___x_2357_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2365_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2363_; 
if (v_isShared_2361_ == 0)
{
v___x_2363_ = v___x_2360_;
goto v_reusejp_2362_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_a_2358_);
v___x_2363_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2362_;
}
v_reusejp_2362_:
{
return v___x_2363_;
}
}
}
}
}
else
{
lean_object* v___x_2366_; 
v___x_2366_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2321_, v___f_2351_, v___x_2352_, v___x_2352_, v___y_2308_, v___y_2309_, v___y_2310_, v___y_2311_);
v___y_2335_ = v___x_2366_;
goto v___jp_2334_;
}
v___jp_2326_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; lean_object* v___x_2329_; lean_object* v___x_2331_; 
lean_inc(v_a_2316_);
v___x_2327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2327_, 0, v_a_2316_);
v___x_2328_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2328_, 0, v___x_2327_);
v___x_2329_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2329_, 0, v___x_2328_);
lean_ctor_set(v___x_2329_, 1, v___x_2325_);
if (v_isShared_2324_ == 0)
{
lean_ctor_set(v___x_2323_, 0, v___x_2329_);
v___x_2331_ = v___x_2323_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2332_; 
v_reuseFailAlloc_2332_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2332_, 0, v___x_2329_);
v___x_2331_ = v_reuseFailAlloc_2332_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
return v___x_2331_;
}
}
v___jp_2334_:
{
if (lean_obj_tag(v___y_2335_) == 0)
{
lean_object* v_a_2336_; uint8_t v___x_2337_; 
v_a_2336_ = lean_ctor_get(v___y_2335_, 0);
lean_inc(v_a_2336_);
lean_dec_ref_known(v___y_2335_, 1);
v___x_2337_ = lean_unbox(v_a_2336_);
lean_dec(v_a_2336_);
if (v___x_2337_ == 0)
{
size_t v___x_2338_; size_t v___x_2339_; 
lean_del_object(v___x_2323_);
v___x_2338_ = ((size_t)1ULL);
v___x_2339_ = lean_usize_add(v_i_2306_, v___x_2338_);
v_i_2306_ = v___x_2339_;
v_b_2307_ = v___x_2333_;
goto _start;
}
else
{
lean_dec(v___x_2302_);
goto v___jp_2326_;
}
}
else
{
lean_object* v_a_2341_; lean_object* v___x_2343_; uint8_t v_isShared_2344_; uint8_t v_isSharedCheck_2348_; 
lean_del_object(v___x_2323_);
lean_dec(v___x_2302_);
v_a_2341_ = lean_ctor_get(v___y_2335_, 0);
v_isSharedCheck_2348_ = !lean_is_exclusive(v___y_2335_);
if (v_isSharedCheck_2348_ == 0)
{
v___x_2343_ = v___y_2335_;
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
else
{
lean_inc(v_a_2341_);
lean_dec(v___y_2335_);
v___x_2343_ = lean_box(0);
v_isShared_2344_ = v_isSharedCheck_2348_;
goto v_resetjp_2342_;
}
v_resetjp_2342_:
{
lean_object* v___x_2346_; 
if (v_isShared_2344_ == 0)
{
v___x_2346_ = v___x_2343_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2347_; 
v_reuseFailAlloc_2347_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2347_, 0, v_a_2341_);
v___x_2346_ = v_reuseFailAlloc_2347_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
return v___x_2346_;
}
}
}
}
}
}
else
{
lean_object* v_a_2368_; lean_object* v___x_2370_; uint8_t v_isShared_2371_; uint8_t v_isSharedCheck_2375_; 
lean_dec(v___x_2302_);
v_a_2368_ = lean_ctor_get(v___x_2320_, 0);
v_isSharedCheck_2375_ = !lean_is_exclusive(v___x_2320_);
if (v_isSharedCheck_2375_ == 0)
{
v___x_2370_ = v___x_2320_;
v_isShared_2371_ = v_isSharedCheck_2375_;
goto v_resetjp_2369_;
}
else
{
lean_inc(v_a_2368_);
lean_dec(v___x_2320_);
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
lean_dec(v___x_2302_);
v_a_2376_ = lean_ctor_get(v___x_2318_, 0);
v_isSharedCheck_2383_ = !lean_is_exclusive(v___x_2318_);
if (v_isSharedCheck_2383_ == 0)
{
v___x_2378_ = v___x_2318_;
v_isShared_2379_ = v_isSharedCheck_2383_;
goto v_resetjp_2377_;
}
else
{
lean_inc(v_a_2376_);
lean_dec(v___x_2318_);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2384_, lean_object* v_projInfo_x3f_2385_, lean_object* v___x_2386_, lean_object* v_argVars_2387_, lean_object* v_as_2388_, lean_object* v_sz_2389_, lean_object* v_i_2390_, lean_object* v_b_2391_, lean_object* v___y_2392_, lean_object* v___y_2393_, lean_object* v___y_2394_, lean_object* v___y_2395_, lean_object* v___y_2396_){
_start:
{
size_t v_sz_boxed_2397_; size_t v_i_boxed_2398_; lean_object* v_res_2399_; 
v_sz_boxed_2397_ = lean_unbox_usize(v_sz_2389_);
lean_dec(v_sz_2389_);
v_i_boxed_2398_ = lean_unbox_usize(v_i_2390_);
lean_dec(v_i_2390_);
v_res_2399_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2384_, v_projInfo_x3f_2385_, v___x_2386_, v_argVars_2387_, v_as_2388_, v_sz_boxed_2397_, v_i_boxed_2398_, v_b_2391_, v___y_2392_, v___y_2393_, v___y_2394_, v___y_2395_);
lean_dec(v___y_2395_);
lean_dec_ref(v___y_2394_);
lean_dec(v___y_2393_);
lean_dec_ref(v___y_2392_);
lean_dec_ref(v_as_2388_);
lean_dec_ref(v_argVars_2387_);
lean_dec(v_projInfo_x3f_2385_);
lean_dec_ref(v_fst_2384_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_, lean_object* v___y_2404_){
_start:
{
lean_object* v___x_2406_; lean_object* v_env_2407_; lean_object* v___x_2408_; lean_object* v_mctx_2409_; lean_object* v_lctx_2410_; lean_object* v_options_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2406_ = lean_st_ref_get(v___y_2404_);
v_env_2407_ = lean_ctor_get(v___x_2406_, 0);
lean_inc_ref(v_env_2407_);
lean_dec(v___x_2406_);
v___x_2408_ = lean_st_ref_get(v___y_2402_);
v_mctx_2409_ = lean_ctor_get(v___x_2408_, 0);
lean_inc_ref(v_mctx_2409_);
lean_dec(v___x_2408_);
v_lctx_2410_ = lean_ctor_get(v___y_2401_, 2);
v_options_2411_ = lean_ctor_get(v___y_2403_, 1);
lean_inc_ref(v_options_2411_);
lean_inc_ref(v_lctx_2410_);
v___x_2412_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2412_, 0, v_env_2407_);
lean_ctor_set(v___x_2412_, 1, v_mctx_2409_);
lean_ctor_set(v___x_2412_, 2, v_lctx_2410_);
lean_ctor_set(v___x_2412_, 3, v_options_2411_);
v___x_2413_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2413_, 0, v___x_2412_);
lean_ctor_set(v___x_2413_, 1, v_msgData_2400_);
v___x_2414_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2414_, 0, v___x_2413_);
return v___x_2414_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2415_, lean_object* v___y_2416_, lean_object* v___y_2417_, lean_object* v___y_2418_, lean_object* v___y_2419_, lean_object* v___y_2420_){
_start:
{
lean_object* v_res_2421_; 
v_res_2421_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2415_, v___y_2416_, v___y_2417_, v___y_2418_, v___y_2419_);
lean_dec(v___y_2419_);
lean_dec_ref(v___y_2418_);
lean_dec(v___y_2417_);
lean_dec_ref(v___y_2416_);
return v_res_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_){
_start:
{
lean_object* v_ref_2428_; lean_object* v___x_2429_; lean_object* v_a_2430_; lean_object* v___x_2432_; uint8_t v_isShared_2433_; uint8_t v_isSharedCheck_2438_; 
v_ref_2428_ = lean_ctor_get(v___y_2425_, 4);
v___x_2429_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
v_a_2430_ = lean_ctor_get(v___x_2429_, 0);
v_isSharedCheck_2438_ = !lean_is_exclusive(v___x_2429_);
if (v_isSharedCheck_2438_ == 0)
{
v___x_2432_ = v___x_2429_;
v_isShared_2433_ = v_isSharedCheck_2438_;
goto v_resetjp_2431_;
}
else
{
lean_inc(v_a_2430_);
lean_dec(v___x_2429_);
v___x_2432_ = lean_box(0);
v_isShared_2433_ = v_isSharedCheck_2438_;
goto v_resetjp_2431_;
}
v_resetjp_2431_:
{
lean_object* v___x_2434_; lean_object* v___x_2436_; 
lean_inc(v_ref_2428_);
v___x_2434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2434_, 0, v_ref_2428_);
lean_ctor_set(v___x_2434_, 1, v_a_2430_);
if (v_isShared_2433_ == 0)
{
lean_ctor_set_tag(v___x_2432_, 1);
lean_ctor_set(v___x_2432_, 0, v___x_2434_);
v___x_2436_ = v___x_2432_;
goto v_reusejp_2435_;
}
else
{
lean_object* v_reuseFailAlloc_2437_; 
v_reuseFailAlloc_2437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2437_, 0, v___x_2434_);
v___x_2436_ = v_reuseFailAlloc_2437_;
goto v_reusejp_2435_;
}
v_reusejp_2435_:
{
return v___x_2436_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2439_, lean_object* v___y_2440_, lean_object* v___y_2441_, lean_object* v___y_2442_, lean_object* v___y_2443_, lean_object* v___y_2444_){
_start:
{
lean_object* v_res_2445_; 
v_res_2445_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2439_, v___y_2440_, v___y_2441_, v___y_2442_, v___y_2443_);
lean_dec(v___y_2443_);
lean_dec_ref(v___y_2442_);
lean_dec(v___y_2441_);
lean_dec_ref(v___y_2440_);
return v_res_2445_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2446_, size_t v_sz_2447_, size_t v_i_2448_, lean_object* v_bs_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_, lean_object* v___y_2452_, lean_object* v___y_2453_){
_start:
{
uint8_t v___x_2455_; 
v___x_2455_ = lean_usize_dec_lt(v_i_2448_, v_sz_2447_);
if (v___x_2455_ == 0)
{
lean_object* v___x_2456_; 
v___x_2456_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2456_, 0, v_bs_2449_);
return v___x_2456_;
}
else
{
lean_object* v___x_2457_; lean_object* v_v_2458_; lean_object* v___x_2459_; lean_object* v___x_2460_; 
v___x_2457_ = l_Lean_instInhabitedExpr;
v_v_2458_ = lean_array_uget_borrowed(v_bs_2449_, v_i_2448_);
v___x_2459_ = lean_array_get_borrowed(v___x_2457_, v_fst_2446_, v_v_2458_);
lean_inc(v___y_2453_);
lean_inc_ref(v___y_2452_);
lean_inc(v___y_2451_);
lean_inc_ref(v___y_2450_);
lean_inc(v___x_2459_);
v___x_2460_ = lean_infer_type(v___x_2459_, v___y_2450_, v___y_2451_, v___y_2452_, v___y_2453_);
if (lean_obj_tag(v___x_2460_) == 0)
{
lean_object* v_a_2461_; lean_object* v___x_2462_; 
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
lean_inc(v_a_2461_);
lean_dec_ref_known(v___x_2460_, 1);
v___x_2462_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2461_, v___y_2451_);
if (lean_obj_tag(v___x_2462_) == 0)
{
lean_object* v_a_2463_; lean_object* v___x_2464_; lean_object* v_bs_x27_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; size_t v___x_2468_; size_t v___x_2469_; lean_object* v___x_2470_; 
v_a_2463_ = lean_ctor_get(v___x_2462_, 0);
lean_inc(v_a_2463_);
lean_dec_ref_known(v___x_2462_, 1);
v___x_2464_ = lean_unsigned_to_nat(0u);
v_bs_x27_2465_ = lean_array_uset(v_bs_2449_, v_i_2448_, v___x_2464_);
v___x_2466_ = l_Lean_Expr_setPPExplicit(v_a_2463_, v___x_2455_);
v___x_2467_ = l_Lean_indentExpr(v___x_2466_);
v___x_2468_ = ((size_t)1ULL);
v___x_2469_ = lean_usize_add(v_i_2448_, v___x_2468_);
v___x_2470_ = lean_array_uset(v_bs_x27_2465_, v_i_2448_, v___x_2467_);
v_i_2448_ = v___x_2469_;
v_bs_2449_ = v___x_2470_;
goto _start;
}
else
{
lean_object* v_a_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2479_; 
lean_dec_ref(v_bs_2449_);
v_a_2472_ = lean_ctor_get(v___x_2462_, 0);
v_isSharedCheck_2479_ = !lean_is_exclusive(v___x_2462_);
if (v_isSharedCheck_2479_ == 0)
{
v___x_2474_ = v___x_2462_;
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_a_2472_);
lean_dec(v___x_2462_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2479_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v___x_2477_; 
if (v_isShared_2475_ == 0)
{
v___x_2477_ = v___x_2474_;
goto v_reusejp_2476_;
}
else
{
lean_object* v_reuseFailAlloc_2478_; 
v_reuseFailAlloc_2478_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2478_, 0, v_a_2472_);
v___x_2477_ = v_reuseFailAlloc_2478_;
goto v_reusejp_2476_;
}
v_reusejp_2476_:
{
return v___x_2477_;
}
}
}
}
else
{
lean_object* v_a_2480_; lean_object* v___x_2482_; uint8_t v_isShared_2483_; uint8_t v_isSharedCheck_2487_; 
lean_dec_ref(v_bs_2449_);
v_a_2480_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2487_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2487_ == 0)
{
v___x_2482_ = v___x_2460_;
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
else
{
lean_inc(v_a_2480_);
lean_dec(v___x_2460_);
v___x_2482_ = lean_box(0);
v_isShared_2483_ = v_isSharedCheck_2487_;
goto v_resetjp_2481_;
}
v_resetjp_2481_:
{
lean_object* v___x_2485_; 
if (v_isShared_2483_ == 0)
{
v___x_2485_ = v___x_2482_;
goto v_reusejp_2484_;
}
else
{
lean_object* v_reuseFailAlloc_2486_; 
v_reuseFailAlloc_2486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2486_, 0, v_a_2480_);
v___x_2485_ = v_reuseFailAlloc_2486_;
goto v_reusejp_2484_;
}
v_reusejp_2484_:
{
return v___x_2485_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2488_, lean_object* v_sz_2489_, lean_object* v_i_2490_, lean_object* v_bs_2491_, lean_object* v___y_2492_, lean_object* v___y_2493_, lean_object* v___y_2494_, lean_object* v___y_2495_, lean_object* v___y_2496_){
_start:
{
size_t v_sz_boxed_2497_; size_t v_i_boxed_2498_; lean_object* v_res_2499_; 
v_sz_boxed_2497_ = lean_unbox_usize(v_sz_2489_);
lean_dec(v_sz_2489_);
v_i_boxed_2498_ = lean_unbox_usize(v_i_2490_);
lean_dec(v_i_2490_);
v_res_2499_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2488_, v_sz_boxed_2497_, v_i_boxed_2498_, v_bs_2491_, v___y_2492_, v___y_2493_, v___y_2494_, v___y_2495_);
lean_dec(v___y_2495_);
lean_dec_ref(v___y_2494_);
lean_dec(v___y_2493_);
lean_dec_ref(v___y_2492_);
lean_dec_ref(v_fst_2488_);
return v_res_2499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object* v___x_2500_, lean_object* v_snd_2501_, lean_object* v___f_2502_, lean_object* v_____r_2503_, lean_object* v___y_2504_, lean_object* v___y_2505_, lean_object* v___y_2506_, lean_object* v___y_2507_){
_start:
{
lean_object* v___x_2509_; lean_object* v___x_2510_; lean_object* v___x_2511_; 
v___x_2509_ = lean_unsigned_to_nat(0u);
v___x_2510_ = lean_array_get_borrowed(v___x_2500_, v_snd_2501_, v___x_2509_);
lean_inc(v___y_2507_);
lean_inc_ref(v___y_2506_);
lean_inc(v___y_2505_);
lean_inc_ref(v___y_2504_);
lean_inc(v___x_2510_);
v___x_2511_ = lean_apply_6(v___f_2502_, v___x_2510_, v___y_2504_, v___y_2505_, v___y_2506_, v___y_2507_, lean_box(0));
return v___x_2511_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object* v___x_2512_, lean_object* v_snd_2513_, lean_object* v___f_2514_, lean_object* v_____r_2515_, lean_object* v___y_2516_, lean_object* v___y_2517_, lean_object* v___y_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_){
_start:
{
lean_object* v_res_2521_; 
v_res_2521_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2512_, v_snd_2513_, v___f_2514_, v_____r_2515_, v___y_2516_, v___y_2517_, v___y_2518_, v___y_2519_);
lean_dec(v___y_2519_);
lean_dec_ref(v___y_2518_);
lean_dec(v___y_2517_);
lean_dec_ref(v___y_2516_);
lean_dec(v_snd_2513_);
lean_dec(v___x_2512_);
return v_res_2521_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2525_; lean_object* v___x_2526_; 
v___x_2525_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1));
v___x_2526_ = l_Lean_MessageData_ofFormat(v___x_2525_);
return v___x_2526_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3));
v___x_2529_ = l_Lean_stringToMessageData(v___x_2528_);
return v___x_2529_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5));
v___x_2532_ = l_Lean_stringToMessageData(v___x_2531_);
return v___x_2532_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7));
v___x_2535_ = l_Lean_stringToMessageData(v___x_2534_);
return v___x_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(lean_object* v_fst_2536_, lean_object* v_argVars_2537_, lean_object* v_inst_2538_, lean_object* v_a_2539_, lean_object* v_projInfo_x3f_2540_, lean_object* v_a_2541_, lean_object* v___y_2542_, lean_object* v___y_2543_, lean_object* v___y_2544_, lean_object* v___y_2545_){
_start:
{
lean_object* v___y_2548_; lean_object* v_fst_2568_; lean_object* v_snd_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2646_; 
v_fst_2568_ = lean_ctor_get(v_a_2541_, 0);
v_snd_2569_ = lean_ctor_get(v_a_2541_, 1);
v_isSharedCheck_2646_ = !lean_is_exclusive(v_a_2541_);
if (v_isSharedCheck_2646_ == 0)
{
v___x_2571_ = v_a_2541_;
v_isShared_2572_ = v_isSharedCheck_2646_;
goto v_resetjp_2570_;
}
else
{
lean_inc(v_snd_2569_);
lean_inc(v_fst_2568_);
lean_dec(v_a_2541_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2646_;
goto v_resetjp_2570_;
}
v___jp_2547_:
{
if (lean_obj_tag(v___y_2548_) == 0)
{
lean_object* v_a_2549_; lean_object* v___x_2551_; uint8_t v_isShared_2552_; uint8_t v_isSharedCheck_2559_; 
v_a_2549_ = lean_ctor_get(v___y_2548_, 0);
v_isSharedCheck_2559_ = !lean_is_exclusive(v___y_2548_);
if (v_isSharedCheck_2559_ == 0)
{
v___x_2551_ = v___y_2548_;
v_isShared_2552_ = v_isSharedCheck_2559_;
goto v_resetjp_2550_;
}
else
{
lean_inc(v_a_2549_);
lean_dec(v___y_2548_);
v___x_2551_ = lean_box(0);
v_isShared_2552_ = v_isSharedCheck_2559_;
goto v_resetjp_2550_;
}
v_resetjp_2550_:
{
if (lean_obj_tag(v_a_2549_) == 0)
{
lean_object* v_a_2553_; lean_object* v___x_2555_; 
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_inst_2538_);
lean_dec_ref(v_argVars_2537_);
lean_dec_ref(v_fst_2536_);
v_a_2553_ = lean_ctor_get(v_a_2549_, 0);
lean_inc(v_a_2553_);
lean_dec_ref_known(v_a_2549_, 1);
if (v_isShared_2552_ == 0)
{
lean_ctor_set(v___x_2551_, 0, v_a_2553_);
v___x_2555_ = v___x_2551_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_a_2553_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
else
{
lean_object* v_a_2557_; 
lean_del_object(v___x_2551_);
v_a_2557_ = lean_ctor_get(v_a_2549_, 0);
lean_inc(v_a_2557_);
lean_dec_ref_known(v_a_2549_, 1);
v_a_2541_ = v_a_2557_;
goto _start;
}
}
}
else
{
lean_object* v_a_2560_; lean_object* v___x_2562_; uint8_t v_isShared_2563_; uint8_t v_isSharedCheck_2567_; 
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_inst_2538_);
lean_dec_ref(v_argVars_2537_);
lean_dec_ref(v_fst_2536_);
v_a_2560_ = lean_ctor_get(v___y_2548_, 0);
v_isSharedCheck_2567_ = !lean_is_exclusive(v___y_2548_);
if (v_isSharedCheck_2567_ == 0)
{
v___x_2562_ = v___y_2548_;
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
else
{
lean_inc(v_a_2560_);
lean_dec(v___y_2548_);
v___x_2562_ = lean_box(0);
v_isShared_2563_ = v_isSharedCheck_2567_;
goto v_resetjp_2561_;
}
v_resetjp_2561_:
{
lean_object* v___x_2565_; 
if (v_isShared_2563_ == 0)
{
v___x_2565_ = v___x_2562_;
goto v_reusejp_2564_;
}
else
{
lean_object* v_reuseFailAlloc_2566_; 
v_reuseFailAlloc_2566_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2566_, 0, v_a_2560_);
v___x_2565_ = v_reuseFailAlloc_2566_;
goto v_reusejp_2564_;
}
v_reusejp_2564_:
{
return v___x_2565_;
}
}
}
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2574_; uint8_t v___x_2575_; 
v___x_2573_ = lean_array_get_size(v_snd_2569_);
v___x_2574_ = lean_unsigned_to_nat(0u);
v___x_2575_ = lean_nat_dec_eq(v___x_2573_, v___x_2574_);
if (v___x_2575_ == 0)
{
lean_object* v___x_2576_; lean_object* v___x_2577_; size_t v_sz_2578_; size_t v___x_2579_; lean_object* v___x_2580_; 
lean_del_object(v___x_2571_);
v___x_2576_ = lean_box(0);
v___x_2577_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2578_ = lean_array_size(v_snd_2569_);
v___x_2579_ = ((size_t)0ULL);
v___x_2580_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2536_, v_projInfo_x3f_2540_, v___x_2573_, v_argVars_2537_, v_snd_2569_, v_sz_2578_, v___x_2579_, v___x_2577_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2580_) == 0)
{
lean_object* v_a_2581_; lean_object* v_fst_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2632_; 
v_a_2581_ = lean_ctor_get(v___x_2580_, 0);
lean_inc(v_a_2581_);
lean_dec_ref_known(v___x_2580_, 1);
v_fst_2582_ = lean_ctor_get(v_a_2581_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_a_2581_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; 
v_unused_2633_ = lean_ctor_get(v_a_2581_, 1);
lean_dec(v_unused_2633_);
v___x_2584_ = v_a_2581_;
v_isShared_2585_ = v_isSharedCheck_2632_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_fst_2582_);
lean_dec(v_a_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2632_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
lean_object* v___x_2586_; lean_object* v___f_2587_; 
v___x_2586_ = l_Lean_instInhabitedExpr;
lean_inc(v_snd_2569_);
lean_inc_ref(v_argVars_2537_);
lean_inc_ref(v_fst_2536_);
lean_inc(v_fst_2568_);
v___f_2587_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed), 11, 5);
lean_closure_set(v___f_2587_, 0, v_fst_2568_);
lean_closure_set(v___f_2587_, 1, v___x_2586_);
lean_closure_set(v___f_2587_, 2, v_fst_2536_);
lean_closure_set(v___f_2587_, 3, v_argVars_2537_);
lean_closure_set(v___f_2587_, 4, v_snd_2569_);
if (lean_obj_tag(v_fst_2582_) == 0)
{
lean_dec(v_fst_2568_);
goto v___jp_2588_;
}
else
{
lean_object* v_val_2629_; 
v_val_2629_ = lean_ctor_get(v_fst_2582_, 0);
lean_inc(v_val_2629_);
lean_dec_ref_known(v_fst_2582_, 1);
if (lean_obj_tag(v_val_2629_) == 0)
{
lean_dec(v_fst_2568_);
goto v___jp_2588_;
}
else
{
lean_object* v_val_2630_; lean_object* v___x_2631_; 
lean_dec_ref(v___f_2587_);
lean_del_object(v___x_2584_);
v_val_2630_ = lean_ctor_get(v_val_2629_, 0);
lean_inc(v_val_2630_);
lean_dec_ref_known(v_val_2629_, 1);
v___x_2631_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2568_, v___x_2586_, v_fst_2536_, v_argVars_2537_, v_snd_2569_, v_val_2630_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v_snd_2569_);
v___y_2548_ = v___x_2631_;
goto v___jp_2547_;
}
}
v___jp_2588_:
{
lean_object* v_options_2589_; lean_object* v___x_2590_; uint8_t v___x_2591_; 
v_options_2589_ = lean_ctor_get(v___y_2544_, 1);
v___x_2590_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2591_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2589_, v___x_2590_);
if (v___x_2591_ == 0)
{
lean_object* v___x_2592_; 
lean_del_object(v___x_2584_);
v___x_2592_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2574_, v_snd_2569_, v___f_2587_, v___x_2576_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v_snd_2569_);
v___y_2548_ = v___x_2592_;
goto v___jp_2547_;
}
else
{
lean_object* v___x_2593_; 
lean_inc(v_snd_2569_);
v___x_2593_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2536_, v_sz_2578_, v___x_2579_, v_snd_2569_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2593_) == 0)
{
lean_object* v_a_2594_; lean_object* v___x_2595_; lean_object* v___x_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2601_; 
v_a_2594_ = lean_ctor_get(v___x_2593_, 0);
lean_inc(v_a_2594_);
lean_dec_ref_known(v___x_2593_, 1);
v___x_2595_ = lean_array_to_list(v_a_2594_);
v___x_2596_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2597_ = l_Lean_MessageData_joinSep(v___x_2595_, v___x_2596_);
v___x_2598_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4);
lean_inc_ref(v_inst_2538_);
v___x_2599_ = l_Lean_MessageData_ofExpr(v_inst_2538_);
if (v_isShared_2585_ == 0)
{
lean_ctor_set_tag(v___x_2584_, 7);
lean_ctor_set(v___x_2584_, 1, v___x_2599_);
lean_ctor_set(v___x_2584_, 0, v___x_2598_);
v___x_2601_ = v___x_2584_;
goto v_reusejp_2600_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v___x_2598_);
lean_ctor_set(v_reuseFailAlloc_2620_, 1, v___x_2599_);
v___x_2601_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2600_;
}
v_reusejp_2600_:
{
lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; 
v___x_2602_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6);
v___x_2603_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2603_, 0, v___x_2601_);
lean_ctor_set(v___x_2603_, 1, v___x_2602_);
lean_inc_ref(v_a_2539_);
v___x_2604_ = l_Lean_indentExpr(v_a_2539_);
v___x_2605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2603_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
v___x_2606_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2608_, 0, v___x_2607_);
lean_ctor_set(v___x_2608_, 1, v___x_2597_);
v___x_2609_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2608_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
if (lean_obj_tag(v___x_2609_) == 0)
{
lean_object* v_a_2610_; lean_object* v___x_2611_; 
v_a_2610_ = lean_ctor_get(v___x_2609_, 0);
lean_inc(v_a_2610_);
lean_dec_ref_known(v___x_2609_, 1);
v___x_2611_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v___x_2574_, v_snd_2569_, v___f_2587_, v_a_2610_, v___y_2542_, v___y_2543_, v___y_2544_, v___y_2545_);
lean_dec(v_snd_2569_);
v___y_2548_ = v___x_2611_;
goto v___jp_2547_;
}
else
{
lean_object* v_a_2612_; lean_object* v___x_2614_; uint8_t v_isShared_2615_; uint8_t v_isSharedCheck_2619_; 
lean_dec_ref(v___f_2587_);
lean_dec(v_snd_2569_);
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_inst_2538_);
lean_dec_ref(v_argVars_2537_);
lean_dec_ref(v_fst_2536_);
v_a_2612_ = lean_ctor_get(v___x_2609_, 0);
v_isSharedCheck_2619_ = !lean_is_exclusive(v___x_2609_);
if (v_isSharedCheck_2619_ == 0)
{
v___x_2614_ = v___x_2609_;
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
else
{
lean_inc(v_a_2612_);
lean_dec(v___x_2609_);
v___x_2614_ = lean_box(0);
v_isShared_2615_ = v_isSharedCheck_2619_;
goto v_resetjp_2613_;
}
v_resetjp_2613_:
{
lean_object* v___x_2617_; 
if (v_isShared_2615_ == 0)
{
v___x_2617_ = v___x_2614_;
goto v_reusejp_2616_;
}
else
{
lean_object* v_reuseFailAlloc_2618_; 
v_reuseFailAlloc_2618_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2618_, 0, v_a_2612_);
v___x_2617_ = v_reuseFailAlloc_2618_;
goto v_reusejp_2616_;
}
v_reusejp_2616_:
{
return v___x_2617_;
}
}
}
}
}
else
{
lean_object* v_a_2621_; lean_object* v___x_2623_; uint8_t v_isShared_2624_; uint8_t v_isSharedCheck_2628_; 
lean_dec_ref(v___f_2587_);
lean_del_object(v___x_2584_);
lean_dec(v_snd_2569_);
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_inst_2538_);
lean_dec_ref(v_argVars_2537_);
lean_dec_ref(v_fst_2536_);
v_a_2621_ = lean_ctor_get(v___x_2593_, 0);
v_isSharedCheck_2628_ = !lean_is_exclusive(v___x_2593_);
if (v_isSharedCheck_2628_ == 0)
{
v___x_2623_ = v___x_2593_;
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
else
{
lean_inc(v_a_2621_);
lean_dec(v___x_2593_);
v___x_2623_ = lean_box(0);
v_isShared_2624_ = v_isSharedCheck_2628_;
goto v_resetjp_2622_;
}
v_resetjp_2622_:
{
lean_object* v___x_2626_; 
if (v_isShared_2624_ == 0)
{
v___x_2626_ = v___x_2623_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_a_2621_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2634_; lean_object* v___x_2636_; uint8_t v_isShared_2637_; uint8_t v_isSharedCheck_2641_; 
lean_dec(v_snd_2569_);
lean_dec(v_fst_2568_);
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_inst_2538_);
lean_dec_ref(v_argVars_2537_);
lean_dec_ref(v_fst_2536_);
v_a_2634_ = lean_ctor_get(v___x_2580_, 0);
v_isSharedCheck_2641_ = !lean_is_exclusive(v___x_2580_);
if (v_isSharedCheck_2641_ == 0)
{
v___x_2636_ = v___x_2580_;
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
else
{
lean_inc(v_a_2634_);
lean_dec(v___x_2580_);
v___x_2636_ = lean_box(0);
v_isShared_2637_ = v_isSharedCheck_2641_;
goto v_resetjp_2635_;
}
v_resetjp_2635_:
{
lean_object* v___x_2639_; 
if (v_isShared_2637_ == 0)
{
v___x_2639_ = v___x_2636_;
goto v_reusejp_2638_;
}
else
{
lean_object* v_reuseFailAlloc_2640_; 
v_reuseFailAlloc_2640_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2640_, 0, v_a_2634_);
v___x_2639_ = v_reuseFailAlloc_2640_;
goto v_reusejp_2638_;
}
v_reusejp_2638_:
{
return v___x_2639_;
}
}
}
}
else
{
lean_object* v___x_2643_; 
lean_dec_ref(v_a_2539_);
lean_dec_ref(v_inst_2538_);
lean_dec_ref(v_argVars_2537_);
lean_dec_ref(v_fst_2536_);
if (v_isShared_2572_ == 0)
{
v___x_2643_ = v___x_2571_;
goto v_reusejp_2642_;
}
else
{
lean_object* v_reuseFailAlloc_2645_; 
v_reuseFailAlloc_2645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2645_, 0, v_fst_2568_);
lean_ctor_set(v_reuseFailAlloc_2645_, 1, v_snd_2569_);
v___x_2643_ = v_reuseFailAlloc_2645_;
goto v_reusejp_2642_;
}
v_reusejp_2642_:
{
lean_object* v___x_2644_; 
v___x_2644_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2643_);
return v___x_2644_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___boxed(lean_object* v_fst_2647_, lean_object* v_argVars_2648_, lean_object* v_inst_2649_, lean_object* v_a_2650_, lean_object* v_projInfo_x3f_2651_, lean_object* v_a_2652_, lean_object* v___y_2653_, lean_object* v___y_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_){
_start:
{
lean_object* v_res_2658_; 
v_res_2658_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2647_, v_argVars_2648_, v_inst_2649_, v_a_2650_, v_projInfo_x3f_2651_, v_a_2652_, v___y_2653_, v___y_2654_, v___y_2655_, v___y_2656_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v___y_2654_);
lean_dec_ref(v___y_2653_);
lean_dec(v_projInfo_x3f_2651_);
return v_res_2658_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2659_, lean_object* v_a_2660_, lean_object* v_a_2661_){
_start:
{
if (lean_obj_tag(v_a_2660_) == 0)
{
lean_object* v___x_2662_; 
v___x_2662_ = l_List_reverse___redArg(v_a_2661_);
return v___x_2662_;
}
else
{
lean_object* v_head_2663_; lean_object* v_tail_2664_; lean_object* v___x_2666_; uint8_t v_isShared_2667_; uint8_t v_isSharedCheck_2679_; 
v_head_2663_ = lean_ctor_get(v_a_2660_, 0);
v_tail_2664_ = lean_ctor_get(v_a_2660_, 1);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_a_2660_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2666_ = v_a_2660_;
v_isShared_2667_ = v_isSharedCheck_2679_;
goto v_resetjp_2665_;
}
else
{
lean_inc(v_tail_2664_);
lean_inc(v_head_2663_);
lean_dec(v_a_2660_);
v___x_2666_ = lean_box(0);
v_isShared_2667_ = v_isSharedCheck_2679_;
goto v_resetjp_2665_;
}
v_resetjp_2665_:
{
uint8_t v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; uint8_t v___x_2671_; uint8_t v___x_2672_; uint8_t v___x_2673_; 
v___x_2668_ = 0;
v___x_2669_ = lean_box(v___x_2668_);
v___x_2670_ = lean_array_get(v___x_2669_, v_fst_2659_, v_head_2663_);
lean_dec(v___x_2669_);
v___x_2671_ = 3;
v___x_2672_ = lean_unbox(v___x_2670_);
lean_dec(v___x_2670_);
v___x_2673_ = l_Lean_instBEqBinderInfo_beq(v___x_2672_, v___x_2671_);
if (v___x_2673_ == 0)
{
lean_del_object(v___x_2666_);
lean_dec(v_head_2663_);
v_a_2660_ = v_tail_2664_;
goto _start;
}
else
{
lean_object* v___x_2676_; 
if (v_isShared_2667_ == 0)
{
lean_ctor_set(v___x_2666_, 1, v_a_2661_);
v___x_2676_ = v___x_2666_;
goto v_reusejp_2675_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_head_2663_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_a_2661_);
v___x_2676_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2675_;
}
v_reusejp_2675_:
{
v_a_2660_ = v_tail_2664_;
v_a_2661_ = v___x_2676_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2680_, lean_object* v_a_2681_, lean_object* v_a_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2680_, v_a_2681_, v_a_2682_);
lean_dec_ref(v_fst_2680_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2684_, size_t v_sz_2685_, size_t v_i_2686_, lean_object* v_bs_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_){
_start:
{
uint8_t v___x_2693_; 
v___x_2693_ = lean_usize_dec_lt(v_i_2686_, v_sz_2685_);
if (v___x_2693_ == 0)
{
lean_object* v___x_2694_; 
v___x_2694_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2694_, 0, v_bs_2687_);
return v___x_2694_;
}
else
{
lean_object* v___x_2695_; lean_object* v_v_2696_; lean_object* v___x_2697_; lean_object* v___x_2698_; 
v___x_2695_ = l_Lean_instInhabitedExpr;
v_v_2696_ = lean_array_uget_borrowed(v_bs_2687_, v_i_2686_);
v___x_2697_ = lean_array_get_borrowed(v___x_2695_, v_argVars_2684_, v_v_2696_);
lean_inc(v___y_2691_);
lean_inc_ref(v___y_2690_);
lean_inc(v___y_2689_);
lean_inc_ref(v___y_2688_);
lean_inc(v___x_2697_);
v___x_2698_ = lean_infer_type(v___x_2697_, v___y_2688_, v___y_2689_, v___y_2690_, v___y_2691_);
if (lean_obj_tag(v___x_2698_) == 0)
{
lean_object* v_a_2699_; lean_object* v___x_2700_; lean_object* v_bs_x27_2701_; lean_object* v___x_2702_; size_t v___x_2703_; size_t v___x_2704_; lean_object* v___x_2705_; 
v_a_2699_ = lean_ctor_get(v___x_2698_, 0);
lean_inc(v_a_2699_);
lean_dec_ref_known(v___x_2698_, 1);
v___x_2700_ = lean_unsigned_to_nat(0u);
v_bs_x27_2701_ = lean_array_uset(v_bs_2687_, v_i_2686_, v___x_2700_);
v___x_2702_ = l_Lean_indentExpr(v_a_2699_);
v___x_2703_ = ((size_t)1ULL);
v___x_2704_ = lean_usize_add(v_i_2686_, v___x_2703_);
v___x_2705_ = lean_array_uset(v_bs_x27_2701_, v_i_2686_, v___x_2702_);
v_i_2686_ = v___x_2704_;
v_bs_2687_ = v___x_2705_;
goto _start;
}
else
{
lean_object* v_a_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2714_; 
lean_dec_ref(v_bs_2687_);
v_a_2707_ = lean_ctor_get(v___x_2698_, 0);
v_isSharedCheck_2714_ = !lean_is_exclusive(v___x_2698_);
if (v_isSharedCheck_2714_ == 0)
{
v___x_2709_ = v___x_2698_;
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
else
{
lean_inc(v_a_2707_);
lean_dec(v___x_2698_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2714_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2712_; 
if (v_isShared_2710_ == 0)
{
v___x_2712_ = v___x_2709_;
goto v_reusejp_2711_;
}
else
{
lean_object* v_reuseFailAlloc_2713_; 
v_reuseFailAlloc_2713_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2713_, 0, v_a_2707_);
v___x_2712_ = v_reuseFailAlloc_2713_;
goto v_reusejp_2711_;
}
v_reusejp_2711_:
{
return v___x_2712_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2715_, lean_object* v_sz_2716_, lean_object* v_i_2717_, lean_object* v_bs_2718_, lean_object* v___y_2719_, lean_object* v___y_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_){
_start:
{
size_t v_sz_boxed_2724_; size_t v_i_boxed_2725_; lean_object* v_res_2726_; 
v_sz_boxed_2724_ = lean_unbox_usize(v_sz_2716_);
lean_dec(v_sz_2716_);
v_i_boxed_2725_ = lean_unbox_usize(v_i_2717_);
lean_dec(v_i_2717_);
v_res_2726_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2715_, v_sz_boxed_2724_, v_i_boxed_2725_, v_bs_2718_, v___y_2719_, v___y_2720_, v___y_2721_, v___y_2722_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec(v___y_2720_);
lean_dec_ref(v___y_2719_);
lean_dec_ref(v_argVars_2715_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2727_, lean_object* v_a_2728_){
_start:
{
if (lean_obj_tag(v_a_2727_) == 0)
{
lean_object* v___x_2729_; 
v___x_2729_ = l_List_reverse___redArg(v_a_2728_);
return v___x_2729_;
}
else
{
lean_object* v_head_2730_; lean_object* v_tail_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2742_; 
v_head_2730_ = lean_ctor_get(v_a_2727_, 0);
v_tail_2731_ = lean_ctor_get(v_a_2727_, 1);
v_isSharedCheck_2742_ = !lean_is_exclusive(v_a_2727_);
if (v_isSharedCheck_2742_ == 0)
{
v___x_2733_ = v_a_2727_;
v_isShared_2734_ = v_isSharedCheck_2742_;
goto v_resetjp_2732_;
}
else
{
lean_inc(v_tail_2731_);
lean_inc(v_head_2730_);
lean_dec(v_a_2727_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2742_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2739_; 
v___x_2735_ = l_Nat_reprFast(v_head_2730_);
v___x_2736_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2736_, 0, v___x_2735_);
v___x_2737_ = l_Lean_MessageData_ofFormat(v___x_2736_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 1, v_a_2728_);
lean_ctor_set(v___x_2733_, 0, v___x_2737_);
v___x_2739_ = v___x_2733_;
goto v_reusejp_2738_;
}
else
{
lean_object* v_reuseFailAlloc_2741_; 
v_reuseFailAlloc_2741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2741_, 0, v___x_2737_);
lean_ctor_set(v_reuseFailAlloc_2741_, 1, v_a_2728_);
v___x_2739_ = v_reuseFailAlloc_2741_;
goto v_reusejp_2738_;
}
v_reusejp_2738_:
{
v_a_2727_ = v_tail_2731_;
v_a_2728_ = v___x_2739_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2743_; double v___x_2744_; 
v___x_2743_ = lean_unsigned_to_nat(0u);
v___x_2744_ = lean_float_of_nat(v___x_2743_);
return v___x_2744_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2747_, lean_object* v_msg_2748_, lean_object* v___y_2749_, lean_object* v___y_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_){
_start:
{
lean_object* v_ref_2754_; lean_object* v___x_2755_; lean_object* v_a_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2800_; 
v_ref_2754_ = lean_ctor_get(v___y_2751_, 4);
v___x_2755_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2748_, v___y_2749_, v___y_2750_, v___y_2751_, v___y_2752_);
v_a_2756_ = lean_ctor_get(v___x_2755_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v___x_2755_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2758_ = v___x_2755_;
v_isShared_2759_ = v_isSharedCheck_2800_;
goto v_resetjp_2757_;
}
else
{
lean_inc(v_a_2756_);
lean_dec(v___x_2755_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2800_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v_traceState_2761_; lean_object* v_env_2762_; lean_object* v_nextMacroScope_2763_; lean_object* v_ngen_2764_; lean_object* v_auxDeclNGen_2765_; lean_object* v_cache_2766_; lean_object* v_messages_2767_; lean_object* v_infoState_2768_; lean_object* v_snapshotTasks_2769_; lean_object* v___x_2771_; uint8_t v_isShared_2772_; uint8_t v_isSharedCheck_2799_; 
v___x_2760_ = lean_st_ref_take(v___y_2752_);
v_traceState_2761_ = lean_ctor_get(v___x_2760_, 4);
v_env_2762_ = lean_ctor_get(v___x_2760_, 0);
v_nextMacroScope_2763_ = lean_ctor_get(v___x_2760_, 1);
v_ngen_2764_ = lean_ctor_get(v___x_2760_, 2);
v_auxDeclNGen_2765_ = lean_ctor_get(v___x_2760_, 3);
v_cache_2766_ = lean_ctor_get(v___x_2760_, 5);
v_messages_2767_ = lean_ctor_get(v___x_2760_, 6);
v_infoState_2768_ = lean_ctor_get(v___x_2760_, 7);
v_snapshotTasks_2769_ = lean_ctor_get(v___x_2760_, 8);
v_isSharedCheck_2799_ = !lean_is_exclusive(v___x_2760_);
if (v_isSharedCheck_2799_ == 0)
{
v___x_2771_ = v___x_2760_;
v_isShared_2772_ = v_isSharedCheck_2799_;
goto v_resetjp_2770_;
}
else
{
lean_inc(v_snapshotTasks_2769_);
lean_inc(v_infoState_2768_);
lean_inc(v_messages_2767_);
lean_inc(v_cache_2766_);
lean_inc(v_traceState_2761_);
lean_inc(v_auxDeclNGen_2765_);
lean_inc(v_ngen_2764_);
lean_inc(v_nextMacroScope_2763_);
lean_inc(v_env_2762_);
lean_dec(v___x_2760_);
v___x_2771_ = lean_box(0);
v_isShared_2772_ = v_isSharedCheck_2799_;
goto v_resetjp_2770_;
}
v_resetjp_2770_:
{
uint64_t v_tid_2773_; lean_object* v_traces_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2798_; 
v_tid_2773_ = lean_ctor_get_uint64(v_traceState_2761_, sizeof(void*)*1);
v_traces_2774_ = lean_ctor_get(v_traceState_2761_, 0);
v_isSharedCheck_2798_ = !lean_is_exclusive(v_traceState_2761_);
if (v_isSharedCheck_2798_ == 0)
{
v___x_2776_ = v_traceState_2761_;
v_isShared_2777_ = v_isSharedCheck_2798_;
goto v_resetjp_2775_;
}
else
{
lean_inc(v_traces_2774_);
lean_dec(v_traceState_2761_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2798_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; double v___x_2779_; uint8_t v___x_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2778_ = lean_box(0);
v___x_2779_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2780_ = 0;
v___x_2781_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___x_2782_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2782_, 0, v_cls_2747_);
lean_ctor_set(v___x_2782_, 1, v___x_2778_);
lean_ctor_set(v___x_2782_, 2, v___x_2781_);
lean_ctor_set_float(v___x_2782_, sizeof(void*)*3, v___x_2779_);
lean_ctor_set_float(v___x_2782_, sizeof(void*)*3 + 8, v___x_2779_);
lean_ctor_set_uint8(v___x_2782_, sizeof(void*)*3 + 16, v___x_2780_);
v___x_2783_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2784_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2784_, 0, v___x_2782_);
lean_ctor_set(v___x_2784_, 1, v_a_2756_);
lean_ctor_set(v___x_2784_, 2, v___x_2783_);
lean_inc(v_ref_2754_);
v___x_2785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2785_, 0, v_ref_2754_);
lean_ctor_set(v___x_2785_, 1, v___x_2784_);
v___x_2786_ = l_Lean_PersistentArray_push___redArg(v_traces_2774_, v___x_2785_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 0, v___x_2786_);
v___x_2788_ = v___x_2776_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2786_);
lean_ctor_set_uint64(v_reuseFailAlloc_2797_, sizeof(void*)*1, v_tid_2773_);
v___x_2788_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
lean_object* v___x_2790_; 
if (v_isShared_2772_ == 0)
{
lean_ctor_set(v___x_2771_, 4, v___x_2788_);
v___x_2790_ = v___x_2771_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2796_; 
v_reuseFailAlloc_2796_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2796_, 0, v_env_2762_);
lean_ctor_set(v_reuseFailAlloc_2796_, 1, v_nextMacroScope_2763_);
lean_ctor_set(v_reuseFailAlloc_2796_, 2, v_ngen_2764_);
lean_ctor_set(v_reuseFailAlloc_2796_, 3, v_auxDeclNGen_2765_);
lean_ctor_set(v_reuseFailAlloc_2796_, 4, v___x_2788_);
lean_ctor_set(v_reuseFailAlloc_2796_, 5, v_cache_2766_);
lean_ctor_set(v_reuseFailAlloc_2796_, 6, v_messages_2767_);
lean_ctor_set(v_reuseFailAlloc_2796_, 7, v_infoState_2768_);
lean_ctor_set(v_reuseFailAlloc_2796_, 8, v_snapshotTasks_2769_);
v___x_2790_ = v_reuseFailAlloc_2796_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2791_ = lean_st_ref_put(v___y_2752_, v___x_2790_);
v___x_2792_ = lean_box(0);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 0, v___x_2792_);
v___x_2794_ = v___x_2758_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v___x_2792_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2801_, lean_object* v_msg_2802_, lean_object* v___y_2803_, lean_object* v___y_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_){
_start:
{
lean_object* v_res_2808_; 
v_res_2808_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2801_, v_msg_2802_, v___y_2803_, v___y_2804_, v___y_2805_, v___y_2806_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
lean_dec(v___y_2804_);
lean_dec_ref(v___y_2803_);
return v_res_2808_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; 
v___x_2816_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2817_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2818_ = l_Lean_Name_append(v___x_2817_, v___x_2816_);
return v___x_2818_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2820_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2821_ = l_Lean_stringToMessageData(v___x_2820_);
return v___x_2821_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2823_; lean_object* v___x_2824_; 
v___x_2823_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2824_ = l_Lean_stringToMessageData(v___x_2823_);
return v___x_2824_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2826_; lean_object* v___x_2827_; 
v___x_2826_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2827_ = l_Lean_stringToMessageData(v___x_2826_);
return v___x_2827_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2829_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2830_ = l_Lean_stringToMessageData(v___x_2829_);
return v___x_2830_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2831_, lean_object* v_fst_2832_, lean_object* v_fst_2833_, lean_object* v_inst_2834_, lean_object* v_a_2835_, lean_object* v_projInfo_x3f_2836_, lean_object* v_argVars_2837_, lean_object* v_x_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2831_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2844_) == 0)
{
lean_object* v_a_2845_; lean_object* v_dummy_2846_; lean_object* v_nargs_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; size_t v_sz_2855_; size_t v___x_2856_; lean_object* v___x_2857_; 
v_a_2845_ = lean_ctor_get(v___x_2844_, 0);
lean_inc(v_a_2845_);
lean_dec_ref_known(v___x_2844_, 1);
v_dummy_2846_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2847_ = l_Lean_Expr_getAppNumArgs(v_a_2831_);
lean_inc(v_nargs_2847_);
v___x_2848_ = lean_mk_array(v_nargs_2847_, v_dummy_2846_);
v___x_2849_ = lean_unsigned_to_nat(1u);
v___x_2850_ = lean_nat_sub(v_nargs_2847_, v___x_2849_);
lean_dec(v_nargs_2847_);
lean_inc_ref(v_a_2831_);
v___x_2851_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2831_, v___x_2848_, v___x_2850_);
v___x_2852_ = lean_array_get_size(v___x_2851_);
v___x_2853_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2854_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2854_, 0, v___x_2853_);
lean_ctor_set(v___x_2854_, 1, v___x_2852_);
v_sz_2855_ = lean_array_size(v___x_2851_);
v___x_2856_ = ((size_t)0ULL);
v___x_2857_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2845_, v_fst_2832_, v_argVars_2837_, v___x_2851_, v_sz_2855_, v___x_2856_, v___x_2854_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
lean_dec_ref(v___x_2851_);
lean_dec(v_a_2845_);
if (lean_obj_tag(v___x_2857_) == 0)
{
lean_object* v___x_2858_; lean_object* v___x_2859_; lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; 
lean_dec_ref_known(v___x_2857_, 1);
v___x_2858_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2859_ = lean_array_get_size(v_fst_2832_);
v___x_2860_ = l_List_range(v___x_2859_);
v___x_2861_ = lean_box(0);
v___x_2862_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2833_, v___x_2860_, v___x_2861_);
v___x_2863_ = lean_array_mk(v___x_2862_);
v___x_2864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2864_, 0, v___x_2858_);
lean_ctor_set(v___x_2864_, 1, v___x_2863_);
lean_inc_ref(v_inst_2834_);
lean_inc_ref(v_argVars_2837_);
v___x_2865_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2832_, v_argVars_2837_, v_inst_2834_, v_a_2835_, v_projInfo_x3f_2836_, v___x_2864_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
if (lean_obj_tag(v___x_2865_) == 0)
{
lean_object* v_a_2866_; lean_object* v___x_2868_; uint8_t v_isShared_2869_; uint8_t v_isSharedCheck_2959_; 
v_a_2866_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2868_ = v___x_2865_;
v_isShared_2869_ = v_isSharedCheck_2959_;
goto v_resetjp_2867_;
}
else
{
lean_inc(v_a_2866_);
lean_dec(v___x_2865_);
v___x_2868_ = lean_box(0);
v_isShared_2869_ = v_isSharedCheck_2959_;
goto v_resetjp_2867_;
}
v_resetjp_2867_:
{
lean_object* v_fst_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2957_; 
v_fst_2870_ = lean_ctor_get(v_a_2866_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v_a_2866_);
if (v_isSharedCheck_2957_ == 0)
{
lean_object* v_unused_2958_; 
v_unused_2958_ = lean_ctor_get(v_a_2866_, 1);
lean_dec(v_unused_2958_);
v___x_2872_ = v_a_2866_;
v_isShared_2873_ = v_isSharedCheck_2957_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_fst_2870_);
lean_dec(v_a_2866_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2957_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v___y_2875_; lean_object* v___y_2876_; lean_object* v___y_2877_; lean_object* v_toCold_2878_; lean_object* v_options_2879_; lean_object* v___y_2880_; lean_object* v_toCold_2937_; lean_object* v_options_2938_; lean_object* v___x_2939_; uint8_t v___x_2940_; 
v_toCold_2937_ = lean_ctor_get(v___y_2841_, 0);
v_options_2938_ = lean_ctor_get(v___y_2841_, 1);
v___x_2939_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2940_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2938_, v___x_2939_);
if (v___x_2940_ == 0)
{
lean_dec_ref(v_a_2831_);
v___y_2875_ = v___y_2839_;
v___y_2876_ = v___y_2840_;
v___y_2877_ = v___y_2841_;
v_toCold_2878_ = v_toCold_2937_;
v_options_2879_ = v_options_2938_;
v___y_2880_ = v___y_2842_;
goto v___jp_2874_;
}
else
{
lean_object* v___x_2941_; lean_object* v_a_2942_; uint8_t v___x_2943_; 
v___x_2941_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2831_, v___y_2840_);
v_a_2942_ = lean_ctor_get(v___x_2941_, 0);
lean_inc(v_a_2942_);
lean_dec_ref(v___x_2941_);
v___x_2943_ = l_Lean_Expr_hasExprMVar(v_a_2942_);
if (v___x_2943_ == 0)
{
lean_dec(v_a_2942_);
v___y_2875_ = v___y_2839_;
v___y_2876_ = v___y_2840_;
v___y_2877_ = v___y_2841_;
v_toCold_2878_ = v_toCold_2937_;
v_options_2879_ = v_options_2938_;
v___y_2880_ = v___y_2842_;
goto v___jp_2874_;
}
else
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v_a_2949_; lean_object* v___x_2951_; uint8_t v_isShared_2952_; uint8_t v_isSharedCheck_2956_; 
lean_del_object(v___x_2872_);
lean_dec(v_fst_2870_);
lean_del_object(v___x_2868_);
lean_dec_ref(v_argVars_2837_);
lean_dec_ref(v_inst_2834_);
v___x_2944_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_2945_ = l_Lean_Expr_setPPExplicit(v_a_2942_, v___x_2943_);
v___x_2946_ = l_Lean_indentExpr(v___x_2945_);
v___x_2947_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2947_, 0, v___x_2944_);
lean_ctor_set(v___x_2947_, 1, v___x_2946_);
v___x_2948_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2947_, v___y_2839_, v___y_2840_, v___y_2841_, v___y_2842_);
v_a_2949_ = lean_ctor_get(v___x_2948_, 0);
v_isSharedCheck_2956_ = !lean_is_exclusive(v___x_2948_);
if (v_isSharedCheck_2956_ == 0)
{
v___x_2951_ = v___x_2948_;
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
else
{
lean_inc(v_a_2949_);
lean_dec(v___x_2948_);
v___x_2951_ = lean_box(0);
v_isShared_2952_ = v_isSharedCheck_2956_;
goto v_resetjp_2950_;
}
v_resetjp_2950_:
{
lean_object* v___x_2954_; 
if (v_isShared_2952_ == 0)
{
v___x_2954_ = v___x_2951_;
goto v_reusejp_2953_;
}
else
{
lean_object* v_reuseFailAlloc_2955_; 
v_reuseFailAlloc_2955_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2955_, 0, v_a_2949_);
v___x_2954_ = v_reuseFailAlloc_2955_;
goto v_reusejp_2953_;
}
v_reusejp_2953_:
{
return v___x_2954_;
}
}
}
}
v___jp_2874_:
{
uint8_t v_hasTrace_2881_; 
v_hasTrace_2881_ = lean_ctor_get_uint8(v_options_2879_, sizeof(void*)*1);
if (v_hasTrace_2881_ == 0)
{
lean_object* v___x_2883_; 
lean_del_object(v___x_2872_);
lean_dec_ref(v_argVars_2837_);
lean_dec_ref(v_inst_2834_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v_fst_2870_);
v___x_2883_ = v___x_2868_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2884_; 
v_reuseFailAlloc_2884_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2884_, 0, v_fst_2870_);
v___x_2883_ = v_reuseFailAlloc_2884_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
return v___x_2883_;
}
}
else
{
lean_object* v_inheritedTraceOptions_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; uint8_t v___x_2888_; 
v_inheritedTraceOptions_2885_ = lean_ctor_get(v_toCold_2878_, 4);
v___x_2886_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2887_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2888_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2885_, v_options_2879_, v___x_2887_);
if (v___x_2888_ == 0)
{
lean_object* v___x_2890_; 
lean_del_object(v___x_2872_);
lean_dec_ref(v_argVars_2837_);
lean_dec_ref(v_inst_2834_);
if (v_isShared_2869_ == 0)
{
lean_ctor_set(v___x_2868_, 0, v_fst_2870_);
v___x_2890_ = v___x_2868_;
goto v_reusejp_2889_;
}
else
{
lean_object* v_reuseFailAlloc_2891_; 
v_reuseFailAlloc_2891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2891_, 0, v_fst_2870_);
v___x_2890_ = v_reuseFailAlloc_2891_;
goto v_reusejp_2889_;
}
v_reusejp_2889_:
{
return v___x_2890_;
}
}
else
{
size_t v_sz_2892_; lean_object* v___x_2893_; 
lean_del_object(v___x_2868_);
v_sz_2892_ = lean_array_size(v_fst_2870_);
lean_inc(v_fst_2870_);
v___x_2893_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2837_, v_sz_2892_, v___x_2856_, v_fst_2870_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2880_);
lean_dec_ref(v_argVars_2837_);
if (lean_obj_tag(v___x_2893_) == 0)
{
lean_object* v_a_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2898_; 
v_a_2894_ = lean_ctor_get(v___x_2893_, 0);
lean_inc(v_a_2894_);
lean_dec_ref_known(v___x_2893_, 1);
v___x_2895_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_2896_ = l_Lean_MessageData_ofExpr(v_inst_2834_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set_tag(v___x_2872_, 7);
lean_ctor_set(v___x_2872_, 1, v___x_2896_);
lean_ctor_set(v___x_2872_, 0, v___x_2895_);
v___x_2898_ = v___x_2872_;
goto v_reusejp_2897_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v___x_2895_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v___x_2896_);
v___x_2898_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2897_;
}
v_reusejp_2897_:
{
lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; 
v___x_2899_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_2900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2900_, 0, v___x_2898_);
lean_ctor_set(v___x_2900_, 1, v___x_2899_);
lean_inc(v_fst_2870_);
v___x_2901_ = lean_array_to_list(v_fst_2870_);
v___x_2902_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_2901_, v___x_2861_);
v___x_2903_ = l_Lean_MessageData_ofList(v___x_2902_);
v___x_2904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2904_, 0, v___x_2900_);
lean_ctor_set(v___x_2904_, 1, v___x_2903_);
v___x_2905_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_2906_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2906_, 0, v___x_2904_);
lean_ctor_set(v___x_2906_, 1, v___x_2905_);
v___x_2907_ = lean_array_to_list(v_a_2894_);
v___x_2908_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2909_ = l_Lean_MessageData_joinSep(v___x_2907_, v___x_2908_);
v___x_2910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2910_, 0, v___x_2906_);
lean_ctor_set(v___x_2910_, 1, v___x_2909_);
v___x_2911_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2886_, v___x_2910_, v___y_2875_, v___y_2876_, v___y_2877_, v___y_2880_);
if (lean_obj_tag(v___x_2911_) == 0)
{
lean_object* v___x_2913_; uint8_t v_isShared_2914_; uint8_t v_isSharedCheck_2918_; 
v_isSharedCheck_2918_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2918_ == 0)
{
lean_object* v_unused_2919_; 
v_unused_2919_ = lean_ctor_get(v___x_2911_, 0);
lean_dec(v_unused_2919_);
v___x_2913_ = v___x_2911_;
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
else
{
lean_dec(v___x_2911_);
v___x_2913_ = lean_box(0);
v_isShared_2914_ = v_isSharedCheck_2918_;
goto v_resetjp_2912_;
}
v_resetjp_2912_:
{
lean_object* v___x_2916_; 
if (v_isShared_2914_ == 0)
{
lean_ctor_set(v___x_2913_, 0, v_fst_2870_);
v___x_2916_ = v___x_2913_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_fst_2870_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
}
else
{
lean_object* v_a_2920_; lean_object* v___x_2922_; uint8_t v_isShared_2923_; uint8_t v_isSharedCheck_2927_; 
lean_dec(v_fst_2870_);
v_a_2920_ = lean_ctor_get(v___x_2911_, 0);
v_isSharedCheck_2927_ = !lean_is_exclusive(v___x_2911_);
if (v_isSharedCheck_2927_ == 0)
{
v___x_2922_ = v___x_2911_;
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
else
{
lean_inc(v_a_2920_);
lean_dec(v___x_2911_);
v___x_2922_ = lean_box(0);
v_isShared_2923_ = v_isSharedCheck_2927_;
goto v_resetjp_2921_;
}
v_resetjp_2921_:
{
lean_object* v___x_2925_; 
if (v_isShared_2923_ == 0)
{
v___x_2925_ = v___x_2922_;
goto v_reusejp_2924_;
}
else
{
lean_object* v_reuseFailAlloc_2926_; 
v_reuseFailAlloc_2926_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2926_, 0, v_a_2920_);
v___x_2925_ = v_reuseFailAlloc_2926_;
goto v_reusejp_2924_;
}
v_reusejp_2924_:
{
return v___x_2925_;
}
}
}
}
}
else
{
lean_object* v_a_2929_; lean_object* v___x_2931_; uint8_t v_isShared_2932_; uint8_t v_isSharedCheck_2936_; 
lean_del_object(v___x_2872_);
lean_dec(v_fst_2870_);
lean_dec_ref(v_inst_2834_);
v_a_2929_ = lean_ctor_get(v___x_2893_, 0);
v_isSharedCheck_2936_ = !lean_is_exclusive(v___x_2893_);
if (v_isSharedCheck_2936_ == 0)
{
v___x_2931_ = v___x_2893_;
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
else
{
lean_inc(v_a_2929_);
lean_dec(v___x_2893_);
v___x_2931_ = lean_box(0);
v_isShared_2932_ = v_isSharedCheck_2936_;
goto v_resetjp_2930_;
}
v_resetjp_2930_:
{
lean_object* v___x_2934_; 
if (v_isShared_2932_ == 0)
{
v___x_2934_ = v___x_2931_;
goto v_reusejp_2933_;
}
else
{
lean_object* v_reuseFailAlloc_2935_; 
v_reuseFailAlloc_2935_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2935_, 0, v_a_2929_);
v___x_2934_ = v_reuseFailAlloc_2935_;
goto v_reusejp_2933_;
}
v_reusejp_2933_:
{
return v___x_2934_;
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
lean_object* v_a_2960_; lean_object* v___x_2962_; uint8_t v_isShared_2963_; uint8_t v_isSharedCheck_2967_; 
lean_dec_ref(v_argVars_2837_);
lean_dec_ref(v_inst_2834_);
lean_dec_ref(v_a_2831_);
v_a_2960_ = lean_ctor_get(v___x_2865_, 0);
v_isSharedCheck_2967_ = !lean_is_exclusive(v___x_2865_);
if (v_isSharedCheck_2967_ == 0)
{
v___x_2962_ = v___x_2865_;
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
else
{
lean_inc(v_a_2960_);
lean_dec(v___x_2865_);
v___x_2962_ = lean_box(0);
v_isShared_2963_ = v_isSharedCheck_2967_;
goto v_resetjp_2961_;
}
v_resetjp_2961_:
{
lean_object* v___x_2965_; 
if (v_isShared_2963_ == 0)
{
v___x_2965_ = v___x_2962_;
goto v_reusejp_2964_;
}
else
{
lean_object* v_reuseFailAlloc_2966_; 
v_reuseFailAlloc_2966_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2966_, 0, v_a_2960_);
v___x_2965_ = v_reuseFailAlloc_2966_;
goto v_reusejp_2964_;
}
v_reusejp_2964_:
{
return v___x_2965_;
}
}
}
}
else
{
lean_object* v_a_2968_; lean_object* v___x_2970_; uint8_t v_isShared_2971_; uint8_t v_isSharedCheck_2975_; 
lean_dec_ref(v_argVars_2837_);
lean_dec_ref(v_a_2835_);
lean_dec_ref(v_inst_2834_);
lean_dec_ref(v_fst_2832_);
lean_dec_ref(v_a_2831_);
v_a_2968_ = lean_ctor_get(v___x_2857_, 0);
v_isSharedCheck_2975_ = !lean_is_exclusive(v___x_2857_);
if (v_isSharedCheck_2975_ == 0)
{
v___x_2970_ = v___x_2857_;
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
else
{
lean_inc(v_a_2968_);
lean_dec(v___x_2857_);
v___x_2970_ = lean_box(0);
v_isShared_2971_ = v_isSharedCheck_2975_;
goto v_resetjp_2969_;
}
v_resetjp_2969_:
{
lean_object* v___x_2973_; 
if (v_isShared_2971_ == 0)
{
v___x_2973_ = v___x_2970_;
goto v_reusejp_2972_;
}
else
{
lean_object* v_reuseFailAlloc_2974_; 
v_reuseFailAlloc_2974_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2974_, 0, v_a_2968_);
v___x_2973_ = v_reuseFailAlloc_2974_;
goto v_reusejp_2972_;
}
v_reusejp_2972_:
{
return v___x_2973_;
}
}
}
}
else
{
lean_dec_ref(v_argVars_2837_);
lean_dec_ref(v_a_2835_);
lean_dec_ref(v_inst_2834_);
lean_dec_ref(v_fst_2832_);
lean_dec_ref(v_a_2831_);
return v___x_2844_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_2976_, lean_object* v_fst_2977_, lean_object* v_fst_2978_, lean_object* v_inst_2979_, lean_object* v_a_2980_, lean_object* v_projInfo_x3f_2981_, lean_object* v_argVars_2982_, lean_object* v_x_2983_, lean_object* v___y_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_){
_start:
{
lean_object* v_res_2989_; 
v_res_2989_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_2976_, v_fst_2977_, v_fst_2978_, v_inst_2979_, v_a_2980_, v_projInfo_x3f_2981_, v_argVars_2982_, v_x_2983_, v___y_2984_, v___y_2985_, v___y_2986_, v___y_2987_);
lean_dec(v___y_2987_);
lean_dec_ref(v___y_2986_);
lean_dec(v___y_2985_);
lean_dec_ref(v___y_2984_);
lean_dec_ref(v_x_2983_);
lean_dec(v_projInfo_x3f_2981_);
lean_dec_ref(v_fst_2978_);
return v_res_2989_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(lean_object* v_inst_2990_, lean_object* v_projInfo_x3f_2991_, lean_object* v___y_2992_, lean_object* v___y_2993_, lean_object* v___y_2994_, lean_object* v___y_2995_){
_start:
{
lean_object* v___x_2997_; 
lean_inc(v___y_2995_);
lean_inc_ref(v___y_2994_);
lean_inc(v___y_2993_);
lean_inc_ref(v___y_2992_);
lean_inc_ref(v_inst_2990_);
v___x_2997_ = lean_infer_type(v_inst_2990_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_2997_) == 0)
{
lean_object* v_a_2998_; lean_object* v___x_2999_; uint8_t v___x_3000_; lean_object* v___x_3001_; 
v_a_2998_ = lean_ctor_get(v___x_2997_, 0);
lean_inc_n(v_a_2998_, 2);
lean_dec_ref_known(v___x_2997_, 1);
v___x_2999_ = lean_box(0);
v___x_3000_ = 0;
v___x_3001_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_2998_, v___x_2999_, v___x_3000_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_3001_) == 0)
{
lean_object* v_a_3002_; lean_object* v_snd_3003_; lean_object* v_fst_3004_; lean_object* v_fst_3005_; lean_object* v_snd_3006_; lean_object* v___x_3007_; 
v_a_3002_ = lean_ctor_get(v___x_3001_, 0);
lean_inc(v_a_3002_);
lean_dec_ref_known(v___x_3001_, 1);
v_snd_3003_ = lean_ctor_get(v_a_3002_, 1);
lean_inc(v_snd_3003_);
v_fst_3004_ = lean_ctor_get(v_a_3002_, 0);
lean_inc(v_fst_3004_);
lean_dec(v_a_3002_);
v_fst_3005_ = lean_ctor_get(v_snd_3003_, 0);
lean_inc(v_fst_3005_);
v_snd_3006_ = lean_ctor_get(v_snd_3003_, 1);
lean_inc(v_snd_3006_);
lean_dec(v_snd_3003_);
lean_inc(v___y_2995_);
lean_inc_ref(v___y_2994_);
lean_inc(v___y_2993_);
lean_inc_ref(v___y_2992_);
v___x_3007_ = lean_whnf(v_snd_3006_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
if (lean_obj_tag(v___x_3007_) == 0)
{
lean_object* v_a_3008_; lean_object* v___f_3009_; uint8_t v___x_3010_; lean_object* v___x_3011_; 
v_a_3008_ = lean_ctor_get(v___x_3007_, 0);
lean_inc(v_a_3008_);
lean_dec_ref_known(v___x_3007_, 1);
lean_inc(v_a_2998_);
v___f_3009_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3009_, 0, v_a_3008_);
lean_closure_set(v___f_3009_, 1, v_fst_3004_);
lean_closure_set(v___f_3009_, 2, v_fst_3005_);
lean_closure_set(v___f_3009_, 3, v_inst_2990_);
lean_closure_set(v___f_3009_, 4, v_a_2998_);
lean_closure_set(v___f_3009_, 5, v_projInfo_x3f_2991_);
v___x_3010_ = 0;
v___x_3011_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2998_, v___f_3009_, v___x_3010_, v___x_3010_, v___y_2992_, v___y_2993_, v___y_2994_, v___y_2995_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
return v___x_3011_;
}
else
{
lean_object* v_a_3012_; lean_object* v___x_3014_; uint8_t v_isShared_3015_; uint8_t v_isSharedCheck_3019_; 
lean_dec(v_fst_3005_);
lean_dec(v_fst_3004_);
lean_dec(v_a_2998_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v_projInfo_x3f_2991_);
lean_dec_ref(v_inst_2990_);
v_a_3012_ = lean_ctor_get(v___x_3007_, 0);
v_isSharedCheck_3019_ = !lean_is_exclusive(v___x_3007_);
if (v_isSharedCheck_3019_ == 0)
{
v___x_3014_ = v___x_3007_;
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
else
{
lean_inc(v_a_3012_);
lean_dec(v___x_3007_);
v___x_3014_ = lean_box(0);
v_isShared_3015_ = v_isSharedCheck_3019_;
goto v_resetjp_3013_;
}
v_resetjp_3013_:
{
lean_object* v___x_3017_; 
if (v_isShared_3015_ == 0)
{
v___x_3017_ = v___x_3014_;
goto v_reusejp_3016_;
}
else
{
lean_object* v_reuseFailAlloc_3018_; 
v_reuseFailAlloc_3018_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3018_, 0, v_a_3012_);
v___x_3017_ = v_reuseFailAlloc_3018_;
goto v_reusejp_3016_;
}
v_reusejp_3016_:
{
return v___x_3017_;
}
}
}
}
else
{
lean_object* v_a_3020_; lean_object* v___x_3022_; uint8_t v_isShared_3023_; uint8_t v_isSharedCheck_3027_; 
lean_dec(v_a_2998_);
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v_projInfo_x3f_2991_);
lean_dec_ref(v_inst_2990_);
v_a_3020_ = lean_ctor_get(v___x_3001_, 0);
v_isSharedCheck_3027_ = !lean_is_exclusive(v___x_3001_);
if (v_isSharedCheck_3027_ == 0)
{
v___x_3022_ = v___x_3001_;
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
else
{
lean_inc(v_a_3020_);
lean_dec(v___x_3001_);
v___x_3022_ = lean_box(0);
v_isShared_3023_ = v_isSharedCheck_3027_;
goto v_resetjp_3021_;
}
v_resetjp_3021_:
{
lean_object* v___x_3025_; 
if (v_isShared_3023_ == 0)
{
v___x_3025_ = v___x_3022_;
goto v_reusejp_3024_;
}
else
{
lean_object* v_reuseFailAlloc_3026_; 
v_reuseFailAlloc_3026_ = lean_alloc_ctor(1, 1, 0);
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
}
else
{
lean_object* v_a_3028_; lean_object* v___x_3030_; uint8_t v_isShared_3031_; uint8_t v_isSharedCheck_3035_; 
lean_dec(v___y_2995_);
lean_dec_ref(v___y_2994_);
lean_dec(v___y_2993_);
lean_dec_ref(v___y_2992_);
lean_dec(v_projInfo_x3f_2991_);
lean_dec_ref(v_inst_2990_);
v_a_3028_ = lean_ctor_get(v___x_2997_, 0);
v_isSharedCheck_3035_ = !lean_is_exclusive(v___x_2997_);
if (v_isSharedCheck_3035_ == 0)
{
v___x_3030_ = v___x_2997_;
v_isShared_3031_ = v_isSharedCheck_3035_;
goto v_resetjp_3029_;
}
else
{
lean_inc(v_a_3028_);
lean_dec(v___x_2997_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1___boxed(lean_object* v_inst_3036_, lean_object* v_projInfo_x3f_3037_, lean_object* v___y_3038_, lean_object* v___y_3039_, lean_object* v___y_3040_, lean_object* v___y_3041_, lean_object* v___y_3042_){
_start:
{
lean_object* v_res_3043_; 
v_res_3043_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3036_, v_projInfo_x3f_3037_, v___y_3038_, v___y_3039_, v___y_3040_, v___y_3041_);
return v_res_3043_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_3044_, lean_object* v_projInfo_x3f_3045_, lean_object* v_a_3046_, lean_object* v_a_3047_, lean_object* v_a_3048_, lean_object* v_a_3049_){
_start:
{
lean_object* v___y_3052_; lean_object* v___x_3069_; uint8_t v_transparency_3070_; uint8_t v___x_3071_; uint8_t v___x_3072_; 
v___x_3069_ = l_Lean_Meta_Context_config(v_a_3046_);
v_transparency_3070_ = lean_ctor_get_uint8(v___x_3069_, 9);
lean_dec_ref(v___x_3069_);
v___x_3071_ = 2;
v___x_3072_ = l_Lean_Meta_instBEqTransparencyMode_beq(v_transparency_3070_, v___x_3071_);
if (v___x_3072_ == 0)
{
lean_object* v_keyedConfig_3073_; uint8_t v_trackZetaDelta_3074_; lean_object* v_zetaDeltaSet_3075_; lean_object* v_lctx_3076_; lean_object* v_localInstances_3077_; lean_object* v_defEqCtx_x3f_3078_; lean_object* v_synthPendingDepth_3079_; lean_object* v_customCanUnfoldPredicate_x3f_3080_; uint8_t v_univApprox_3081_; uint8_t v_inTypeClassResolution_3082_; uint8_t v_cacheInferType_3083_; lean_object* v___x_3084_; lean_object* v___x_3085_; lean_object* v___x_3086_; 
v_keyedConfig_3073_ = lean_ctor_get(v_a_3046_, 0);
v_trackZetaDelta_3074_ = lean_ctor_get_uint8(v_a_3046_, sizeof(void*)*7);
v_zetaDeltaSet_3075_ = lean_ctor_get(v_a_3046_, 1);
v_lctx_3076_ = lean_ctor_get(v_a_3046_, 2);
v_localInstances_3077_ = lean_ctor_get(v_a_3046_, 3);
v_defEqCtx_x3f_3078_ = lean_ctor_get(v_a_3046_, 4);
v_synthPendingDepth_3079_ = lean_ctor_get(v_a_3046_, 5);
v_customCanUnfoldPredicate_x3f_3080_ = lean_ctor_get(v_a_3046_, 6);
v_univApprox_3081_ = lean_ctor_get_uint8(v_a_3046_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3082_ = lean_ctor_get_uint8(v_a_3046_, sizeof(void*)*7 + 2);
v_cacheInferType_3083_ = lean_ctor_get_uint8(v_a_3046_, sizeof(void*)*7 + 3);
lean_inc_ref(v_keyedConfig_3073_);
v___x_3084_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3071_, v_keyedConfig_3073_);
lean_inc(v_customCanUnfoldPredicate_x3f_3080_);
lean_inc(v_synthPendingDepth_3079_);
lean_inc(v_defEqCtx_x3f_3078_);
lean_inc_ref(v_localInstances_3077_);
lean_inc_ref(v_lctx_3076_);
lean_inc(v_zetaDeltaSet_3075_);
v___x_3085_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3085_, 0, v___x_3084_);
lean_ctor_set(v___x_3085_, 1, v_zetaDeltaSet_3075_);
lean_ctor_set(v___x_3085_, 2, v_lctx_3076_);
lean_ctor_set(v___x_3085_, 3, v_localInstances_3077_);
lean_ctor_set(v___x_3085_, 4, v_defEqCtx_x3f_3078_);
lean_ctor_set(v___x_3085_, 5, v_synthPendingDepth_3079_);
lean_ctor_set(v___x_3085_, 6, v_customCanUnfoldPredicate_x3f_3080_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*7, v_trackZetaDelta_3074_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*7 + 1, v_univApprox_3081_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3082_);
lean_ctor_set_uint8(v___x_3085_, sizeof(void*)*7 + 3, v_cacheInferType_3083_);
lean_inc(v_a_3049_);
lean_inc_ref(v_a_3048_);
lean_inc(v_a_3047_);
v___x_3086_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3044_, v_projInfo_x3f_3045_, v___x_3085_, v_a_3047_, v_a_3048_, v_a_3049_);
v___y_3052_ = v___x_3086_;
goto v___jp_3051_;
}
else
{
lean_object* v___x_3087_; 
lean_inc(v_a_3049_);
lean_inc_ref(v_a_3048_);
lean_inc(v_a_3047_);
lean_inc_ref(v_a_3046_);
v___x_3087_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__1(v_inst_3044_, v_projInfo_x3f_3045_, v_a_3046_, v_a_3047_, v_a_3048_, v_a_3049_);
v___y_3052_ = v___x_3087_;
goto v___jp_3051_;
}
v___jp_3051_:
{
if (lean_obj_tag(v___y_3052_) == 0)
{
lean_object* v_a_3053_; lean_object* v___x_3055_; uint8_t v_isShared_3056_; uint8_t v_isSharedCheck_3060_; 
v_a_3053_ = lean_ctor_get(v___y_3052_, 0);
v_isSharedCheck_3060_ = !lean_is_exclusive(v___y_3052_);
if (v_isSharedCheck_3060_ == 0)
{
v___x_3055_ = v___y_3052_;
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
else
{
lean_inc(v_a_3053_);
lean_dec(v___y_3052_);
v___x_3055_ = lean_box(0);
v_isShared_3056_ = v_isSharedCheck_3060_;
goto v_resetjp_3054_;
}
v_resetjp_3054_:
{
lean_object* v___x_3058_; 
if (v_isShared_3056_ == 0)
{
v___x_3058_ = v___x_3055_;
goto v_reusejp_3057_;
}
else
{
lean_object* v_reuseFailAlloc_3059_; 
v_reuseFailAlloc_3059_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3059_, 0, v_a_3053_);
v___x_3058_ = v_reuseFailAlloc_3059_;
goto v_reusejp_3057_;
}
v_reusejp_3057_:
{
return v___x_3058_;
}
}
}
else
{
lean_object* v_a_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3068_; 
v_a_3061_ = lean_ctor_get(v___y_3052_, 0);
v_isSharedCheck_3068_ = !lean_is_exclusive(v___y_3052_);
if (v_isSharedCheck_3068_ == 0)
{
v___x_3063_ = v___y_3052_;
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_a_3061_);
lean_dec(v___y_3052_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3068_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3066_; 
if (v_isShared_3064_ == 0)
{
v___x_3066_ = v___x_3063_;
goto v_reusejp_3065_;
}
else
{
lean_object* v_reuseFailAlloc_3067_; 
v_reuseFailAlloc_3067_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3067_, 0, v_a_3061_);
v___x_3066_ = v_reuseFailAlloc_3067_;
goto v_reusejp_3065_;
}
v_reusejp_3065_:
{
return v___x_3066_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_3088_, lean_object* v_projInfo_x3f_3089_, lean_object* v_a_3090_, lean_object* v_a_3091_, lean_object* v_a_3092_, lean_object* v_a_3093_, lean_object* v_a_3094_){
_start:
{
lean_object* v_res_3095_; 
v_res_3095_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_3088_, v_projInfo_x3f_3089_, v_a_3090_, v_a_3091_, v_a_3092_, v_a_3093_);
lean_dec(v_a_3093_);
lean_dec_ref(v_a_3092_);
lean_dec(v_a_3091_);
lean_dec_ref(v_a_3090_);
return v_res_3095_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_3096_, lean_object* v_a_3097_, lean_object* v___x_3098_, lean_object* v_inst_3099_, lean_object* v_R_3100_, lean_object* v_a_3101_, lean_object* v_b_3102_, lean_object* v_c_3103_, lean_object* v___y_3104_, lean_object* v___y_3105_, lean_object* v___y_3106_, lean_object* v___y_3107_){
_start:
{
lean_object* v___x_3109_; 
v___x_3109_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_3096_, v_a_3097_, v___x_3098_, v_a_3101_, v_b_3102_);
return v___x_3109_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_3110_, lean_object* v_a_3111_, lean_object* v___x_3112_, lean_object* v_inst_3113_, lean_object* v_R_3114_, lean_object* v_a_3115_, lean_object* v_b_3116_, lean_object* v_c_3117_, lean_object* v___y_3118_, lean_object* v___y_3119_, lean_object* v___y_3120_, lean_object* v___y_3121_, lean_object* v___y_3122_){
_start:
{
lean_object* v_res_3123_; 
v_res_3123_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_3110_, v_a_3111_, v___x_3112_, v_inst_3113_, v_R_3114_, v_a_3115_, v_b_3116_, v_c_3117_, v___y_3118_, v___y_3119_, v___y_3120_, v___y_3121_);
lean_dec(v___y_3121_);
lean_dec_ref(v___y_3120_);
lean_dec(v___y_3119_);
lean_dec_ref(v___y_3118_);
lean_dec(v___x_3112_);
lean_dec_ref(v_a_3111_);
lean_dec(v_upperBound_3110_);
return v_res_3123_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3124_, lean_object* v_msg_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v___x_3131_; 
v___x_3131_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3125_, v___y_3126_, v___y_3127_, v___y_3128_, v___y_3129_);
return v___x_3131_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3132_, lean_object* v_msg_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_, lean_object* v___y_3138_){
_start:
{
lean_object* v_res_3139_; 
v_res_3139_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3132_, v_msg_3133_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
lean_dec(v___y_3137_);
lean_dec_ref(v___y_3136_);
lean_dec(v___y_3135_);
lean_dec_ref(v___y_3134_);
return v_res_3139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_3140_, lean_object* v_argVars_3141_, lean_object* v_inst_3142_, lean_object* v_a_3143_, lean_object* v_projInfo_x3f_3144_, lean_object* v_inst_3145_, lean_object* v_a_3146_, lean_object* v___y_3147_, lean_object* v___y_3148_, lean_object* v___y_3149_, lean_object* v___y_3150_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_3140_, v_argVars_3141_, v_inst_3142_, v_a_3143_, v_projInfo_x3f_3144_, v_a_3146_, v___y_3147_, v___y_3148_, v___y_3149_, v___y_3150_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_3153_, lean_object* v_argVars_3154_, lean_object* v_inst_3155_, lean_object* v_a_3156_, lean_object* v_projInfo_x3f_3157_, lean_object* v_inst_3158_, lean_object* v_a_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
lean_object* v_res_3165_; 
v_res_3165_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_3153_, v_argVars_3154_, v_inst_3155_, v_a_3156_, v_projInfo_x3f_3157_, v_inst_3158_, v_a_3159_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
lean_dec(v_projInfo_x3f_3157_);
return v_res_3165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(lean_object* v_type_3166_, lean_object* v_k_3167_, uint8_t v_cleanupAnnotations_3168_, lean_object* v___y_3169_, lean_object* v___y_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_){
_start:
{
lean_object* v___f_3174_; uint8_t v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; 
v___f_3174_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3174_, 0, v_k_3167_);
v___x_3175_ = 0;
v___x_3176_ = lean_box(0);
v___x_3177_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3175_, v___x_3176_, v_type_3166_, v___f_3174_, v_cleanupAnnotations_3168_, v___x_3175_, v___y_3169_, v___y_3170_, v___y_3171_, v___y_3172_);
if (lean_obj_tag(v___x_3177_) == 0)
{
lean_object* v_a_3178_; lean_object* v___x_3180_; uint8_t v_isShared_3181_; uint8_t v_isSharedCheck_3185_; 
v_a_3178_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3185_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3185_ == 0)
{
v___x_3180_ = v___x_3177_;
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
else
{
lean_inc(v_a_3178_);
lean_dec(v___x_3177_);
v___x_3180_ = lean_box(0);
v_isShared_3181_ = v_isSharedCheck_3185_;
goto v_resetjp_3179_;
}
v_resetjp_3179_:
{
lean_object* v___x_3183_; 
if (v_isShared_3181_ == 0)
{
v___x_3183_ = v___x_3180_;
goto v_reusejp_3182_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_a_3178_);
v___x_3183_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3182_;
}
v_reusejp_3182_:
{
return v___x_3183_;
}
}
}
else
{
lean_object* v_a_3186_; lean_object* v___x_3188_; uint8_t v_isShared_3189_; uint8_t v_isSharedCheck_3193_; 
v_a_3186_ = lean_ctor_get(v___x_3177_, 0);
v_isSharedCheck_3193_ = !lean_is_exclusive(v___x_3177_);
if (v_isSharedCheck_3193_ == 0)
{
v___x_3188_ = v___x_3177_;
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
else
{
lean_inc(v_a_3186_);
lean_dec(v___x_3177_);
v___x_3188_ = lean_box(0);
v_isShared_3189_ = v_isSharedCheck_3193_;
goto v_resetjp_3187_;
}
v_resetjp_3187_:
{
lean_object* v___x_3191_; 
if (v_isShared_3189_ == 0)
{
v___x_3191_ = v___x_3188_;
goto v_reusejp_3190_;
}
else
{
lean_object* v_reuseFailAlloc_3192_; 
v_reuseFailAlloc_3192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3192_, 0, v_a_3186_);
v___x_3191_ = v_reuseFailAlloc_3192_;
goto v_reusejp_3190_;
}
v_reusejp_3190_:
{
return v___x_3191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg___boxed(lean_object* v_type_3194_, lean_object* v_k_3195_, lean_object* v_cleanupAnnotations_3196_, lean_object* v___y_3197_, lean_object* v___y_3198_, lean_object* v___y_3199_, lean_object* v___y_3200_, lean_object* v___y_3201_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3202_; lean_object* v_res_3203_; 
v_cleanupAnnotations_boxed_3202_ = lean_unbox(v_cleanupAnnotations_3196_);
v_res_3203_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3194_, v_k_3195_, v_cleanupAnnotations_boxed_3202_, v___y_3197_, v___y_3198_, v___y_3199_, v___y_3200_);
lean_dec(v___y_3200_);
lean_dec_ref(v___y_3199_);
lean_dec(v___y_3198_);
lean_dec_ref(v___y_3197_);
return v_res_3203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(lean_object* v_00_u03b1_3204_, lean_object* v_type_3205_, lean_object* v_k_3206_, uint8_t v_cleanupAnnotations_3207_, lean_object* v___y_3208_, lean_object* v___y_3209_, lean_object* v___y_3210_, lean_object* v___y_3211_){
_start:
{
lean_object* v___x_3213_; 
v___x_3213_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3205_, v_k_3206_, v_cleanupAnnotations_3207_, v___y_3208_, v___y_3209_, v___y_3210_, v___y_3211_);
return v___x_3213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___boxed(lean_object* v_00_u03b1_3214_, lean_object* v_type_3215_, lean_object* v_k_3216_, lean_object* v_cleanupAnnotations_3217_, lean_object* v___y_3218_, lean_object* v___y_3219_, lean_object* v___y_3220_, lean_object* v___y_3221_, lean_object* v___y_3222_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3223_; lean_object* v_res_3224_; 
v_cleanupAnnotations_boxed_3223_ = lean_unbox(v_cleanupAnnotations_3217_);
v_res_3224_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(v_00_u03b1_3214_, v_type_3215_, v_k_3216_, v_cleanupAnnotations_boxed_3223_, v___y_3218_, v___y_3219_, v___y_3220_, v___y_3221_);
lean_dec(v___y_3221_);
lean_dec_ref(v___y_3220_);
lean_dec(v___y_3219_);
lean_dec_ref(v___y_3218_);
return v_res_3224_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0(uint8_t v_suppressElabErrors_3232_, uint8_t v___y_3233_, lean_object* v_x_3234_){
_start:
{
if (lean_obj_tag(v_x_3234_) == 1)
{
lean_object* v_pre_3235_; 
v_pre_3235_ = lean_ctor_get(v_x_3234_, 0);
switch(lean_obj_tag(v_pre_3235_))
{
case 1:
{
lean_object* v_pre_3236_; 
v_pre_3236_ = lean_ctor_get(v_pre_3235_, 0);
switch(lean_obj_tag(v_pre_3236_))
{
case 0:
{
lean_object* v_str_3237_; lean_object* v_str_3238_; lean_object* v___x_3239_; uint8_t v___x_3240_; 
v_str_3237_ = lean_ctor_get(v_x_3234_, 1);
v_str_3238_ = lean_ctor_get(v_pre_3235_, 1);
v___x_3239_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__0));
v___x_3240_ = lean_string_dec_eq(v_str_3238_, v___x_3239_);
if (v___x_3240_ == 0)
{
lean_object* v___x_3241_; uint8_t v___x_3242_; 
v___x_3241_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__1));
v___x_3242_ = lean_string_dec_eq(v_str_3238_, v___x_3241_);
if (v___x_3242_ == 0)
{
return v___x_3242_;
}
else
{
lean_object* v___x_3243_; uint8_t v___x_3244_; 
v___x_3243_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__2));
v___x_3244_ = lean_string_dec_eq(v_str_3237_, v___x_3243_);
if (v___x_3244_ == 0)
{
return v___x_3244_;
}
else
{
return v_suppressElabErrors_3232_;
}
}
}
else
{
lean_object* v___x_3245_; uint8_t v___x_3246_; 
v___x_3245_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__3));
v___x_3246_ = lean_string_dec_eq(v_str_3237_, v___x_3245_);
if (v___x_3246_ == 0)
{
return v___x_3246_;
}
else
{
return v_suppressElabErrors_3232_;
}
}
}
case 1:
{
lean_object* v_pre_3247_; 
v_pre_3247_ = lean_ctor_get(v_pre_3236_, 0);
if (lean_obj_tag(v_pre_3247_) == 0)
{
lean_object* v_str_3248_; lean_object* v_str_3249_; lean_object* v_str_3250_; lean_object* v___x_3251_; uint8_t v___x_3252_; 
v_str_3248_ = lean_ctor_get(v_x_3234_, 1);
v_str_3249_ = lean_ctor_get(v_pre_3235_, 1);
v_str_3250_ = lean_ctor_get(v_pre_3236_, 1);
v___x_3251_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__4));
v___x_3252_ = lean_string_dec_eq(v_str_3250_, v___x_3251_);
if (v___x_3252_ == 0)
{
return v___x_3252_;
}
else
{
lean_object* v___x_3253_; uint8_t v___x_3254_; 
v___x_3253_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__5));
v___x_3254_ = lean_string_dec_eq(v_str_3249_, v___x_3253_);
if (v___x_3254_ == 0)
{
return v___x_3254_;
}
else
{
lean_object* v___x_3255_; uint8_t v___x_3256_; 
v___x_3255_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___closed__6));
v___x_3256_ = lean_string_dec_eq(v_str_3248_, v___x_3255_);
if (v___x_3256_ == 0)
{
return v___x_3256_;
}
else
{
return v_suppressElabErrors_3232_;
}
}
}
}
else
{
return v___y_3233_;
}
}
default: 
{
return v___y_3233_;
}
}
}
case 0:
{
lean_object* v_str_3257_; lean_object* v___x_3258_; uint8_t v___x_3259_; 
v_str_3257_ = lean_ctor_get(v_x_3234_, 1);
v___x_3258_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3259_ = lean_string_dec_eq(v_str_3257_, v___x_3258_);
if (v___x_3259_ == 0)
{
return v___x_3259_;
}
else
{
return v_suppressElabErrors_3232_;
}
}
default: 
{
return v___y_3233_;
}
}
}
else
{
return v___y_3233_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___boxed(lean_object* v_suppressElabErrors_3260_, lean_object* v___y_3261_, lean_object* v_x_3262_){
_start:
{
uint8_t v_suppressElabErrors_boxed_3263_; uint8_t v___y_10276__boxed_3264_; uint8_t v_res_3265_; lean_object* v_r_3266_; 
v_suppressElabErrors_boxed_3263_ = lean_unbox(v_suppressElabErrors_3260_);
v___y_10276__boxed_3264_ = lean_unbox(v___y_3261_);
v_res_3265_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0(v_suppressElabErrors_boxed_3263_, v___y_10276__boxed_3264_, v_x_3262_);
lean_dec(v_x_3262_);
v_r_3266_ = lean_box(v_res_3265_);
return v_r_3266_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4(lean_object* v_ref_3267_, lean_object* v_msgData_3268_, uint8_t v_severity_3269_, uint8_t v_isSilent_3270_, lean_object* v___y_3271_, lean_object* v___y_3272_, lean_object* v___y_3273_, lean_object* v___y_3274_){
_start:
{
uint8_t v___y_3277_; lean_object* v___y_3278_; lean_object* v___y_3279_; lean_object* v___y_3280_; uint8_t v___y_3281_; lean_object* v___y_3282_; lean_object* v___y_3283_; lean_object* v___y_3284_; lean_object* v___y_3285_; lean_object* v___y_3313_; uint8_t v___y_3314_; lean_object* v___y_3315_; uint8_t v___y_3316_; lean_object* v___y_3317_; uint8_t v___y_3318_; lean_object* v___y_3319_; lean_object* v___y_3339_; uint8_t v___y_3340_; uint8_t v___y_3341_; lean_object* v___y_3342_; lean_object* v___y_3343_; uint8_t v___y_3344_; lean_object* v___y_3345_; lean_object* v___y_3349_; uint8_t v___y_3350_; lean_object* v___y_3351_; lean_object* v___y_3352_; uint8_t v___y_3353_; uint8_t v___y_3354_; uint8_t v___x_3359_; lean_object* v___y_3361_; uint8_t v___y_3362_; lean_object* v___y_3363_; lean_object* v___y_3364_; uint8_t v___y_3365_; uint8_t v___y_3366_; uint8_t v___y_3368_; uint8_t v___x_3382_; 
v___x_3359_ = 2;
v___x_3382_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3269_, v___x_3359_);
if (v___x_3382_ == 0)
{
v___y_3368_ = v___x_3382_;
goto v___jp_3367_;
}
else
{
uint8_t v___x_3383_; 
lean_inc_ref(v_msgData_3268_);
v___x_3383_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3268_);
v___y_3368_ = v___x_3383_;
goto v___jp_3367_;
}
v___jp_3276_:
{
lean_object* v___x_3286_; lean_object* v_currNamespace_3287_; lean_object* v_openDecls_3288_; lean_object* v_env_3289_; lean_object* v_nextMacroScope_3290_; lean_object* v_ngen_3291_; lean_object* v_auxDeclNGen_3292_; lean_object* v_traceState_3293_; lean_object* v_cache_3294_; lean_object* v_messages_3295_; lean_object* v_infoState_3296_; lean_object* v_snapshotTasks_3297_; lean_object* v___x_3299_; uint8_t v_isShared_3300_; uint8_t v_isSharedCheck_3311_; 
v___x_3286_ = lean_st_ref_take(v___y_3285_);
v_currNamespace_3287_ = lean_ctor_get(v___y_3284_, 5);
v_openDecls_3288_ = lean_ctor_get(v___y_3284_, 6);
v_env_3289_ = lean_ctor_get(v___x_3286_, 0);
v_nextMacroScope_3290_ = lean_ctor_get(v___x_3286_, 1);
v_ngen_3291_ = lean_ctor_get(v___x_3286_, 2);
v_auxDeclNGen_3292_ = lean_ctor_get(v___x_3286_, 3);
v_traceState_3293_ = lean_ctor_get(v___x_3286_, 4);
v_cache_3294_ = lean_ctor_get(v___x_3286_, 5);
v_messages_3295_ = lean_ctor_get(v___x_3286_, 6);
v_infoState_3296_ = lean_ctor_get(v___x_3286_, 7);
v_snapshotTasks_3297_ = lean_ctor_get(v___x_3286_, 8);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3286_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3299_ = v___x_3286_;
v_isShared_3300_ = v_isSharedCheck_3311_;
goto v_resetjp_3298_;
}
else
{
lean_inc(v_snapshotTasks_3297_);
lean_inc(v_infoState_3296_);
lean_inc(v_messages_3295_);
lean_inc(v_cache_3294_);
lean_inc(v_traceState_3293_);
lean_inc(v_auxDeclNGen_3292_);
lean_inc(v_ngen_3291_);
lean_inc(v_nextMacroScope_3290_);
lean_inc(v_env_3289_);
lean_dec(v___x_3286_);
v___x_3299_ = lean_box(0);
v_isShared_3300_ = v_isSharedCheck_3311_;
goto v_resetjp_3298_;
}
v_resetjp_3298_:
{
lean_object* v___x_3301_; lean_object* v___x_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3306_; 
lean_inc(v_openDecls_3288_);
lean_inc(v_currNamespace_3287_);
v___x_3301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3301_, 0, v_currNamespace_3287_);
lean_ctor_set(v___x_3301_, 1, v_openDecls_3288_);
v___x_3302_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3302_, 0, v___x_3301_);
lean_ctor_set(v___x_3302_, 1, v___y_3278_);
lean_inc_ref(v___y_3279_);
lean_inc_ref(v___y_3282_);
v___x_3303_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3303_, 0, v___y_3282_);
lean_ctor_set(v___x_3303_, 1, v___y_3283_);
lean_ctor_set(v___x_3303_, 2, v___y_3280_);
lean_ctor_set(v___x_3303_, 3, v___y_3279_);
lean_ctor_set(v___x_3303_, 4, v___x_3302_);
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*5, v___y_3281_);
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*5 + 1, v___y_3277_);
lean_ctor_set_uint8(v___x_3303_, sizeof(void*)*5 + 2, v_isSilent_3270_);
v___x_3304_ = l_Lean_MessageLog_add(v___x_3303_, v_messages_3295_);
if (v_isShared_3300_ == 0)
{
lean_ctor_set(v___x_3299_, 6, v___x_3304_);
v___x_3306_ = v___x_3299_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v_env_3289_);
lean_ctor_set(v_reuseFailAlloc_3310_, 1, v_nextMacroScope_3290_);
lean_ctor_set(v_reuseFailAlloc_3310_, 2, v_ngen_3291_);
lean_ctor_set(v_reuseFailAlloc_3310_, 3, v_auxDeclNGen_3292_);
lean_ctor_set(v_reuseFailAlloc_3310_, 4, v_traceState_3293_);
lean_ctor_set(v_reuseFailAlloc_3310_, 5, v_cache_3294_);
lean_ctor_set(v_reuseFailAlloc_3310_, 6, v___x_3304_);
lean_ctor_set(v_reuseFailAlloc_3310_, 7, v_infoState_3296_);
lean_ctor_set(v_reuseFailAlloc_3310_, 8, v_snapshotTasks_3297_);
v___x_3306_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
lean_object* v___x_3307_; lean_object* v___x_3308_; lean_object* v___x_3309_; 
v___x_3307_ = lean_st_ref_put(v___y_3285_, v___x_3306_);
v___x_3308_ = lean_box(0);
v___x_3309_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3308_);
return v___x_3309_;
}
}
}
v___jp_3312_:
{
lean_object* v_fileName_3320_; lean_object* v_fileMap_3321_; lean_object* v___x_3322_; lean_object* v___x_3323_; lean_object* v_a_3324_; lean_object* v___x_3326_; uint8_t v_isShared_3327_; uint8_t v_isSharedCheck_3337_; 
v_fileName_3320_ = lean_ctor_get(v___y_3317_, 0);
v_fileMap_3321_ = lean_ctor_get(v___y_3317_, 1);
v___x_3322_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3268_);
v___x_3323_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3322_, v___y_3271_, v___y_3272_, v___y_3273_, v___y_3274_);
v_a_3324_ = lean_ctor_get(v___x_3323_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v___x_3323_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3326_ = v___x_3323_;
v_isShared_3327_ = v_isSharedCheck_3337_;
goto v_resetjp_3325_;
}
else
{
lean_inc(v_a_3324_);
lean_dec(v___x_3323_);
v___x_3326_ = lean_box(0);
v_isShared_3327_ = v_isSharedCheck_3337_;
goto v_resetjp_3325_;
}
v_resetjp_3325_:
{
lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
lean_inc_ref_n(v_fileMap_3321_, 2);
v___x_3328_ = l_Lean_FileMap_toPosition(v_fileMap_3321_, v___y_3315_);
lean_dec(v___y_3315_);
v___x_3329_ = l_Lean_FileMap_toPosition(v_fileMap_3321_, v___y_3319_);
lean_dec(v___y_3319_);
v___x_3330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3330_, 0, v___x_3329_);
v___x_3331_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3316_ == 0)
{
lean_del_object(v___x_3326_);
lean_dec_ref(v___y_3313_);
v___y_3277_ = v___y_3314_;
v___y_3278_ = v_a_3324_;
v___y_3279_ = v___x_3331_;
v___y_3280_ = v___x_3330_;
v___y_3281_ = v___y_3318_;
v___y_3282_ = v_fileName_3320_;
v___y_3283_ = v___x_3328_;
v___y_3284_ = v___y_3273_;
v___y_3285_ = v___y_3274_;
goto v___jp_3276_;
}
else
{
uint8_t v___x_3332_; 
lean_inc(v_a_3324_);
v___x_3332_ = l_Lean_MessageData_hasTag(v___y_3313_, v_a_3324_);
if (v___x_3332_ == 0)
{
lean_object* v___x_3333_; lean_object* v___x_3335_; 
lean_dec_ref_known(v___x_3330_, 1);
lean_dec_ref(v___x_3328_);
lean_dec(v_a_3324_);
v___x_3333_ = lean_box(0);
if (v_isShared_3327_ == 0)
{
lean_ctor_set(v___x_3326_, 0, v___x_3333_);
v___x_3335_ = v___x_3326_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3333_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
return v___x_3335_;
}
}
else
{
lean_del_object(v___x_3326_);
v___y_3277_ = v___y_3314_;
v___y_3278_ = v_a_3324_;
v___y_3279_ = v___x_3331_;
v___y_3280_ = v___x_3330_;
v___y_3281_ = v___y_3318_;
v___y_3282_ = v_fileName_3320_;
v___y_3283_ = v___x_3328_;
v___y_3284_ = v___y_3273_;
v___y_3285_ = v___y_3274_;
goto v___jp_3276_;
}
}
}
}
v___jp_3338_:
{
lean_object* v___x_3346_; 
v___x_3346_ = l_Lean_Syntax_getTailPos_x3f(v___y_3343_, v___y_3344_);
lean_dec(v___y_3343_);
if (lean_obj_tag(v___x_3346_) == 0)
{
lean_inc(v___y_3345_);
v___y_3313_ = v___y_3339_;
v___y_3314_ = v___y_3340_;
v___y_3315_ = v___y_3345_;
v___y_3316_ = v___y_3341_;
v___y_3317_ = v___y_3342_;
v___y_3318_ = v___y_3344_;
v___y_3319_ = v___y_3345_;
goto v___jp_3312_;
}
else
{
lean_object* v_val_3347_; 
v_val_3347_ = lean_ctor_get(v___x_3346_, 0);
lean_inc(v_val_3347_);
lean_dec_ref_known(v___x_3346_, 1);
v___y_3313_ = v___y_3339_;
v___y_3314_ = v___y_3340_;
v___y_3315_ = v___y_3345_;
v___y_3316_ = v___y_3341_;
v___y_3317_ = v___y_3342_;
v___y_3318_ = v___y_3344_;
v___y_3319_ = v_val_3347_;
goto v___jp_3312_;
}
}
v___jp_3348_:
{
lean_object* v_ref_3355_; lean_object* v___x_3356_; 
v_ref_3355_ = l_Lean_replaceRef(v_ref_3267_, v___y_3351_);
v___x_3356_ = l_Lean_Syntax_getPos_x3f(v_ref_3355_, v___y_3353_);
if (lean_obj_tag(v___x_3356_) == 0)
{
lean_object* v___x_3357_; 
v___x_3357_ = lean_unsigned_to_nat(0u);
v___y_3339_ = v___y_3349_;
v___y_3340_ = v___y_3354_;
v___y_3341_ = v___y_3350_;
v___y_3342_ = v___y_3352_;
v___y_3343_ = v_ref_3355_;
v___y_3344_ = v___y_3353_;
v___y_3345_ = v___x_3357_;
goto v___jp_3338_;
}
else
{
lean_object* v_val_3358_; 
v_val_3358_ = lean_ctor_get(v___x_3356_, 0);
lean_inc(v_val_3358_);
lean_dec_ref_known(v___x_3356_, 1);
v___y_3339_ = v___y_3349_;
v___y_3340_ = v___y_3354_;
v___y_3341_ = v___y_3350_;
v___y_3342_ = v___y_3352_;
v___y_3343_ = v_ref_3355_;
v___y_3344_ = v___y_3353_;
v___y_3345_ = v_val_3358_;
goto v___jp_3338_;
}
}
v___jp_3360_:
{
if (v___y_3366_ == 0)
{
v___y_3349_ = v___y_3364_;
v___y_3350_ = v___y_3362_;
v___y_3351_ = v___y_3361_;
v___y_3352_ = v___y_3363_;
v___y_3353_ = v___y_3365_;
v___y_3354_ = v_severity_3269_;
goto v___jp_3348_;
}
else
{
v___y_3349_ = v___y_3364_;
v___y_3350_ = v___y_3362_;
v___y_3351_ = v___y_3361_;
v___y_3352_ = v___y_3363_;
v___y_3353_ = v___y_3365_;
v___y_3354_ = v___x_3359_;
goto v___jp_3348_;
}
}
v___jp_3367_:
{
if (v___y_3368_ == 0)
{
lean_object* v_toCold_3369_; lean_object* v_options_3370_; lean_object* v_ref_3371_; uint8_t v_suppressElabErrors_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___f_3375_; uint8_t v___x_3376_; uint8_t v___x_3377_; 
v_toCold_3369_ = lean_ctor_get(v___y_3273_, 0);
v_options_3370_ = lean_ctor_get(v___y_3273_, 1);
v_ref_3371_ = lean_ctor_get(v___y_3273_, 4);
v_suppressElabErrors_3372_ = lean_ctor_get_uint8(v___y_3273_, sizeof(void*)*10 + 1);
v___x_3373_ = lean_box(v_suppressElabErrors_3372_);
v___x_3374_ = lean_box(v___y_3368_);
v___f_3375_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3375_, 0, v___x_3373_);
lean_closure_set(v___f_3375_, 1, v___x_3374_);
v___x_3376_ = 1;
v___x_3377_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3269_, v___x_3376_);
if (v___x_3377_ == 0)
{
v___y_3361_ = v_ref_3371_;
v___y_3362_ = v_suppressElabErrors_3372_;
v___y_3363_ = v_toCold_3369_;
v___y_3364_ = v___f_3375_;
v___y_3365_ = v___y_3368_;
v___y_3366_ = v___x_3377_;
goto v___jp_3360_;
}
else
{
lean_object* v___x_3378_; uint8_t v___x_3379_; 
v___x_3378_ = l_Lean_warningAsError;
v___x_3379_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3370_, v___x_3378_);
v___y_3361_ = v_ref_3371_;
v___y_3362_ = v_suppressElabErrors_3372_;
v___y_3363_ = v_toCold_3369_;
v___y_3364_ = v___f_3375_;
v___y_3365_ = v___y_3368_;
v___y_3366_ = v___x_3379_;
goto v___jp_3360_;
}
}
else
{
lean_object* v___x_3380_; lean_object* v___x_3381_; 
lean_dec_ref(v_msgData_3268_);
v___x_3380_ = lean_box(0);
v___x_3381_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3381_, 0, v___x_3380_);
return v___x_3381_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4___boxed(lean_object* v_ref_3384_, lean_object* v_msgData_3385_, lean_object* v_severity_3386_, lean_object* v_isSilent_3387_, lean_object* v___y_3388_, lean_object* v___y_3389_, lean_object* v___y_3390_, lean_object* v___y_3391_, lean_object* v___y_3392_){
_start:
{
uint8_t v_severity_boxed_3393_; uint8_t v_isSilent_boxed_3394_; lean_object* v_res_3395_; 
v_severity_boxed_3393_ = lean_unbox(v_severity_3386_);
v_isSilent_boxed_3394_ = lean_unbox(v_isSilent_3387_);
v_res_3395_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4(v_ref_3384_, v_msgData_3385_, v_severity_boxed_3393_, v_isSilent_boxed_3394_, v___y_3388_, v___y_3389_, v___y_3390_, v___y_3391_);
lean_dec(v___y_3391_);
lean_dec_ref(v___y_3390_);
lean_dec(v___y_3389_);
lean_dec_ref(v___y_3388_);
lean_dec(v_ref_3384_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(lean_object* v_msgData_3396_, uint8_t v_severity_3397_, uint8_t v_isSilent_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v_ref_3404_; lean_object* v___x_3405_; 
v_ref_3404_ = lean_ctor_get(v___y_3401_, 4);
v___x_3405_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2_spec__4(v_ref_3404_, v_msgData_3396_, v_severity_3397_, v_isSilent_3398_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
return v___x_3405_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2___boxed(lean_object* v_msgData_3406_, lean_object* v_severity_3407_, lean_object* v_isSilent_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_, lean_object* v___y_3411_, lean_object* v___y_3412_, lean_object* v___y_3413_){
_start:
{
uint8_t v_severity_boxed_3414_; uint8_t v_isSilent_boxed_3415_; lean_object* v_res_3416_; 
v_severity_boxed_3414_ = lean_unbox(v_severity_3407_);
v_isSilent_boxed_3415_ = lean_unbox(v_isSilent_3408_);
v_res_3416_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(v_msgData_3406_, v_severity_boxed_3414_, v_isSilent_boxed_3415_, v___y_3409_, v___y_3410_, v___y_3411_, v___y_3412_);
lean_dec(v___y_3412_);
lean_dec_ref(v___y_3411_);
lean_dec(v___y_3410_);
lean_dec_ref(v___y_3409_);
return v_res_3416_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_msgData_3417_, lean_object* v___y_3418_, lean_object* v___y_3419_, lean_object* v___y_3420_, lean_object* v___y_3421_){
_start:
{
uint8_t v___x_3423_; uint8_t v___x_3424_; lean_object* v___x_3425_; 
v___x_3423_ = 1;
v___x_3424_ = 0;
v___x_3425_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2_spec__2(v_msgData_3417_, v___x_3423_, v___x_3424_, v___y_3418_, v___y_3419_, v___y_3420_, v___y_3421_);
return v___x_3425_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_msgData_3426_, lean_object* v___y_3427_, lean_object* v___y_3428_, lean_object* v___y_3429_, lean_object* v___y_3430_, lean_object* v___y_3431_){
_start:
{
lean_object* v_res_3432_; 
v_res_3432_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_msgData_3426_, v___y_3427_, v___y_3428_, v___y_3429_, v___y_3430_);
lean_dec(v___y_3430_);
lean_dec_ref(v___y_3429_);
lean_dec(v___y_3428_);
lean_dec_ref(v___y_3427_);
return v_res_3432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(lean_object* v_as_3433_, size_t v_sz_3434_, size_t v_i_3435_, lean_object* v_b_3436_, lean_object* v___y_3437_, lean_object* v___y_3438_, lean_object* v___y_3439_, lean_object* v___y_3440_){
_start:
{
lean_object* v_a_3443_; uint8_t v___x_3447_; 
v___x_3447_ = lean_usize_dec_lt(v_i_3435_, v_sz_3434_);
if (v___x_3447_ == 0)
{
lean_object* v___x_3448_; 
v___x_3448_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3448_, 0, v_b_3436_);
return v___x_3448_;
}
else
{
lean_object* v_a_3449_; lean_object* v___x_3450_; lean_object* v___x_3451_; 
v_a_3449_ = lean_array_uget_borrowed(v_as_3433_, v_i_3435_);
v___x_3450_ = l_Lean_Expr_fvarId_x21(v_a_3449_);
lean_inc(v___x_3450_);
v___x_3451_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_3450_, v___y_3438_, v___y_3439_, v___y_3440_);
if (lean_obj_tag(v___x_3451_) == 0)
{
lean_object* v_a_3452_; lean_object* v___x_3453_; uint8_t v___x_3454_; uint8_t v___x_3455_; 
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
lean_inc(v_a_3452_);
lean_dec_ref_known(v___x_3451_, 1);
v___x_3453_ = lean_box(0);
v___x_3454_ = lean_unbox(v_a_3452_);
lean_dec(v_a_3452_);
v___x_3455_ = l_Lean_BinderInfo_isInstImplicit(v___x_3454_);
if (v___x_3455_ == 0)
{
lean_dec(v___x_3450_);
v_a_3443_ = v___x_3453_;
goto v___jp_3442_;
}
else
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
v___x_3456_ = lean_st_ref_take(v___y_3437_);
v___x_3457_ = l_Lean_CollectFVars_State_add(v___x_3456_, v___x_3450_);
v___x_3458_ = lean_st_ref_put(v___y_3437_, v___x_3457_);
v_a_3443_ = v___x_3453_;
goto v___jp_3442_;
}
}
else
{
lean_object* v_a_3459_; lean_object* v___x_3461_; uint8_t v_isShared_3462_; uint8_t v_isSharedCheck_3466_; 
lean_dec(v___x_3450_);
v_a_3459_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3466_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3466_ == 0)
{
v___x_3461_ = v___x_3451_;
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
else
{
lean_inc(v_a_3459_);
lean_dec(v___x_3451_);
v___x_3461_ = lean_box(0);
v_isShared_3462_ = v_isSharedCheck_3466_;
goto v_resetjp_3460_;
}
v_resetjp_3460_:
{
lean_object* v___x_3464_; 
if (v_isShared_3462_ == 0)
{
v___x_3464_ = v___x_3461_;
goto v_reusejp_3463_;
}
else
{
lean_object* v_reuseFailAlloc_3465_; 
v_reuseFailAlloc_3465_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3465_, 0, v_a_3459_);
v___x_3464_ = v_reuseFailAlloc_3465_;
goto v_reusejp_3463_;
}
v_reusejp_3463_:
{
return v___x_3464_;
}
}
}
}
v___jp_3442_:
{
size_t v___x_3444_; size_t v___x_3445_; 
v___x_3444_ = ((size_t)1ULL);
v___x_3445_ = lean_usize_add(v_i_3435_, v___x_3444_);
v_i_3435_ = v___x_3445_;
v_b_3436_ = v_a_3443_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg___boxed(lean_object* v_as_3467_, lean_object* v_sz_3468_, lean_object* v_i_3469_, lean_object* v_b_3470_, lean_object* v___y_3471_, lean_object* v___y_3472_, lean_object* v___y_3473_, lean_object* v___y_3474_, lean_object* v___y_3475_){
_start:
{
size_t v_sz_boxed_3476_; size_t v_i_boxed_3477_; lean_object* v_res_3478_; 
v_sz_boxed_3476_ = lean_unbox_usize(v_sz_3468_);
lean_dec(v_sz_3468_);
v_i_boxed_3477_ = lean_unbox_usize(v_i_3469_);
lean_dec(v_i_3469_);
v_res_3478_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(v_as_3467_, v_sz_boxed_3476_, v_i_boxed_3477_, v_b_3470_, v___y_3471_, v___y_3472_, v___y_3473_, v___y_3474_);
lean_dec(v___y_3474_);
lean_dec_ref(v___y_3473_);
lean_dec_ref(v___y_3472_);
lean_dec(v___y_3471_);
lean_dec_ref(v_as_3467_);
return v_res_3478_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(lean_object* v_k_3479_, lean_object* v_t_3480_){
_start:
{
if (lean_obj_tag(v_t_3480_) == 0)
{
lean_object* v_k_3481_; lean_object* v_l_3482_; lean_object* v_r_3483_; uint8_t v___x_3484_; 
v_k_3481_ = lean_ctor_get(v_t_3480_, 1);
v_l_3482_ = lean_ctor_get(v_t_3480_, 3);
v_r_3483_ = lean_ctor_get(v_t_3480_, 4);
v___x_3484_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3479_, v_k_3481_);
switch(v___x_3484_)
{
case 0:
{
v_t_3480_ = v_l_3482_;
goto _start;
}
case 1:
{
uint8_t v___x_3486_; 
v___x_3486_ = 1;
return v___x_3486_;
}
default: 
{
v_t_3480_ = v_r_3483_;
goto _start;
}
}
}
else
{
uint8_t v___x_3488_; 
v___x_3488_ = 0;
return v___x_3488_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg___boxed(lean_object* v_k_3489_, lean_object* v_t_3490_){
_start:
{
uint8_t v_res_3491_; lean_object* v_r_3492_; 
v_res_3491_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_k_3489_, v_t_3490_);
lean_dec(v_t_3490_);
lean_dec(v_k_3489_);
v_r_3492_ = lean_box(v_res_3491_);
return v_r_3492_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1(void){
_start:
{
lean_object* v___x_3494_; lean_object* v___x_3495_; 
v___x_3494_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__0));
v___x_3495_ = l_Lean_stringToMessageData(v___x_3494_);
return v___x_3495_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3(void){
_start:
{
lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3497_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__2));
v___x_3498_ = l_Lean_stringToMessageData(v___x_3497_);
return v___x_3498_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object* v_a_3499_, lean_object* v_as_3500_, size_t v_sz_3501_, size_t v_i_3502_, lean_object* v_b_3503_, lean_object* v___y_3504_, lean_object* v___y_3505_, lean_object* v___y_3506_){
_start:
{
lean_object* v_a_3509_; uint8_t v___x_3513_; 
v___x_3513_ = lean_usize_dec_lt(v_i_3502_, v_sz_3501_);
if (v___x_3513_ == 0)
{
lean_object* v___x_3514_; 
v___x_3514_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3514_, 0, v_b_3503_);
return v___x_3514_;
}
else
{
lean_object* v_snd_3515_; 
v_snd_3515_ = lean_ctor_get(v_b_3503_, 1);
lean_inc(v_snd_3515_);
if (lean_obj_tag(v_snd_3515_) == 0)
{
lean_object* v_fst_3516_; lean_object* v___x_3518_; uint8_t v_isShared_3519_; uint8_t v_isSharedCheck_3524_; 
v_fst_3516_ = lean_ctor_get(v_b_3503_, 0);
v_isSharedCheck_3524_ = !lean_is_exclusive(v_b_3503_);
if (v_isSharedCheck_3524_ == 0)
{
lean_object* v_unused_3525_; 
v_unused_3525_ = lean_ctor_get(v_b_3503_, 1);
lean_dec(v_unused_3525_);
v___x_3518_ = v_b_3503_;
v_isShared_3519_ = v_isSharedCheck_3524_;
goto v_resetjp_3517_;
}
else
{
lean_inc(v_fst_3516_);
lean_dec(v_b_3503_);
v___x_3518_ = lean_box(0);
v_isShared_3519_ = v_isSharedCheck_3524_;
goto v_resetjp_3517_;
}
v_resetjp_3517_:
{
lean_object* v___x_3521_; 
if (v_isShared_3519_ == 0)
{
v___x_3521_ = v___x_3518_;
goto v_reusejp_3520_;
}
else
{
lean_object* v_reuseFailAlloc_3523_; 
v_reuseFailAlloc_3523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3523_, 0, v_fst_3516_);
lean_ctor_set(v_reuseFailAlloc_3523_, 1, v_snd_3515_);
v___x_3521_ = v_reuseFailAlloc_3523_;
goto v_reusejp_3520_;
}
v_reusejp_3520_:
{
lean_object* v___x_3522_; 
v___x_3522_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3522_, 0, v___x_3521_);
return v___x_3522_;
}
}
}
else
{
lean_object* v_fst_3526_; lean_object* v___x_3528_; uint8_t v_isShared_3529_; uint8_t v_isSharedCheck_3583_; 
v_fst_3526_ = lean_ctor_get(v_b_3503_, 0);
v_isSharedCheck_3583_ = !lean_is_exclusive(v_b_3503_);
if (v_isSharedCheck_3583_ == 0)
{
lean_object* v_unused_3584_; 
v_unused_3584_ = lean_ctor_get(v_b_3503_, 1);
lean_dec(v_unused_3584_);
v___x_3528_ = v_b_3503_;
v_isShared_3529_ = v_isSharedCheck_3583_;
goto v_resetjp_3527_;
}
else
{
lean_inc(v_fst_3526_);
lean_dec(v_b_3503_);
v___x_3528_ = lean_box(0);
v_isShared_3529_ = v_isSharedCheck_3583_;
goto v_resetjp_3527_;
}
v_resetjp_3527_:
{
lean_object* v_val_3530_; lean_object* v___x_3532_; uint8_t v_isShared_3533_; uint8_t v_isSharedCheck_3582_; 
v_val_3530_ = lean_ctor_get(v_snd_3515_, 0);
v_isSharedCheck_3582_ = !lean_is_exclusive(v_snd_3515_);
if (v_isSharedCheck_3582_ == 0)
{
v___x_3532_ = v_snd_3515_;
v_isShared_3533_ = v_isSharedCheck_3582_;
goto v_resetjp_3531_;
}
else
{
lean_inc(v_val_3530_);
lean_dec(v_snd_3515_);
v___x_3532_ = lean_box(0);
v_isShared_3533_ = v_isSharedCheck_3582_;
goto v_resetjp_3531_;
}
v_resetjp_3531_:
{
lean_object* v_fvarSet_3534_; lean_object* v_a_3535_; lean_object* v___x_3536_; lean_object* v___x_3537_; lean_object* v___x_3539_; 
v_fvarSet_3534_ = lean_ctor_get(v_a_3499_, 1);
v_a_3535_ = lean_array_uget_borrowed(v_as_3500_, v_i_3502_);
v___x_3536_ = lean_unsigned_to_nat(1u);
v___x_3537_ = lean_nat_add(v_val_3530_, v___x_3536_);
if (v_isShared_3533_ == 0)
{
lean_ctor_set(v___x_3532_, 0, v___x_3537_);
v___x_3539_ = v___x_3532_;
goto v_reusejp_3538_;
}
else
{
lean_object* v_reuseFailAlloc_3581_; 
v_reuseFailAlloc_3581_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3581_, 0, v___x_3537_);
v___x_3539_ = v_reuseFailAlloc_3581_;
goto v_reusejp_3538_;
}
v_reusejp_3538_:
{
lean_object* v___x_3540_; uint8_t v___x_3541_; 
v___x_3540_ = l_Lean_Expr_fvarId_x21(v_a_3535_);
v___x_3541_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v___x_3540_, v_fvarSet_3534_);
if (v___x_3541_ == 0)
{
lean_object* v___x_3542_; 
v___x_3542_ = l_Lean_FVarId_getDecl___redArg(v___x_3540_, v___y_3504_, v___y_3505_, v___y_3506_);
if (lean_obj_tag(v___x_3542_) == 0)
{
lean_object* v_a_3543_; lean_object* v___x_3544_; 
v_a_3543_ = lean_ctor_get(v___x_3542_, 0);
lean_inc(v_a_3543_);
lean_dec_ref_known(v___x_3542_, 1);
v___x_3544_ = l_Lean_LocalDecl_ppAsBinder(v_a_3543_);
if (lean_obj_tag(v___x_3544_) == 1)
{
lean_object* v_val_3545_; lean_object* v___x_3547_; uint8_t v_isShared_3548_; uint8_t v_isSharedCheck_3566_; 
v_val_3545_ = lean_ctor_get(v___x_3544_, 0);
v_isSharedCheck_3566_ = !lean_is_exclusive(v___x_3544_);
if (v_isSharedCheck_3566_ == 0)
{
v___x_3547_ = v___x_3544_;
v_isShared_3548_ = v_isSharedCheck_3566_;
goto v_resetjp_3546_;
}
else
{
lean_inc(v_val_3545_);
lean_dec(v___x_3544_);
v___x_3547_ = lean_box(0);
v_isShared_3548_ = v_isSharedCheck_3566_;
goto v_resetjp_3546_;
}
v_resetjp_3546_:
{
lean_object* v___x_3549_; lean_object* v___x_3550_; lean_object* v___x_3552_; 
v___x_3549_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__1);
v___x_3550_ = l_Nat_reprFast(v_val_3530_);
if (v_isShared_3548_ == 0)
{
lean_ctor_set_tag(v___x_3547_, 3);
lean_ctor_set(v___x_3547_, 0, v___x_3550_);
v___x_3552_ = v___x_3547_;
goto v_reusejp_3551_;
}
else
{
lean_object* v_reuseFailAlloc_3565_; 
v_reuseFailAlloc_3565_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3565_, 0, v___x_3550_);
v___x_3552_ = v_reuseFailAlloc_3565_;
goto v_reusejp_3551_;
}
v_reusejp_3551_:
{
lean_object* v___x_3553_; lean_object* v___x_3554_; lean_object* v___x_3555_; lean_object* v___x_3556_; lean_object* v___x_3557_; lean_object* v___x_3558_; lean_object* v___x_3559_; lean_object* v___x_3560_; lean_object* v___x_3561_; lean_object* v___x_3563_; 
v___x_3553_ = l_Lean_MessageData_ofFormat(v___x_3552_);
v___x_3554_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3554_, 0, v___x_3549_);
lean_ctor_set(v___x_3554_, 1, v___x_3553_);
v___x_3555_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___closed__3);
v___x_3556_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3556_, 0, v___x_3554_);
lean_ctor_set(v___x_3556_, 1, v___x_3555_);
v___x_3557_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3557_, 0, v___x_3556_);
lean_ctor_set(v___x_3557_, 1, v_val_3545_);
v___x_3558_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3559_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3559_, 0, v___x_3557_);
lean_ctor_set(v___x_3559_, 1, v___x_3558_);
v___x_3560_ = l_Lean_indentD(v___x_3559_);
v___x_3561_ = lean_array_push(v_fst_3526_, v___x_3560_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 1, v___x_3539_);
lean_ctor_set(v___x_3528_, 0, v___x_3561_);
v___x_3563_ = v___x_3528_;
goto v_reusejp_3562_;
}
else
{
lean_object* v_reuseFailAlloc_3564_; 
v_reuseFailAlloc_3564_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3564_, 0, v___x_3561_);
lean_ctor_set(v_reuseFailAlloc_3564_, 1, v___x_3539_);
v___x_3563_ = v_reuseFailAlloc_3564_;
goto v_reusejp_3562_;
}
v_reusejp_3562_:
{
v_a_3509_ = v___x_3563_;
goto v___jp_3508_;
}
}
}
}
else
{
lean_object* v___x_3568_; 
lean_dec(v___x_3544_);
lean_dec(v_val_3530_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 1, v___x_3539_);
v___x_3568_ = v___x_3528_;
goto v_reusejp_3567_;
}
else
{
lean_object* v_reuseFailAlloc_3569_; 
v_reuseFailAlloc_3569_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3569_, 0, v_fst_3526_);
lean_ctor_set(v_reuseFailAlloc_3569_, 1, v___x_3539_);
v___x_3568_ = v_reuseFailAlloc_3569_;
goto v_reusejp_3567_;
}
v_reusejp_3567_:
{
v_a_3509_ = v___x_3568_;
goto v___jp_3508_;
}
}
}
else
{
lean_object* v_a_3570_; lean_object* v___x_3572_; uint8_t v_isShared_3573_; uint8_t v_isSharedCheck_3577_; 
lean_dec_ref(v___x_3539_);
lean_dec(v_val_3530_);
lean_del_object(v___x_3528_);
lean_dec(v_fst_3526_);
v_a_3570_ = lean_ctor_get(v___x_3542_, 0);
v_isSharedCheck_3577_ = !lean_is_exclusive(v___x_3542_);
if (v_isSharedCheck_3577_ == 0)
{
v___x_3572_ = v___x_3542_;
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
else
{
lean_inc(v_a_3570_);
lean_dec(v___x_3542_);
v___x_3572_ = lean_box(0);
v_isShared_3573_ = v_isSharedCheck_3577_;
goto v_resetjp_3571_;
}
v_resetjp_3571_:
{
lean_object* v___x_3575_; 
if (v_isShared_3573_ == 0)
{
v___x_3575_ = v___x_3572_;
goto v_reusejp_3574_;
}
else
{
lean_object* v_reuseFailAlloc_3576_; 
v_reuseFailAlloc_3576_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3576_, 0, v_a_3570_);
v___x_3575_ = v_reuseFailAlloc_3576_;
goto v_reusejp_3574_;
}
v_reusejp_3574_:
{
return v___x_3575_;
}
}
}
}
else
{
lean_object* v___x_3579_; 
lean_dec(v___x_3540_);
lean_dec(v_val_3530_);
if (v_isShared_3529_ == 0)
{
lean_ctor_set(v___x_3528_, 1, v___x_3539_);
v___x_3579_ = v___x_3528_;
goto v_reusejp_3578_;
}
else
{
lean_object* v_reuseFailAlloc_3580_; 
v_reuseFailAlloc_3580_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3580_, 0, v_fst_3526_);
lean_ctor_set(v_reuseFailAlloc_3580_, 1, v___x_3539_);
v___x_3579_ = v_reuseFailAlloc_3580_;
goto v_reusejp_3578_;
}
v_reusejp_3578_:
{
v_a_3509_ = v___x_3579_;
goto v___jp_3508_;
}
}
}
}
}
}
}
v___jp_3508_:
{
size_t v___x_3510_; size_t v___x_3511_; 
v___x_3510_ = ((size_t)1ULL);
v___x_3511_ = lean_usize_add(v_i_3502_, v___x_3510_);
v_i_3502_ = v___x_3511_;
v_b_3503_ = v_a_3509_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object* v_a_3585_, lean_object* v_as_3586_, lean_object* v_sz_3587_, lean_object* v_i_3588_, lean_object* v_b_3589_, lean_object* v___y_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_){
_start:
{
size_t v_sz_boxed_3594_; size_t v_i_boxed_3595_; lean_object* v_res_3596_; 
v_sz_boxed_3594_ = lean_unbox_usize(v_sz_3587_);
lean_dec(v_sz_3587_);
v_i_boxed_3595_ = lean_unbox_usize(v_i_3588_);
lean_dec(v_i_3588_);
v_res_3596_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_a_3585_, v_as_3586_, v_sz_boxed_3594_, v_i_boxed_3595_, v_b_3589_, v___y_3590_, v___y_3591_, v___y_3592_);
lean_dec(v___y_3592_);
lean_dec_ref(v___y_3591_);
lean_dec_ref(v___y_3590_);
lean_dec_ref(v_as_3586_);
lean_dec_ref(v_a_3585_);
return v_res_3596_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3598_; lean_object* v___x_3599_; 
v___x_3598_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0));
v___x_3599_ = l_Lean_stringToMessageData(v___x_3598_);
return v___x_3599_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3601_; lean_object* v___x_3602_; 
v___x_3601_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2));
v___x_3602_ = l_Lean_stringToMessageData(v___x_3601_);
return v___x_3602_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3603_; lean_object* v___x_3604_; lean_object* v___x_3605_; 
v___x_3603_ = lean_box(0);
v___x_3604_ = lean_unsigned_to_nat(16u);
v___x_3605_ = lean_mk_array(v___x_3604_, v___x_3603_);
return v___x_3605_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; 
v___x_3606_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4);
v___x_3607_ = lean_unsigned_to_nat(0u);
v___x_3608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3607_);
lean_ctor_set(v___x_3608_, 1, v___x_3606_);
return v___x_3608_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10(void){
_start:
{
lean_object* v___x_3617_; lean_object* v___x_3618_; 
v___x_3617_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9));
v___x_3618_ = l_Lean_stringToMessageData(v___x_3617_);
return v___x_3618_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12(void){
_start:
{
lean_object* v___x_3620_; lean_object* v___x_3621_; 
v___x_3620_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11));
v___x_3621_ = l_Lean_stringToMessageData(v___x_3620_);
return v___x_3621_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v___x_3623_, lean_object* v___x_3624_, lean_object* v_args_3625_, lean_object* v_ty_3626_, lean_object* v___y_3627_, lean_object* v___y_3628_, lean_object* v___y_3629_, lean_object* v___y_3630_){
_start:
{
lean_object* v___y_3633_; lean_object* v___y_3634_; lean_object* v___y_3635_; lean_object* v___x_3649_; lean_object* v___x_3650_; lean_object* v___x_3651_; lean_object* v___x_3652_; lean_object* v___x_3653_; lean_object* v___y_3709_; lean_object* v___x_3710_; 
v___x_3649_ = lean_unsigned_to_nat(0u);
v___x_3650_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5);
v___x_3651_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6));
v___x_3652_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3652_, 0, v___x_3650_);
lean_ctor_set(v___x_3652_, 1, v___x_3623_);
lean_ctor_set(v___x_3652_, 2, v___x_3651_);
v___x_3653_ = lean_st_mk_ref(v___x_3652_);
v___x_3710_ = l_Lean_Expr_collectFVars(v_ty_3626_, v___x_3653_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
if (lean_obj_tag(v___x_3710_) == 0)
{
lean_object* v___x_3711_; size_t v_sz_3712_; size_t v___x_3713_; lean_object* v___x_3714_; 
lean_dec_ref_known(v___x_3710_, 1);
v___x_3711_ = lean_box(0);
v_sz_3712_ = lean_array_size(v_args_3625_);
v___x_3713_ = ((size_t)0ULL);
v___x_3714_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(v_args_3625_, v_sz_3712_, v___x_3713_, v___x_3711_, v___x_3653_, v___y_3627_, v___y_3629_, v___y_3630_);
if (lean_obj_tag(v___x_3714_) == 0)
{
lean_dec_ref_known(v___x_3714_, 1);
goto v___jp_3654_;
}
else
{
v___y_3709_ = v___x_3714_;
goto v___jp_3708_;
}
}
else
{
v___y_3709_ = v___x_3710_;
goto v___jp_3708_;
}
v___jp_3632_:
{
lean_object* v___x_3636_; lean_object* v___x_3637_; lean_object* v___x_3638_; lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; uint8_t v___x_3646_; 
lean_inc_ref(v___y_3635_);
v___x_3636_ = l_Lean_stringToMessageData(v___y_3635_);
v___x_3637_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3637_, 0, v___y_3633_);
lean_ctor_set(v___x_3637_, 1, v___x_3636_);
v___x_3638_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1);
v___x_3639_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3639_, 0, v___x_3637_);
lean_ctor_set(v___x_3639_, 1, v___x_3638_);
v___x_3640_ = lean_array_to_list(v___y_3634_);
v___x_3641_ = l_Lean_MessageData_nil;
v___x_3642_ = l_Lean_MessageData_joinSep(v___x_3640_, v___x_3641_);
v___x_3643_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3639_);
lean_ctor_set(v___x_3643_, 1, v___x_3642_);
v___x_3644_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3);
v___x_3645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3645_, 0, v___x_3643_);
lean_ctor_set(v___x_3645_, 1, v___x_3644_);
v___x_3646_ = l_Lean_Expr_hasSorry(v___x_3624_);
if (v___x_3646_ == 0)
{
lean_object* v___x_3647_; 
v___x_3647_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3645_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
return v___x_3647_;
}
else
{
lean_object* v___x_3648_; 
v___x_3648_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(v___x_3645_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
return v___x_3648_;
}
}
v___jp_3654_:
{
lean_object* v___x_3655_; lean_object* v___x_3656_; 
v___x_3655_ = lean_st_ref_get(v___x_3653_);
lean_dec(v___x_3653_);
v___x_3656_ = l_Lean_CollectFVars_State_addDependencies(v___x_3655_, v___y_3627_, v___y_3628_, v___y_3629_, v___y_3630_);
if (lean_obj_tag(v___x_3656_) == 0)
{
lean_object* v_a_3657_; lean_object* v___x_3658_; lean_object* v___x_3659_; size_t v_sz_3660_; size_t v___x_3661_; lean_object* v___x_3662_; 
v_a_3657_ = lean_ctor_get(v___x_3656_, 0);
lean_inc(v_a_3657_);
lean_dec_ref_known(v___x_3656_, 1);
v___x_3658_ = lean_unsigned_to_nat(1u);
v___x_3659_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8));
v_sz_3660_ = lean_array_size(v_args_3625_);
v___x_3661_ = ((size_t)0ULL);
v___x_3662_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_a_3657_, v_args_3625_, v_sz_3660_, v___x_3661_, v___x_3659_, v___y_3627_, v___y_3629_, v___y_3630_);
lean_dec(v_a_3657_);
if (lean_obj_tag(v___x_3662_) == 0)
{
lean_object* v_a_3663_; lean_object* v___x_3665_; uint8_t v_isShared_3666_; uint8_t v_isSharedCheck_3691_; 
v_a_3663_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3691_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3691_ == 0)
{
v___x_3665_ = v___x_3662_;
v_isShared_3666_ = v_isSharedCheck_3691_;
goto v_resetjp_3664_;
}
else
{
lean_inc(v_a_3663_);
lean_dec(v___x_3662_);
v___x_3665_ = lean_box(0);
v_isShared_3666_ = v_isSharedCheck_3691_;
goto v_resetjp_3664_;
}
v_resetjp_3664_:
{
lean_object* v_fst_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3689_; 
v_fst_3667_ = lean_ctor_get(v_a_3663_, 0);
v_isSharedCheck_3689_ = !lean_is_exclusive(v_a_3663_);
if (v_isSharedCheck_3689_ == 0)
{
lean_object* v_unused_3690_; 
v_unused_3690_ = lean_ctor_get(v_a_3663_, 1);
lean_dec(v_unused_3690_);
v___x_3669_ = v_a_3663_;
v_isShared_3670_ = v_isSharedCheck_3689_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_fst_3667_);
lean_dec(v_a_3663_);
v___x_3669_ = lean_box(0);
v_isShared_3670_ = v_isSharedCheck_3689_;
goto v_resetjp_3668_;
}
v_resetjp_3668_:
{
lean_object* v___x_3671_; uint8_t v___x_3672_; 
v___x_3671_ = lean_array_get_size(v_fst_3667_);
v___x_3672_ = lean_nat_dec_eq(v___x_3671_, v___x_3649_);
if (v___x_3672_ == 0)
{
lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; lean_object* v___x_3678_; 
lean_del_object(v___x_3665_);
v___x_3673_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10);
v___x_3674_ = l_Nat_reprFast(v___x_3671_);
v___x_3675_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3675_, 0, v___x_3674_);
v___x_3676_ = l_Lean_MessageData_ofFormat(v___x_3675_);
if (v_isShared_3670_ == 0)
{
lean_ctor_set_tag(v___x_3669_, 7);
lean_ctor_set(v___x_3669_, 1, v___x_3676_);
lean_ctor_set(v___x_3669_, 0, v___x_3673_);
v___x_3678_ = v___x_3669_;
goto v_reusejp_3677_;
}
else
{
lean_object* v_reuseFailAlloc_3684_; 
v_reuseFailAlloc_3684_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3684_, 0, v___x_3673_);
lean_ctor_set(v_reuseFailAlloc_3684_, 1, v___x_3676_);
v___x_3678_ = v_reuseFailAlloc_3684_;
goto v_reusejp_3677_;
}
v_reusejp_3677_:
{
lean_object* v___x_3679_; lean_object* v___x_3680_; uint8_t v___x_3681_; 
v___x_3679_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12);
v___x_3680_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3680_, 0, v___x_3678_);
lean_ctor_set(v___x_3680_, 1, v___x_3679_);
v___x_3681_ = lean_nat_dec_eq(v___x_3671_, v___x_3658_);
if (v___x_3681_ == 0)
{
lean_object* v___x_3682_; 
v___x_3682_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13));
v___y_3633_ = v___x_3680_;
v___y_3634_ = v_fst_3667_;
v___y_3635_ = v___x_3682_;
goto v___jp_3632_;
}
else
{
lean_object* v___x_3683_; 
v___x_3683_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___y_3633_ = v___x_3680_;
v___y_3634_ = v_fst_3667_;
v___y_3635_ = v___x_3683_;
goto v___jp_3632_;
}
}
}
else
{
lean_object* v___x_3685_; lean_object* v___x_3687_; 
lean_del_object(v___x_3669_);
lean_dec(v_fst_3667_);
v___x_3685_ = lean_box(0);
if (v_isShared_3666_ == 0)
{
lean_ctor_set(v___x_3665_, 0, v___x_3685_);
v___x_3687_ = v___x_3665_;
goto v_reusejp_3686_;
}
else
{
lean_object* v_reuseFailAlloc_3688_; 
v_reuseFailAlloc_3688_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3688_, 0, v___x_3685_);
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
else
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3699_; 
v_a_3692_ = lean_ctor_get(v___x_3662_, 0);
v_isSharedCheck_3699_ = !lean_is_exclusive(v___x_3662_);
if (v_isSharedCheck_3699_ == 0)
{
v___x_3694_ = v___x_3662_;
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3662_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3699_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v___x_3697_; 
if (v_isShared_3695_ == 0)
{
v___x_3697_ = v___x_3694_;
goto v_reusejp_3696_;
}
else
{
lean_object* v_reuseFailAlloc_3698_; 
v_reuseFailAlloc_3698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3698_, 0, v_a_3692_);
v___x_3697_ = v_reuseFailAlloc_3698_;
goto v_reusejp_3696_;
}
v_reusejp_3696_:
{
return v___x_3697_;
}
}
}
}
else
{
lean_object* v_a_3700_; lean_object* v___x_3702_; uint8_t v_isShared_3703_; uint8_t v_isSharedCheck_3707_; 
v_a_3700_ = lean_ctor_get(v___x_3656_, 0);
v_isSharedCheck_3707_ = !lean_is_exclusive(v___x_3656_);
if (v_isSharedCheck_3707_ == 0)
{
v___x_3702_ = v___x_3656_;
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
else
{
lean_inc(v_a_3700_);
lean_dec(v___x_3656_);
v___x_3702_ = lean_box(0);
v_isShared_3703_ = v_isSharedCheck_3707_;
goto v_resetjp_3701_;
}
v_resetjp_3701_:
{
lean_object* v___x_3705_; 
if (v_isShared_3703_ == 0)
{
v___x_3705_ = v___x_3702_;
goto v_reusejp_3704_;
}
else
{
lean_object* v_reuseFailAlloc_3706_; 
v_reuseFailAlloc_3706_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3706_, 0, v_a_3700_);
v___x_3705_ = v_reuseFailAlloc_3706_;
goto v_reusejp_3704_;
}
v_reusejp_3704_:
{
return v___x_3705_;
}
}
}
}
v___jp_3708_:
{
if (lean_obj_tag(v___y_3709_) == 0)
{
lean_dec_ref_known(v___y_3709_, 1);
goto v___jp_3654_;
}
else
{
lean_dec(v___x_3653_);
return v___y_3709_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v___x_3715_, lean_object* v___x_3716_, lean_object* v_args_3717_, lean_object* v_ty_3718_, lean_object* v___y_3719_, lean_object* v___y_3720_, lean_object* v___y_3721_, lean_object* v___y_3722_, lean_object* v___y_3723_){
_start:
{
lean_object* v_res_3724_; 
v_res_3724_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v___x_3715_, v___x_3716_, v_args_3717_, v_ty_3718_, v___y_3719_, v___y_3720_, v___y_3721_, v___y_3722_);
lean_dec(v___y_3722_);
lean_dec_ref(v___y_3721_);
lean_dec(v___y_3720_);
lean_dec_ref(v___y_3719_);
lean_dec_ref(v_args_3717_);
lean_dec_ref(v___x_3716_);
return v_res_3724_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object* v_e_3725_){
_start:
{
lean_object* v___x_3726_; 
v___x_3726_ = l_Lean_Expr_cleanupAnnotations(v_e_3725_);
switch(lean_obj_tag(v___x_3726_))
{
case 7:
{
lean_object* v_body_3727_; uint8_t v_binderInfo_3728_; uint8_t v___x_3729_; 
v_body_3727_ = lean_ctor_get(v___x_3726_, 2);
lean_inc_ref(v_body_3727_);
v_binderInfo_3728_ = lean_ctor_get_uint8(v___x_3726_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3726_, 3);
v___x_3729_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3728_);
if (v___x_3729_ == 0)
{
lean_object* v___x_3730_; uint8_t v___x_3731_; 
v___x_3730_ = lean_unsigned_to_nat(0u);
v___x_3731_ = lean_expr_has_loose_bvar(v_body_3727_, v___x_3730_);
if (v___x_3731_ == 0)
{
uint8_t v___x_3732_; 
lean_dec_ref(v_body_3727_);
v___x_3732_ = 1;
return v___x_3732_;
}
else
{
v_e_3725_ = v_body_3727_;
goto _start;
}
}
else
{
v_e_3725_ = v_body_3727_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3735_; 
v_body_3735_ = lean_ctor_get(v___x_3726_, 3);
lean_inc_ref(v_body_3735_);
lean_dec_ref_known(v___x_3726_, 4);
v_e_3725_ = v_body_3735_;
goto _start;
}
default: 
{
uint8_t v___x_3737_; 
lean_dec_ref(v___x_3726_);
v___x_3737_ = 0;
return v___x_3737_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object* v_e_3738_){
_start:
{
uint8_t v_res_3739_; lean_object* v_r_3740_; 
v_res_3739_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(v_e_3738_);
v_r_3740_ = lean_box(v_res_3739_);
return v_r_3740_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_cinfo_3741_, lean_object* v_a_3742_, lean_object* v_a_3743_, lean_object* v_a_3744_, lean_object* v_a_3745_){
_start:
{
lean_object* v___x_3747_; uint8_t v___x_3748_; 
v___x_3747_ = l_Lean_ConstantInfo_type(v_cinfo_3741_);
lean_inc_ref(v___x_3747_);
v___x_3748_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__4(v___x_3747_);
if (v___x_3748_ == 0)
{
lean_object* v___x_3749_; lean_object* v___x_3750_; 
lean_dec_ref(v___x_3747_);
v___x_3749_ = lean_box(0);
v___x_3750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3750_, 0, v___x_3749_);
return v___x_3750_;
}
else
{
lean_object* v___x_3751_; lean_object* v___f_3752_; uint8_t v___x_3753_; lean_object* v___x_3754_; 
v___x_3751_ = lean_box(1);
lean_inc_ref(v___x_3747_);
v___f_3752_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_3752_, 0, v___x_3751_);
lean_closure_set(v___f_3752_, 1, v___x_3747_);
v___x_3753_ = 0;
v___x_3754_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v___x_3747_, v___f_3752_, v___x_3753_, v_a_3742_, v_a_3743_, v_a_3744_, v_a_3745_);
return v___x_3754_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_cinfo_3755_, lean_object* v_a_3756_, lean_object* v_a_3757_, lean_object* v_a_3758_, lean_object* v_a_3759_, lean_object* v_a_3760_){
_start:
{
lean_object* v_res_3761_; 
v_res_3761_ = l_Lean_Meta_checkImpossibleInstance(v_cinfo_3755_, v_a_3756_, v_a_3757_, v_a_3758_, v_a_3759_);
lean_dec(v_a_3759_);
lean_dec_ref(v_a_3758_);
lean_dec(v_a_3757_);
lean_dec_ref(v_a_3756_);
lean_dec_ref(v_cinfo_3755_);
return v_res_3761_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object* v_00_u03b2_3762_, lean_object* v_k_3763_, lean_object* v_t_3764_){
_start:
{
uint8_t v___x_3765_; 
v___x_3765_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___redArg(v_k_3763_, v_t_3764_);
return v___x_3765_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_00_u03b2_3766_, lean_object* v_k_3767_, lean_object* v_t_3768_){
_start:
{
uint8_t v_res_3769_; lean_object* v_r_3770_; 
v_res_3769_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_00_u03b2_3766_, v_k_3767_, v_t_3768_);
lean_dec(v_t_3768_);
lean_dec(v_k_3767_);
v_r_3770_ = lean_box(v_res_3769_);
return v_r_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v_a_3771_, lean_object* v_as_3772_, size_t v_sz_3773_, size_t v_i_3774_, lean_object* v_b_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_){
_start:
{
lean_object* v___x_3781_; 
v___x_3781_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_a_3771_, v_as_3772_, v_sz_3773_, v_i_3774_, v_b_3775_, v___y_3776_, v___y_3778_, v___y_3779_);
return v___x_3781_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v_a_3782_, lean_object* v_as_3783_, lean_object* v_sz_3784_, lean_object* v_i_3785_, lean_object* v_b_3786_, lean_object* v___y_3787_, lean_object* v___y_3788_, lean_object* v___y_3789_, lean_object* v___y_3790_, lean_object* v___y_3791_){
_start:
{
size_t v_sz_boxed_3792_; size_t v_i_boxed_3793_; lean_object* v_res_3794_; 
v_sz_boxed_3792_ = lean_unbox_usize(v_sz_3784_);
lean_dec(v_sz_3784_);
v_i_boxed_3793_ = lean_unbox_usize(v_i_3785_);
lean_dec(v_i_3785_);
v_res_3794_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__1(v_a_3782_, v_as_3783_, v_sz_boxed_3792_, v_i_boxed_3793_, v_b_3786_, v___y_3787_, v___y_3788_, v___y_3789_, v___y_3790_);
lean_dec(v___y_3790_);
lean_dec_ref(v___y_3789_);
lean_dec(v___y_3788_);
lean_dec_ref(v___y_3787_);
lean_dec_ref(v_as_3783_);
lean_dec_ref(v_a_3782_);
return v_res_3794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object* v_as_3795_, size_t v_sz_3796_, size_t v_i_3797_, lean_object* v_b_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_, lean_object* v___y_3802_, lean_object* v___y_3803_){
_start:
{
lean_object* v___x_3805_; 
v___x_3805_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___redArg(v_as_3795_, v_sz_3796_, v_i_3797_, v_b_3798_, v___y_3799_, v___y_3800_, v___y_3802_, v___y_3803_);
return v___x_3805_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object* v_as_3806_, lean_object* v_sz_3807_, lean_object* v_i_3808_, lean_object* v_b_3809_, lean_object* v___y_3810_, lean_object* v___y_3811_, lean_object* v___y_3812_, lean_object* v___y_3813_, lean_object* v___y_3814_, lean_object* v___y_3815_){
_start:
{
size_t v_sz_boxed_3816_; size_t v_i_boxed_3817_; lean_object* v_res_3818_; 
v_sz_boxed_3816_ = lean_unbox_usize(v_sz_3807_);
lean_dec(v_sz_3807_);
v_i_boxed_3817_ = lean_unbox_usize(v_i_3808_);
lean_dec(v_i_3808_);
v_res_3818_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__3(v_as_3806_, v_sz_boxed_3816_, v_i_boxed_3817_, v_b_3809_, v___y_3810_, v___y_3811_, v___y_3812_, v___y_3813_, v___y_3814_);
lean_dec(v___y_3814_);
lean_dec_ref(v___y_3813_);
lean_dec(v___y_3812_);
lean_dec_ref(v___y_3811_);
lean_dec(v___y_3810_);
lean_dec_ref(v_as_3806_);
return v_res_3818_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3820_; lean_object* v___x_3821_; 
v___x_3820_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3821_ = l_Lean_stringToMessageData(v___x_3820_);
return v___x_3821_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3823_; lean_object* v___x_3824_; 
v___x_3823_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3824_ = l_Lean_stringToMessageData(v___x_3823_);
return v___x_3824_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3826_; lean_object* v___x_3827_; 
v___x_3826_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3827_ = l_Lean_stringToMessageData(v___x_3826_);
return v___x_3827_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_c_3828_, lean_object* v_x_3829_, lean_object* v_target_3830_, lean_object* v___y_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_){
_start:
{
lean_object* v___x_3836_; 
lean_inc_ref(v_target_3830_);
v___x_3836_ = l_Lean_Meta_isClass_x3f(v_target_3830_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
if (lean_obj_tag(v___x_3836_) == 0)
{
lean_object* v_a_3837_; lean_object* v___x_3839_; uint8_t v_isShared_3840_; uint8_t v_isSharedCheck_3855_; 
v_a_3837_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3855_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3855_ == 0)
{
v___x_3839_ = v___x_3836_;
v_isShared_3840_ = v_isSharedCheck_3855_;
goto v_resetjp_3838_;
}
else
{
lean_inc(v_a_3837_);
lean_dec(v___x_3836_);
v___x_3839_ = lean_box(0);
v_isShared_3840_ = v_isSharedCheck_3855_;
goto v_resetjp_3838_;
}
v_resetjp_3838_:
{
if (lean_obj_tag(v_a_3837_) == 0)
{
lean_object* v___x_3841_; lean_object* v___x_3842_; lean_object* v___x_3843_; lean_object* v___x_3844_; lean_object* v___x_3845_; lean_object* v___x_3846_; lean_object* v___x_3847_; lean_object* v___x_3848_; lean_object* v___x_3849_; lean_object* v___x_3850_; 
lean_del_object(v___x_3839_);
v___x_3841_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3842_ = l_Lean_MessageData_ofExpr(v_c_3828_);
v___x_3843_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3843_, 0, v___x_3841_);
lean_ctor_set(v___x_3843_, 1, v___x_3842_);
v___x_3844_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3845_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3845_, 0, v___x_3843_);
lean_ctor_set(v___x_3845_, 1, v___x_3844_);
v___x_3846_ = l_Lean_MessageData_ofExpr(v_target_3830_);
v___x_3847_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3847_, 0, v___x_3845_);
lean_ctor_set(v___x_3847_, 1, v___x_3846_);
v___x_3848_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3849_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3849_, 0, v___x_3847_);
lean_ctor_set(v___x_3849_, 1, v___x_3848_);
v___x_3850_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3849_, v___y_3831_, v___y_3832_, v___y_3833_, v___y_3834_);
return v___x_3850_;
}
else
{
lean_object* v___x_3851_; lean_object* v___x_3853_; 
lean_dec_ref_known(v_a_3837_, 1);
lean_dec_ref(v_target_3830_);
lean_dec_ref(v_c_3828_);
v___x_3851_ = lean_box(0);
if (v_isShared_3840_ == 0)
{
lean_ctor_set(v___x_3839_, 0, v___x_3851_);
v___x_3853_ = v___x_3839_;
goto v_reusejp_3852_;
}
else
{
lean_object* v_reuseFailAlloc_3854_; 
v_reuseFailAlloc_3854_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3854_, 0, v___x_3851_);
v___x_3853_ = v_reuseFailAlloc_3854_;
goto v_reusejp_3852_;
}
v_reusejp_3852_:
{
return v___x_3853_;
}
}
}
}
else
{
lean_object* v_a_3856_; lean_object* v___x_3858_; uint8_t v_isShared_3859_; uint8_t v_isSharedCheck_3863_; 
lean_dec_ref(v_target_3830_);
lean_dec_ref(v_c_3828_);
v_a_3856_ = lean_ctor_get(v___x_3836_, 0);
v_isSharedCheck_3863_ = !lean_is_exclusive(v___x_3836_);
if (v_isSharedCheck_3863_ == 0)
{
v___x_3858_ = v___x_3836_;
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
else
{
lean_inc(v_a_3856_);
lean_dec(v___x_3836_);
v___x_3858_ = lean_box(0);
v_isShared_3859_ = v_isSharedCheck_3863_;
goto v_resetjp_3857_;
}
v_resetjp_3857_:
{
lean_object* v___x_3861_; 
if (v_isShared_3859_ == 0)
{
v___x_3861_ = v___x_3858_;
goto v_reusejp_3860_;
}
else
{
lean_object* v_reuseFailAlloc_3862_; 
v_reuseFailAlloc_3862_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3862_, 0, v_a_3856_);
v___x_3861_ = v_reuseFailAlloc_3862_;
goto v_reusejp_3860_;
}
v_reusejp_3860_:
{
return v___x_3861_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_c_3864_, lean_object* v_x_3865_, lean_object* v_target_3866_, lean_object* v___y_3867_, lean_object* v___y_3868_, lean_object* v___y_3869_, lean_object* v___y_3870_, lean_object* v___y_3871_){
_start:
{
lean_object* v_res_3872_; 
v_res_3872_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_c_3864_, v_x_3865_, v_target_3866_, v___y_3867_, v___y_3868_, v___y_3869_, v___y_3870_);
lean_dec(v___y_3870_);
lean_dec_ref(v___y_3869_);
lean_dec(v___y_3868_);
lean_dec_ref(v___y_3867_);
lean_dec_ref(v_x_3865_);
return v_res_3872_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_c_3873_, lean_object* v_a_3874_, lean_object* v_a_3875_, lean_object* v_a_3876_, lean_object* v_a_3877_){
_start:
{
lean_object* v___x_3879_; 
lean_inc(v_a_3877_);
lean_inc_ref(v_a_3876_);
lean_inc(v_a_3875_);
lean_inc_ref(v_a_3874_);
lean_inc_ref(v_c_3873_);
v___x_3879_ = lean_infer_type(v_c_3873_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_);
if (lean_obj_tag(v___x_3879_) == 0)
{
lean_object* v_a_3880_; lean_object* v___f_3881_; uint8_t v___x_3882_; lean_object* v___x_3883_; 
v_a_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc(v_a_3880_);
lean_dec_ref_known(v___x_3879_, 1);
v___f_3881_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3881_, 0, v_c_3873_);
v___x_3882_ = 0;
v___x_3883_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3880_, v___f_3881_, v___x_3882_, v___x_3882_, v_a_3874_, v_a_3875_, v_a_3876_, v_a_3877_);
return v___x_3883_;
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_dec_ref(v_c_3873_);
v_a_3884_ = lean_ctor_get(v___x_3879_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3879_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3879_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3879_);
v___x_3886_ = lean_box(0);
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
v_resetjp_3885_:
{
lean_object* v___x_3889_; 
if (v_isShared_3887_ == 0)
{
v___x_3889_ = v___x_3886_;
goto v_reusejp_3888_;
}
else
{
lean_object* v_reuseFailAlloc_3890_; 
v_reuseFailAlloc_3890_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3890_, 0, v_a_3884_);
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
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_c_3892_, lean_object* v_a_3893_, lean_object* v_a_3894_, lean_object* v_a_3895_, lean_object* v_a_3896_, lean_object* v_a_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_Meta_checkNonClassInstance(v_c_3892_, v_a_3893_, v_a_3894_, v_a_3895_, v_a_3896_);
lean_dec(v_a_3896_);
lean_dec_ref(v_a_3895_);
lean_dec(v_a_3894_);
lean_dec_ref(v_a_3893_);
return v_res_3898_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3909_, lean_object* v___y_3910_){
_start:
{
lean_object* v___x_3912_; lean_object* v_env_3913_; lean_object* v___x_3914_; lean_object* v___x_3915_; 
v___x_3912_ = lean_st_ref_get(v___y_3910_);
v_env_3913_ = lean_ctor_get(v___x_3912_, 0);
lean_inc_ref(v_env_3913_);
lean_dec(v___x_3912_);
v___x_3914_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3913_, v_declName_3909_);
v___x_3915_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3915_, 0, v___x_3914_);
return v___x_3915_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3916_, lean_object* v___y_3917_, lean_object* v___y_3918_){
_start:
{
lean_object* v_res_3919_; 
v_res_3919_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3916_, v___y_3917_);
lean_dec(v___y_3917_);
return v_res_3919_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3920_, lean_object* v___y_3921_, lean_object* v___y_3922_, lean_object* v___y_3923_, lean_object* v___y_3924_){
_start:
{
lean_object* v___x_3926_; 
v___x_3926_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3920_, v___y_3924_);
return v___x_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3927_, lean_object* v___y_3928_, lean_object* v___y_3929_, lean_object* v___y_3930_, lean_object* v___y_3931_, lean_object* v___y_3932_){
_start:
{
lean_object* v_res_3933_; 
v_res_3933_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3927_, v___y_3928_, v___y_3929_, v___y_3930_, v___y_3931_);
lean_dec(v___y_3931_);
lean_dec_ref(v___y_3930_);
lean_dec(v___y_3929_);
lean_dec_ref(v___y_3928_);
return v_res_3933_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3934_; 
v___x_3934_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3934_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3935_; lean_object* v___x_3936_; 
v___x_3935_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3936_, 0, v___x_3935_);
return v___x_3936_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3937_; lean_object* v___x_3938_; 
v___x_3937_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3938_, 0, v___x_3937_);
lean_ctor_set(v___x_3938_, 1, v___x_3937_);
return v___x_3938_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3939_; lean_object* v___x_3940_; 
v___x_3939_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3940_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3940_, 0, v___x_3939_);
lean_ctor_set(v___x_3940_, 1, v___x_3939_);
lean_ctor_set(v___x_3940_, 2, v___x_3939_);
lean_ctor_set(v___x_3940_, 3, v___x_3939_);
lean_ctor_set(v___x_3940_, 4, v___x_3939_);
lean_ctor_set(v___x_3940_, 5, v___x_3939_);
return v___x_3940_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3941_, lean_object* v_b_3942_, uint8_t v_kind_3943_, lean_object* v___y_3944_, lean_object* v___y_3945_, lean_object* v___y_3946_){
_start:
{
lean_object* v_currNamespace_3948_; lean_object* v___x_3949_; lean_object* v_env_3950_; lean_object* v_nextMacroScope_3951_; lean_object* v_ngen_3952_; lean_object* v_auxDeclNGen_3953_; lean_object* v_traceState_3954_; lean_object* v_messages_3955_; lean_object* v_infoState_3956_; lean_object* v_snapshotTasks_3957_; lean_object* v___x_3959_; uint8_t v_isShared_3960_; uint8_t v_isSharedCheck_3984_; 
v_currNamespace_3948_ = lean_ctor_get(v___y_3945_, 5);
v___x_3949_ = lean_st_ref_take(v___y_3946_);
v_env_3950_ = lean_ctor_get(v___x_3949_, 0);
v_nextMacroScope_3951_ = lean_ctor_get(v___x_3949_, 1);
v_ngen_3952_ = lean_ctor_get(v___x_3949_, 2);
v_auxDeclNGen_3953_ = lean_ctor_get(v___x_3949_, 3);
v_traceState_3954_ = lean_ctor_get(v___x_3949_, 4);
v_messages_3955_ = lean_ctor_get(v___x_3949_, 6);
v_infoState_3956_ = lean_ctor_get(v___x_3949_, 7);
v_snapshotTasks_3957_ = lean_ctor_get(v___x_3949_, 8);
v_isSharedCheck_3984_ = !lean_is_exclusive(v___x_3949_);
if (v_isSharedCheck_3984_ == 0)
{
lean_object* v_unused_3985_; 
v_unused_3985_ = lean_ctor_get(v___x_3949_, 5);
lean_dec(v_unused_3985_);
v___x_3959_ = v___x_3949_;
v_isShared_3960_ = v_isSharedCheck_3984_;
goto v_resetjp_3958_;
}
else
{
lean_inc(v_snapshotTasks_3957_);
lean_inc(v_infoState_3956_);
lean_inc(v_messages_3955_);
lean_inc(v_traceState_3954_);
lean_inc(v_auxDeclNGen_3953_);
lean_inc(v_ngen_3952_);
lean_inc(v_nextMacroScope_3951_);
lean_inc(v_env_3950_);
lean_dec(v___x_3949_);
v___x_3959_ = lean_box(0);
v_isShared_3960_ = v_isSharedCheck_3984_;
goto v_resetjp_3958_;
}
v_resetjp_3958_:
{
lean_object* v___x_3961_; lean_object* v___x_3962_; lean_object* v___x_3964_; 
lean_inc(v_currNamespace_3948_);
v___x_3961_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3950_, v_ext_3941_, v_b_3942_, v_kind_3943_, v_currNamespace_3948_);
v___x_3962_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3960_ == 0)
{
lean_ctor_set(v___x_3959_, 5, v___x_3962_);
lean_ctor_set(v___x_3959_, 0, v___x_3961_);
v___x_3964_ = v___x_3959_;
goto v_reusejp_3963_;
}
else
{
lean_object* v_reuseFailAlloc_3983_; 
v_reuseFailAlloc_3983_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3983_, 0, v___x_3961_);
lean_ctor_set(v_reuseFailAlloc_3983_, 1, v_nextMacroScope_3951_);
lean_ctor_set(v_reuseFailAlloc_3983_, 2, v_ngen_3952_);
lean_ctor_set(v_reuseFailAlloc_3983_, 3, v_auxDeclNGen_3953_);
lean_ctor_set(v_reuseFailAlloc_3983_, 4, v_traceState_3954_);
lean_ctor_set(v_reuseFailAlloc_3983_, 5, v___x_3962_);
lean_ctor_set(v_reuseFailAlloc_3983_, 6, v_messages_3955_);
lean_ctor_set(v_reuseFailAlloc_3983_, 7, v_infoState_3956_);
lean_ctor_set(v_reuseFailAlloc_3983_, 8, v_snapshotTasks_3957_);
v___x_3964_ = v_reuseFailAlloc_3983_;
goto v_reusejp_3963_;
}
v_reusejp_3963_:
{
lean_object* v___x_3965_; lean_object* v___x_3966_; lean_object* v_mctx_3967_; lean_object* v_zetaDeltaFVarIds_3968_; lean_object* v_postponed_3969_; lean_object* v_diag_3970_; lean_object* v___x_3972_; uint8_t v_isShared_3973_; uint8_t v_isSharedCheck_3981_; 
v___x_3965_ = lean_st_ref_put(v___y_3946_, v___x_3964_);
v___x_3966_ = lean_st_ref_take(v___y_3944_);
v_mctx_3967_ = lean_ctor_get(v___x_3966_, 0);
v_zetaDeltaFVarIds_3968_ = lean_ctor_get(v___x_3966_, 2);
v_postponed_3969_ = lean_ctor_get(v___x_3966_, 3);
v_diag_3970_ = lean_ctor_get(v___x_3966_, 4);
v_isSharedCheck_3981_ = !lean_is_exclusive(v___x_3966_);
if (v_isSharedCheck_3981_ == 0)
{
lean_object* v_unused_3982_; 
v_unused_3982_ = lean_ctor_get(v___x_3966_, 1);
lean_dec(v_unused_3982_);
v___x_3972_ = v___x_3966_;
v_isShared_3973_ = v_isSharedCheck_3981_;
goto v_resetjp_3971_;
}
else
{
lean_inc(v_diag_3970_);
lean_inc(v_postponed_3969_);
lean_inc(v_zetaDeltaFVarIds_3968_);
lean_inc(v_mctx_3967_);
lean_dec(v___x_3966_);
v___x_3972_ = lean_box(0);
v_isShared_3973_ = v_isSharedCheck_3981_;
goto v_resetjp_3971_;
}
v_resetjp_3971_:
{
lean_object* v___x_3974_; lean_object* v___x_3976_; 
v___x_3974_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3973_ == 0)
{
lean_ctor_set(v___x_3972_, 1, v___x_3974_);
v___x_3976_ = v___x_3972_;
goto v_reusejp_3975_;
}
else
{
lean_object* v_reuseFailAlloc_3980_; 
v_reuseFailAlloc_3980_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3980_, 0, v_mctx_3967_);
lean_ctor_set(v_reuseFailAlloc_3980_, 1, v___x_3974_);
lean_ctor_set(v_reuseFailAlloc_3980_, 2, v_zetaDeltaFVarIds_3968_);
lean_ctor_set(v_reuseFailAlloc_3980_, 3, v_postponed_3969_);
lean_ctor_set(v_reuseFailAlloc_3980_, 4, v_diag_3970_);
v___x_3976_ = v_reuseFailAlloc_3980_;
goto v_reusejp_3975_;
}
v_reusejp_3975_:
{
lean_object* v___x_3977_; lean_object* v___x_3978_; lean_object* v___x_3979_; 
v___x_3977_ = lean_st_ref_put(v___y_3944_, v___x_3976_);
v___x_3978_ = lean_box(0);
v___x_3979_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3979_, 0, v___x_3978_);
return v___x_3979_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3986_, lean_object* v_b_3987_, lean_object* v_kind_3988_, lean_object* v___y_3989_, lean_object* v___y_3990_, lean_object* v___y_3991_, lean_object* v___y_3992_){
_start:
{
uint8_t v_kind_boxed_3993_; lean_object* v_res_3994_; 
v_kind_boxed_3993_ = lean_unbox(v_kind_3988_);
v_res_3994_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3986_, v_b_3987_, v_kind_boxed_3993_, v___y_3989_, v___y_3990_, v___y_3991_);
lean_dec(v___y_3991_);
lean_dec_ref(v___y_3990_);
lean_dec(v___y_3989_);
return v_res_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3995_, lean_object* v_00_u03b2_3996_, lean_object* v_00_u03c3_3997_, lean_object* v_ext_3998_, lean_object* v_b_3999_, uint8_t v_kind_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_, lean_object* v___y_4004_){
_start:
{
lean_object* v___x_4006_; 
v___x_4006_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3998_, v_b_3999_, v_kind_4000_, v___y_4002_, v___y_4003_, v___y_4004_);
return v___x_4006_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_4007_, lean_object* v_00_u03b2_4008_, lean_object* v_00_u03c3_4009_, lean_object* v_ext_4010_, lean_object* v_b_4011_, lean_object* v_kind_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
uint8_t v_kind_boxed_4018_; lean_object* v_res_4019_; 
v_kind_boxed_4018_ = lean_unbox(v_kind_4012_);
v_res_4019_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_4007_, v_00_u03b2_4008_, v_00_u03c3_4009_, v_ext_4010_, v_b_4011_, v_kind_boxed_4018_, v___y_4013_, v___y_4014_, v___y_4015_, v___y_4016_);
lean_dec(v___y_4016_);
lean_dec_ref(v___y_4015_);
lean_dec(v___y_4014_);
lean_dec_ref(v___y_4013_);
return v_res_4019_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_4020_, lean_object* v___y_4021_){
_start:
{
lean_object* v___x_4023_; lean_object* v_env_4024_; uint8_t v___x_4025_; lean_object* v___x_4026_; lean_object* v___x_4027_; 
v___x_4023_ = lean_st_ref_get(v___y_4021_);
v_env_4024_ = lean_ctor_get(v___x_4023_, 0);
lean_inc_ref(v_env_4024_);
lean_dec(v___x_4023_);
v___x_4025_ = l_Lean_getReducibilityStatusCore(v_env_4024_, v_declName_4020_);
v___x_4026_ = lean_box(v___x_4025_);
v___x_4027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4027_, 0, v___x_4026_);
return v___x_4027_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_4028_, lean_object* v___y_4029_, lean_object* v___y_4030_){
_start:
{
lean_object* v_res_4031_; 
v_res_4031_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4028_, v___y_4029_);
lean_dec(v___y_4029_);
return v_res_4031_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_, lean_object* v___y_4036_){
_start:
{
lean_object* v___x_4038_; 
v___x_4038_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4032_, v___y_4036_);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
return v_res_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_4046_, lean_object* v_msg_4047_, lean_object* v___y_4048_, lean_object* v___y_4049_, lean_object* v___y_4050_, lean_object* v___y_4051_){
_start:
{
lean_object* v_toCold_4053_; lean_object* v_options_4054_; lean_object* v_currRecDepth_4055_; lean_object* v_maxRecDepth_4056_; lean_object* v_ref_4057_; lean_object* v_currNamespace_4058_; lean_object* v_openDecls_4059_; lean_object* v_initHeartbeats_4060_; lean_object* v_maxHeartbeats_4061_; lean_object* v_currMacroScope_4062_; uint8_t v_diag_4063_; uint8_t v_suppressElabErrors_4064_; lean_object* v_ref_4065_; lean_object* v___x_4066_; lean_object* v___x_4067_; 
v_toCold_4053_ = lean_ctor_get(v___y_4050_, 0);
v_options_4054_ = lean_ctor_get(v___y_4050_, 1);
v_currRecDepth_4055_ = lean_ctor_get(v___y_4050_, 2);
v_maxRecDepth_4056_ = lean_ctor_get(v___y_4050_, 3);
v_ref_4057_ = lean_ctor_get(v___y_4050_, 4);
v_currNamespace_4058_ = lean_ctor_get(v___y_4050_, 5);
v_openDecls_4059_ = lean_ctor_get(v___y_4050_, 6);
v_initHeartbeats_4060_ = lean_ctor_get(v___y_4050_, 7);
v_maxHeartbeats_4061_ = lean_ctor_get(v___y_4050_, 8);
v_currMacroScope_4062_ = lean_ctor_get(v___y_4050_, 9);
v_diag_4063_ = lean_ctor_get_uint8(v___y_4050_, sizeof(void*)*10);
v_suppressElabErrors_4064_ = lean_ctor_get_uint8(v___y_4050_, sizeof(void*)*10 + 1);
v_ref_4065_ = l_Lean_replaceRef(v_ref_4046_, v_ref_4057_);
lean_inc(v_currMacroScope_4062_);
lean_inc(v_maxHeartbeats_4061_);
lean_inc(v_initHeartbeats_4060_);
lean_inc(v_openDecls_4059_);
lean_inc(v_currNamespace_4058_);
lean_inc(v_maxRecDepth_4056_);
lean_inc(v_currRecDepth_4055_);
lean_inc_ref(v_options_4054_);
lean_inc_ref(v_toCold_4053_);
v___x_4066_ = lean_alloc_ctor(0, 10, 2);
lean_ctor_set(v___x_4066_, 0, v_toCold_4053_);
lean_ctor_set(v___x_4066_, 1, v_options_4054_);
lean_ctor_set(v___x_4066_, 2, v_currRecDepth_4055_);
lean_ctor_set(v___x_4066_, 3, v_maxRecDepth_4056_);
lean_ctor_set(v___x_4066_, 4, v_ref_4065_);
lean_ctor_set(v___x_4066_, 5, v_currNamespace_4058_);
lean_ctor_set(v___x_4066_, 6, v_openDecls_4059_);
lean_ctor_set(v___x_4066_, 7, v_initHeartbeats_4060_);
lean_ctor_set(v___x_4066_, 8, v_maxHeartbeats_4061_);
lean_ctor_set(v___x_4066_, 9, v_currMacroScope_4062_);
lean_ctor_set_uint8(v___x_4066_, sizeof(void*)*10, v_diag_4063_);
lean_ctor_set_uint8(v___x_4066_, sizeof(void*)*10 + 1, v_suppressElabErrors_4064_);
v___x_4067_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_4047_, v___y_4048_, v___y_4049_, v___x_4066_, v___y_4051_);
lean_dec_ref_known(v___x_4066_, 10);
return v___x_4067_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_4068_, lean_object* v_msg_4069_, lean_object* v___y_4070_, lean_object* v___y_4071_, lean_object* v___y_4072_, lean_object* v___y_4073_, lean_object* v___y_4074_){
_start:
{
lean_object* v_res_4075_; 
v_res_4075_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4068_, v_msg_4069_, v___y_4070_, v___y_4071_, v___y_4072_, v___y_4073_);
lean_dec(v___y_4073_);
lean_dec_ref(v___y_4072_);
lean_dec(v___y_4071_);
lean_dec_ref(v___y_4070_);
lean_dec(v_ref_4068_);
return v_res_4075_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_4076_; 
v___x_4076_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4076_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4078_, 0, v___x_4077_);
return v___x_4078_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4079_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4080_ = lean_unsigned_to_nat(0u);
v___x_4081_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4081_, 0, v___x_4080_);
lean_ctor_set(v___x_4081_, 1, v___x_4080_);
lean_ctor_set(v___x_4081_, 2, v___x_4080_);
lean_ctor_set(v___x_4081_, 3, v___x_4080_);
lean_ctor_set(v___x_4081_, 4, v___x_4079_);
lean_ctor_set(v___x_4081_, 5, v___x_4079_);
lean_ctor_set(v___x_4081_, 6, v___x_4079_);
lean_ctor_set(v___x_4081_, 7, v___x_4079_);
lean_ctor_set(v___x_4081_, 8, v___x_4079_);
lean_ctor_set(v___x_4081_, 9, v___x_4079_);
lean_ctor_set(v___x_4081_, 10, v___x_4079_);
return v___x_4081_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4082_ = lean_unsigned_to_nat(32u);
v___x_4083_ = lean_mk_empty_array_with_capacity(v___x_4082_);
v___x_4084_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4084_, 0, v___x_4083_);
return v___x_4084_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_4085_; lean_object* v___x_4086_; lean_object* v___x_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; lean_object* v___x_4090_; 
v___x_4085_ = ((size_t)5ULL);
v___x_4086_ = lean_unsigned_to_nat(0u);
v___x_4087_ = lean_unsigned_to_nat(32u);
v___x_4088_ = lean_mk_empty_array_with_capacity(v___x_4087_);
v___x_4089_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4090_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4090_, 0, v___x_4089_);
lean_ctor_set(v___x_4090_, 1, v___x_4088_);
lean_ctor_set(v___x_4090_, 2, v___x_4086_);
lean_ctor_set(v___x_4090_, 3, v___x_4086_);
lean_ctor_set_usize(v___x_4090_, 4, v___x_4085_);
return v___x_4090_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_4091_; lean_object* v___x_4092_; lean_object* v___x_4093_; lean_object* v___x_4094_; 
v___x_4091_ = lean_box(1);
v___x_4092_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_4093_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4094_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4094_, 0, v___x_4093_);
lean_ctor_set(v___x_4094_, 1, v___x_4092_);
lean_ctor_set(v___x_4094_, 2, v___x_4091_);
return v___x_4094_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_4096_; lean_object* v___x_4097_; 
v___x_4096_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_4097_ = l_Lean_stringToMessageData(v___x_4096_);
return v___x_4097_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_4100_ = l_Lean_stringToMessageData(v___x_4099_);
return v___x_4100_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4102_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_4103_ = l_Lean_stringToMessageData(v___x_4102_);
return v___x_4103_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4105_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_4106_ = l_Lean_stringToMessageData(v___x_4105_);
return v___x_4106_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_4108_; lean_object* v___x_4109_; 
v___x_4108_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_4109_ = l_Lean_stringToMessageData(v___x_4108_);
return v___x_4109_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4111_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_4112_ = l_Lean_stringToMessageData(v___x_4111_);
return v___x_4112_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_4114_; lean_object* v___x_4115_; 
v___x_4114_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_4115_ = l_Lean_stringToMessageData(v___x_4114_);
return v___x_4115_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_4116_, lean_object* v_declHint_4117_, lean_object* v___y_4118_){
_start:
{
lean_object* v___x_4120_; lean_object* v_env_4121_; uint8_t v___x_4122_; 
v___x_4120_ = lean_st_ref_get(v___y_4118_);
v_env_4121_ = lean_ctor_get(v___x_4120_, 0);
lean_inc_ref(v_env_4121_);
lean_dec(v___x_4120_);
v___x_4122_ = l_Lean_Name_isAnonymous(v_declHint_4117_);
if (v___x_4122_ == 0)
{
uint8_t v_isExporting_4123_; 
v_isExporting_4123_ = lean_ctor_get_uint8(v_env_4121_, sizeof(void*)*8);
if (v_isExporting_4123_ == 0)
{
lean_object* v___x_4124_; 
lean_dec_ref(v_env_4121_);
lean_dec(v_declHint_4117_);
v___x_4124_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4124_, 0, v_msg_4116_);
return v___x_4124_;
}
else
{
lean_object* v___x_4125_; uint8_t v___x_4126_; 
lean_inc_ref(v_env_4121_);
v___x_4125_ = l_Lean_Environment_setExporting(v_env_4121_, v___x_4122_);
lean_inc(v_declHint_4117_);
lean_inc_ref(v___x_4125_);
v___x_4126_ = l_Lean_Environment_contains(v___x_4125_, v_declHint_4117_, v_isExporting_4123_);
if (v___x_4126_ == 0)
{
lean_object* v___x_4127_; 
lean_dec_ref(v___x_4125_);
lean_dec_ref(v_env_4121_);
lean_dec(v_declHint_4117_);
v___x_4127_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4127_, 0, v_msg_4116_);
return v___x_4127_;
}
else
{
lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4132_; lean_object* v_c_4133_; lean_object* v___x_4134_; 
v___x_4128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4129_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_4130_ = l_Lean_Options_empty;
v___x_4131_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4131_, 0, v___x_4125_);
lean_ctor_set(v___x_4131_, 1, v___x_4128_);
lean_ctor_set(v___x_4131_, 2, v___x_4129_);
lean_ctor_set(v___x_4131_, 3, v___x_4130_);
lean_inc(v_declHint_4117_);
v___x_4132_ = l_Lean_MessageData_ofConstName(v_declHint_4117_, v___x_4122_);
v_c_4133_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4133_, 0, v___x_4131_);
lean_ctor_set(v_c_4133_, 1, v___x_4132_);
v___x_4134_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4121_, v_declHint_4117_);
if (lean_obj_tag(v___x_4134_) == 0)
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; 
lean_dec_ref(v_env_4121_);
lean_dec(v_declHint_4117_);
v___x_4135_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
lean_ctor_set(v___x_4136_, 1, v_c_4133_);
v___x_4137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_4138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4136_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
v___x_4139_ = l_Lean_MessageData_note(v___x_4138_);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v_msg_4116_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4140_);
return v___x_4141_;
}
else
{
lean_object* v_val_4142_; lean_object* v___x_4144_; uint8_t v_isShared_4145_; uint8_t v_isSharedCheck_4177_; 
v_val_4142_ = lean_ctor_get(v___x_4134_, 0);
v_isSharedCheck_4177_ = !lean_is_exclusive(v___x_4134_);
if (v_isSharedCheck_4177_ == 0)
{
v___x_4144_ = v___x_4134_;
v_isShared_4145_ = v_isSharedCheck_4177_;
goto v_resetjp_4143_;
}
else
{
lean_inc(v_val_4142_);
lean_dec(v___x_4134_);
v___x_4144_ = lean_box(0);
v_isShared_4145_ = v_isSharedCheck_4177_;
goto v_resetjp_4143_;
}
v_resetjp_4143_:
{
lean_object* v___x_4146_; lean_object* v___x_4147_; lean_object* v___x_4148_; lean_object* v_mod_4149_; uint8_t v___x_4150_; 
v___x_4146_ = lean_box(0);
v___x_4147_ = l_Lean_Environment_header(v_env_4121_);
lean_dec_ref(v_env_4121_);
v___x_4148_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4147_);
v_mod_4149_ = lean_array_get(v___x_4146_, v___x_4148_, v_val_4142_);
lean_dec(v_val_4142_);
lean_dec_ref(v___x_4148_);
v___x_4150_ = l_Lean_isPrivateName(v_declHint_4117_);
lean_dec(v_declHint_4117_);
if (v___x_4150_ == 0)
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v___x_4156_; lean_object* v___x_4157_; lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4162_; 
v___x_4151_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_4152_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4152_, 0, v___x_4151_);
lean_ctor_set(v___x_4152_, 1, v_c_4133_);
v___x_4153_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_4154_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4152_);
lean_ctor_set(v___x_4154_, 1, v___x_4153_);
v___x_4155_ = l_Lean_MessageData_ofName(v_mod_4149_);
v___x_4156_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4156_, 0, v___x_4154_);
lean_ctor_set(v___x_4156_, 1, v___x_4155_);
v___x_4157_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_4158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4158_, 0, v___x_4156_);
lean_ctor_set(v___x_4158_, 1, v___x_4157_);
v___x_4159_ = l_Lean_MessageData_note(v___x_4158_);
v___x_4160_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4160_, 0, v_msg_4116_);
lean_ctor_set(v___x_4160_, 1, v___x_4159_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set_tag(v___x_4144_, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4160_);
v___x_4162_ = v___x_4144_;
goto v_reusejp_4161_;
}
else
{
lean_object* v_reuseFailAlloc_4163_; 
v_reuseFailAlloc_4163_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4163_, 0, v___x_4160_);
v___x_4162_ = v_reuseFailAlloc_4163_;
goto v_reusejp_4161_;
}
v_reusejp_4161_:
{
return v___x_4162_;
}
}
else
{
lean_object* v___x_4164_; lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v___x_4172_; lean_object* v___x_4173_; lean_object* v___x_4175_; 
v___x_4164_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4165_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4165_, 0, v___x_4164_);
lean_ctor_set(v___x_4165_, 1, v_c_4133_);
v___x_4166_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_4167_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4165_);
lean_ctor_set(v___x_4167_, 1, v___x_4166_);
v___x_4168_ = l_Lean_MessageData_ofName(v_mod_4149_);
v___x_4169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4169_, 0, v___x_4167_);
lean_ctor_set(v___x_4169_, 1, v___x_4168_);
v___x_4170_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_4171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4171_, 0, v___x_4169_);
lean_ctor_set(v___x_4171_, 1, v___x_4170_);
v___x_4172_ = l_Lean_MessageData_note(v___x_4171_);
v___x_4173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4173_, 0, v_msg_4116_);
lean_ctor_set(v___x_4173_, 1, v___x_4172_);
if (v_isShared_4145_ == 0)
{
lean_ctor_set_tag(v___x_4144_, 0);
lean_ctor_set(v___x_4144_, 0, v___x_4173_);
v___x_4175_ = v___x_4144_;
goto v_reusejp_4174_;
}
else
{
lean_object* v_reuseFailAlloc_4176_; 
v_reuseFailAlloc_4176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4176_, 0, v___x_4173_);
v___x_4175_ = v_reuseFailAlloc_4176_;
goto v_reusejp_4174_;
}
v_reusejp_4174_:
{
return v___x_4175_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4178_; 
lean_dec_ref(v_env_4121_);
lean_dec(v_declHint_4117_);
v___x_4178_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4178_, 0, v_msg_4116_);
return v___x_4178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_4179_, lean_object* v_declHint_4180_, lean_object* v___y_4181_, lean_object* v___y_4182_){
_start:
{
lean_object* v_res_4183_; 
v_res_4183_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4179_, v_declHint_4180_, v___y_4181_);
lean_dec(v___y_4181_);
return v_res_4183_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(lean_object* v_msg_4184_, lean_object* v_declHint_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_, lean_object* v___y_4188_, lean_object* v___y_4189_){
_start:
{
lean_object* v___x_4191_; lean_object* v_a_4192_; lean_object* v___x_4194_; uint8_t v_isShared_4195_; uint8_t v_isSharedCheck_4201_; 
v___x_4191_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4184_, v_declHint_4185_, v___y_4189_);
v_a_4192_ = lean_ctor_get(v___x_4191_, 0);
v_isSharedCheck_4201_ = !lean_is_exclusive(v___x_4191_);
if (v_isSharedCheck_4201_ == 0)
{
v___x_4194_ = v___x_4191_;
v_isShared_4195_ = v_isSharedCheck_4201_;
goto v_resetjp_4193_;
}
else
{
lean_inc(v_a_4192_);
lean_dec(v___x_4191_);
v___x_4194_ = lean_box(0);
v_isShared_4195_ = v_isSharedCheck_4201_;
goto v_resetjp_4193_;
}
v_resetjp_4193_:
{
lean_object* v___x_4196_; lean_object* v___x_4197_; lean_object* v___x_4199_; 
v___x_4196_ = l_Lean_unknownIdentifierMessageTag;
v___x_4197_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4197_, 0, v___x_4196_);
lean_ctor_set(v___x_4197_, 1, v_a_4192_);
if (v_isShared_4195_ == 0)
{
lean_ctor_set(v___x_4194_, 0, v___x_4197_);
v___x_4199_ = v___x_4194_;
goto v_reusejp_4198_;
}
else
{
lean_object* v_reuseFailAlloc_4200_; 
v_reuseFailAlloc_4200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4200_, 0, v___x_4197_);
v___x_4199_ = v_reuseFailAlloc_4200_;
goto v_reusejp_4198_;
}
v_reusejp_4198_:
{
return v___x_4199_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_4202_, lean_object* v_declHint_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
lean_object* v_res_4209_; 
v_res_4209_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4202_, v_declHint_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
lean_dec(v___y_4207_);
lean_dec_ref(v___y_4206_);
lean_dec(v___y_4205_);
lean_dec_ref(v___y_4204_);
return v_res_4209_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_ref_4210_, lean_object* v_msg_4211_, lean_object* v_declHint_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_, lean_object* v___y_4215_, lean_object* v___y_4216_){
_start:
{
lean_object* v___x_4218_; lean_object* v_a_4219_; lean_object* v___x_4220_; 
v___x_4218_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4211_, v_declHint_4212_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
v_a_4219_ = lean_ctor_get(v___x_4218_, 0);
lean_inc(v_a_4219_);
lean_dec_ref(v___x_4218_);
v___x_4220_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4210_, v_a_4219_, v___y_4213_, v___y_4214_, v___y_4215_, v___y_4216_);
return v___x_4220_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_ref_4221_, lean_object* v_msg_4222_, lean_object* v_declHint_4223_, lean_object* v___y_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v_res_4229_; 
v_res_4229_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4221_, v_msg_4222_, v_declHint_4223_, v___y_4224_, v___y_4225_, v___y_4226_, v___y_4227_);
lean_dec(v___y_4227_);
lean_dec_ref(v___y_4226_);
lean_dec(v___y_4225_);
lean_dec_ref(v___y_4224_);
lean_dec(v_ref_4221_);
return v_res_4229_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_4231_; lean_object* v___x_4232_; 
v___x_4231_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_4232_ = l_Lean_stringToMessageData(v___x_4231_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_4233_, lean_object* v_constName_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v___x_4240_; uint8_t v___x_4241_; lean_object* v___x_4242_; lean_object* v___x_4243_; lean_object* v___x_4244_; lean_object* v___x_4245_; lean_object* v___x_4246_; 
v___x_4240_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_4241_ = 0;
lean_inc(v_constName_4234_);
v___x_4242_ = l_Lean_MessageData_ofConstName(v_constName_4234_, v___x_4241_);
v___x_4243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4243_, 0, v___x_4240_);
lean_ctor_set(v___x_4243_, 1, v___x_4242_);
v___x_4244_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4245_, 0, v___x_4243_);
lean_ctor_set(v___x_4245_, 1, v___x_4244_);
v___x_4246_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4233_, v___x_4245_, v_constName_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_);
return v___x_4246_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_4247_, lean_object* v_constName_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4247_, v_constName_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v_ref_4247_);
return v_res_4254_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_4255_, lean_object* v___y_4256_, lean_object* v___y_4257_, lean_object* v___y_4258_, lean_object* v___y_4259_){
_start:
{
lean_object* v_ref_4261_; lean_object* v___x_4262_; 
v_ref_4261_ = lean_ctor_get(v___y_4258_, 4);
v___x_4262_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4261_, v_constName_4255_, v___y_4256_, v___y_4257_, v___y_4258_, v___y_4259_);
return v___x_4262_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_){
_start:
{
lean_object* v_res_4269_; 
v_res_4269_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4263_, v___y_4264_, v___y_4265_, v___y_4266_, v___y_4267_);
lean_dec(v___y_4267_);
lean_dec_ref(v___y_4266_);
lean_dec(v___y_4265_);
lean_dec_ref(v___y_4264_);
return v_res_4269_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_4270_, lean_object* v___y_4271_, lean_object* v___y_4272_, lean_object* v___y_4273_, lean_object* v___y_4274_){
_start:
{
lean_object* v___x_4276_; lean_object* v_env_4277_; uint8_t v___x_4278_; lean_object* v___x_4279_; 
v___x_4276_ = lean_st_ref_get(v___y_4274_);
v_env_4277_ = lean_ctor_get(v___x_4276_, 0);
lean_inc_ref(v_env_4277_);
lean_dec(v___x_4276_);
v___x_4278_ = 0;
lean_inc(v_constName_4270_);
v___x_4279_ = l_Lean_Environment_find_x3f(v_env_4277_, v_constName_4270_, v___x_4278_);
if (lean_obj_tag(v___x_4279_) == 0)
{
lean_object* v___x_4280_; 
v___x_4280_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4270_, v___y_4271_, v___y_4272_, v___y_4273_, v___y_4274_);
return v___x_4280_;
}
else
{
lean_object* v_val_4281_; lean_object* v___x_4283_; uint8_t v_isShared_4284_; uint8_t v_isSharedCheck_4288_; 
lean_dec(v_constName_4270_);
v_val_4281_ = lean_ctor_get(v___x_4279_, 0);
v_isSharedCheck_4288_ = !lean_is_exclusive(v___x_4279_);
if (v_isSharedCheck_4288_ == 0)
{
v___x_4283_ = v___x_4279_;
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
else
{
lean_inc(v_val_4281_);
lean_dec(v___x_4279_);
v___x_4283_ = lean_box(0);
v_isShared_4284_ = v_isSharedCheck_4288_;
goto v_resetjp_4282_;
}
v_resetjp_4282_:
{
lean_object* v___x_4286_; 
if (v_isShared_4284_ == 0)
{
lean_ctor_set_tag(v___x_4283_, 0);
v___x_4286_ = v___x_4283_;
goto v_reusejp_4285_;
}
else
{
lean_object* v_reuseFailAlloc_4287_; 
v_reuseFailAlloc_4287_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4287_, 0, v_val_4281_);
v___x_4286_ = v_reuseFailAlloc_4287_;
goto v_reusejp_4285_;
}
v_reusejp_4285_:
{
return v___x_4286_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_, lean_object* v___y_4294_){
_start:
{
lean_object* v_res_4295_; 
v_res_4295_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_4289_, v___y_4290_, v___y_4291_, v___y_4292_, v___y_4293_);
lean_dec(v___y_4293_);
lean_dec_ref(v___y_4292_);
lean_dec(v___y_4291_);
lean_dec_ref(v___y_4290_);
return v_res_4295_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_, lean_object* v___y_4300_){
_start:
{
lean_object* v___x_4302_; lean_object* v_env_4303_; uint8_t v___x_4304_; lean_object* v___x_4305_; 
v___x_4302_ = lean_st_ref_get(v___y_4300_);
v_env_4303_ = lean_ctor_get(v___x_4302_, 0);
lean_inc_ref(v_env_4303_);
lean_dec(v___x_4302_);
v___x_4304_ = 0;
lean_inc(v_constName_4296_);
v___x_4305_ = l_Lean_Environment_findConstVal_x3f(v_env_4303_, v_constName_4296_, v___x_4304_);
if (lean_obj_tag(v___x_4305_) == 0)
{
lean_object* v___x_4306_; 
v___x_4306_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4296_, v___y_4297_, v___y_4298_, v___y_4299_, v___y_4300_);
return v___x_4306_;
}
else
{
lean_object* v_val_4307_; lean_object* v___x_4309_; uint8_t v_isShared_4310_; uint8_t v_isSharedCheck_4314_; 
lean_dec(v_constName_4296_);
v_val_4307_ = lean_ctor_get(v___x_4305_, 0);
v_isSharedCheck_4314_ = !lean_is_exclusive(v___x_4305_);
if (v_isSharedCheck_4314_ == 0)
{
v___x_4309_ = v___x_4305_;
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
else
{
lean_inc(v_val_4307_);
lean_dec(v___x_4305_);
v___x_4309_ = lean_box(0);
v_isShared_4310_ = v_isSharedCheck_4314_;
goto v_resetjp_4308_;
}
v_resetjp_4308_:
{
lean_object* v___x_4312_; 
if (v_isShared_4310_ == 0)
{
lean_ctor_set_tag(v___x_4309_, 0);
v___x_4312_ = v___x_4309_;
goto v_reusejp_4311_;
}
else
{
lean_object* v_reuseFailAlloc_4313_; 
v_reuseFailAlloc_4313_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4313_, 0, v_val_4307_);
v___x_4312_ = v_reuseFailAlloc_4313_;
goto v_reusejp_4311_;
}
v_reusejp_4311_:
{
return v___x_4312_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_, lean_object* v___y_4320_){
_start:
{
lean_object* v_res_4321_; 
v_res_4321_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4315_, v___y_4316_, v___y_4317_, v___y_4318_, v___y_4319_);
lean_dec(v___y_4319_);
lean_dec_ref(v___y_4318_);
lean_dec(v___y_4317_);
lean_dec_ref(v___y_4316_);
return v_res_4321_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4322_, lean_object* v_a_4323_){
_start:
{
if (lean_obj_tag(v_a_4322_) == 0)
{
lean_object* v___x_4324_; 
v___x_4324_ = l_List_reverse___redArg(v_a_4323_);
return v___x_4324_;
}
else
{
lean_object* v_head_4325_; lean_object* v_tail_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4335_; 
v_head_4325_ = lean_ctor_get(v_a_4322_, 0);
v_tail_4326_ = lean_ctor_get(v_a_4322_, 1);
v_isSharedCheck_4335_ = !lean_is_exclusive(v_a_4322_);
if (v_isSharedCheck_4335_ == 0)
{
v___x_4328_ = v_a_4322_;
v_isShared_4329_ = v_isSharedCheck_4335_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_tail_4326_);
lean_inc(v_head_4325_);
lean_dec(v_a_4322_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4335_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4330_; lean_object* v___x_4332_; 
v___x_4330_ = l_Lean_mkLevelParam(v_head_4325_);
if (v_isShared_4329_ == 0)
{
lean_ctor_set(v___x_4328_, 1, v_a_4323_);
lean_ctor_set(v___x_4328_, 0, v___x_4330_);
v___x_4332_ = v___x_4328_;
goto v_reusejp_4331_;
}
else
{
lean_object* v_reuseFailAlloc_4334_; 
v_reuseFailAlloc_4334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4334_, 0, v___x_4330_);
lean_ctor_set(v_reuseFailAlloc_4334_, 1, v_a_4323_);
v___x_4332_ = v_reuseFailAlloc_4334_;
goto v_reusejp_4331_;
}
v_reusejp_4331_:
{
v_a_4322_ = v_tail_4326_;
v_a_4323_ = v___x_4332_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_, lean_object* v___y_4340_){
_start:
{
lean_object* v___x_4342_; 
lean_inc(v_constName_4336_);
v___x_4342_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4336_, v___y_4337_, v___y_4338_, v___y_4339_, v___y_4340_);
if (lean_obj_tag(v___x_4342_) == 0)
{
lean_object* v_a_4343_; lean_object* v___x_4345_; uint8_t v_isShared_4346_; uint8_t v_isSharedCheck_4354_; 
v_a_4343_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4354_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4354_ == 0)
{
v___x_4345_ = v___x_4342_;
v_isShared_4346_ = v_isSharedCheck_4354_;
goto v_resetjp_4344_;
}
else
{
lean_inc(v_a_4343_);
lean_dec(v___x_4342_);
v___x_4345_ = lean_box(0);
v_isShared_4346_ = v_isSharedCheck_4354_;
goto v_resetjp_4344_;
}
v_resetjp_4344_:
{
lean_object* v_levelParams_4347_; lean_object* v___x_4348_; lean_object* v___x_4349_; lean_object* v___x_4350_; lean_object* v___x_4352_; 
v_levelParams_4347_ = lean_ctor_get(v_a_4343_, 1);
lean_inc(v_levelParams_4347_);
lean_dec(v_a_4343_);
v___x_4348_ = lean_box(0);
v___x_4349_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4347_, v___x_4348_);
v___x_4350_ = l_Lean_mkConst(v_constName_4336_, v___x_4349_);
if (v_isShared_4346_ == 0)
{
lean_ctor_set(v___x_4345_, 0, v___x_4350_);
v___x_4352_ = v___x_4345_;
goto v_reusejp_4351_;
}
else
{
lean_object* v_reuseFailAlloc_4353_; 
v_reuseFailAlloc_4353_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4353_, 0, v___x_4350_);
v___x_4352_ = v_reuseFailAlloc_4353_;
goto v_reusejp_4351_;
}
v_reusejp_4351_:
{
return v___x_4352_;
}
}
}
else
{
lean_object* v_a_4355_; lean_object* v___x_4357_; uint8_t v_isShared_4358_; uint8_t v_isSharedCheck_4362_; 
lean_dec(v_constName_4336_);
v_a_4355_ = lean_ctor_get(v___x_4342_, 0);
v_isSharedCheck_4362_ = !lean_is_exclusive(v___x_4342_);
if (v_isSharedCheck_4362_ == 0)
{
v___x_4357_ = v___x_4342_;
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
else
{
lean_inc(v_a_4355_);
lean_dec(v___x_4342_);
v___x_4357_ = lean_box(0);
v_isShared_4358_ = v_isSharedCheck_4362_;
goto v_resetjp_4356_;
}
v_resetjp_4356_:
{
lean_object* v___x_4360_; 
if (v_isShared_4358_ == 0)
{
v___x_4360_ = v___x_4357_;
goto v_reusejp_4359_;
}
else
{
lean_object* v_reuseFailAlloc_4361_; 
v_reuseFailAlloc_4361_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4361_, 0, v_a_4355_);
v___x_4360_ = v_reuseFailAlloc_4361_;
goto v_reusejp_4359_;
}
v_reusejp_4359_:
{
return v___x_4360_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_, lean_object* v___y_4366_, lean_object* v___y_4367_, lean_object* v___y_4368_){
_start:
{
lean_object* v_res_4369_; 
v_res_4369_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4363_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
lean_dec(v___y_4367_);
lean_dec_ref(v___y_4366_);
lean_dec(v___y_4365_);
lean_dec_ref(v___y_4364_);
return v_res_4369_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4371_; lean_object* v___x_4372_; 
v___x_4371_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4372_ = l_Lean_stringToMessageData(v___x_4371_);
return v___x_4372_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4374_; lean_object* v___x_4375_; 
v___x_4374_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4375_ = l_Lean_stringToMessageData(v___x_4374_);
return v___x_4375_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4377_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_4378_ = l_Lean_stringToMessageData(v___x_4377_);
return v___x_4378_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__7(void){
_start:
{
lean_object* v___x_4380_; lean_object* v___x_4381_; 
v___x_4380_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__6));
v___x_4381_ = l_Lean_stringToMessageData(v___x_4380_);
return v___x_4381_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4382_, uint8_t v_attrKind_4383_, lean_object* v_prio_4384_, lean_object* v_a_4385_, lean_object* v_a_4386_, lean_object* v_a_4387_, lean_object* v_a_4388_){
_start:
{
lean_object* v___x_4390_; 
lean_inc(v_declName_4382_);
v___x_4390_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4382_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4390_) == 0)
{
lean_object* v_a_4391_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___y_4396_; lean_object* v___y_4397_; lean_object* v___y_4421_; lean_object* v___y_4422_; lean_object* v___y_4423_; lean_object* v___y_4424_; lean_object* v___x_4469_; 
v_a_4391_ = lean_ctor_get(v___x_4390_, 0);
lean_inc(v_a_4391_);
lean_dec_ref_known(v___x_4390_, 1);
lean_inc(v_declName_4382_);
v___x_4469_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4382_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_object* v_a_4470_; lean_object* v___x_4471_; uint8_t v___x_4472_; 
v_a_4470_ = lean_ctor_get(v___x_4469_, 0);
lean_inc(v_a_4470_);
lean_dec_ref_known(v___x_4469_, 1);
v___x_4471_ = l_Lean_ConstantInfo_type(v_a_4470_);
v___x_4472_ = l_Lean_Expr_hasSorry(v___x_4471_);
lean_dec_ref(v___x_4471_);
if (v___x_4472_ == 0)
{
lean_object* v___x_4473_; 
lean_inc(v_a_4391_);
v___x_4473_ = l_Lean_Meta_checkNonClassInstance(v_a_4391_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
if (lean_obj_tag(v___x_4473_) == 0)
{
lean_object* v___x_4474_; 
lean_dec_ref_known(v___x_4473_, 1);
v___x_4474_ = l_Lean_Meta_checkImpossibleInstance(v_a_4470_, v_a_4385_, v_a_4386_, v_a_4387_, v_a_4388_);
lean_dec(v_a_4470_);
if (lean_obj_tag(v___x_4474_) == 0)
{
lean_dec_ref_known(v___x_4474_, 1);
v___y_4421_ = v_a_4385_;
v___y_4422_ = v_a_4386_;
v___y_4423_ = v_a_4387_;
v___y_4424_ = v_a_4388_;
goto v___jp_4420_;
}
else
{
lean_dec(v_a_4391_);
lean_dec(v_prio_4384_);
lean_dec(v_declName_4382_);
return v___x_4474_;
}
}
else
{
lean_dec(v_a_4470_);
lean_dec(v_a_4391_);
lean_dec(v_prio_4384_);
lean_dec(v_declName_4382_);
return v___x_4473_;
}
}
else
{
lean_dec(v_a_4470_);
v___y_4421_ = v_a_4385_;
v___y_4422_ = v_a_4386_;
v___y_4423_ = v_a_4387_;
v___y_4424_ = v_a_4388_;
goto v___jp_4420_;
}
}
else
{
lean_object* v_a_4475_; lean_object* v___x_4477_; uint8_t v_isShared_4478_; uint8_t v_isSharedCheck_4482_; 
lean_dec(v_a_4391_);
lean_dec(v_prio_4384_);
lean_dec(v_declName_4382_);
v_a_4475_ = lean_ctor_get(v___x_4469_, 0);
v_isSharedCheck_4482_ = !lean_is_exclusive(v___x_4469_);
if (v_isSharedCheck_4482_ == 0)
{
v___x_4477_ = v___x_4469_;
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
else
{
lean_inc(v_a_4475_);
lean_dec(v___x_4469_);
v___x_4477_ = lean_box(0);
v_isShared_4478_ = v_isSharedCheck_4482_;
goto v_resetjp_4476_;
}
v_resetjp_4476_:
{
lean_object* v___x_4480_; 
if (v_isShared_4478_ == 0)
{
v___x_4480_ = v___x_4477_;
goto v_reusejp_4479_;
}
else
{
lean_object* v_reuseFailAlloc_4481_; 
v_reuseFailAlloc_4481_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4481_, 0, v_a_4475_);
v___x_4480_ = v_reuseFailAlloc_4481_;
goto v_reusejp_4479_;
}
v_reusejp_4479_:
{
return v___x_4480_;
}
}
}
v___jp_4392_:
{
lean_object* v___x_4398_; lean_object* v_a_4399_; lean_object* v___x_4401_; uint8_t v_isShared_4402_; uint8_t v_isSharedCheck_4419_; 
lean_inc(v_declName_4382_);
v___x_4398_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4382_, v___y_4397_);
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
v_isSharedCheck_4419_ = !lean_is_exclusive(v___x_4398_);
if (v_isSharedCheck_4419_ == 0)
{
v___x_4401_ = v___x_4398_;
v_isShared_4402_ = v_isSharedCheck_4419_;
goto v_resetjp_4400_;
}
else
{
lean_inc(v_a_4399_);
lean_dec(v___x_4398_);
v___x_4401_ = lean_box(0);
v_isShared_4402_ = v_isSharedCheck_4419_;
goto v_resetjp_4400_;
}
v_resetjp_4400_:
{
lean_object* v___x_4403_; 
lean_inc(v_a_4391_);
v___x_4403_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4391_, v_a_4399_, v___y_4394_, v___y_4395_, v___y_4396_, v___y_4397_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; lean_object* v___x_4405_; lean_object* v___x_4407_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
v___x_4405_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4402_ == 0)
{
lean_ctor_set_tag(v___x_4401_, 1);
lean_ctor_set(v___x_4401_, 0, v_declName_4382_);
v___x_4407_ = v___x_4401_;
goto v_reusejp_4406_;
}
else
{
lean_object* v_reuseFailAlloc_4410_; 
v_reuseFailAlloc_4410_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4410_, 0, v_declName_4382_);
v___x_4407_ = v_reuseFailAlloc_4410_;
goto v_reusejp_4406_;
}
v_reusejp_4406_:
{
lean_object* v___x_4408_; lean_object* v___x_4409_; 
v___x_4408_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4408_, 0, v___y_4393_);
lean_ctor_set(v___x_4408_, 1, v_a_4391_);
lean_ctor_set(v___x_4408_, 2, v_prio_4384_);
lean_ctor_set(v___x_4408_, 3, v___x_4407_);
lean_ctor_set(v___x_4408_, 4, v_a_4404_);
lean_ctor_set_uint8(v___x_4408_, sizeof(void*)*5, v_attrKind_4383_);
v___x_4409_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4405_, v___x_4408_, v_attrKind_4383_, v___y_4395_, v___y_4396_, v___y_4397_);
return v___x_4409_;
}
}
else
{
lean_object* v_a_4411_; lean_object* v___x_4413_; uint8_t v_isShared_4414_; uint8_t v_isSharedCheck_4418_; 
lean_del_object(v___x_4401_);
lean_dec_ref(v___y_4393_);
lean_dec(v_a_4391_);
lean_dec(v_prio_4384_);
lean_dec(v_declName_4382_);
v_a_4411_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4418_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4418_ == 0)
{
v___x_4413_ = v___x_4403_;
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
else
{
lean_inc(v_a_4411_);
lean_dec(v___x_4403_);
v___x_4413_ = lean_box(0);
v_isShared_4414_ = v_isSharedCheck_4418_;
goto v_resetjp_4412_;
}
v_resetjp_4412_:
{
lean_object* v___x_4416_; 
if (v_isShared_4414_ == 0)
{
v___x_4416_ = v___x_4413_;
goto v_reusejp_4415_;
}
else
{
lean_object* v_reuseFailAlloc_4417_; 
v_reuseFailAlloc_4417_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4417_, 0, v_a_4411_);
v___x_4416_ = v_reuseFailAlloc_4417_;
goto v_reusejp_4415_;
}
v_reusejp_4415_:
{
return v___x_4416_;
}
}
}
}
}
v___jp_4420_:
{
lean_object* v___x_4425_; 
lean_inc(v_a_4391_);
v___x_4425_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4391_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4427_; lean_object* v_a_4428_; uint8_t v___x_4429_; uint8_t v___x_4430_; uint8_t v___x_4431_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4426_);
lean_dec_ref_known(v___x_4425_, 1);
lean_inc(v_declName_4382_);
v___x_4427_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4382_, v___y_4424_);
v_a_4428_ = lean_ctor_get(v___x_4427_, 0);
lean_inc(v_a_4428_);
lean_dec_ref(v___x_4427_);
v___x_4429_ = 1;
v___x_4430_ = lean_unbox(v_a_4428_);
lean_dec(v_a_4428_);
v___x_4431_ = l_Lean_instBEqReducibilityStatus_beq(v___x_4430_, v___x_4429_);
if (v___x_4431_ == 0)
{
v___y_4393_ = v_a_4426_;
v___y_4394_ = v___y_4421_;
v___y_4395_ = v___y_4422_;
v___y_4396_ = v___y_4423_;
v___y_4397_ = v___y_4424_;
goto v___jp_4392_;
}
else
{
lean_object* v___x_4432_; 
lean_inc(v_declName_4382_);
v___x_4432_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4382_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4432_) == 0)
{
lean_object* v_a_4433_; uint8_t v___x_4434_; 
v_a_4433_ = lean_ctor_get(v___x_4432_, 0);
lean_inc(v_a_4433_);
lean_dec_ref_known(v___x_4432_, 1);
v___x_4434_ = l_Lean_ConstantInfo_isDefinition(v_a_4433_);
lean_dec(v_a_4433_);
if (v___x_4434_ == 0)
{
lean_object* v___x_4435_; lean_object* v_env_4436_; uint8_t v___x_4437_; 
v___x_4435_ = lean_st_ref_get(v___y_4424_);
v_env_4436_ = lean_ctor_get(v___x_4435_, 0);
lean_inc_ref(v_env_4436_);
lean_dec(v___x_4435_);
lean_inc(v_declName_4382_);
v___x_4437_ = l_Lean_wasOriginallyDefn(v_env_4436_, v_declName_4382_);
if (v___x_4437_ == 0)
{
v___y_4393_ = v_a_4426_;
v___y_4394_ = v___y_4421_;
v___y_4395_ = v___y_4422_;
v___y_4396_ = v___y_4423_;
v___y_4397_ = v___y_4424_;
goto v___jp_4392_;
}
else
{
lean_object* v___x_4438_; lean_object* v___x_4439_; lean_object* v___x_4440_; lean_object* v___x_4441_; lean_object* v___x_4442_; lean_object* v___x_4443_; 
v___x_4438_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4382_);
v___x_4439_ = l_Lean_MessageData_ofName(v_declName_4382_);
v___x_4440_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4440_, 0, v___x_4438_);
lean_ctor_set(v___x_4440_, 1, v___x_4439_);
v___x_4441_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4442_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4442_, 0, v___x_4440_);
lean_ctor_set(v___x_4442_, 1, v___x_4441_);
v___x_4443_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(v___x_4442_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_dec_ref_known(v___x_4443_, 1);
v___y_4393_ = v_a_4426_;
v___y_4394_ = v___y_4421_;
v___y_4395_ = v___y_4422_;
v___y_4396_ = v___y_4423_;
v___y_4397_ = v___y_4424_;
goto v___jp_4392_;
}
else
{
lean_dec(v_a_4426_);
lean_dec(v_a_4391_);
lean_dec(v_prio_4384_);
lean_dec(v_declName_4382_);
return v___x_4443_;
}
}
}
else
{
lean_object* v_options_4444_; lean_object* v___x_4445_; uint8_t v___x_4446_; 
v_options_4444_ = lean_ctor_get(v___y_4423_, 1);
v___x_4445_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility));
v___x_4446_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_4444_, v___x_4445_);
if (v___x_4446_ == 0)
{
v___y_4393_ = v_a_4426_;
v___y_4394_ = v___y_4421_;
v___y_4395_ = v___y_4422_;
v___y_4396_ = v___y_4423_;
v___y_4397_ = v___y_4424_;
goto v___jp_4392_;
}
else
{
lean_object* v___x_4447_; lean_object* v___x_4448_; lean_object* v___x_4449_; lean_object* v___x_4450_; lean_object* v___x_4451_; lean_object* v___x_4452_; 
v___x_4447_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
lean_inc(v_declName_4382_);
v___x_4448_ = l_Lean_MessageData_ofName(v_declName_4382_);
v___x_4449_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4449_, 0, v___x_4447_);
lean_ctor_set(v___x_4449_, 1, v___x_4448_);
v___x_4450_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__7, &l_Lean_Meta_addInstance___closed__7_once, _init_l_Lean_Meta_addInstance___closed__7);
v___x_4451_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4451_, 0, v___x_4449_);
lean_ctor_set(v___x_4451_, 1, v___x_4450_);
v___x_4452_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__2(v___x_4451_, v___y_4421_, v___y_4422_, v___y_4423_, v___y_4424_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_dec_ref_known(v___x_4452_, 1);
v___y_4393_ = v_a_4426_;
v___y_4394_ = v___y_4421_;
v___y_4395_ = v___y_4422_;
v___y_4396_ = v___y_4423_;
v___y_4397_ = v___y_4424_;
goto v___jp_4392_;
}
else
{
lean_dec(v_a_4426_);
lean_dec(v_a_4391_);
lean_dec(v_prio_4384_);
lean_dec(v_declName_4382_);
return v___x_4452_;
}
}
}
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_dec(v_a_4426_);
lean_dec(v_a_4391_);
lean_dec(v_prio_4384_);
lean_dec(v_declName_4382_);
v_a_4453_ = lean_ctor_get(v___x_4432_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4432_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4432_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4432_);
v___x_4455_ = lean_box(0);
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
v_resetjp_4454_:
{
lean_object* v___x_4458_; 
if (v_isShared_4456_ == 0)
{
v___x_4458_ = v___x_4455_;
goto v_reusejp_4457_;
}
else
{
lean_object* v_reuseFailAlloc_4459_; 
v_reuseFailAlloc_4459_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4459_, 0, v_a_4453_);
v___x_4458_ = v_reuseFailAlloc_4459_;
goto v_reusejp_4457_;
}
v_reusejp_4457_:
{
return v___x_4458_;
}
}
}
}
}
else
{
lean_object* v_a_4461_; lean_object* v___x_4463_; uint8_t v_isShared_4464_; uint8_t v_isSharedCheck_4468_; 
lean_dec(v_a_4391_);
lean_dec(v_prio_4384_);
lean_dec(v_declName_4382_);
v_a_4461_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4468_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4468_ == 0)
{
v___x_4463_ = v___x_4425_;
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
else
{
lean_inc(v_a_4461_);
lean_dec(v___x_4425_);
v___x_4463_ = lean_box(0);
v_isShared_4464_ = v_isSharedCheck_4468_;
goto v_resetjp_4462_;
}
v_resetjp_4462_:
{
lean_object* v___x_4466_; 
if (v_isShared_4464_ == 0)
{
v___x_4466_ = v___x_4463_;
goto v_reusejp_4465_;
}
else
{
lean_object* v_reuseFailAlloc_4467_; 
v_reuseFailAlloc_4467_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4467_, 0, v_a_4461_);
v___x_4466_ = v_reuseFailAlloc_4467_;
goto v_reusejp_4465_;
}
v_reusejp_4465_:
{
return v___x_4466_;
}
}
}
}
}
else
{
lean_object* v_a_4483_; lean_object* v___x_4485_; uint8_t v_isShared_4486_; uint8_t v_isSharedCheck_4490_; 
lean_dec(v_prio_4384_);
lean_dec(v_declName_4382_);
v_a_4483_ = lean_ctor_get(v___x_4390_, 0);
v_isSharedCheck_4490_ = !lean_is_exclusive(v___x_4390_);
if (v_isSharedCheck_4490_ == 0)
{
v___x_4485_ = v___x_4390_;
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
else
{
lean_inc(v_a_4483_);
lean_dec(v___x_4390_);
v___x_4485_ = lean_box(0);
v_isShared_4486_ = v_isSharedCheck_4490_;
goto v_resetjp_4484_;
}
v_resetjp_4484_:
{
lean_object* v___x_4488_; 
if (v_isShared_4486_ == 0)
{
v___x_4488_ = v___x_4485_;
goto v_reusejp_4487_;
}
else
{
lean_object* v_reuseFailAlloc_4489_; 
v_reuseFailAlloc_4489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4489_, 0, v_a_4483_);
v___x_4488_ = v_reuseFailAlloc_4489_;
goto v_reusejp_4487_;
}
v_reusejp_4487_:
{
return v___x_4488_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4491_, lean_object* v_attrKind_4492_, lean_object* v_prio_4493_, lean_object* v_a_4494_, lean_object* v_a_4495_, lean_object* v_a_4496_, lean_object* v_a_4497_, lean_object* v_a_4498_){
_start:
{
uint8_t v_attrKind_boxed_4499_; lean_object* v_res_4500_; 
v_attrKind_boxed_4499_ = lean_unbox(v_attrKind_4492_);
v_res_4500_ = l_Lean_Meta_addInstance(v_declName_4491_, v_attrKind_boxed_4499_, v_prio_4493_, v_a_4494_, v_a_4495_, v_a_4496_, v_a_4497_);
lean_dec(v_a_4497_);
lean_dec_ref(v_a_4496_);
lean_dec(v_a_4495_);
lean_dec_ref(v_a_4494_);
return v_res_4500_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_4501_, lean_object* v_constName_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_, lean_object* v___y_4505_, lean_object* v___y_4506_){
_start:
{
lean_object* v___x_4508_; 
v___x_4508_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4502_, v___y_4503_, v___y_4504_, v___y_4505_, v___y_4506_);
return v___x_4508_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4509_, lean_object* v_constName_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_, lean_object* v___y_4514_, lean_object* v___y_4515_){
_start:
{
lean_object* v_res_4516_; 
v_res_4516_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_4509_, v_constName_4510_, v___y_4511_, v___y_4512_, v___y_4513_, v___y_4514_);
lean_dec(v___y_4514_);
lean_dec_ref(v___y_4513_);
lean_dec(v___y_4512_);
lean_dec_ref(v___y_4511_);
return v_res_4516_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_4517_, lean_object* v_ref_4518_, lean_object* v_constName_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v___x_4525_; 
v___x_4525_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4518_, v_constName_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4526_, lean_object* v_ref_4527_, lean_object* v_constName_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_, lean_object* v___y_4533_){
_start:
{
lean_object* v_res_4534_; 
v_res_4534_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_4526_, v_ref_4527_, v_constName_4528_, v___y_4529_, v___y_4530_, v___y_4531_, v___y_4532_);
lean_dec(v___y_4532_);
lean_dec_ref(v___y_4531_);
lean_dec(v___y_4530_);
lean_dec_ref(v___y_4529_);
lean_dec(v_ref_4527_);
return v_res_4534_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b1_4535_, lean_object* v_ref_4536_, lean_object* v_msg_4537_, lean_object* v_declHint_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_, lean_object* v___y_4541_, lean_object* v___y_4542_){
_start:
{
lean_object* v___x_4544_; 
v___x_4544_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4536_, v_msg_4537_, v_declHint_4538_, v___y_4539_, v___y_4540_, v___y_4541_, v___y_4542_);
return v___x_4544_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4545_, lean_object* v_ref_4546_, lean_object* v_msg_4547_, lean_object* v_declHint_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_, lean_object* v___y_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_){
_start:
{
lean_object* v_res_4554_; 
v_res_4554_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(v_00_u03b1_4545_, v_ref_4546_, v_msg_4547_, v_declHint_4548_, v___y_4549_, v___y_4550_, v___y_4551_, v___y_4552_);
lean_dec(v___y_4552_);
lean_dec_ref(v___y_4551_);
lean_dec(v___y_4550_);
lean_dec_ref(v___y_4549_);
lean_dec(v_ref_4546_);
return v_res_4554_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_4555_, lean_object* v_declHint_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_, lean_object* v___y_4560_){
_start:
{
lean_object* v___x_4562_; 
v___x_4562_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4555_, v_declHint_4556_, v___y_4560_);
return v___x_4562_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_4563_, lean_object* v_declHint_4564_, lean_object* v___y_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_){
_start:
{
lean_object* v_res_4570_; 
v_res_4570_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(v_msg_4563_, v_declHint_4564_, v___y_4565_, v___y_4566_, v___y_4567_, v___y_4568_);
lean_dec(v___y_4568_);
lean_dec_ref(v___y_4567_);
lean_dec(v___y_4566_);
lean_dec_ref(v___y_4565_);
return v_res_4570_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_4571_, lean_object* v_ref_4572_, lean_object* v_msg_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v___x_4579_; 
v___x_4579_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4572_, v_msg_4573_, v___y_4574_, v___y_4575_, v___y_4576_, v___y_4577_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4580_, lean_object* v_ref_4581_, lean_object* v_msg_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_, lean_object* v___y_4587_){
_start:
{
lean_object* v_res_4588_; 
v_res_4588_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_4580_, v_ref_4581_, v_msg_4582_, v___y_4583_, v___y_4584_, v___y_4585_, v___y_4586_);
lean_dec(v___y_4586_);
lean_dec_ref(v___y_4585_);
lean_dec(v___y_4584_);
lean_dec_ref(v___y_4583_);
lean_dec(v_ref_4581_);
return v_res_4588_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4589_, uint8_t v_s_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_){
_start:
{
lean_object* v___x_4594_; lean_object* v_env_4595_; lean_object* v_nextMacroScope_4596_; lean_object* v_ngen_4597_; lean_object* v_auxDeclNGen_4598_; lean_object* v_traceState_4599_; lean_object* v_messages_4600_; lean_object* v_infoState_4601_; lean_object* v_snapshotTasks_4602_; lean_object* v___x_4604_; uint8_t v_isShared_4605_; uint8_t v_isSharedCheck_4631_; 
v___x_4594_ = lean_st_ref_take(v___y_4592_);
v_env_4595_ = lean_ctor_get(v___x_4594_, 0);
v_nextMacroScope_4596_ = lean_ctor_get(v___x_4594_, 1);
v_ngen_4597_ = lean_ctor_get(v___x_4594_, 2);
v_auxDeclNGen_4598_ = lean_ctor_get(v___x_4594_, 3);
v_traceState_4599_ = lean_ctor_get(v___x_4594_, 4);
v_messages_4600_ = lean_ctor_get(v___x_4594_, 6);
v_infoState_4601_ = lean_ctor_get(v___x_4594_, 7);
v_snapshotTasks_4602_ = lean_ctor_get(v___x_4594_, 8);
v_isSharedCheck_4631_ = !lean_is_exclusive(v___x_4594_);
if (v_isSharedCheck_4631_ == 0)
{
lean_object* v_unused_4632_; 
v_unused_4632_ = lean_ctor_get(v___x_4594_, 5);
lean_dec(v_unused_4632_);
v___x_4604_ = v___x_4594_;
v_isShared_4605_ = v_isSharedCheck_4631_;
goto v_resetjp_4603_;
}
else
{
lean_inc(v_snapshotTasks_4602_);
lean_inc(v_infoState_4601_);
lean_inc(v_messages_4600_);
lean_inc(v_traceState_4599_);
lean_inc(v_auxDeclNGen_4598_);
lean_inc(v_ngen_4597_);
lean_inc(v_nextMacroScope_4596_);
lean_inc(v_env_4595_);
lean_dec(v___x_4594_);
v___x_4604_ = lean_box(0);
v_isShared_4605_ = v_isSharedCheck_4631_;
goto v_resetjp_4603_;
}
v_resetjp_4603_:
{
uint8_t v___x_4606_; lean_object* v___x_4607_; lean_object* v___x_4608_; lean_object* v___x_4609_; lean_object* v___x_4611_; 
v___x_4606_ = 0;
v___x_4607_ = lean_box(0);
v___x_4608_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4595_, v_declName_4589_, v_s_4590_, v___x_4606_, v___x_4607_);
v___x_4609_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4605_ == 0)
{
lean_ctor_set(v___x_4604_, 5, v___x_4609_);
lean_ctor_set(v___x_4604_, 0, v___x_4608_);
v___x_4611_ = v___x_4604_;
goto v_reusejp_4610_;
}
else
{
lean_object* v_reuseFailAlloc_4630_; 
v_reuseFailAlloc_4630_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4630_, 0, v___x_4608_);
lean_ctor_set(v_reuseFailAlloc_4630_, 1, v_nextMacroScope_4596_);
lean_ctor_set(v_reuseFailAlloc_4630_, 2, v_ngen_4597_);
lean_ctor_set(v_reuseFailAlloc_4630_, 3, v_auxDeclNGen_4598_);
lean_ctor_set(v_reuseFailAlloc_4630_, 4, v_traceState_4599_);
lean_ctor_set(v_reuseFailAlloc_4630_, 5, v___x_4609_);
lean_ctor_set(v_reuseFailAlloc_4630_, 6, v_messages_4600_);
lean_ctor_set(v_reuseFailAlloc_4630_, 7, v_infoState_4601_);
lean_ctor_set(v_reuseFailAlloc_4630_, 8, v_snapshotTasks_4602_);
v___x_4611_ = v_reuseFailAlloc_4630_;
goto v_reusejp_4610_;
}
v_reusejp_4610_:
{
lean_object* v___x_4612_; lean_object* v___x_4613_; lean_object* v_mctx_4614_; lean_object* v_zetaDeltaFVarIds_4615_; lean_object* v_postponed_4616_; lean_object* v_diag_4617_; lean_object* v___x_4619_; uint8_t v_isShared_4620_; uint8_t v_isSharedCheck_4628_; 
v___x_4612_ = lean_st_ref_put(v___y_4592_, v___x_4611_);
v___x_4613_ = lean_st_ref_take(v___y_4591_);
v_mctx_4614_ = lean_ctor_get(v___x_4613_, 0);
v_zetaDeltaFVarIds_4615_ = lean_ctor_get(v___x_4613_, 2);
v_postponed_4616_ = lean_ctor_get(v___x_4613_, 3);
v_diag_4617_ = lean_ctor_get(v___x_4613_, 4);
v_isSharedCheck_4628_ = !lean_is_exclusive(v___x_4613_);
if (v_isSharedCheck_4628_ == 0)
{
lean_object* v_unused_4629_; 
v_unused_4629_ = lean_ctor_get(v___x_4613_, 1);
lean_dec(v_unused_4629_);
v___x_4619_ = v___x_4613_;
v_isShared_4620_ = v_isSharedCheck_4628_;
goto v_resetjp_4618_;
}
else
{
lean_inc(v_diag_4617_);
lean_inc(v_postponed_4616_);
lean_inc(v_zetaDeltaFVarIds_4615_);
lean_inc(v_mctx_4614_);
lean_dec(v___x_4613_);
v___x_4619_ = lean_box(0);
v_isShared_4620_ = v_isSharedCheck_4628_;
goto v_resetjp_4618_;
}
v_resetjp_4618_:
{
lean_object* v___x_4621_; lean_object* v___x_4623_; 
v___x_4621_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_4620_ == 0)
{
lean_ctor_set(v___x_4619_, 1, v___x_4621_);
v___x_4623_ = v___x_4619_;
goto v_reusejp_4622_;
}
else
{
lean_object* v_reuseFailAlloc_4627_; 
v_reuseFailAlloc_4627_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4627_, 0, v_mctx_4614_);
lean_ctor_set(v_reuseFailAlloc_4627_, 1, v___x_4621_);
lean_ctor_set(v_reuseFailAlloc_4627_, 2, v_zetaDeltaFVarIds_4615_);
lean_ctor_set(v_reuseFailAlloc_4627_, 3, v_postponed_4616_);
lean_ctor_set(v_reuseFailAlloc_4627_, 4, v_diag_4617_);
v___x_4623_ = v_reuseFailAlloc_4627_;
goto v_reusejp_4622_;
}
v_reusejp_4622_:
{
lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; 
v___x_4624_ = lean_st_ref_put(v___y_4591_, v___x_4623_);
v___x_4625_ = lean_box(0);
v___x_4626_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4626_, 0, v___x_4625_);
return v___x_4626_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4633_, lean_object* v_s_4634_, lean_object* v___y_4635_, lean_object* v___y_4636_, lean_object* v___y_4637_){
_start:
{
uint8_t v_s_boxed_4638_; lean_object* v_res_4639_; 
v_s_boxed_4638_ = lean_unbox(v_s_4634_);
v_res_4639_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4633_, v_s_boxed_4638_, v___y_4635_, v___y_4636_);
lean_dec(v___y_4636_);
lean_dec(v___y_4635_);
return v_res_4639_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4640_, uint8_t v_s_4641_, lean_object* v___y_4642_, lean_object* v___y_4643_, lean_object* v___y_4644_, lean_object* v___y_4645_){
_start:
{
lean_object* v___x_4647_; 
v___x_4647_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4640_, v_s_4641_, v___y_4643_, v___y_4645_);
return v___x_4647_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4648_, lean_object* v_s_4649_, lean_object* v___y_4650_, lean_object* v___y_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
uint8_t v_s_boxed_4655_; lean_object* v_res_4656_; 
v_s_boxed_4655_ = lean_unbox(v_s_4649_);
v_res_4656_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4648_, v_s_boxed_4655_, v___y_4650_, v___y_4651_, v___y_4652_, v___y_4653_);
lean_dec(v___y_4653_);
lean_dec_ref(v___y_4652_);
lean_dec(v___y_4651_);
lean_dec_ref(v___y_4650_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4657_, uint8_t v_attrKind_4658_, lean_object* v_prio_4659_, lean_object* v_a_4660_, lean_object* v_a_4661_, lean_object* v_a_4662_, lean_object* v_a_4663_){
_start:
{
uint8_t v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4665_ = 4;
lean_inc(v_declName_4657_);
v___x_4666_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4657_, v___x_4665_, v_a_4661_, v_a_4663_);
lean_dec_ref(v___x_4666_);
v___x_4667_ = l_Lean_Meta_addInstance(v_declName_4657_, v_attrKind_4658_, v_prio_4659_, v_a_4660_, v_a_4661_, v_a_4662_, v_a_4663_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4668_, lean_object* v_attrKind_4669_, lean_object* v_prio_4670_, lean_object* v_a_4671_, lean_object* v_a_4672_, lean_object* v_a_4673_, lean_object* v_a_4674_, lean_object* v_a_4675_){
_start:
{
uint8_t v_attrKind_boxed_4676_; lean_object* v_res_4677_; 
v_attrKind_boxed_4676_ = lean_unbox(v_attrKind_4669_);
v_res_4677_ = l_Lean_Meta_registerInstance(v_declName_4668_, v_attrKind_boxed_4676_, v_prio_4670_, v_a_4671_, v_a_4672_, v_a_4673_, v_a_4674_);
lean_dec(v_a_4674_);
lean_dec_ref(v_a_4673_);
lean_dec(v_a_4672_);
lean_dec_ref(v_a_4671_);
return v_res_4677_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4678_, lean_object* v_x_4679_){
_start:
{
lean_inc_ref(v_a_4678_);
return v_a_4678_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4680_, lean_object* v_x_4681_){
_start:
{
lean_object* v_res_4682_; 
v_res_4682_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4680_, v_x_4681_);
lean_dec_ref(v_x_4681_);
lean_dec_ref(v_a_4680_);
return v_res_4682_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4683_, lean_object* v___y_4684_, lean_object* v___y_4685_){
_start:
{
lean_object* v___x_4687_; lean_object* v_env_4688_; lean_object* v_options_4689_; lean_object* v___x_4690_; lean_object* v___x_4691_; lean_object* v___x_4692_; lean_object* v___x_4693_; lean_object* v___x_4694_; lean_object* v___x_4695_; lean_object* v___x_4696_; 
v___x_4687_ = lean_st_ref_get(v___y_4685_);
v_env_4688_ = lean_ctor_get(v___x_4687_, 0);
lean_inc_ref(v_env_4688_);
lean_dec(v___x_4687_);
v_options_4689_ = lean_ctor_get(v___y_4684_, 1);
v___x_4690_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4691_ = lean_unsigned_to_nat(32u);
v___x_4692_ = lean_mk_empty_array_with_capacity(v___x_4691_);
lean_dec_ref(v___x_4692_);
v___x_4693_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_4689_);
v___x_4694_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4694_, 0, v_env_4688_);
lean_ctor_set(v___x_4694_, 1, v___x_4690_);
lean_ctor_set(v___x_4694_, 2, v___x_4693_);
lean_ctor_set(v___x_4694_, 3, v_options_4689_);
v___x_4695_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4695_, 0, v___x_4694_);
lean_ctor_set(v___x_4695_, 1, v_msgData_4683_);
v___x_4696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4696_, 0, v___x_4695_);
return v___x_4696_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4697_, lean_object* v___y_4698_, lean_object* v___y_4699_, lean_object* v___y_4700_){
_start:
{
lean_object* v_res_4701_; 
v_res_4701_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4697_, v___y_4698_, v___y_4699_);
lean_dec(v___y_4699_);
lean_dec_ref(v___y_4698_);
return v_res_4701_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4702_, lean_object* v___y_4703_, lean_object* v___y_4704_){
_start:
{
lean_object* v_ref_4706_; lean_object* v___x_4707_; lean_object* v_a_4708_; lean_object* v___x_4710_; uint8_t v_isShared_4711_; uint8_t v_isSharedCheck_4716_; 
v_ref_4706_ = lean_ctor_get(v___y_4703_, 4);
v___x_4707_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4702_, v___y_4703_, v___y_4704_);
v_a_4708_ = lean_ctor_get(v___x_4707_, 0);
v_isSharedCheck_4716_ = !lean_is_exclusive(v___x_4707_);
if (v_isSharedCheck_4716_ == 0)
{
v___x_4710_ = v___x_4707_;
v_isShared_4711_ = v_isSharedCheck_4716_;
goto v_resetjp_4709_;
}
else
{
lean_inc(v_a_4708_);
lean_dec(v___x_4707_);
v___x_4710_ = lean_box(0);
v_isShared_4711_ = v_isSharedCheck_4716_;
goto v_resetjp_4709_;
}
v_resetjp_4709_:
{
lean_object* v___x_4712_; lean_object* v___x_4714_; 
lean_inc(v_ref_4706_);
v___x_4712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4712_, 0, v_ref_4706_);
lean_ctor_set(v___x_4712_, 1, v_a_4708_);
if (v_isShared_4711_ == 0)
{
lean_ctor_set_tag(v___x_4710_, 1);
lean_ctor_set(v___x_4710_, 0, v___x_4712_);
v___x_4714_ = v___x_4710_;
goto v_reusejp_4713_;
}
else
{
lean_object* v_reuseFailAlloc_4715_; 
v_reuseFailAlloc_4715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4715_, 0, v___x_4712_);
v___x_4714_ = v_reuseFailAlloc_4715_;
goto v_reusejp_4713_;
}
v_reusejp_4713_:
{
return v___x_4714_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4717_, lean_object* v___y_4718_, lean_object* v___y_4719_, lean_object* v___y_4720_){
_start:
{
lean_object* v_res_4721_; 
v_res_4721_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4717_, v___y_4718_, v___y_4719_);
lean_dec(v___y_4719_);
lean_dec_ref(v___y_4718_);
return v_res_4721_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4722_, lean_object* v_i_4723_, lean_object* v_k_4724_){
_start:
{
lean_object* v___x_4725_; uint8_t v___x_4726_; 
v___x_4725_ = lean_array_get_size(v_keys_4722_);
v___x_4726_ = lean_nat_dec_lt(v_i_4723_, v___x_4725_);
if (v___x_4726_ == 0)
{
lean_dec(v_i_4723_);
return v___x_4726_;
}
else
{
lean_object* v_k_x27_4727_; uint8_t v___x_4728_; 
v_k_x27_4727_ = lean_array_fget_borrowed(v_keys_4722_, v_i_4723_);
v___x_4728_ = lean_name_eq(v_k_4724_, v_k_x27_4727_);
if (v___x_4728_ == 0)
{
lean_object* v___x_4729_; lean_object* v___x_4730_; 
v___x_4729_ = lean_unsigned_to_nat(1u);
v___x_4730_ = lean_nat_add(v_i_4723_, v___x_4729_);
lean_dec(v_i_4723_);
v_i_4723_ = v___x_4730_;
goto _start;
}
else
{
lean_dec(v_i_4723_);
return v___x_4726_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4732_, lean_object* v_i_4733_, lean_object* v_k_4734_){
_start:
{
uint8_t v_res_4735_; lean_object* v_r_4736_; 
v_res_4735_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4732_, v_i_4733_, v_k_4734_);
lean_dec(v_k_4734_);
lean_dec_ref(v_keys_4732_);
v_r_4736_ = lean_box(v_res_4735_);
return v_r_4736_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4737_, size_t v_x_4738_, lean_object* v_x_4739_){
_start:
{
if (lean_obj_tag(v_x_4737_) == 0)
{
lean_object* v_es_4740_; lean_object* v___x_4741_; size_t v___x_4742_; size_t v___x_4743_; lean_object* v_j_4744_; lean_object* v___x_4745_; 
v_es_4740_ = lean_ctor_get(v_x_4737_, 0);
v___x_4741_ = lean_box(2);
v___x_4742_ = ((size_t)31ULL);
v___x_4743_ = lean_usize_land(v_x_4738_, v___x_4742_);
v_j_4744_ = lean_usize_to_nat(v___x_4743_);
v___x_4745_ = lean_array_get_borrowed(v___x_4741_, v_es_4740_, v_j_4744_);
lean_dec(v_j_4744_);
switch(lean_obj_tag(v___x_4745_))
{
case 0:
{
lean_object* v_key_4746_; uint8_t v___x_4747_; 
v_key_4746_ = lean_ctor_get(v___x_4745_, 0);
v___x_4747_ = lean_name_eq(v_x_4739_, v_key_4746_);
return v___x_4747_;
}
case 1:
{
lean_object* v_node_4748_; size_t v___x_4749_; size_t v___x_4750_; 
v_node_4748_ = lean_ctor_get(v___x_4745_, 0);
v___x_4749_ = ((size_t)5ULL);
v___x_4750_ = lean_usize_shift_right(v_x_4738_, v___x_4749_);
v_x_4737_ = v_node_4748_;
v_x_4738_ = v___x_4750_;
goto _start;
}
default: 
{
uint8_t v___x_4752_; 
v___x_4752_ = 0;
return v___x_4752_;
}
}
}
else
{
lean_object* v_ks_4753_; lean_object* v___x_4754_; uint8_t v___x_4755_; 
v_ks_4753_ = lean_ctor_get(v_x_4737_, 0);
v___x_4754_ = lean_unsigned_to_nat(0u);
v___x_4755_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4753_, v___x_4754_, v_x_4739_);
return v___x_4755_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4756_, lean_object* v_x_4757_, lean_object* v_x_4758_){
_start:
{
size_t v_x_2371__boxed_4759_; uint8_t v_res_4760_; lean_object* v_r_4761_; 
v_x_2371__boxed_4759_ = lean_unbox_usize(v_x_4757_);
lean_dec(v_x_4757_);
v_res_4760_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4756_, v_x_2371__boxed_4759_, v_x_4758_);
lean_dec(v_x_4758_);
lean_dec_ref(v_x_4756_);
v_r_4761_ = lean_box(v_res_4760_);
return v_r_4761_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4762_, lean_object* v_x_4763_){
_start:
{
uint64_t v___y_4765_; 
if (lean_obj_tag(v_x_4763_) == 0)
{
uint64_t v___x_4768_; 
v___x_4768_ = 1723ULL;
v___y_4765_ = v___x_4768_;
goto v___jp_4764_;
}
else
{
uint64_t v_hash_4769_; 
v_hash_4769_ = lean_ctor_get_uint64(v_x_4763_, sizeof(void*)*2);
v___y_4765_ = v_hash_4769_;
goto v___jp_4764_;
}
v___jp_4764_:
{
size_t v___x_4766_; uint8_t v___x_4767_; 
v___x_4766_ = lean_uint64_to_usize(v___y_4765_);
v___x_4767_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4762_, v___x_4766_, v_x_4763_);
return v___x_4767_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4770_, lean_object* v_x_4771_){
_start:
{
uint8_t v_res_4772_; lean_object* v_r_4773_; 
v_res_4772_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4770_, v_x_4771_);
lean_dec(v_x_4771_);
lean_dec_ref(v_x_4770_);
v_r_4773_ = lean_box(v_res_4772_);
return v_r_4773_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4774_, lean_object* v_declName_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v_instanceNames_4782_; uint8_t v___x_4783_; 
v_instanceNames_4782_ = lean_ctor_get(v_d_4774_, 1);
v___x_4783_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4782_, v_declName_4775_);
if (v___x_4783_ == 0)
{
lean_object* v___x_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; lean_object* v___x_4788_; lean_object* v___x_4789_; lean_object* v_a_4790_; lean_object* v___x_4792_; uint8_t v_isShared_4793_; uint8_t v_isSharedCheck_4797_; 
lean_dec_ref(v_d_4774_);
v___x_4784_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4785_ = l_Lean_MessageData_ofConstName(v_declName_4775_, v___x_4783_);
v___x_4786_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4786_, 0, v___x_4784_);
lean_ctor_set(v___x_4786_, 1, v___x_4785_);
v___x_4787_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4788_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4788_, 0, v___x_4786_);
lean_ctor_set(v___x_4788_, 1, v___x_4787_);
v___x_4789_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4788_, v___y_4776_, v___y_4777_);
v_a_4790_ = lean_ctor_get(v___x_4789_, 0);
v_isSharedCheck_4797_ = !lean_is_exclusive(v___x_4789_);
if (v_isSharedCheck_4797_ == 0)
{
v___x_4792_ = v___x_4789_;
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
else
{
lean_inc(v_a_4790_);
lean_dec(v___x_4789_);
v___x_4792_ = lean_box(0);
v_isShared_4793_ = v_isSharedCheck_4797_;
goto v_resetjp_4791_;
}
v_resetjp_4791_:
{
lean_object* v___x_4795_; 
if (v_isShared_4793_ == 0)
{
v___x_4795_ = v___x_4792_;
goto v_reusejp_4794_;
}
else
{
lean_object* v_reuseFailAlloc_4796_; 
v_reuseFailAlloc_4796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4796_, 0, v_a_4790_);
v___x_4795_ = v_reuseFailAlloc_4796_;
goto v_reusejp_4794_;
}
v_reusejp_4794_:
{
return v___x_4795_;
}
}
}
else
{
goto v___jp_4779_;
}
v___jp_4779_:
{
lean_object* v___x_4780_; lean_object* v___x_4781_; 
v___x_4780_ = l_Lean_Meta_Instances_eraseCore(v_d_4774_, v_declName_4775_);
v___x_4781_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4781_, 0, v___x_4780_);
return v___x_4781_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4798_, lean_object* v_declName_4799_, lean_object* v___y_4800_, lean_object* v___y_4801_, lean_object* v___y_4802_){
_start:
{
lean_object* v_res_4803_; 
v_res_4803_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4798_, v_declName_4799_, v___y_4800_, v___y_4801_);
lean_dec(v___y_4801_);
lean_dec_ref(v___y_4800_);
return v_res_4803_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4804_, lean_object* v_declName_4805_, lean_object* v___y_4806_, lean_object* v___y_4807_){
_start:
{
lean_object* v___x_4809_; lean_object* v_env_4810_; lean_object* v___x_4811_; lean_object* v_ext_4812_; lean_object* v_toEnvExtension_4813_; lean_object* v_asyncMode_4814_; lean_object* v___x_4815_; lean_object* v___x_4816_; 
v___x_4809_ = lean_st_ref_get(v___y_4807_);
v_env_4810_ = lean_ctor_get(v___x_4809_, 0);
lean_inc_ref(v_env_4810_);
lean_dec(v___x_4809_);
v___x_4811_ = l_Lean_Meta_instanceExtension;
v_ext_4812_ = lean_ctor_get(v___x_4811_, 1);
v_toEnvExtension_4813_ = lean_ctor_get(v_ext_4812_, 0);
v_asyncMode_4814_ = lean_ctor_get(v_toEnvExtension_4813_, 2);
v___x_4815_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4804_, v___x_4811_, v_env_4810_, v_asyncMode_4814_);
v___x_4816_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4815_, v_declName_4805_, v___y_4806_, v___y_4807_);
if (lean_obj_tag(v___x_4816_) == 0)
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4846_; 
v_a_4817_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4846_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4846_ == 0)
{
v___x_4819_ = v___x_4816_;
v_isShared_4820_ = v_isSharedCheck_4846_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4816_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4846_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4821_; lean_object* v_env_4822_; lean_object* v_nextMacroScope_4823_; lean_object* v_ngen_4824_; lean_object* v_auxDeclNGen_4825_; lean_object* v_traceState_4826_; lean_object* v_messages_4827_; lean_object* v_infoState_4828_; lean_object* v_snapshotTasks_4829_; lean_object* v___x_4831_; uint8_t v_isShared_4832_; uint8_t v_isSharedCheck_4844_; 
v___x_4821_ = lean_st_ref_take(v___y_4807_);
v_env_4822_ = lean_ctor_get(v___x_4821_, 0);
v_nextMacroScope_4823_ = lean_ctor_get(v___x_4821_, 1);
v_ngen_4824_ = lean_ctor_get(v___x_4821_, 2);
v_auxDeclNGen_4825_ = lean_ctor_get(v___x_4821_, 3);
v_traceState_4826_ = lean_ctor_get(v___x_4821_, 4);
v_messages_4827_ = lean_ctor_get(v___x_4821_, 6);
v_infoState_4828_ = lean_ctor_get(v___x_4821_, 7);
v_snapshotTasks_4829_ = lean_ctor_get(v___x_4821_, 8);
v_isSharedCheck_4844_ = !lean_is_exclusive(v___x_4821_);
if (v_isSharedCheck_4844_ == 0)
{
lean_object* v_unused_4845_; 
v_unused_4845_ = lean_ctor_get(v___x_4821_, 5);
lean_dec(v_unused_4845_);
v___x_4831_ = v___x_4821_;
v_isShared_4832_ = v_isSharedCheck_4844_;
goto v_resetjp_4830_;
}
else
{
lean_inc(v_snapshotTasks_4829_);
lean_inc(v_infoState_4828_);
lean_inc(v_messages_4827_);
lean_inc(v_traceState_4826_);
lean_inc(v_auxDeclNGen_4825_);
lean_inc(v_ngen_4824_);
lean_inc(v_nextMacroScope_4823_);
lean_inc(v_env_4822_);
lean_dec(v___x_4821_);
v___x_4831_ = lean_box(0);
v_isShared_4832_ = v_isSharedCheck_4844_;
goto v_resetjp_4830_;
}
v_resetjp_4830_:
{
lean_object* v___f_4833_; lean_object* v___x_4834_; lean_object* v___x_4835_; lean_object* v___x_4837_; 
v___f_4833_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4833_, 0, v_a_4817_);
v___x_4834_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4811_, v_env_4822_, v___f_4833_);
v___x_4835_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4832_ == 0)
{
lean_ctor_set(v___x_4831_, 5, v___x_4835_);
lean_ctor_set(v___x_4831_, 0, v___x_4834_);
v___x_4837_ = v___x_4831_;
goto v_reusejp_4836_;
}
else
{
lean_object* v_reuseFailAlloc_4843_; 
v_reuseFailAlloc_4843_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4843_, 0, v___x_4834_);
lean_ctor_set(v_reuseFailAlloc_4843_, 1, v_nextMacroScope_4823_);
lean_ctor_set(v_reuseFailAlloc_4843_, 2, v_ngen_4824_);
lean_ctor_set(v_reuseFailAlloc_4843_, 3, v_auxDeclNGen_4825_);
lean_ctor_set(v_reuseFailAlloc_4843_, 4, v_traceState_4826_);
lean_ctor_set(v_reuseFailAlloc_4843_, 5, v___x_4835_);
lean_ctor_set(v_reuseFailAlloc_4843_, 6, v_messages_4827_);
lean_ctor_set(v_reuseFailAlloc_4843_, 7, v_infoState_4828_);
lean_ctor_set(v_reuseFailAlloc_4843_, 8, v_snapshotTasks_4829_);
v___x_4837_ = v_reuseFailAlloc_4843_;
goto v_reusejp_4836_;
}
v_reusejp_4836_:
{
lean_object* v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4841_; 
v___x_4838_ = lean_st_ref_put(v___y_4807_, v___x_4837_);
v___x_4839_ = lean_box(0);
if (v_isShared_4820_ == 0)
{
lean_ctor_set(v___x_4819_, 0, v___x_4839_);
v___x_4841_ = v___x_4819_;
goto v_reusejp_4840_;
}
else
{
lean_object* v_reuseFailAlloc_4842_; 
v_reuseFailAlloc_4842_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4842_, 0, v___x_4839_);
v___x_4841_ = v_reuseFailAlloc_4842_;
goto v_reusejp_4840_;
}
v_reusejp_4840_:
{
return v___x_4841_;
}
}
}
}
}
else
{
lean_object* v_a_4847_; lean_object* v___x_4849_; uint8_t v_isShared_4850_; uint8_t v_isSharedCheck_4854_; 
v_a_4847_ = lean_ctor_get(v___x_4816_, 0);
v_isSharedCheck_4854_ = !lean_is_exclusive(v___x_4816_);
if (v_isSharedCheck_4854_ == 0)
{
v___x_4849_ = v___x_4816_;
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
else
{
lean_inc(v_a_4847_);
lean_dec(v___x_4816_);
v___x_4849_ = lean_box(0);
v_isShared_4850_ = v_isSharedCheck_4854_;
goto v_resetjp_4848_;
}
v_resetjp_4848_:
{
lean_object* v___x_4852_; 
if (v_isShared_4850_ == 0)
{
v___x_4852_ = v___x_4849_;
goto v_reusejp_4851_;
}
else
{
lean_object* v_reuseFailAlloc_4853_; 
v_reuseFailAlloc_4853_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4853_, 0, v_a_4847_);
v___x_4852_ = v_reuseFailAlloc_4853_;
goto v_reusejp_4851_;
}
v_reusejp_4851_:
{
return v___x_4852_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4855_, lean_object* v_declName_4856_, lean_object* v___y_4857_, lean_object* v___y_4858_, lean_object* v___y_4859_){
_start:
{
lean_object* v_res_4860_; 
v_res_4860_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4855_, v_declName_4856_, v___y_4857_, v___y_4858_);
lean_dec(v___y_4858_);
lean_dec_ref(v___y_4857_);
lean_dec_ref(v___x_4855_);
return v_res_4860_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4867_; uint64_t v___x_4868_; 
v___x_4867_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4868_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4867_);
return v___x_4868_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; 
v___x_4869_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4870_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4871_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4871_, 0, v___x_4870_);
lean_ctor_set_uint64(v___x_4871_, sizeof(void*)*1, v___x_4869_);
return v___x_4871_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4872_; 
v___x_4872_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4872_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4873_; lean_object* v___x_4874_; 
v___x_4873_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4874_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4873_);
return v___x_4874_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4875_; lean_object* v___x_4876_; 
v___x_4875_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4876_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4875_);
lean_ctor_set(v___x_4876_, 1, v___x_4875_);
lean_ctor_set(v___x_4876_, 2, v___x_4875_);
lean_ctor_set(v___x_4876_, 3, v___x_4875_);
lean_ctor_set(v___x_4876_, 4, v___x_4875_);
lean_ctor_set(v___x_4876_, 5, v___x_4875_);
return v___x_4876_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4877_; lean_object* v___x_4878_; 
v___x_4877_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4877_);
lean_ctor_set(v___x_4878_, 1, v___x_4877_);
lean_ctor_set(v___x_4878_, 2, v___x_4877_);
lean_ctor_set(v___x_4878_, 3, v___x_4877_);
lean_ctor_set(v___x_4878_, 4, v___x_4877_);
return v___x_4878_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4879_, lean_object* v___x_4880_, lean_object* v_declName_4881_, lean_object* v_stx_4882_, uint8_t v_attrKind_4883_, lean_object* v___y_4884_, lean_object* v___y_4885_){
_start:
{
lean_object* v___x_4887_; lean_object* v___x_4888_; lean_object* v___x_4889_; 
v___x_4887_ = lean_unsigned_to_nat(1u);
v___x_4888_ = l_Lean_Syntax_getArg(v_stx_4882_, v___x_4887_);
v___x_4889_ = l_Lean_getAttrParamOptPrio(v___x_4888_, v___y_4884_, v___y_4885_);
if (lean_obj_tag(v___x_4889_) == 0)
{
lean_object* v_a_4890_; uint8_t v___x_4891_; uint8_t v___x_4892_; lean_object* v___x_4893_; lean_object* v___x_4894_; lean_object* v___x_4895_; lean_object* v___x_4896_; lean_object* v___x_4897_; size_t v___x_4898_; lean_object* v___x_4899_; lean_object* v___x_4900_; lean_object* v___x_4901_; lean_object* v___x_4902_; lean_object* v___x_4903_; lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; lean_object* v___x_4907_; lean_object* v___x_4908_; lean_object* v___x_4909_; lean_object* v___x_4910_; 
v_a_4890_ = lean_ctor_get(v___x_4889_, 0);
lean_inc(v_a_4890_);
lean_dec_ref_known(v___x_4889_, 1);
v___x_4891_ = 0;
v___x_4892_ = 1;
v___x_4893_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4894_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4895_ = lean_unsigned_to_nat(32u);
v___x_4896_ = lean_mk_empty_array_with_capacity(v___x_4895_);
v___x_4897_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4898_ = ((size_t)5ULL);
lean_inc_n(v___x_4879_, 6);
v___x_4899_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4899_, 0, v___x_4897_);
lean_ctor_set(v___x_4899_, 1, v___x_4896_);
lean_ctor_set(v___x_4899_, 2, v___x_4879_);
lean_ctor_set(v___x_4899_, 3, v___x_4879_);
lean_ctor_set_usize(v___x_4899_, 4, v___x_4898_);
v___x_4900_ = lean_box(1);
lean_inc_ref(v___x_4899_);
v___x_4901_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4901_, 0, v___x_4894_);
lean_ctor_set(v___x_4901_, 1, v___x_4899_);
lean_ctor_set(v___x_4901_, 2, v___x_4900_);
v___x_4902_ = lean_mk_empty_array_with_capacity(v___x_4879_);
v___x_4903_ = lean_box(0);
lean_inc(v___x_4880_);
v___x_4904_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4904_, 0, v___x_4893_);
lean_ctor_set(v___x_4904_, 1, v___x_4880_);
lean_ctor_set(v___x_4904_, 2, v___x_4901_);
lean_ctor_set(v___x_4904_, 3, v___x_4902_);
lean_ctor_set(v___x_4904_, 4, v___x_4903_);
lean_ctor_set(v___x_4904_, 5, v___x_4879_);
lean_ctor_set(v___x_4904_, 6, v___x_4903_);
lean_ctor_set_uint8(v___x_4904_, sizeof(void*)*7, v___x_4891_);
lean_ctor_set_uint8(v___x_4904_, sizeof(void*)*7 + 1, v___x_4891_);
lean_ctor_set_uint8(v___x_4904_, sizeof(void*)*7 + 2, v___x_4891_);
lean_ctor_set_uint8(v___x_4904_, sizeof(void*)*7 + 3, v___x_4892_);
v___x_4905_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4905_, 0, v___x_4879_);
lean_ctor_set(v___x_4905_, 1, v___x_4879_);
lean_ctor_set(v___x_4905_, 2, v___x_4879_);
lean_ctor_set(v___x_4905_, 3, v___x_4879_);
lean_ctor_set(v___x_4905_, 4, v___x_4894_);
lean_ctor_set(v___x_4905_, 5, v___x_4894_);
lean_ctor_set(v___x_4905_, 6, v___x_4894_);
lean_ctor_set(v___x_4905_, 7, v___x_4894_);
lean_ctor_set(v___x_4905_, 8, v___x_4894_);
lean_ctor_set(v___x_4905_, 9, v___x_4894_);
lean_ctor_set(v___x_4905_, 10, v___x_4894_);
v___x_4906_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4907_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4908_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4908_, 0, v___x_4905_);
lean_ctor_set(v___x_4908_, 1, v___x_4906_);
lean_ctor_set(v___x_4908_, 2, v___x_4880_);
lean_ctor_set(v___x_4908_, 3, v___x_4899_);
lean_ctor_set(v___x_4908_, 4, v___x_4907_);
v___x_4909_ = lean_st_mk_ref(v___x_4908_);
v___x_4910_ = l_Lean_Meta_addInstance(v_declName_4881_, v_attrKind_4883_, v_a_4890_, v___x_4904_, v___x_4909_, v___y_4884_, v___y_4885_);
lean_dec_ref_known(v___x_4904_, 7);
if (lean_obj_tag(v___x_4910_) == 0)
{
lean_object* v___x_4912_; uint8_t v_isShared_4913_; uint8_t v_isSharedCheck_4919_; 
v_isSharedCheck_4919_ = !lean_is_exclusive(v___x_4910_);
if (v_isSharedCheck_4919_ == 0)
{
lean_object* v_unused_4920_; 
v_unused_4920_ = lean_ctor_get(v___x_4910_, 0);
lean_dec(v_unused_4920_);
v___x_4912_ = v___x_4910_;
v_isShared_4913_ = v_isSharedCheck_4919_;
goto v_resetjp_4911_;
}
else
{
lean_dec(v___x_4910_);
v___x_4912_ = lean_box(0);
v_isShared_4913_ = v_isSharedCheck_4919_;
goto v_resetjp_4911_;
}
v_resetjp_4911_:
{
lean_object* v___x_4914_; lean_object* v___x_4915_; lean_object* v___x_4917_; 
v___x_4914_ = lean_st_ref_get(v___x_4909_);
lean_dec(v___x_4909_);
lean_dec(v___x_4914_);
v___x_4915_ = lean_box(0);
if (v_isShared_4913_ == 0)
{
lean_ctor_set(v___x_4912_, 0, v___x_4915_);
v___x_4917_ = v___x_4912_;
goto v_reusejp_4916_;
}
else
{
lean_object* v_reuseFailAlloc_4918_; 
v_reuseFailAlloc_4918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4918_, 0, v___x_4915_);
v___x_4917_ = v_reuseFailAlloc_4918_;
goto v_reusejp_4916_;
}
v_reusejp_4916_:
{
return v___x_4917_;
}
}
}
else
{
lean_dec(v___x_4909_);
return v___x_4910_;
}
}
else
{
lean_object* v_a_4921_; lean_object* v___x_4923_; uint8_t v_isShared_4924_; uint8_t v_isSharedCheck_4928_; 
lean_dec(v_declName_4881_);
lean_dec(v___x_4880_);
lean_dec(v___x_4879_);
v_a_4921_ = lean_ctor_get(v___x_4889_, 0);
v_isSharedCheck_4928_ = !lean_is_exclusive(v___x_4889_);
if (v_isSharedCheck_4928_ == 0)
{
v___x_4923_ = v___x_4889_;
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
else
{
lean_inc(v_a_4921_);
lean_dec(v___x_4889_);
v___x_4923_ = lean_box(0);
v_isShared_4924_ = v_isSharedCheck_4928_;
goto v_resetjp_4922_;
}
v_resetjp_4922_:
{
lean_object* v___x_4926_; 
if (v_isShared_4924_ == 0)
{
v___x_4926_ = v___x_4923_;
goto v_reusejp_4925_;
}
else
{
lean_object* v_reuseFailAlloc_4927_; 
v_reuseFailAlloc_4927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4927_, 0, v_a_4921_);
v___x_4926_ = v_reuseFailAlloc_4927_;
goto v_reusejp_4925_;
}
v_reusejp_4925_:
{
return v___x_4926_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4929_, lean_object* v___x_4930_, lean_object* v_declName_4931_, lean_object* v_stx_4932_, lean_object* v_attrKind_4933_, lean_object* v___y_4934_, lean_object* v___y_4935_, lean_object* v___y_4936_){
_start:
{
uint8_t v_attrKind_boxed_4937_; lean_object* v_res_4938_; 
v_attrKind_boxed_4937_ = lean_unbox(v_attrKind_4933_);
v_res_4938_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4929_, v___x_4930_, v_declName_4931_, v_stx_4932_, v_attrKind_boxed_4937_, v___y_4934_, v___y_4935_);
lean_dec(v___y_4935_);
lean_dec_ref(v___y_4934_);
lean_dec(v_stx_4932_);
return v_res_4938_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4939_; lean_object* v___f_4940_; 
v___x_4939_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4940_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4940_, 0, v___x_4939_);
return v___f_4940_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_5007_; lean_object* v___f_5008_; lean_object* v___x_5009_; lean_object* v___x_5010_; 
v___f_5007_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_5008_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5009_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5010_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5010_, 0, v___x_5009_);
lean_ctor_set(v___x_5010_, 1, v___f_5008_);
lean_ctor_set(v___x_5010_, 2, v___f_5007_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5012_; lean_object* v___x_5013_; 
v___x_5012_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5013_ = l_Lean_registerBuiltinAttribute(v___x_5012_);
return v___x_5013_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5014_){
_start:
{
lean_object* v_res_5015_; 
v_res_5015_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5015_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_5016_, lean_object* v_x_5017_, lean_object* v_x_5018_){
_start:
{
uint8_t v___x_5019_; 
v___x_5019_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_5017_, v_x_5018_);
return v___x_5019_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_5020_, lean_object* v_x_5021_, lean_object* v_x_5022_){
_start:
{
uint8_t v_res_5023_; lean_object* v_r_5024_; 
v_res_5023_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_5020_, v_x_5021_, v_x_5022_);
lean_dec(v_x_5022_);
lean_dec_ref(v_x_5021_);
v_r_5024_ = lean_box(v_res_5023_);
return v_r_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_5025_, lean_object* v_msg_5026_, lean_object* v___y_5027_, lean_object* v___y_5028_){
_start:
{
lean_object* v___x_5030_; 
v___x_5030_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_5026_, v___y_5027_, v___y_5028_);
return v___x_5030_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_5031_, lean_object* v_msg_5032_, lean_object* v___y_5033_, lean_object* v___y_5034_, lean_object* v___y_5035_){
_start:
{
lean_object* v_res_5036_; 
v_res_5036_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_5031_, v_msg_5032_, v___y_5033_, v___y_5034_);
lean_dec(v___y_5034_);
lean_dec_ref(v___y_5033_);
return v_res_5036_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5037_, lean_object* v_x_5038_, size_t v_x_5039_, lean_object* v_x_5040_){
_start:
{
uint8_t v___x_5041_; 
v___x_5041_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5038_, v_x_5039_, v_x_5040_);
return v___x_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5042_, lean_object* v_x_5043_, lean_object* v_x_5044_, lean_object* v_x_5045_){
_start:
{
size_t v_x_3020__boxed_5046_; uint8_t v_res_5047_; lean_object* v_r_5048_; 
v_x_3020__boxed_5046_ = lean_unbox_usize(v_x_5044_);
lean_dec(v_x_5044_);
v_res_5047_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_5042_, v_x_5043_, v_x_3020__boxed_5046_, v_x_5045_);
lean_dec(v_x_5045_);
lean_dec_ref(v_x_5043_);
v_r_5048_ = lean_box(v_res_5047_);
return v_r_5048_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5049_, lean_object* v_keys_5050_, lean_object* v_vals_5051_, lean_object* v_heq_5052_, lean_object* v_i_5053_, lean_object* v_k_5054_){
_start:
{
uint8_t v___x_5055_; 
v___x_5055_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_5050_, v_i_5053_, v_k_5054_);
return v___x_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5056_, lean_object* v_keys_5057_, lean_object* v_vals_5058_, lean_object* v_heq_5059_, lean_object* v_i_5060_, lean_object* v_k_5061_){
_start:
{
uint8_t v_res_5062_; lean_object* v_r_5063_; 
v_res_5062_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_5056_, v_keys_5057_, v_vals_5058_, v_heq_5059_, v_i_5060_, v_k_5061_);
lean_dec(v_k_5061_);
lean_dec_ref(v_vals_5058_);
lean_dec_ref(v_keys_5057_);
v_r_5063_ = lean_box(v_res_5062_);
return v_r_5063_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5066_; lean_object* v___x_5067_; lean_object* v___x_5068_; 
v___x_5066_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5067_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5068_ = l_Lean_addBuiltinDocString(v___x_5066_, v___x_5067_);
return v___x_5068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5069_){
_start:
{
lean_object* v_res_5070_; 
v_res_5070_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5070_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_5071_){
_start:
{
lean_object* v___x_5073_; lean_object* v_env_5074_; lean_object* v___x_5075_; lean_object* v_ext_5076_; lean_object* v_toEnvExtension_5077_; lean_object* v_asyncMode_5078_; lean_object* v___x_5079_; lean_object* v___x_5080_; lean_object* v_discrTree_5081_; lean_object* v___x_5082_; 
v___x_5073_ = lean_st_ref_get(v_a_5071_);
v_env_5074_ = lean_ctor_get(v___x_5073_, 0);
lean_inc_ref(v_env_5074_);
lean_dec(v___x_5073_);
v___x_5075_ = l_Lean_Meta_instanceExtension;
v_ext_5076_ = lean_ctor_get(v___x_5075_, 1);
v_toEnvExtension_5077_ = lean_ctor_get(v_ext_5076_, 0);
v_asyncMode_5078_ = lean_ctor_get(v_toEnvExtension_5077_, 2);
v___x_5079_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5080_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5079_, v___x_5075_, v_env_5074_, v_asyncMode_5078_);
v_discrTree_5081_ = lean_ctor_get(v___x_5080_, 0);
lean_inc_ref(v_discrTree_5081_);
lean_dec(v___x_5080_);
v___x_5082_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5082_, 0, v_discrTree_5081_);
return v___x_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_5083_, lean_object* v_a_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5083_);
lean_dec(v_a_5083_);
return v_res_5085_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_5086_, lean_object* v_a_5087_){
_start:
{
lean_object* v___x_5089_; 
v___x_5089_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5087_);
return v___x_5089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_5090_, lean_object* v_a_5091_, lean_object* v_a_5092_){
_start:
{
lean_object* v_res_5093_; 
v_res_5093_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_5090_, v_a_5091_);
lean_dec(v_a_5091_);
lean_dec_ref(v_a_5090_);
return v_res_5093_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_5094_){
_start:
{
lean_object* v___x_5096_; lean_object* v_env_5097_; lean_object* v___x_5098_; lean_object* v_ext_5099_; lean_object* v_toEnvExtension_5100_; lean_object* v_asyncMode_5101_; lean_object* v___x_5102_; lean_object* v___x_5103_; lean_object* v_erased_5104_; lean_object* v___x_5105_; 
v___x_5096_ = lean_st_ref_get(v_a_5094_);
v_env_5097_ = lean_ctor_get(v___x_5096_, 0);
lean_inc_ref(v_env_5097_);
lean_dec(v___x_5096_);
v___x_5098_ = l_Lean_Meta_instanceExtension;
v_ext_5099_ = lean_ctor_get(v___x_5098_, 1);
v_toEnvExtension_5100_ = lean_ctor_get(v_ext_5099_, 0);
v_asyncMode_5101_ = lean_ctor_get(v_toEnvExtension_5100_, 2);
v___x_5102_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5103_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5102_, v___x_5098_, v_env_5097_, v_asyncMode_5101_);
v_erased_5104_ = lean_ctor_get(v___x_5103_, 2);
lean_inc_ref(v_erased_5104_);
lean_dec(v___x_5103_);
v___x_5105_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5105_, 0, v_erased_5104_);
return v___x_5105_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_5106_, lean_object* v_a_5107_){
_start:
{
lean_object* v_res_5108_; 
v_res_5108_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5106_);
lean_dec(v_a_5106_);
return v_res_5108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v___x_5112_; 
v___x_5112_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5110_);
return v___x_5112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_){
_start:
{
lean_object* v_res_5116_; 
v_res_5116_ = l_Lean_Meta_getErasedInstances(v_a_5113_, v_a_5114_);
lean_dec(v_a_5114_);
lean_dec_ref(v_a_5113_);
return v_res_5116_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_5117_, lean_object* v_declName_5118_){
_start:
{
lean_object* v___x_5119_; lean_object* v_ext_5120_; lean_object* v_toEnvExtension_5121_; lean_object* v_asyncMode_5122_; lean_object* v___x_5123_; lean_object* v___x_5124_; lean_object* v_instanceNames_5125_; uint8_t v___x_5126_; 
v___x_5119_ = l_Lean_Meta_instanceExtension;
v_ext_5120_ = lean_ctor_get(v___x_5119_, 1);
v_toEnvExtension_5121_ = lean_ctor_get(v_ext_5120_, 0);
v_asyncMode_5122_ = lean_ctor_get(v_toEnvExtension_5121_, 2);
v___x_5123_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5124_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5123_, v___x_5119_, v_env_5117_, v_asyncMode_5122_);
v_instanceNames_5125_ = lean_ctor_get(v___x_5124_, 1);
lean_inc_ref(v_instanceNames_5125_);
lean_dec(v___x_5124_);
v___x_5126_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_5125_, v_declName_5118_);
lean_dec_ref(v_instanceNames_5125_);
return v___x_5126_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_5127_, lean_object* v_declName_5128_){
_start:
{
uint8_t v_res_5129_; lean_object* v_r_5130_; 
v_res_5129_ = l_Lean_Meta_isInstanceCore(v_env_5127_, v_declName_5128_);
lean_dec(v_declName_5128_);
v_r_5130_ = lean_box(v_res_5129_);
return v_r_5130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_5131_, lean_object* v_a_5132_){
_start:
{
lean_object* v___x_5134_; lean_object* v_env_5135_; uint8_t v___x_5136_; lean_object* v___x_5137_; lean_object* v___x_5138_; 
v___x_5134_ = lean_st_ref_get(v_a_5132_);
v_env_5135_ = lean_ctor_get(v___x_5134_, 0);
lean_inc_ref(v_env_5135_);
lean_dec(v___x_5134_);
v___x_5136_ = l_Lean_Meta_isInstanceCore(v_env_5135_, v_declName_5131_);
v___x_5137_ = lean_box(v___x_5136_);
v___x_5138_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5138_, 0, v___x_5137_);
return v___x_5138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_5139_, lean_object* v_a_5140_, lean_object* v_a_5141_){
_start:
{
lean_object* v_res_5142_; 
v_res_5142_ = l_Lean_Meta_isInstance___redArg(v_declName_5139_, v_a_5140_);
lean_dec(v_a_5140_);
lean_dec(v_declName_5139_);
return v_res_5142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_5143_, lean_object* v_a_5144_, lean_object* v_a_5145_){
_start:
{
lean_object* v___x_5147_; 
v___x_5147_ = l_Lean_Meta_isInstance___redArg(v_declName_5143_, v_a_5145_);
return v___x_5147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_5148_, lean_object* v_a_5149_, lean_object* v_a_5150_, lean_object* v_a_5151_){
_start:
{
lean_object* v_res_5152_; 
v_res_5152_ = l_Lean_Meta_isInstance(v_declName_5148_, v_a_5149_, v_a_5150_);
lean_dec(v_a_5150_);
lean_dec_ref(v_a_5149_);
lean_dec(v_declName_5148_);
return v_res_5152_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5153_, lean_object* v_vals_5154_, lean_object* v_i_5155_, lean_object* v_k_5156_){
_start:
{
lean_object* v___x_5157_; uint8_t v___x_5158_; 
v___x_5157_ = lean_array_get_size(v_keys_5153_);
v___x_5158_ = lean_nat_dec_lt(v_i_5155_, v___x_5157_);
if (v___x_5158_ == 0)
{
lean_object* v___x_5159_; 
lean_dec(v_i_5155_);
v___x_5159_ = lean_box(0);
return v___x_5159_;
}
else
{
lean_object* v_k_x27_5160_; uint8_t v___x_5161_; 
v_k_x27_5160_ = lean_array_fget_borrowed(v_keys_5153_, v_i_5155_);
v___x_5161_ = lean_name_eq(v_k_5156_, v_k_x27_5160_);
if (v___x_5161_ == 0)
{
lean_object* v___x_5162_; lean_object* v___x_5163_; 
v___x_5162_ = lean_unsigned_to_nat(1u);
v___x_5163_ = lean_nat_add(v_i_5155_, v___x_5162_);
lean_dec(v_i_5155_);
v_i_5155_ = v___x_5163_;
goto _start;
}
else
{
lean_object* v___x_5165_; lean_object* v___x_5166_; 
v___x_5165_ = lean_array_fget_borrowed(v_vals_5154_, v_i_5155_);
lean_dec(v_i_5155_);
lean_inc(v___x_5165_);
v___x_5166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5166_, 0, v___x_5165_);
return v___x_5166_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5167_, lean_object* v_vals_5168_, lean_object* v_i_5169_, lean_object* v_k_5170_){
_start:
{
lean_object* v_res_5171_; 
v_res_5171_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5167_, v_vals_5168_, v_i_5169_, v_k_5170_);
lean_dec(v_k_5170_);
lean_dec_ref(v_vals_5168_);
lean_dec_ref(v_keys_5167_);
return v_res_5171_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_5172_, size_t v_x_5173_, lean_object* v_x_5174_){
_start:
{
if (lean_obj_tag(v_x_5172_) == 0)
{
lean_object* v_es_5175_; lean_object* v___x_5176_; size_t v___x_5177_; size_t v___x_5178_; lean_object* v_j_5179_; lean_object* v___x_5180_; 
v_es_5175_ = lean_ctor_get(v_x_5172_, 0);
v___x_5176_ = lean_box(2);
v___x_5177_ = ((size_t)31ULL);
v___x_5178_ = lean_usize_land(v_x_5173_, v___x_5177_);
v_j_5179_ = lean_usize_to_nat(v___x_5178_);
v___x_5180_ = lean_array_get_borrowed(v___x_5176_, v_es_5175_, v_j_5179_);
lean_dec(v_j_5179_);
switch(lean_obj_tag(v___x_5180_))
{
case 0:
{
lean_object* v_key_5181_; lean_object* v_val_5182_; uint8_t v___x_5183_; 
v_key_5181_ = lean_ctor_get(v___x_5180_, 0);
v_val_5182_ = lean_ctor_get(v___x_5180_, 1);
v___x_5183_ = lean_name_eq(v_x_5174_, v_key_5181_);
if (v___x_5183_ == 0)
{
lean_object* v___x_5184_; 
v___x_5184_ = lean_box(0);
return v___x_5184_;
}
else
{
lean_object* v___x_5185_; 
lean_inc(v_val_5182_);
v___x_5185_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5185_, 0, v_val_5182_);
return v___x_5185_;
}
}
case 1:
{
lean_object* v_node_5186_; size_t v___x_5187_; size_t v___x_5188_; 
v_node_5186_ = lean_ctor_get(v___x_5180_, 0);
v___x_5187_ = ((size_t)5ULL);
v___x_5188_ = lean_usize_shift_right(v_x_5173_, v___x_5187_);
v_x_5172_ = v_node_5186_;
v_x_5173_ = v___x_5188_;
goto _start;
}
default: 
{
lean_object* v___x_5190_; 
v___x_5190_ = lean_box(0);
return v___x_5190_;
}
}
}
else
{
lean_object* v_ks_5191_; lean_object* v_vs_5192_; lean_object* v___x_5193_; lean_object* v___x_5194_; 
v_ks_5191_ = lean_ctor_get(v_x_5172_, 0);
v_vs_5192_ = lean_ctor_get(v_x_5172_, 1);
v___x_5193_ = lean_unsigned_to_nat(0u);
v___x_5194_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5191_, v_vs_5192_, v___x_5193_, v_x_5174_);
return v___x_5194_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5195_, lean_object* v_x_5196_, lean_object* v_x_5197_){
_start:
{
size_t v_x_477__boxed_5198_; lean_object* v_res_5199_; 
v_x_477__boxed_5198_ = lean_unbox_usize(v_x_5196_);
lean_dec(v_x_5196_);
v_res_5199_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5195_, v_x_477__boxed_5198_, v_x_5197_);
lean_dec(v_x_5197_);
lean_dec_ref(v_x_5195_);
return v_res_5199_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_5200_, lean_object* v_x_5201_){
_start:
{
uint64_t v___y_5203_; 
if (lean_obj_tag(v_x_5201_) == 0)
{
uint64_t v___x_5206_; 
v___x_5206_ = 1723ULL;
v___y_5203_ = v___x_5206_;
goto v___jp_5202_;
}
else
{
uint64_t v_hash_5207_; 
v_hash_5207_ = lean_ctor_get_uint64(v_x_5201_, sizeof(void*)*2);
v___y_5203_ = v_hash_5207_;
goto v___jp_5202_;
}
v___jp_5202_:
{
size_t v___x_5204_; lean_object* v___x_5205_; 
v___x_5204_ = lean_uint64_to_usize(v___y_5203_);
v___x_5205_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5200_, v___x_5204_, v_x_5201_);
return v___x_5205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_5208_, lean_object* v_x_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5208_, v_x_5209_);
lean_dec(v_x_5209_);
lean_dec_ref(v_x_5208_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_5211_, lean_object* v_a_5212_){
_start:
{
lean_object* v___x_5214_; lean_object* v_env_5215_; lean_object* v___x_5216_; lean_object* v_ext_5217_; lean_object* v_toEnvExtension_5218_; lean_object* v_asyncMode_5219_; lean_object* v___x_5220_; lean_object* v___x_5221_; lean_object* v_instanceNames_5222_; lean_object* v___x_5223_; 
v___x_5214_ = lean_st_ref_get(v_a_5212_);
v_env_5215_ = lean_ctor_get(v___x_5214_, 0);
lean_inc_ref(v_env_5215_);
lean_dec(v___x_5214_);
v___x_5216_ = l_Lean_Meta_instanceExtension;
v_ext_5217_ = lean_ctor_get(v___x_5216_, 1);
v_toEnvExtension_5218_ = lean_ctor_get(v_ext_5217_, 0);
v_asyncMode_5219_ = lean_ctor_get(v_toEnvExtension_5218_, 2);
v___x_5220_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5221_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5220_, v___x_5216_, v_env_5215_, v_asyncMode_5219_);
v_instanceNames_5222_ = lean_ctor_get(v___x_5221_, 1);
lean_inc_ref(v_instanceNames_5222_);
lean_dec(v___x_5221_);
v___x_5223_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5222_, v_declName_5211_);
lean_dec_ref(v_instanceNames_5222_);
if (lean_obj_tag(v___x_5223_) == 1)
{
lean_object* v_val_5224_; lean_object* v___x_5226_; uint8_t v_isShared_5227_; uint8_t v_isSharedCheck_5233_; 
v_val_5224_ = lean_ctor_get(v___x_5223_, 0);
v_isSharedCheck_5233_ = !lean_is_exclusive(v___x_5223_);
if (v_isSharedCheck_5233_ == 0)
{
v___x_5226_ = v___x_5223_;
v_isShared_5227_ = v_isSharedCheck_5233_;
goto v_resetjp_5225_;
}
else
{
lean_inc(v_val_5224_);
lean_dec(v___x_5223_);
v___x_5226_ = lean_box(0);
v_isShared_5227_ = v_isSharedCheck_5233_;
goto v_resetjp_5225_;
}
v_resetjp_5225_:
{
lean_object* v_priority_5228_; lean_object* v___x_5230_; 
v_priority_5228_ = lean_ctor_get(v_val_5224_, 2);
lean_inc(v_priority_5228_);
lean_dec(v_val_5224_);
if (v_isShared_5227_ == 0)
{
lean_ctor_set(v___x_5226_, 0, v_priority_5228_);
v___x_5230_ = v___x_5226_;
goto v_reusejp_5229_;
}
else
{
lean_object* v_reuseFailAlloc_5232_; 
v_reuseFailAlloc_5232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5232_, 0, v_priority_5228_);
v___x_5230_ = v_reuseFailAlloc_5232_;
goto v_reusejp_5229_;
}
v_reusejp_5229_:
{
lean_object* v___x_5231_; 
v___x_5231_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5231_, 0, v___x_5230_);
return v___x_5231_;
}
}
}
else
{
lean_object* v___x_5234_; lean_object* v___x_5235_; 
lean_dec(v___x_5223_);
v___x_5234_ = lean_box(0);
v___x_5235_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5235_, 0, v___x_5234_);
return v___x_5235_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_5236_, lean_object* v_a_5237_, lean_object* v_a_5238_){
_start:
{
lean_object* v_res_5239_; 
v_res_5239_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5236_, v_a_5237_);
lean_dec(v_a_5237_);
lean_dec(v_declName_5236_);
return v_res_5239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_5240_, lean_object* v_a_5241_, lean_object* v_a_5242_){
_start:
{
lean_object* v___x_5244_; 
v___x_5244_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5240_, v_a_5242_);
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_5245_, lean_object* v_a_5246_, lean_object* v_a_5247_, lean_object* v_a_5248_){
_start:
{
lean_object* v_res_5249_; 
v_res_5249_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_5245_, v_a_5246_, v_a_5247_);
lean_dec(v_a_5247_);
lean_dec_ref(v_a_5246_);
lean_dec(v_declName_5245_);
return v_res_5249_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_5250_, lean_object* v_x_5251_, lean_object* v_x_5252_){
_start:
{
lean_object* v___x_5253_; 
v___x_5253_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5251_, v_x_5252_);
return v___x_5253_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_5254_, lean_object* v_x_5255_, lean_object* v_x_5256_){
_start:
{
lean_object* v_res_5257_; 
v_res_5257_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_5254_, v_x_5255_, v_x_5256_);
lean_dec(v_x_5256_);
lean_dec_ref(v_x_5255_);
return v_res_5257_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5258_, lean_object* v_x_5259_, size_t v_x_5260_, lean_object* v_x_5261_){
_start:
{
lean_object* v___x_5262_; 
v___x_5262_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5259_, v_x_5260_, v_x_5261_);
return v___x_5262_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5263_, lean_object* v_x_5264_, lean_object* v_x_5265_, lean_object* v_x_5266_){
_start:
{
size_t v_x_588__boxed_5267_; lean_object* v_res_5268_; 
v_x_588__boxed_5267_ = lean_unbox_usize(v_x_5265_);
lean_dec(v_x_5265_);
v_res_5268_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_5263_, v_x_5264_, v_x_588__boxed_5267_, v_x_5266_);
lean_dec(v_x_5266_);
lean_dec_ref(v_x_5264_);
return v_res_5268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5269_, lean_object* v_keys_5270_, lean_object* v_vals_5271_, lean_object* v_heq_5272_, lean_object* v_i_5273_, lean_object* v_k_5274_){
_start:
{
lean_object* v___x_5275_; 
v___x_5275_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5270_, v_vals_5271_, v_i_5273_, v_k_5274_);
return v___x_5275_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5276_, lean_object* v_keys_5277_, lean_object* v_vals_5278_, lean_object* v_heq_5279_, lean_object* v_i_5280_, lean_object* v_k_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5276_, v_keys_5277_, v_vals_5278_, v_heq_5279_, v_i_5280_, v_k_5281_);
lean_dec(v_k_5281_);
lean_dec_ref(v_vals_5278_);
lean_dec_ref(v_keys_5277_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_5283_, lean_object* v_a_5284_){
_start:
{
lean_object* v___x_5286_; lean_object* v_env_5287_; lean_object* v___x_5288_; lean_object* v_ext_5289_; lean_object* v_toEnvExtension_5290_; lean_object* v_asyncMode_5291_; lean_object* v___x_5292_; lean_object* v___x_5293_; lean_object* v_instanceNames_5294_; lean_object* v___x_5295_; 
v___x_5286_ = lean_st_ref_get(v_a_5284_);
v_env_5287_ = lean_ctor_get(v___x_5286_, 0);
lean_inc_ref(v_env_5287_);
lean_dec(v___x_5286_);
v___x_5288_ = l_Lean_Meta_instanceExtension;
v_ext_5289_ = lean_ctor_get(v___x_5288_, 1);
v_toEnvExtension_5290_ = lean_ctor_get(v_ext_5289_, 0);
v_asyncMode_5291_ = lean_ctor_get(v_toEnvExtension_5290_, 2);
v___x_5292_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5293_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5292_, v___x_5288_, v_env_5287_, v_asyncMode_5291_);
v_instanceNames_5294_ = lean_ctor_get(v___x_5293_, 1);
lean_inc_ref(v_instanceNames_5294_);
lean_dec(v___x_5293_);
v___x_5295_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5294_, v_declName_5283_);
lean_dec_ref(v_instanceNames_5294_);
if (lean_obj_tag(v___x_5295_) == 1)
{
lean_object* v_val_5296_; lean_object* v___x_5298_; uint8_t v_isShared_5299_; uint8_t v_isSharedCheck_5306_; 
v_val_5296_ = lean_ctor_get(v___x_5295_, 0);
v_isSharedCheck_5306_ = !lean_is_exclusive(v___x_5295_);
if (v_isSharedCheck_5306_ == 0)
{
v___x_5298_ = v___x_5295_;
v_isShared_5299_ = v_isSharedCheck_5306_;
goto v_resetjp_5297_;
}
else
{
lean_inc(v_val_5296_);
lean_dec(v___x_5295_);
v___x_5298_ = lean_box(0);
v_isShared_5299_ = v_isSharedCheck_5306_;
goto v_resetjp_5297_;
}
v_resetjp_5297_:
{
uint8_t v_attrKind_5300_; lean_object* v___x_5301_; lean_object* v___x_5303_; 
v_attrKind_5300_ = lean_ctor_get_uint8(v_val_5296_, sizeof(void*)*5);
lean_dec(v_val_5296_);
v___x_5301_ = lean_box(v_attrKind_5300_);
if (v_isShared_5299_ == 0)
{
lean_ctor_set(v___x_5298_, 0, v___x_5301_);
v___x_5303_ = v___x_5298_;
goto v_reusejp_5302_;
}
else
{
lean_object* v_reuseFailAlloc_5305_; 
v_reuseFailAlloc_5305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5305_, 0, v___x_5301_);
v___x_5303_ = v_reuseFailAlloc_5305_;
goto v_reusejp_5302_;
}
v_reusejp_5302_:
{
lean_object* v___x_5304_; 
v___x_5304_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5304_, 0, v___x_5303_);
return v___x_5304_;
}
}
}
else
{
lean_object* v___x_5307_; lean_object* v___x_5308_; 
lean_dec(v___x_5295_);
v___x_5307_ = lean_box(0);
v___x_5308_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5308_, 0, v___x_5307_);
return v___x_5308_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_5309_, lean_object* v_a_5310_, lean_object* v_a_5311_){
_start:
{
lean_object* v_res_5312_; 
v_res_5312_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5309_, v_a_5310_);
lean_dec(v_a_5310_);
lean_dec(v_declName_5309_);
return v_res_5312_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_5313_, lean_object* v_a_5314_, lean_object* v_a_5315_){
_start:
{
lean_object* v___x_5317_; 
v___x_5317_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5313_, v_a_5315_);
return v___x_5317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_5318_, lean_object* v_a_5319_, lean_object* v_a_5320_, lean_object* v_a_5321_){
_start:
{
lean_object* v_res_5322_; 
v_res_5322_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_5318_, v_a_5319_, v_a_5320_);
lean_dec(v_a_5320_);
lean_dec_ref(v_a_5319_);
lean_dec(v_declName_5318_);
return v_res_5322_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5327_, lean_object* v_v_5328_, lean_object* v_t_5329_){
_start:
{
if (lean_obj_tag(v_t_5329_) == 0)
{
lean_object* v_size_5330_; lean_object* v_k_5331_; lean_object* v_v_5332_; lean_object* v_l_5333_; lean_object* v_r_5334_; lean_object* v___x_5336_; uint8_t v_isShared_5337_; uint8_t v_isSharedCheck_5615_; 
v_size_5330_ = lean_ctor_get(v_t_5329_, 0);
v_k_5331_ = lean_ctor_get(v_t_5329_, 1);
v_v_5332_ = lean_ctor_get(v_t_5329_, 2);
v_l_5333_ = lean_ctor_get(v_t_5329_, 3);
v_r_5334_ = lean_ctor_get(v_t_5329_, 4);
v_isSharedCheck_5615_ = !lean_is_exclusive(v_t_5329_);
if (v_isSharedCheck_5615_ == 0)
{
v___x_5336_ = v_t_5329_;
v_isShared_5337_ = v_isSharedCheck_5615_;
goto v_resetjp_5335_;
}
else
{
lean_inc(v_r_5334_);
lean_inc(v_l_5333_);
lean_inc(v_v_5332_);
lean_inc(v_k_5331_);
lean_inc(v_size_5330_);
lean_dec(v_t_5329_);
v___x_5336_ = lean_box(0);
v_isShared_5337_ = v_isSharedCheck_5615_;
goto v_resetjp_5335_;
}
v_resetjp_5335_:
{
uint8_t v___x_5338_; 
v___x_5338_ = lean_nat_dec_lt(v_k_5331_, v_k_5327_);
if (v___x_5338_ == 0)
{
uint8_t v___x_5339_; 
v___x_5339_ = lean_nat_dec_eq(v_k_5331_, v_k_5327_);
if (v___x_5339_ == 0)
{
lean_object* v_impl_5340_; lean_object* v___x_5341_; 
lean_dec(v_size_5330_);
v_impl_5340_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5327_, v_v_5328_, v_r_5334_);
v___x_5341_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5333_) == 0)
{
lean_object* v_size_5342_; lean_object* v_size_5343_; lean_object* v_k_5344_; lean_object* v_v_5345_; lean_object* v_l_5346_; lean_object* v_r_5347_; lean_object* v___x_5348_; lean_object* v___x_5349_; uint8_t v___x_5350_; 
v_size_5342_ = lean_ctor_get(v_l_5333_, 0);
v_size_5343_ = lean_ctor_get(v_impl_5340_, 0);
lean_inc(v_size_5343_);
v_k_5344_ = lean_ctor_get(v_impl_5340_, 1);
lean_inc(v_k_5344_);
v_v_5345_ = lean_ctor_get(v_impl_5340_, 2);
lean_inc(v_v_5345_);
v_l_5346_ = lean_ctor_get(v_impl_5340_, 3);
lean_inc(v_l_5346_);
v_r_5347_ = lean_ctor_get(v_impl_5340_, 4);
lean_inc(v_r_5347_);
v___x_5348_ = lean_unsigned_to_nat(3u);
v___x_5349_ = lean_nat_mul(v___x_5348_, v_size_5342_);
v___x_5350_ = lean_nat_dec_lt(v___x_5349_, v_size_5343_);
lean_dec(v___x_5349_);
if (v___x_5350_ == 0)
{
lean_object* v___x_5351_; lean_object* v___x_5352_; lean_object* v___x_5354_; 
lean_dec(v_r_5347_);
lean_dec(v_l_5346_);
lean_dec(v_v_5345_);
lean_dec(v_k_5344_);
v___x_5351_ = lean_nat_add(v___x_5341_, v_size_5342_);
v___x_5352_ = lean_nat_add(v___x_5351_, v_size_5343_);
lean_dec(v_size_5343_);
lean_dec(v___x_5351_);
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 4, v_impl_5340_);
lean_ctor_set(v___x_5336_, 0, v___x_5352_);
v___x_5354_ = v___x_5336_;
goto v_reusejp_5353_;
}
else
{
lean_object* v_reuseFailAlloc_5355_; 
v_reuseFailAlloc_5355_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5355_, 0, v___x_5352_);
lean_ctor_set(v_reuseFailAlloc_5355_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5355_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5355_, 3, v_l_5333_);
lean_ctor_set(v_reuseFailAlloc_5355_, 4, v_impl_5340_);
v___x_5354_ = v_reuseFailAlloc_5355_;
goto v_reusejp_5353_;
}
v_reusejp_5353_:
{
return v___x_5354_;
}
}
else
{
lean_object* v___x_5357_; uint8_t v_isShared_5358_; uint8_t v_isSharedCheck_5419_; 
v_isSharedCheck_5419_ = !lean_is_exclusive(v_impl_5340_);
if (v_isSharedCheck_5419_ == 0)
{
lean_object* v_unused_5420_; lean_object* v_unused_5421_; lean_object* v_unused_5422_; lean_object* v_unused_5423_; lean_object* v_unused_5424_; 
v_unused_5420_ = lean_ctor_get(v_impl_5340_, 4);
lean_dec(v_unused_5420_);
v_unused_5421_ = lean_ctor_get(v_impl_5340_, 3);
lean_dec(v_unused_5421_);
v_unused_5422_ = lean_ctor_get(v_impl_5340_, 2);
lean_dec(v_unused_5422_);
v_unused_5423_ = lean_ctor_get(v_impl_5340_, 1);
lean_dec(v_unused_5423_);
v_unused_5424_ = lean_ctor_get(v_impl_5340_, 0);
lean_dec(v_unused_5424_);
v___x_5357_ = v_impl_5340_;
v_isShared_5358_ = v_isSharedCheck_5419_;
goto v_resetjp_5356_;
}
else
{
lean_dec(v_impl_5340_);
v___x_5357_ = lean_box(0);
v_isShared_5358_ = v_isSharedCheck_5419_;
goto v_resetjp_5356_;
}
v_resetjp_5356_:
{
lean_object* v_size_5359_; lean_object* v_k_5360_; lean_object* v_v_5361_; lean_object* v_l_5362_; lean_object* v_r_5363_; lean_object* v_size_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; uint8_t v___x_5367_; 
v_size_5359_ = lean_ctor_get(v_l_5346_, 0);
v_k_5360_ = lean_ctor_get(v_l_5346_, 1);
v_v_5361_ = lean_ctor_get(v_l_5346_, 2);
v_l_5362_ = lean_ctor_get(v_l_5346_, 3);
v_r_5363_ = lean_ctor_get(v_l_5346_, 4);
v_size_5364_ = lean_ctor_get(v_r_5347_, 0);
v___x_5365_ = lean_unsigned_to_nat(2u);
v___x_5366_ = lean_nat_mul(v___x_5365_, v_size_5364_);
v___x_5367_ = lean_nat_dec_lt(v_size_5359_, v___x_5366_);
lean_dec(v___x_5366_);
if (v___x_5367_ == 0)
{
lean_object* v___x_5369_; uint8_t v_isShared_5370_; uint8_t v_isSharedCheck_5395_; 
lean_inc(v_r_5363_);
lean_inc(v_l_5362_);
lean_inc(v_v_5361_);
lean_inc(v_k_5360_);
v_isSharedCheck_5395_ = !lean_is_exclusive(v_l_5346_);
if (v_isSharedCheck_5395_ == 0)
{
lean_object* v_unused_5396_; lean_object* v_unused_5397_; lean_object* v_unused_5398_; lean_object* v_unused_5399_; lean_object* v_unused_5400_; 
v_unused_5396_ = lean_ctor_get(v_l_5346_, 4);
lean_dec(v_unused_5396_);
v_unused_5397_ = lean_ctor_get(v_l_5346_, 3);
lean_dec(v_unused_5397_);
v_unused_5398_ = lean_ctor_get(v_l_5346_, 2);
lean_dec(v_unused_5398_);
v_unused_5399_ = lean_ctor_get(v_l_5346_, 1);
lean_dec(v_unused_5399_);
v_unused_5400_ = lean_ctor_get(v_l_5346_, 0);
lean_dec(v_unused_5400_);
v___x_5369_ = v_l_5346_;
v_isShared_5370_ = v_isSharedCheck_5395_;
goto v_resetjp_5368_;
}
else
{
lean_dec(v_l_5346_);
v___x_5369_ = lean_box(0);
v_isShared_5370_ = v_isSharedCheck_5395_;
goto v_resetjp_5368_;
}
v_resetjp_5368_:
{
lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___y_5374_; lean_object* v___y_5375_; lean_object* v___y_5376_; lean_object* v___y_5385_; 
v___x_5371_ = lean_nat_add(v___x_5341_, v_size_5342_);
v___x_5372_ = lean_nat_add(v___x_5371_, v_size_5343_);
lean_dec(v_size_5343_);
if (lean_obj_tag(v_l_5362_) == 0)
{
lean_object* v_size_5393_; 
v_size_5393_ = lean_ctor_get(v_l_5362_, 0);
lean_inc(v_size_5393_);
v___y_5385_ = v_size_5393_;
goto v___jp_5384_;
}
else
{
lean_object* v___x_5394_; 
v___x_5394_ = lean_unsigned_to_nat(0u);
v___y_5385_ = v___x_5394_;
goto v___jp_5384_;
}
v___jp_5373_:
{
lean_object* v___x_5377_; lean_object* v___x_5379_; 
v___x_5377_ = lean_nat_add(v___y_5375_, v___y_5376_);
lean_dec(v___y_5376_);
lean_dec(v___y_5375_);
if (v_isShared_5370_ == 0)
{
lean_ctor_set(v___x_5369_, 4, v_r_5347_);
lean_ctor_set(v___x_5369_, 3, v_r_5363_);
lean_ctor_set(v___x_5369_, 2, v_v_5345_);
lean_ctor_set(v___x_5369_, 1, v_k_5344_);
lean_ctor_set(v___x_5369_, 0, v___x_5377_);
v___x_5379_ = v___x_5369_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5383_; 
v_reuseFailAlloc_5383_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5383_, 0, v___x_5377_);
lean_ctor_set(v_reuseFailAlloc_5383_, 1, v_k_5344_);
lean_ctor_set(v_reuseFailAlloc_5383_, 2, v_v_5345_);
lean_ctor_set(v_reuseFailAlloc_5383_, 3, v_r_5363_);
lean_ctor_set(v_reuseFailAlloc_5383_, 4, v_r_5347_);
v___x_5379_ = v_reuseFailAlloc_5383_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
lean_object* v___x_5381_; 
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 4, v___x_5379_);
lean_ctor_set(v___x_5357_, 3, v___y_5374_);
lean_ctor_set(v___x_5357_, 2, v_v_5361_);
lean_ctor_set(v___x_5357_, 1, v_k_5360_);
lean_ctor_set(v___x_5357_, 0, v___x_5372_);
v___x_5381_ = v___x_5357_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v___x_5372_);
lean_ctor_set(v_reuseFailAlloc_5382_, 1, v_k_5360_);
lean_ctor_set(v_reuseFailAlloc_5382_, 2, v_v_5361_);
lean_ctor_set(v_reuseFailAlloc_5382_, 3, v___y_5374_);
lean_ctor_set(v_reuseFailAlloc_5382_, 4, v___x_5379_);
v___x_5381_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
return v___x_5381_;
}
}
}
v___jp_5384_:
{
lean_object* v___x_5386_; lean_object* v___x_5388_; 
v___x_5386_ = lean_nat_add(v___x_5371_, v___y_5385_);
lean_dec(v___y_5385_);
lean_dec(v___x_5371_);
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 4, v_l_5362_);
lean_ctor_set(v___x_5336_, 0, v___x_5386_);
v___x_5388_ = v___x_5336_;
goto v_reusejp_5387_;
}
else
{
lean_object* v_reuseFailAlloc_5392_; 
v_reuseFailAlloc_5392_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5392_, 0, v___x_5386_);
lean_ctor_set(v_reuseFailAlloc_5392_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5392_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5392_, 3, v_l_5333_);
lean_ctor_set(v_reuseFailAlloc_5392_, 4, v_l_5362_);
v___x_5388_ = v_reuseFailAlloc_5392_;
goto v_reusejp_5387_;
}
v_reusejp_5387_:
{
lean_object* v___x_5389_; 
v___x_5389_ = lean_nat_add(v___x_5341_, v_size_5364_);
if (lean_obj_tag(v_r_5363_) == 0)
{
lean_object* v_size_5390_; 
v_size_5390_ = lean_ctor_get(v_r_5363_, 0);
lean_inc(v_size_5390_);
v___y_5374_ = v___x_5388_;
v___y_5375_ = v___x_5389_;
v___y_5376_ = v_size_5390_;
goto v___jp_5373_;
}
else
{
lean_object* v___x_5391_; 
v___x_5391_ = lean_unsigned_to_nat(0u);
v___y_5374_ = v___x_5388_;
v___y_5375_ = v___x_5389_;
v___y_5376_ = v___x_5391_;
goto v___jp_5373_;
}
}
}
}
}
else
{
lean_object* v___x_5401_; lean_object* v___x_5402_; lean_object* v___x_5403_; lean_object* v___x_5405_; 
lean_del_object(v___x_5336_);
v___x_5401_ = lean_nat_add(v___x_5341_, v_size_5342_);
v___x_5402_ = lean_nat_add(v___x_5401_, v_size_5343_);
lean_dec(v_size_5343_);
v___x_5403_ = lean_nat_add(v___x_5401_, v_size_5359_);
lean_dec(v___x_5401_);
lean_inc_ref(v_l_5333_);
if (v_isShared_5358_ == 0)
{
lean_ctor_set(v___x_5357_, 4, v_l_5346_);
lean_ctor_set(v___x_5357_, 3, v_l_5333_);
lean_ctor_set(v___x_5357_, 2, v_v_5332_);
lean_ctor_set(v___x_5357_, 1, v_k_5331_);
lean_ctor_set(v___x_5357_, 0, v___x_5403_);
v___x_5405_ = v___x_5357_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5418_; 
v_reuseFailAlloc_5418_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5418_, 0, v___x_5403_);
lean_ctor_set(v_reuseFailAlloc_5418_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5418_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5418_, 3, v_l_5333_);
lean_ctor_set(v_reuseFailAlloc_5418_, 4, v_l_5346_);
v___x_5405_ = v_reuseFailAlloc_5418_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
lean_object* v___x_5407_; uint8_t v_isShared_5408_; uint8_t v_isSharedCheck_5412_; 
v_isSharedCheck_5412_ = !lean_is_exclusive(v_l_5333_);
if (v_isSharedCheck_5412_ == 0)
{
lean_object* v_unused_5413_; lean_object* v_unused_5414_; lean_object* v_unused_5415_; lean_object* v_unused_5416_; lean_object* v_unused_5417_; 
v_unused_5413_ = lean_ctor_get(v_l_5333_, 4);
lean_dec(v_unused_5413_);
v_unused_5414_ = lean_ctor_get(v_l_5333_, 3);
lean_dec(v_unused_5414_);
v_unused_5415_ = lean_ctor_get(v_l_5333_, 2);
lean_dec(v_unused_5415_);
v_unused_5416_ = lean_ctor_get(v_l_5333_, 1);
lean_dec(v_unused_5416_);
v_unused_5417_ = lean_ctor_get(v_l_5333_, 0);
lean_dec(v_unused_5417_);
v___x_5407_ = v_l_5333_;
v_isShared_5408_ = v_isSharedCheck_5412_;
goto v_resetjp_5406_;
}
else
{
lean_dec(v_l_5333_);
v___x_5407_ = lean_box(0);
v_isShared_5408_ = v_isSharedCheck_5412_;
goto v_resetjp_5406_;
}
v_resetjp_5406_:
{
lean_object* v___x_5410_; 
if (v_isShared_5408_ == 0)
{
lean_ctor_set(v___x_5407_, 4, v_r_5347_);
lean_ctor_set(v___x_5407_, 3, v___x_5405_);
lean_ctor_set(v___x_5407_, 2, v_v_5345_);
lean_ctor_set(v___x_5407_, 1, v_k_5344_);
lean_ctor_set(v___x_5407_, 0, v___x_5402_);
v___x_5410_ = v___x_5407_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5411_; 
v_reuseFailAlloc_5411_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5411_, 0, v___x_5402_);
lean_ctor_set(v_reuseFailAlloc_5411_, 1, v_k_5344_);
lean_ctor_set(v_reuseFailAlloc_5411_, 2, v_v_5345_);
lean_ctor_set(v_reuseFailAlloc_5411_, 3, v___x_5405_);
lean_ctor_set(v_reuseFailAlloc_5411_, 4, v_r_5347_);
v___x_5410_ = v_reuseFailAlloc_5411_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
return v___x_5410_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5425_; 
v_l_5425_ = lean_ctor_get(v_impl_5340_, 3);
lean_inc(v_l_5425_);
if (lean_obj_tag(v_l_5425_) == 0)
{
lean_object* v_r_5426_; lean_object* v_k_5427_; lean_object* v_v_5428_; lean_object* v___x_5430_; uint8_t v_isShared_5431_; uint8_t v_isSharedCheck_5451_; 
v_r_5426_ = lean_ctor_get(v_impl_5340_, 4);
v_k_5427_ = lean_ctor_get(v_impl_5340_, 1);
v_v_5428_ = lean_ctor_get(v_impl_5340_, 2);
v_isSharedCheck_5451_ = !lean_is_exclusive(v_impl_5340_);
if (v_isSharedCheck_5451_ == 0)
{
lean_object* v_unused_5452_; lean_object* v_unused_5453_; 
v_unused_5452_ = lean_ctor_get(v_impl_5340_, 3);
lean_dec(v_unused_5452_);
v_unused_5453_ = lean_ctor_get(v_impl_5340_, 0);
lean_dec(v_unused_5453_);
v___x_5430_ = v_impl_5340_;
v_isShared_5431_ = v_isSharedCheck_5451_;
goto v_resetjp_5429_;
}
else
{
lean_inc(v_r_5426_);
lean_inc(v_v_5428_);
lean_inc(v_k_5427_);
lean_dec(v_impl_5340_);
v___x_5430_ = lean_box(0);
v_isShared_5431_ = v_isSharedCheck_5451_;
goto v_resetjp_5429_;
}
v_resetjp_5429_:
{
lean_object* v_k_5432_; lean_object* v_v_5433_; lean_object* v___x_5435_; uint8_t v_isShared_5436_; uint8_t v_isSharedCheck_5447_; 
v_k_5432_ = lean_ctor_get(v_l_5425_, 1);
v_v_5433_ = lean_ctor_get(v_l_5425_, 2);
v_isSharedCheck_5447_ = !lean_is_exclusive(v_l_5425_);
if (v_isSharedCheck_5447_ == 0)
{
lean_object* v_unused_5448_; lean_object* v_unused_5449_; lean_object* v_unused_5450_; 
v_unused_5448_ = lean_ctor_get(v_l_5425_, 4);
lean_dec(v_unused_5448_);
v_unused_5449_ = lean_ctor_get(v_l_5425_, 3);
lean_dec(v_unused_5449_);
v_unused_5450_ = lean_ctor_get(v_l_5425_, 0);
lean_dec(v_unused_5450_);
v___x_5435_ = v_l_5425_;
v_isShared_5436_ = v_isSharedCheck_5447_;
goto v_resetjp_5434_;
}
else
{
lean_inc(v_v_5433_);
lean_inc(v_k_5432_);
lean_dec(v_l_5425_);
v___x_5435_ = lean_box(0);
v_isShared_5436_ = v_isSharedCheck_5447_;
goto v_resetjp_5434_;
}
v_resetjp_5434_:
{
lean_object* v___x_5437_; lean_object* v___x_5439_; 
v___x_5437_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5426_, 2);
if (v_isShared_5436_ == 0)
{
lean_ctor_set(v___x_5435_, 4, v_r_5426_);
lean_ctor_set(v___x_5435_, 3, v_r_5426_);
lean_ctor_set(v___x_5435_, 2, v_v_5332_);
lean_ctor_set(v___x_5435_, 1, v_k_5331_);
lean_ctor_set(v___x_5435_, 0, v___x_5341_);
v___x_5439_ = v___x_5435_;
goto v_reusejp_5438_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v___x_5341_);
lean_ctor_set(v_reuseFailAlloc_5446_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5446_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5446_, 3, v_r_5426_);
lean_ctor_set(v_reuseFailAlloc_5446_, 4, v_r_5426_);
v___x_5439_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5438_;
}
v_reusejp_5438_:
{
lean_object* v___x_5441_; 
lean_inc(v_r_5426_);
if (v_isShared_5431_ == 0)
{
lean_ctor_set(v___x_5430_, 3, v_r_5426_);
lean_ctor_set(v___x_5430_, 0, v___x_5341_);
v___x_5441_ = v___x_5430_;
goto v_reusejp_5440_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v___x_5341_);
lean_ctor_set(v_reuseFailAlloc_5445_, 1, v_k_5427_);
lean_ctor_set(v_reuseFailAlloc_5445_, 2, v_v_5428_);
lean_ctor_set(v_reuseFailAlloc_5445_, 3, v_r_5426_);
lean_ctor_set(v_reuseFailAlloc_5445_, 4, v_r_5426_);
v___x_5441_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5440_;
}
v_reusejp_5440_:
{
lean_object* v___x_5443_; 
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 4, v___x_5441_);
lean_ctor_set(v___x_5336_, 3, v___x_5439_);
lean_ctor_set(v___x_5336_, 2, v_v_5433_);
lean_ctor_set(v___x_5336_, 1, v_k_5432_);
lean_ctor_set(v___x_5336_, 0, v___x_5437_);
v___x_5443_ = v___x_5336_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v___x_5437_);
lean_ctor_set(v_reuseFailAlloc_5444_, 1, v_k_5432_);
lean_ctor_set(v_reuseFailAlloc_5444_, 2, v_v_5433_);
lean_ctor_set(v_reuseFailAlloc_5444_, 3, v___x_5439_);
lean_ctor_set(v_reuseFailAlloc_5444_, 4, v___x_5441_);
v___x_5443_ = v_reuseFailAlloc_5444_;
goto v_reusejp_5442_;
}
v_reusejp_5442_:
{
return v___x_5443_;
}
}
}
}
}
}
else
{
lean_object* v_r_5454_; 
v_r_5454_ = lean_ctor_get(v_impl_5340_, 4);
lean_inc(v_r_5454_);
if (lean_obj_tag(v_r_5454_) == 0)
{
lean_object* v_k_5455_; lean_object* v_v_5456_; lean_object* v___x_5458_; uint8_t v_isShared_5459_; uint8_t v_isSharedCheck_5467_; 
v_k_5455_ = lean_ctor_get(v_impl_5340_, 1);
v_v_5456_ = lean_ctor_get(v_impl_5340_, 2);
v_isSharedCheck_5467_ = !lean_is_exclusive(v_impl_5340_);
if (v_isSharedCheck_5467_ == 0)
{
lean_object* v_unused_5468_; lean_object* v_unused_5469_; lean_object* v_unused_5470_; 
v_unused_5468_ = lean_ctor_get(v_impl_5340_, 4);
lean_dec(v_unused_5468_);
v_unused_5469_ = lean_ctor_get(v_impl_5340_, 3);
lean_dec(v_unused_5469_);
v_unused_5470_ = lean_ctor_get(v_impl_5340_, 0);
lean_dec(v_unused_5470_);
v___x_5458_ = v_impl_5340_;
v_isShared_5459_ = v_isSharedCheck_5467_;
goto v_resetjp_5457_;
}
else
{
lean_inc(v_v_5456_);
lean_inc(v_k_5455_);
lean_dec(v_impl_5340_);
v___x_5458_ = lean_box(0);
v_isShared_5459_ = v_isSharedCheck_5467_;
goto v_resetjp_5457_;
}
v_resetjp_5457_:
{
lean_object* v___x_5460_; lean_object* v___x_5462_; 
v___x_5460_ = lean_unsigned_to_nat(3u);
if (v_isShared_5459_ == 0)
{
lean_ctor_set(v___x_5458_, 4, v_l_5425_);
lean_ctor_set(v___x_5458_, 2, v_v_5332_);
lean_ctor_set(v___x_5458_, 1, v_k_5331_);
lean_ctor_set(v___x_5458_, 0, v___x_5341_);
v___x_5462_ = v___x_5458_;
goto v_reusejp_5461_;
}
else
{
lean_object* v_reuseFailAlloc_5466_; 
v_reuseFailAlloc_5466_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5466_, 0, v___x_5341_);
lean_ctor_set(v_reuseFailAlloc_5466_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5466_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5466_, 3, v_l_5425_);
lean_ctor_set(v_reuseFailAlloc_5466_, 4, v_l_5425_);
v___x_5462_ = v_reuseFailAlloc_5466_;
goto v_reusejp_5461_;
}
v_reusejp_5461_:
{
lean_object* v___x_5464_; 
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 4, v_r_5454_);
lean_ctor_set(v___x_5336_, 3, v___x_5462_);
lean_ctor_set(v___x_5336_, 2, v_v_5456_);
lean_ctor_set(v___x_5336_, 1, v_k_5455_);
lean_ctor_set(v___x_5336_, 0, v___x_5460_);
v___x_5464_ = v___x_5336_;
goto v_reusejp_5463_;
}
else
{
lean_object* v_reuseFailAlloc_5465_; 
v_reuseFailAlloc_5465_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5465_, 0, v___x_5460_);
lean_ctor_set(v_reuseFailAlloc_5465_, 1, v_k_5455_);
lean_ctor_set(v_reuseFailAlloc_5465_, 2, v_v_5456_);
lean_ctor_set(v_reuseFailAlloc_5465_, 3, v___x_5462_);
lean_ctor_set(v_reuseFailAlloc_5465_, 4, v_r_5454_);
v___x_5464_ = v_reuseFailAlloc_5465_;
goto v_reusejp_5463_;
}
v_reusejp_5463_:
{
return v___x_5464_;
}
}
}
}
else
{
lean_object* v___x_5471_; lean_object* v___x_5473_; 
v___x_5471_ = lean_unsigned_to_nat(2u);
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 4, v_impl_5340_);
lean_ctor_set(v___x_5336_, 3, v_r_5454_);
lean_ctor_set(v___x_5336_, 0, v___x_5471_);
v___x_5473_ = v___x_5336_;
goto v_reusejp_5472_;
}
else
{
lean_object* v_reuseFailAlloc_5474_; 
v_reuseFailAlloc_5474_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5474_, 0, v___x_5471_);
lean_ctor_set(v_reuseFailAlloc_5474_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5474_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5474_, 3, v_r_5454_);
lean_ctor_set(v_reuseFailAlloc_5474_, 4, v_impl_5340_);
v___x_5473_ = v_reuseFailAlloc_5474_;
goto v_reusejp_5472_;
}
v_reusejp_5472_:
{
return v___x_5473_;
}
}
}
}
}
else
{
lean_object* v___x_5476_; 
lean_dec(v_v_5332_);
lean_dec(v_k_5331_);
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 2, v_v_5328_);
lean_ctor_set(v___x_5336_, 1, v_k_5327_);
v___x_5476_ = v___x_5336_;
goto v_reusejp_5475_;
}
else
{
lean_object* v_reuseFailAlloc_5477_; 
v_reuseFailAlloc_5477_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5477_, 0, v_size_5330_);
lean_ctor_set(v_reuseFailAlloc_5477_, 1, v_k_5327_);
lean_ctor_set(v_reuseFailAlloc_5477_, 2, v_v_5328_);
lean_ctor_set(v_reuseFailAlloc_5477_, 3, v_l_5333_);
lean_ctor_set(v_reuseFailAlloc_5477_, 4, v_r_5334_);
v___x_5476_ = v_reuseFailAlloc_5477_;
goto v_reusejp_5475_;
}
v_reusejp_5475_:
{
return v___x_5476_;
}
}
}
else
{
lean_object* v_impl_5478_; lean_object* v___x_5479_; 
lean_dec(v_size_5330_);
v_impl_5478_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5327_, v_v_5328_, v_l_5333_);
v___x_5479_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5334_) == 0)
{
lean_object* v_size_5480_; lean_object* v_size_5481_; lean_object* v_k_5482_; lean_object* v_v_5483_; lean_object* v_l_5484_; lean_object* v_r_5485_; lean_object* v___x_5486_; lean_object* v___x_5487_; uint8_t v___x_5488_; 
v_size_5480_ = lean_ctor_get(v_r_5334_, 0);
v_size_5481_ = lean_ctor_get(v_impl_5478_, 0);
lean_inc(v_size_5481_);
v_k_5482_ = lean_ctor_get(v_impl_5478_, 1);
lean_inc(v_k_5482_);
v_v_5483_ = lean_ctor_get(v_impl_5478_, 2);
lean_inc(v_v_5483_);
v_l_5484_ = lean_ctor_get(v_impl_5478_, 3);
lean_inc(v_l_5484_);
v_r_5485_ = lean_ctor_get(v_impl_5478_, 4);
lean_inc(v_r_5485_);
v___x_5486_ = lean_unsigned_to_nat(3u);
v___x_5487_ = lean_nat_mul(v___x_5486_, v_size_5480_);
v___x_5488_ = lean_nat_dec_lt(v___x_5487_, v_size_5481_);
lean_dec(v___x_5487_);
if (v___x_5488_ == 0)
{
lean_object* v___x_5489_; lean_object* v___x_5490_; lean_object* v___x_5492_; 
lean_dec(v_r_5485_);
lean_dec(v_l_5484_);
lean_dec(v_v_5483_);
lean_dec(v_k_5482_);
v___x_5489_ = lean_nat_add(v___x_5479_, v_size_5481_);
lean_dec(v_size_5481_);
v___x_5490_ = lean_nat_add(v___x_5489_, v_size_5480_);
lean_dec(v___x_5489_);
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 3, v_impl_5478_);
lean_ctor_set(v___x_5336_, 0, v___x_5490_);
v___x_5492_ = v___x_5336_;
goto v_reusejp_5491_;
}
else
{
lean_object* v_reuseFailAlloc_5493_; 
v_reuseFailAlloc_5493_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5493_, 0, v___x_5490_);
lean_ctor_set(v_reuseFailAlloc_5493_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5493_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5493_, 3, v_impl_5478_);
lean_ctor_set(v_reuseFailAlloc_5493_, 4, v_r_5334_);
v___x_5492_ = v_reuseFailAlloc_5493_;
goto v_reusejp_5491_;
}
v_reusejp_5491_:
{
return v___x_5492_;
}
}
else
{
lean_object* v___x_5495_; uint8_t v_isShared_5496_; uint8_t v_isSharedCheck_5559_; 
v_isSharedCheck_5559_ = !lean_is_exclusive(v_impl_5478_);
if (v_isSharedCheck_5559_ == 0)
{
lean_object* v_unused_5560_; lean_object* v_unused_5561_; lean_object* v_unused_5562_; lean_object* v_unused_5563_; lean_object* v_unused_5564_; 
v_unused_5560_ = lean_ctor_get(v_impl_5478_, 4);
lean_dec(v_unused_5560_);
v_unused_5561_ = lean_ctor_get(v_impl_5478_, 3);
lean_dec(v_unused_5561_);
v_unused_5562_ = lean_ctor_get(v_impl_5478_, 2);
lean_dec(v_unused_5562_);
v_unused_5563_ = lean_ctor_get(v_impl_5478_, 1);
lean_dec(v_unused_5563_);
v_unused_5564_ = lean_ctor_get(v_impl_5478_, 0);
lean_dec(v_unused_5564_);
v___x_5495_ = v_impl_5478_;
v_isShared_5496_ = v_isSharedCheck_5559_;
goto v_resetjp_5494_;
}
else
{
lean_dec(v_impl_5478_);
v___x_5495_ = lean_box(0);
v_isShared_5496_ = v_isSharedCheck_5559_;
goto v_resetjp_5494_;
}
v_resetjp_5494_:
{
lean_object* v_size_5497_; lean_object* v_size_5498_; lean_object* v_k_5499_; lean_object* v_v_5500_; lean_object* v_l_5501_; lean_object* v_r_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; uint8_t v___x_5505_; 
v_size_5497_ = lean_ctor_get(v_l_5484_, 0);
v_size_5498_ = lean_ctor_get(v_r_5485_, 0);
v_k_5499_ = lean_ctor_get(v_r_5485_, 1);
v_v_5500_ = lean_ctor_get(v_r_5485_, 2);
v_l_5501_ = lean_ctor_get(v_r_5485_, 3);
v_r_5502_ = lean_ctor_get(v_r_5485_, 4);
v___x_5503_ = lean_unsigned_to_nat(2u);
v___x_5504_ = lean_nat_mul(v___x_5503_, v_size_5497_);
v___x_5505_ = lean_nat_dec_lt(v_size_5498_, v___x_5504_);
lean_dec(v___x_5504_);
if (v___x_5505_ == 0)
{
lean_object* v___x_5507_; uint8_t v_isShared_5508_; uint8_t v_isSharedCheck_5534_; 
lean_inc(v_r_5502_);
lean_inc(v_l_5501_);
lean_inc(v_v_5500_);
lean_inc(v_k_5499_);
v_isSharedCheck_5534_ = !lean_is_exclusive(v_r_5485_);
if (v_isSharedCheck_5534_ == 0)
{
lean_object* v_unused_5535_; lean_object* v_unused_5536_; lean_object* v_unused_5537_; lean_object* v_unused_5538_; lean_object* v_unused_5539_; 
v_unused_5535_ = lean_ctor_get(v_r_5485_, 4);
lean_dec(v_unused_5535_);
v_unused_5536_ = lean_ctor_get(v_r_5485_, 3);
lean_dec(v_unused_5536_);
v_unused_5537_ = lean_ctor_get(v_r_5485_, 2);
lean_dec(v_unused_5537_);
v_unused_5538_ = lean_ctor_get(v_r_5485_, 1);
lean_dec(v_unused_5538_);
v_unused_5539_ = lean_ctor_get(v_r_5485_, 0);
lean_dec(v_unused_5539_);
v___x_5507_ = v_r_5485_;
v_isShared_5508_ = v_isSharedCheck_5534_;
goto v_resetjp_5506_;
}
else
{
lean_dec(v_r_5485_);
v___x_5507_ = lean_box(0);
v_isShared_5508_ = v_isSharedCheck_5534_;
goto v_resetjp_5506_;
}
v_resetjp_5506_:
{
lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___y_5512_; lean_object* v___y_5513_; lean_object* v___y_5514_; lean_object* v___x_5522_; lean_object* v___y_5524_; 
v___x_5509_ = lean_nat_add(v___x_5479_, v_size_5481_);
lean_dec(v_size_5481_);
v___x_5510_ = lean_nat_add(v___x_5509_, v_size_5480_);
lean_dec(v___x_5509_);
v___x_5522_ = lean_nat_add(v___x_5479_, v_size_5497_);
if (lean_obj_tag(v_l_5501_) == 0)
{
lean_object* v_size_5532_; 
v_size_5532_ = lean_ctor_get(v_l_5501_, 0);
lean_inc(v_size_5532_);
v___y_5524_ = v_size_5532_;
goto v___jp_5523_;
}
else
{
lean_object* v___x_5533_; 
v___x_5533_ = lean_unsigned_to_nat(0u);
v___y_5524_ = v___x_5533_;
goto v___jp_5523_;
}
v___jp_5511_:
{
lean_object* v___x_5515_; lean_object* v___x_5517_; 
v___x_5515_ = lean_nat_add(v___y_5513_, v___y_5514_);
lean_dec(v___y_5514_);
lean_dec(v___y_5513_);
if (v_isShared_5508_ == 0)
{
lean_ctor_set(v___x_5507_, 4, v_r_5334_);
lean_ctor_set(v___x_5507_, 3, v_r_5502_);
lean_ctor_set(v___x_5507_, 2, v_v_5332_);
lean_ctor_set(v___x_5507_, 1, v_k_5331_);
lean_ctor_set(v___x_5507_, 0, v___x_5515_);
v___x_5517_ = v___x_5507_;
goto v_reusejp_5516_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v___x_5515_);
lean_ctor_set(v_reuseFailAlloc_5521_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5521_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5521_, 3, v_r_5502_);
lean_ctor_set(v_reuseFailAlloc_5521_, 4, v_r_5334_);
v___x_5517_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5516_;
}
v_reusejp_5516_:
{
lean_object* v___x_5519_; 
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 4, v___x_5517_);
lean_ctor_set(v___x_5495_, 3, v___y_5512_);
lean_ctor_set(v___x_5495_, 2, v_v_5500_);
lean_ctor_set(v___x_5495_, 1, v_k_5499_);
lean_ctor_set(v___x_5495_, 0, v___x_5510_);
v___x_5519_ = v___x_5495_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v___x_5510_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v_k_5499_);
lean_ctor_set(v_reuseFailAlloc_5520_, 2, v_v_5500_);
lean_ctor_set(v_reuseFailAlloc_5520_, 3, v___y_5512_);
lean_ctor_set(v_reuseFailAlloc_5520_, 4, v___x_5517_);
v___x_5519_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5518_;
}
v_reusejp_5518_:
{
return v___x_5519_;
}
}
}
v___jp_5523_:
{
lean_object* v___x_5525_; lean_object* v___x_5527_; 
v___x_5525_ = lean_nat_add(v___x_5522_, v___y_5524_);
lean_dec(v___y_5524_);
lean_dec(v___x_5522_);
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 4, v_l_5501_);
lean_ctor_set(v___x_5336_, 3, v_l_5484_);
lean_ctor_set(v___x_5336_, 2, v_v_5483_);
lean_ctor_set(v___x_5336_, 1, v_k_5482_);
lean_ctor_set(v___x_5336_, 0, v___x_5525_);
v___x_5527_ = v___x_5336_;
goto v_reusejp_5526_;
}
else
{
lean_object* v_reuseFailAlloc_5531_; 
v_reuseFailAlloc_5531_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5531_, 0, v___x_5525_);
lean_ctor_set(v_reuseFailAlloc_5531_, 1, v_k_5482_);
lean_ctor_set(v_reuseFailAlloc_5531_, 2, v_v_5483_);
lean_ctor_set(v_reuseFailAlloc_5531_, 3, v_l_5484_);
lean_ctor_set(v_reuseFailAlloc_5531_, 4, v_l_5501_);
v___x_5527_ = v_reuseFailAlloc_5531_;
goto v_reusejp_5526_;
}
v_reusejp_5526_:
{
lean_object* v___x_5528_; 
v___x_5528_ = lean_nat_add(v___x_5479_, v_size_5480_);
if (lean_obj_tag(v_r_5502_) == 0)
{
lean_object* v_size_5529_; 
v_size_5529_ = lean_ctor_get(v_r_5502_, 0);
lean_inc(v_size_5529_);
v___y_5512_ = v___x_5527_;
v___y_5513_ = v___x_5528_;
v___y_5514_ = v_size_5529_;
goto v___jp_5511_;
}
else
{
lean_object* v___x_5530_; 
v___x_5530_ = lean_unsigned_to_nat(0u);
v___y_5512_ = v___x_5527_;
v___y_5513_ = v___x_5528_;
v___y_5514_ = v___x_5530_;
goto v___jp_5511_;
}
}
}
}
}
else
{
lean_object* v___x_5540_; lean_object* v___x_5541_; lean_object* v___x_5542_; lean_object* v___x_5543_; lean_object* v___x_5545_; 
lean_del_object(v___x_5336_);
v___x_5540_ = lean_nat_add(v___x_5479_, v_size_5481_);
lean_dec(v_size_5481_);
v___x_5541_ = lean_nat_add(v___x_5540_, v_size_5480_);
lean_dec(v___x_5540_);
v___x_5542_ = lean_nat_add(v___x_5479_, v_size_5480_);
v___x_5543_ = lean_nat_add(v___x_5542_, v_size_5498_);
lean_dec(v___x_5542_);
lean_inc_ref(v_r_5334_);
if (v_isShared_5496_ == 0)
{
lean_ctor_set(v___x_5495_, 4, v_r_5334_);
lean_ctor_set(v___x_5495_, 3, v_r_5485_);
lean_ctor_set(v___x_5495_, 2, v_v_5332_);
lean_ctor_set(v___x_5495_, 1, v_k_5331_);
lean_ctor_set(v___x_5495_, 0, v___x_5543_);
v___x_5545_ = v___x_5495_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5558_; 
v_reuseFailAlloc_5558_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5558_, 0, v___x_5543_);
lean_ctor_set(v_reuseFailAlloc_5558_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5558_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5558_, 3, v_r_5485_);
lean_ctor_set(v_reuseFailAlloc_5558_, 4, v_r_5334_);
v___x_5545_ = v_reuseFailAlloc_5558_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
lean_object* v___x_5547_; uint8_t v_isShared_5548_; uint8_t v_isSharedCheck_5552_; 
v_isSharedCheck_5552_ = !lean_is_exclusive(v_r_5334_);
if (v_isSharedCheck_5552_ == 0)
{
lean_object* v_unused_5553_; lean_object* v_unused_5554_; lean_object* v_unused_5555_; lean_object* v_unused_5556_; lean_object* v_unused_5557_; 
v_unused_5553_ = lean_ctor_get(v_r_5334_, 4);
lean_dec(v_unused_5553_);
v_unused_5554_ = lean_ctor_get(v_r_5334_, 3);
lean_dec(v_unused_5554_);
v_unused_5555_ = lean_ctor_get(v_r_5334_, 2);
lean_dec(v_unused_5555_);
v_unused_5556_ = lean_ctor_get(v_r_5334_, 1);
lean_dec(v_unused_5556_);
v_unused_5557_ = lean_ctor_get(v_r_5334_, 0);
lean_dec(v_unused_5557_);
v___x_5547_ = v_r_5334_;
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
else
{
lean_dec(v_r_5334_);
v___x_5547_ = lean_box(0);
v_isShared_5548_ = v_isSharedCheck_5552_;
goto v_resetjp_5546_;
}
v_resetjp_5546_:
{
lean_object* v___x_5550_; 
if (v_isShared_5548_ == 0)
{
lean_ctor_set(v___x_5547_, 4, v___x_5545_);
lean_ctor_set(v___x_5547_, 3, v_l_5484_);
lean_ctor_set(v___x_5547_, 2, v_v_5483_);
lean_ctor_set(v___x_5547_, 1, v_k_5482_);
lean_ctor_set(v___x_5547_, 0, v___x_5541_);
v___x_5550_ = v___x_5547_;
goto v_reusejp_5549_;
}
else
{
lean_object* v_reuseFailAlloc_5551_; 
v_reuseFailAlloc_5551_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5551_, 0, v___x_5541_);
lean_ctor_set(v_reuseFailAlloc_5551_, 1, v_k_5482_);
lean_ctor_set(v_reuseFailAlloc_5551_, 2, v_v_5483_);
lean_ctor_set(v_reuseFailAlloc_5551_, 3, v_l_5484_);
lean_ctor_set(v_reuseFailAlloc_5551_, 4, v___x_5545_);
v___x_5550_ = v_reuseFailAlloc_5551_;
goto v_reusejp_5549_;
}
v_reusejp_5549_:
{
return v___x_5550_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5565_; 
v_l_5565_ = lean_ctor_get(v_impl_5478_, 3);
lean_inc(v_l_5565_);
if (lean_obj_tag(v_l_5565_) == 0)
{
lean_object* v_r_5566_; lean_object* v_k_5567_; lean_object* v_v_5568_; lean_object* v___x_5570_; uint8_t v_isShared_5571_; uint8_t v_isSharedCheck_5579_; 
v_r_5566_ = lean_ctor_get(v_impl_5478_, 4);
v_k_5567_ = lean_ctor_get(v_impl_5478_, 1);
v_v_5568_ = lean_ctor_get(v_impl_5478_, 2);
v_isSharedCheck_5579_ = !lean_is_exclusive(v_impl_5478_);
if (v_isSharedCheck_5579_ == 0)
{
lean_object* v_unused_5580_; lean_object* v_unused_5581_; 
v_unused_5580_ = lean_ctor_get(v_impl_5478_, 3);
lean_dec(v_unused_5580_);
v_unused_5581_ = lean_ctor_get(v_impl_5478_, 0);
lean_dec(v_unused_5581_);
v___x_5570_ = v_impl_5478_;
v_isShared_5571_ = v_isSharedCheck_5579_;
goto v_resetjp_5569_;
}
else
{
lean_inc(v_r_5566_);
lean_inc(v_v_5568_);
lean_inc(v_k_5567_);
lean_dec(v_impl_5478_);
v___x_5570_ = lean_box(0);
v_isShared_5571_ = v_isSharedCheck_5579_;
goto v_resetjp_5569_;
}
v_resetjp_5569_:
{
lean_object* v___x_5572_; lean_object* v___x_5574_; 
v___x_5572_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5566_);
if (v_isShared_5571_ == 0)
{
lean_ctor_set(v___x_5570_, 3, v_r_5566_);
lean_ctor_set(v___x_5570_, 2, v_v_5332_);
lean_ctor_set(v___x_5570_, 1, v_k_5331_);
lean_ctor_set(v___x_5570_, 0, v___x_5479_);
v___x_5574_ = v___x_5570_;
goto v_reusejp_5573_;
}
else
{
lean_object* v_reuseFailAlloc_5578_; 
v_reuseFailAlloc_5578_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5578_, 0, v___x_5479_);
lean_ctor_set(v_reuseFailAlloc_5578_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5578_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5578_, 3, v_r_5566_);
lean_ctor_set(v_reuseFailAlloc_5578_, 4, v_r_5566_);
v___x_5574_ = v_reuseFailAlloc_5578_;
goto v_reusejp_5573_;
}
v_reusejp_5573_:
{
lean_object* v___x_5576_; 
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 4, v___x_5574_);
lean_ctor_set(v___x_5336_, 3, v_l_5565_);
lean_ctor_set(v___x_5336_, 2, v_v_5568_);
lean_ctor_set(v___x_5336_, 1, v_k_5567_);
lean_ctor_set(v___x_5336_, 0, v___x_5572_);
v___x_5576_ = v___x_5336_;
goto v_reusejp_5575_;
}
else
{
lean_object* v_reuseFailAlloc_5577_; 
v_reuseFailAlloc_5577_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5577_, 0, v___x_5572_);
lean_ctor_set(v_reuseFailAlloc_5577_, 1, v_k_5567_);
lean_ctor_set(v_reuseFailAlloc_5577_, 2, v_v_5568_);
lean_ctor_set(v_reuseFailAlloc_5577_, 3, v_l_5565_);
lean_ctor_set(v_reuseFailAlloc_5577_, 4, v___x_5574_);
v___x_5576_ = v_reuseFailAlloc_5577_;
goto v_reusejp_5575_;
}
v_reusejp_5575_:
{
return v___x_5576_;
}
}
}
}
else
{
lean_object* v_r_5582_; 
v_r_5582_ = lean_ctor_get(v_impl_5478_, 4);
lean_inc(v_r_5582_);
if (lean_obj_tag(v_r_5582_) == 0)
{
lean_object* v_k_5583_; lean_object* v_v_5584_; lean_object* v___x_5586_; uint8_t v_isShared_5587_; uint8_t v_isSharedCheck_5607_; 
v_k_5583_ = lean_ctor_get(v_impl_5478_, 1);
v_v_5584_ = lean_ctor_get(v_impl_5478_, 2);
v_isSharedCheck_5607_ = !lean_is_exclusive(v_impl_5478_);
if (v_isSharedCheck_5607_ == 0)
{
lean_object* v_unused_5608_; lean_object* v_unused_5609_; lean_object* v_unused_5610_; 
v_unused_5608_ = lean_ctor_get(v_impl_5478_, 4);
lean_dec(v_unused_5608_);
v_unused_5609_ = lean_ctor_get(v_impl_5478_, 3);
lean_dec(v_unused_5609_);
v_unused_5610_ = lean_ctor_get(v_impl_5478_, 0);
lean_dec(v_unused_5610_);
v___x_5586_ = v_impl_5478_;
v_isShared_5587_ = v_isSharedCheck_5607_;
goto v_resetjp_5585_;
}
else
{
lean_inc(v_v_5584_);
lean_inc(v_k_5583_);
lean_dec(v_impl_5478_);
v___x_5586_ = lean_box(0);
v_isShared_5587_ = v_isSharedCheck_5607_;
goto v_resetjp_5585_;
}
v_resetjp_5585_:
{
lean_object* v_k_5588_; lean_object* v_v_5589_; lean_object* v___x_5591_; uint8_t v_isShared_5592_; uint8_t v_isSharedCheck_5603_; 
v_k_5588_ = lean_ctor_get(v_r_5582_, 1);
v_v_5589_ = lean_ctor_get(v_r_5582_, 2);
v_isSharedCheck_5603_ = !lean_is_exclusive(v_r_5582_);
if (v_isSharedCheck_5603_ == 0)
{
lean_object* v_unused_5604_; lean_object* v_unused_5605_; lean_object* v_unused_5606_; 
v_unused_5604_ = lean_ctor_get(v_r_5582_, 4);
lean_dec(v_unused_5604_);
v_unused_5605_ = lean_ctor_get(v_r_5582_, 3);
lean_dec(v_unused_5605_);
v_unused_5606_ = lean_ctor_get(v_r_5582_, 0);
lean_dec(v_unused_5606_);
v___x_5591_ = v_r_5582_;
v_isShared_5592_ = v_isSharedCheck_5603_;
goto v_resetjp_5590_;
}
else
{
lean_inc(v_v_5589_);
lean_inc(v_k_5588_);
lean_dec(v_r_5582_);
v___x_5591_ = lean_box(0);
v_isShared_5592_ = v_isSharedCheck_5603_;
goto v_resetjp_5590_;
}
v_resetjp_5590_:
{
lean_object* v___x_5593_; lean_object* v___x_5595_; 
v___x_5593_ = lean_unsigned_to_nat(3u);
if (v_isShared_5592_ == 0)
{
lean_ctor_set(v___x_5591_, 4, v_l_5565_);
lean_ctor_set(v___x_5591_, 3, v_l_5565_);
lean_ctor_set(v___x_5591_, 2, v_v_5584_);
lean_ctor_set(v___x_5591_, 1, v_k_5583_);
lean_ctor_set(v___x_5591_, 0, v___x_5479_);
v___x_5595_ = v___x_5591_;
goto v_reusejp_5594_;
}
else
{
lean_object* v_reuseFailAlloc_5602_; 
v_reuseFailAlloc_5602_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5602_, 0, v___x_5479_);
lean_ctor_set(v_reuseFailAlloc_5602_, 1, v_k_5583_);
lean_ctor_set(v_reuseFailAlloc_5602_, 2, v_v_5584_);
lean_ctor_set(v_reuseFailAlloc_5602_, 3, v_l_5565_);
lean_ctor_set(v_reuseFailAlloc_5602_, 4, v_l_5565_);
v___x_5595_ = v_reuseFailAlloc_5602_;
goto v_reusejp_5594_;
}
v_reusejp_5594_:
{
lean_object* v___x_5597_; 
if (v_isShared_5587_ == 0)
{
lean_ctor_set(v___x_5586_, 4, v_l_5565_);
lean_ctor_set(v___x_5586_, 2, v_v_5332_);
lean_ctor_set(v___x_5586_, 1, v_k_5331_);
lean_ctor_set(v___x_5586_, 0, v___x_5479_);
v___x_5597_ = v___x_5586_;
goto v_reusejp_5596_;
}
else
{
lean_object* v_reuseFailAlloc_5601_; 
v_reuseFailAlloc_5601_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5601_, 0, v___x_5479_);
lean_ctor_set(v_reuseFailAlloc_5601_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5601_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5601_, 3, v_l_5565_);
lean_ctor_set(v_reuseFailAlloc_5601_, 4, v_l_5565_);
v___x_5597_ = v_reuseFailAlloc_5601_;
goto v_reusejp_5596_;
}
v_reusejp_5596_:
{
lean_object* v___x_5599_; 
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 4, v___x_5597_);
lean_ctor_set(v___x_5336_, 3, v___x_5595_);
lean_ctor_set(v___x_5336_, 2, v_v_5589_);
lean_ctor_set(v___x_5336_, 1, v_k_5588_);
lean_ctor_set(v___x_5336_, 0, v___x_5593_);
v___x_5599_ = v___x_5336_;
goto v_reusejp_5598_;
}
else
{
lean_object* v_reuseFailAlloc_5600_; 
v_reuseFailAlloc_5600_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5600_, 0, v___x_5593_);
lean_ctor_set(v_reuseFailAlloc_5600_, 1, v_k_5588_);
lean_ctor_set(v_reuseFailAlloc_5600_, 2, v_v_5589_);
lean_ctor_set(v_reuseFailAlloc_5600_, 3, v___x_5595_);
lean_ctor_set(v_reuseFailAlloc_5600_, 4, v___x_5597_);
v___x_5599_ = v_reuseFailAlloc_5600_;
goto v_reusejp_5598_;
}
v_reusejp_5598_:
{
return v___x_5599_;
}
}
}
}
}
}
else
{
lean_object* v___x_5611_; lean_object* v___x_5613_; 
v___x_5611_ = lean_unsigned_to_nat(2u);
if (v_isShared_5337_ == 0)
{
lean_ctor_set(v___x_5336_, 4, v_r_5582_);
lean_ctor_set(v___x_5336_, 3, v_impl_5478_);
lean_ctor_set(v___x_5336_, 0, v___x_5611_);
v___x_5613_ = v___x_5336_;
goto v_reusejp_5612_;
}
else
{
lean_object* v_reuseFailAlloc_5614_; 
v_reuseFailAlloc_5614_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5614_, 0, v___x_5611_);
lean_ctor_set(v_reuseFailAlloc_5614_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5614_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5614_, 3, v_impl_5478_);
lean_ctor_set(v_reuseFailAlloc_5614_, 4, v_r_5582_);
v___x_5613_ = v_reuseFailAlloc_5614_;
goto v_reusejp_5612_;
}
v_reusejp_5612_:
{
return v___x_5613_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5616_; lean_object* v___x_5617_; 
v___x_5616_ = lean_unsigned_to_nat(1u);
v___x_5617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5617_, 0, v___x_5616_);
lean_ctor_set(v___x_5617_, 1, v_k_5327_);
lean_ctor_set(v___x_5617_, 2, v_v_5328_);
lean_ctor_set(v___x_5617_, 3, v_t_5329_);
lean_ctor_set(v___x_5617_, 4, v_t_5329_);
return v___x_5617_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5618_, lean_object* v_t_5619_){
_start:
{
if (lean_obj_tag(v_t_5619_) == 0)
{
lean_object* v_k_5620_; lean_object* v_l_5621_; lean_object* v_r_5622_; uint8_t v___x_5623_; 
v_k_5620_ = lean_ctor_get(v_t_5619_, 1);
v_l_5621_ = lean_ctor_get(v_t_5619_, 3);
v_r_5622_ = lean_ctor_get(v_t_5619_, 4);
v___x_5623_ = lean_nat_dec_lt(v_k_5620_, v_k_5618_);
if (v___x_5623_ == 0)
{
uint8_t v___x_5624_; 
v___x_5624_ = lean_nat_dec_eq(v_k_5620_, v_k_5618_);
if (v___x_5624_ == 0)
{
v_t_5619_ = v_r_5622_;
goto _start;
}
else
{
return v___x_5624_;
}
}
else
{
v_t_5619_ = v_l_5621_;
goto _start;
}
}
else
{
uint8_t v___x_5627_; 
v___x_5627_ = 0;
return v___x_5627_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5628_, lean_object* v_t_5629_){
_start:
{
uint8_t v_res_5630_; lean_object* v_r_5631_; 
v_res_5630_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5628_, v_t_5629_);
lean_dec(v_t_5629_);
lean_dec(v_k_5628_);
v_r_5631_ = lean_box(v_res_5630_);
return v_r_5631_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5632_, lean_object* v_e_5633_){
_start:
{
lean_object* v_defaultInstances_5634_; lean_object* v_priorities_5635_; lean_object* v___x_5637_; uint8_t v_isShared_5638_; uint8_t v_isSharedCheck_5662_; 
v_defaultInstances_5634_ = lean_ctor_get(v_d_5632_, 0);
v_priorities_5635_ = lean_ctor_get(v_d_5632_, 1);
v_isSharedCheck_5662_ = !lean_is_exclusive(v_d_5632_);
if (v_isSharedCheck_5662_ == 0)
{
v___x_5637_ = v_d_5632_;
v_isShared_5638_ = v_isSharedCheck_5662_;
goto v_resetjp_5636_;
}
else
{
lean_inc(v_priorities_5635_);
lean_inc(v_defaultInstances_5634_);
lean_dec(v_d_5632_);
v___x_5637_ = lean_box(0);
v_isShared_5638_ = v_isSharedCheck_5662_;
goto v_resetjp_5636_;
}
v_resetjp_5636_:
{
lean_object* v_className_5639_; lean_object* v_instanceName_5640_; lean_object* v_priority_5641_; lean_object* v___y_5643_; uint8_t v___x_5659_; 
v_className_5639_ = lean_ctor_get(v_e_5633_, 0);
lean_inc(v_className_5639_);
v_instanceName_5640_ = lean_ctor_get(v_e_5633_, 1);
lean_inc(v_instanceName_5640_);
v_priority_5641_ = lean_ctor_get(v_e_5633_, 2);
lean_inc(v_priority_5641_);
lean_dec_ref(v_e_5633_);
v___x_5659_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5641_, v_priorities_5635_);
if (v___x_5659_ == 0)
{
lean_object* v___x_5660_; lean_object* v___x_5661_; 
v___x_5660_ = lean_box(0);
lean_inc(v_priority_5641_);
v___x_5661_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5641_, v___x_5660_, v_priorities_5635_);
v___y_5643_ = v___x_5661_;
goto v___jp_5642_;
}
else
{
v___y_5643_ = v_priorities_5635_;
goto v___jp_5642_;
}
v___jp_5642_:
{
lean_object* v___x_5644_; 
v___x_5644_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5634_, v_className_5639_);
if (lean_obj_tag(v___x_5644_) == 0)
{
lean_object* v___x_5645_; lean_object* v___x_5646_; lean_object* v___x_5647_; lean_object* v___x_5648_; lean_object* v___x_5650_; 
v___x_5645_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5645_, 0, v_instanceName_5640_);
lean_ctor_set(v___x_5645_, 1, v_priority_5641_);
v___x_5646_ = lean_box(0);
v___x_5647_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5647_, 0, v___x_5645_);
lean_ctor_set(v___x_5647_, 1, v___x_5646_);
v___x_5648_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5639_, v___x_5647_, v_defaultInstances_5634_);
if (v_isShared_5638_ == 0)
{
lean_ctor_set(v___x_5637_, 1, v___y_5643_);
lean_ctor_set(v___x_5637_, 0, v___x_5648_);
v___x_5650_ = v___x_5637_;
goto v_reusejp_5649_;
}
else
{
lean_object* v_reuseFailAlloc_5651_; 
v_reuseFailAlloc_5651_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5651_, 0, v___x_5648_);
lean_ctor_set(v_reuseFailAlloc_5651_, 1, v___y_5643_);
v___x_5650_ = v_reuseFailAlloc_5651_;
goto v_reusejp_5649_;
}
v_reusejp_5649_:
{
return v___x_5650_;
}
}
else
{
lean_object* v_val_5652_; lean_object* v___x_5653_; lean_object* v___x_5654_; lean_object* v___x_5655_; lean_object* v___x_5657_; 
v_val_5652_ = lean_ctor_get(v___x_5644_, 0);
lean_inc(v_val_5652_);
lean_dec_ref_known(v___x_5644_, 1);
v___x_5653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5653_, 0, v_instanceName_5640_);
lean_ctor_set(v___x_5653_, 1, v_priority_5641_);
v___x_5654_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5654_, 0, v___x_5653_);
lean_ctor_set(v___x_5654_, 1, v_val_5652_);
v___x_5655_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5639_, v___x_5654_, v_defaultInstances_5634_);
if (v_isShared_5638_ == 0)
{
lean_ctor_set(v___x_5637_, 1, v___y_5643_);
lean_ctor_set(v___x_5637_, 0, v___x_5655_);
v___x_5657_ = v___x_5637_;
goto v_reusejp_5656_;
}
else
{
lean_object* v_reuseFailAlloc_5658_; 
v_reuseFailAlloc_5658_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5658_, 0, v___x_5655_);
lean_ctor_set(v_reuseFailAlloc_5658_, 1, v___y_5643_);
v___x_5657_ = v_reuseFailAlloc_5658_;
goto v_reusejp_5656_;
}
v_reusejp_5656_:
{
return v___x_5657_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5663_, lean_object* v_k_5664_, lean_object* v_t_5665_){
_start:
{
uint8_t v___x_5666_; 
v___x_5666_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5664_, v_t_5665_);
return v___x_5666_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5667_, lean_object* v_k_5668_, lean_object* v_t_5669_){
_start:
{
uint8_t v_res_5670_; lean_object* v_r_5671_; 
v_res_5670_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5667_, v_k_5668_, v_t_5669_);
lean_dec(v_t_5669_);
lean_dec(v_k_5668_);
v_r_5671_ = lean_box(v_res_5670_);
return v_r_5671_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5672_, lean_object* v_k_5673_, lean_object* v_v_5674_, lean_object* v_t_5675_, lean_object* v_hl_5676_){
_start:
{
lean_object* v___x_5677_; 
v___x_5677_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5673_, v_v_5674_, v_t_5675_);
return v___x_5677_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object* v_env_5678_, lean_object* v_as_5679_, size_t v_i_5680_, size_t v_stop_5681_, lean_object* v_b_5682_){
_start:
{
lean_object* v___y_5684_; uint8_t v___x_5688_; 
v___x_5688_ = lean_usize_dec_eq(v_i_5680_, v_stop_5681_);
if (v___x_5688_ == 0)
{
lean_object* v___x_5689_; lean_object* v_instanceName_5690_; uint8_t v___x_5691_; lean_object* v___x_5692_; uint8_t v___x_5693_; 
v___x_5689_ = lean_array_uget_borrowed(v_as_5679_, v_i_5680_);
v_instanceName_5690_ = lean_ctor_get(v___x_5689_, 1);
v___x_5691_ = 1;
lean_inc_ref(v_env_5678_);
v___x_5692_ = l_Lean_Environment_setExporting(v_env_5678_, v___x_5691_);
lean_inc(v_instanceName_5690_);
v___x_5693_ = l_Lean_Environment_contains(v___x_5692_, v_instanceName_5690_, v___x_5688_);
if (v___x_5693_ == 0)
{
v___y_5684_ = v_b_5682_;
goto v___jp_5683_;
}
else
{
lean_object* v___x_5694_; 
lean_inc(v___x_5689_);
v___x_5694_ = lean_array_push(v_b_5682_, v___x_5689_);
v___y_5684_ = v___x_5694_;
goto v___jp_5683_;
}
}
else
{
lean_dec_ref(v_env_5678_);
return v_b_5682_;
}
v___jp_5683_:
{
size_t v___x_5685_; size_t v___x_5686_; 
v___x_5685_ = ((size_t)1ULL);
v___x_5686_ = lean_usize_add(v_i_5680_, v___x_5685_);
v_i_5680_ = v___x_5686_;
v_b_5682_ = v___y_5684_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_5695_, lean_object* v_as_5696_, lean_object* v_i_5697_, lean_object* v_stop_5698_, lean_object* v_b_5699_){
_start:
{
size_t v_i_boxed_5700_; size_t v_stop_boxed_5701_; lean_object* v_res_5702_; 
v_i_boxed_5700_ = lean_unbox_usize(v_i_5697_);
lean_dec(v_i_5697_);
v_stop_boxed_5701_ = lean_unbox_usize(v_stop_5698_);
lean_dec(v_stop_5698_);
v_res_5702_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5695_, v_as_5696_, v_i_boxed_5700_, v_stop_boxed_5701_, v_b_5699_);
lean_dec_ref(v_as_5696_);
return v_res_5702_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_env_5705_, lean_object* v_x_5706_, lean_object* v_entries_5707_){
_start:
{
lean_object* v_all_5708_; lean_object* v___x_5709_; lean_object* v___x_5710_; lean_object* v___x_5711_; uint8_t v___x_5712_; 
v_all_5708_ = lean_array_mk(v_entries_5707_);
v___x_5709_ = lean_unsigned_to_nat(0u);
v___x_5710_ = lean_array_get_size(v_all_5708_);
v___x_5711_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5712_ = lean_nat_dec_lt(v___x_5709_, v___x_5710_);
if (v___x_5712_ == 0)
{
lean_object* v___x_5713_; 
lean_dec_ref(v_env_5705_);
v___x_5713_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5713_, 0, v___x_5711_);
lean_ctor_set(v___x_5713_, 1, v___x_5711_);
lean_ctor_set(v___x_5713_, 2, v_all_5708_);
return v___x_5713_;
}
else
{
uint8_t v___x_5714_; 
v___x_5714_ = lean_nat_dec_le(v___x_5710_, v___x_5710_);
if (v___x_5714_ == 0)
{
if (v___x_5712_ == 0)
{
lean_object* v___x_5715_; 
lean_dec_ref(v_env_5705_);
v___x_5715_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5715_, 0, v___x_5711_);
lean_ctor_set(v___x_5715_, 1, v___x_5711_);
lean_ctor_set(v___x_5715_, 2, v_all_5708_);
return v___x_5715_;
}
else
{
size_t v___x_5716_; size_t v___x_5717_; lean_object* v___x_5718_; lean_object* v___x_5719_; 
v___x_5716_ = ((size_t)0ULL);
v___x_5717_ = lean_usize_of_nat(v___x_5710_);
v___x_5718_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5705_, v_all_5708_, v___x_5716_, v___x_5717_, v___x_5711_);
lean_inc_ref(v___x_5718_);
v___x_5719_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5719_, 0, v___x_5718_);
lean_ctor_set(v___x_5719_, 1, v___x_5718_);
lean_ctor_set(v___x_5719_, 2, v_all_5708_);
return v___x_5719_;
}
}
else
{
size_t v___x_5720_; size_t v___x_5721_; lean_object* v___x_5722_; lean_object* v___x_5723_; 
v___x_5720_ = ((size_t)0ULL);
v___x_5721_ = lean_usize_of_nat(v___x_5710_);
v___x_5722_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5705_, v_all_5708_, v___x_5720_, v___x_5721_, v___x_5711_);
lean_inc_ref(v___x_5722_);
v___x_5723_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5723_, 0, v___x_5722_);
lean_ctor_set(v___x_5723_, 1, v___x_5722_);
lean_ctor_set(v___x_5723_, 2, v_all_5708_);
return v___x_5723_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5724_, lean_object* v_x_5725_, lean_object* v_entries_5726_){
_start:
{
lean_object* v_res_5727_; 
v_res_5727_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5724_, v_x_5725_, v_entries_5726_);
lean_dec_ref(v_x_5725_);
return v_res_5727_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5728_){
_start:
{
lean_object* v___x_5729_; 
v___x_5729_ = lean_array_mk(v_es_5728_);
return v___x_5729_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5730_, size_t v_i_5731_, size_t v_stop_5732_, lean_object* v_b_5733_){
_start:
{
uint8_t v___x_5734_; 
v___x_5734_ = lean_usize_dec_eq(v_i_5731_, v_stop_5732_);
if (v___x_5734_ == 0)
{
lean_object* v___x_5735_; lean_object* v___x_5736_; size_t v___x_5737_; size_t v___x_5738_; 
v___x_5735_ = lean_array_uget_borrowed(v_as_5730_, v_i_5731_);
lean_inc(v___x_5735_);
v___x_5736_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5733_, v___x_5735_);
v___x_5737_ = ((size_t)1ULL);
v___x_5738_ = lean_usize_add(v_i_5731_, v___x_5737_);
v_i_5731_ = v___x_5738_;
v_b_5733_ = v___x_5736_;
goto _start;
}
else
{
return v_b_5733_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5740_, lean_object* v_i_5741_, lean_object* v_stop_5742_, lean_object* v_b_5743_){
_start:
{
size_t v_i_boxed_5744_; size_t v_stop_boxed_5745_; lean_object* v_res_5746_; 
v_i_boxed_5744_ = lean_unbox_usize(v_i_5741_);
lean_dec(v_i_5741_);
v_stop_boxed_5745_ = lean_unbox_usize(v_stop_5742_);
lean_dec(v_stop_5742_);
v_res_5746_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5740_, v_i_boxed_5744_, v_stop_boxed_5745_, v_b_5743_);
lean_dec_ref(v_as_5740_);
return v_res_5746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5747_, size_t v_i_5748_, size_t v_stop_5749_, lean_object* v_b_5750_){
_start:
{
lean_object* v___y_5752_; uint8_t v___x_5756_; 
v___x_5756_ = lean_usize_dec_eq(v_i_5748_, v_stop_5749_);
if (v___x_5756_ == 0)
{
lean_object* v___x_5757_; lean_object* v___x_5758_; lean_object* v___x_5759_; uint8_t v___x_5760_; 
v___x_5757_ = lean_array_uget_borrowed(v_as_5747_, v_i_5748_);
v___x_5758_ = lean_unsigned_to_nat(0u);
v___x_5759_ = lean_array_get_size(v___x_5757_);
v___x_5760_ = lean_nat_dec_lt(v___x_5758_, v___x_5759_);
if (v___x_5760_ == 0)
{
v___y_5752_ = v_b_5750_;
goto v___jp_5751_;
}
else
{
size_t v___x_5761_; size_t v___x_5762_; lean_object* v___x_5763_; 
v___x_5761_ = ((size_t)0ULL);
v___x_5762_ = lean_usize_of_nat(v___x_5759_);
v___x_5763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5757_, v___x_5761_, v___x_5762_, v_b_5750_);
v___y_5752_ = v___x_5763_;
goto v___jp_5751_;
}
}
else
{
return v_b_5750_;
}
v___jp_5751_:
{
size_t v___x_5753_; size_t v___x_5754_; 
v___x_5753_ = ((size_t)1ULL);
v___x_5754_ = lean_usize_add(v_i_5748_, v___x_5753_);
v_i_5748_ = v___x_5754_;
v_b_5750_ = v___y_5752_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5764_, lean_object* v_i_5765_, lean_object* v_stop_5766_, lean_object* v_b_5767_){
_start:
{
size_t v_i_boxed_5768_; size_t v_stop_boxed_5769_; lean_object* v_res_5770_; 
v_i_boxed_5768_ = lean_unbox_usize(v_i_5765_);
lean_dec(v_i_5765_);
v_stop_boxed_5769_ = lean_unbox_usize(v_stop_5766_);
lean_dec(v_stop_5766_);
v_res_5770_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5764_, v_i_boxed_5768_, v_stop_boxed_5769_, v_b_5767_);
lean_dec_ref(v_as_5764_);
return v_res_5770_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_5771_, lean_object* v_as_5772_){
_start:
{
lean_object* v___x_5773_; lean_object* v___x_5774_; uint8_t v___x_5775_; 
v___x_5773_ = lean_unsigned_to_nat(0u);
v___x_5774_ = lean_array_get_size(v_as_5772_);
v___x_5775_ = lean_nat_dec_lt(v___x_5773_, v___x_5774_);
if (v___x_5775_ == 0)
{
return v_initState_5771_;
}
else
{
size_t v___x_5776_; size_t v___x_5777_; lean_object* v___x_5778_; 
v___x_5776_ = ((size_t)0ULL);
v___x_5777_ = lean_usize_of_nat(v___x_5774_);
v___x_5778_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5772_, v___x_5776_, v___x_5777_, v_initState_5771_);
return v___x_5778_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_5779_, lean_object* v_as_5780_){
_start:
{
lean_object* v_res_5781_; 
v_res_5781_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_5779_, v_as_5780_);
lean_dec_ref(v_as_5780_);
return v_res_5781_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5782_){
_start:
{
lean_object* v___x_5783_; lean_object* v___x_5784_; 
v___x_5783_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5784_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_5783_, v_es_5782_);
return v___x_5784_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_5785_){
_start:
{
lean_object* v_res_5786_; 
v_res_5786_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_5785_);
lean_dec_ref(v_es_5785_);
return v_res_5786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; 
v___x_5807_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5808_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5807_);
return v___x_5808_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_5809_){
_start:
{
lean_object* v_res_5810_; 
v_res_5810_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_5810_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5811_, lean_object* v___y_5812_, lean_object* v___y_5813_){
_start:
{
lean_object* v___x_5815_; lean_object* v_nextMacroScope_5816_; lean_object* v_ngen_5817_; lean_object* v_auxDeclNGen_5818_; lean_object* v_traceState_5819_; lean_object* v_messages_5820_; lean_object* v_infoState_5821_; lean_object* v_snapshotTasks_5822_; lean_object* v___x_5824_; uint8_t v_isShared_5825_; uint8_t v_isSharedCheck_5848_; 
v___x_5815_ = lean_st_ref_take(v___y_5813_);
v_nextMacroScope_5816_ = lean_ctor_get(v___x_5815_, 1);
v_ngen_5817_ = lean_ctor_get(v___x_5815_, 2);
v_auxDeclNGen_5818_ = lean_ctor_get(v___x_5815_, 3);
v_traceState_5819_ = lean_ctor_get(v___x_5815_, 4);
v_messages_5820_ = lean_ctor_get(v___x_5815_, 6);
v_infoState_5821_ = lean_ctor_get(v___x_5815_, 7);
v_snapshotTasks_5822_ = lean_ctor_get(v___x_5815_, 8);
v_isSharedCheck_5848_ = !lean_is_exclusive(v___x_5815_);
if (v_isSharedCheck_5848_ == 0)
{
lean_object* v_unused_5849_; lean_object* v_unused_5850_; 
v_unused_5849_ = lean_ctor_get(v___x_5815_, 5);
lean_dec(v_unused_5849_);
v_unused_5850_ = lean_ctor_get(v___x_5815_, 0);
lean_dec(v_unused_5850_);
v___x_5824_ = v___x_5815_;
v_isShared_5825_ = v_isSharedCheck_5848_;
goto v_resetjp_5823_;
}
else
{
lean_inc(v_snapshotTasks_5822_);
lean_inc(v_infoState_5821_);
lean_inc(v_messages_5820_);
lean_inc(v_traceState_5819_);
lean_inc(v_auxDeclNGen_5818_);
lean_inc(v_ngen_5817_);
lean_inc(v_nextMacroScope_5816_);
lean_dec(v___x_5815_);
v___x_5824_ = lean_box(0);
v_isShared_5825_ = v_isSharedCheck_5848_;
goto v_resetjp_5823_;
}
v_resetjp_5823_:
{
lean_object* v___x_5826_; lean_object* v___x_5828_; 
v___x_5826_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5825_ == 0)
{
lean_ctor_set(v___x_5824_, 5, v___x_5826_);
lean_ctor_set(v___x_5824_, 0, v_env_5811_);
v___x_5828_ = v___x_5824_;
goto v_reusejp_5827_;
}
else
{
lean_object* v_reuseFailAlloc_5847_; 
v_reuseFailAlloc_5847_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5847_, 0, v_env_5811_);
lean_ctor_set(v_reuseFailAlloc_5847_, 1, v_nextMacroScope_5816_);
lean_ctor_set(v_reuseFailAlloc_5847_, 2, v_ngen_5817_);
lean_ctor_set(v_reuseFailAlloc_5847_, 3, v_auxDeclNGen_5818_);
lean_ctor_set(v_reuseFailAlloc_5847_, 4, v_traceState_5819_);
lean_ctor_set(v_reuseFailAlloc_5847_, 5, v___x_5826_);
lean_ctor_set(v_reuseFailAlloc_5847_, 6, v_messages_5820_);
lean_ctor_set(v_reuseFailAlloc_5847_, 7, v_infoState_5821_);
lean_ctor_set(v_reuseFailAlloc_5847_, 8, v_snapshotTasks_5822_);
v___x_5828_ = v_reuseFailAlloc_5847_;
goto v_reusejp_5827_;
}
v_reusejp_5827_:
{
lean_object* v___x_5829_; lean_object* v___x_5830_; lean_object* v_mctx_5831_; lean_object* v_zetaDeltaFVarIds_5832_; lean_object* v_postponed_5833_; lean_object* v_diag_5834_; lean_object* v___x_5836_; uint8_t v_isShared_5837_; uint8_t v_isSharedCheck_5845_; 
v___x_5829_ = lean_st_ref_put(v___y_5813_, v___x_5828_);
v___x_5830_ = lean_st_ref_take(v___y_5812_);
v_mctx_5831_ = lean_ctor_get(v___x_5830_, 0);
v_zetaDeltaFVarIds_5832_ = lean_ctor_get(v___x_5830_, 2);
v_postponed_5833_ = lean_ctor_get(v___x_5830_, 3);
v_diag_5834_ = lean_ctor_get(v___x_5830_, 4);
v_isSharedCheck_5845_ = !lean_is_exclusive(v___x_5830_);
if (v_isSharedCheck_5845_ == 0)
{
lean_object* v_unused_5846_; 
v_unused_5846_ = lean_ctor_get(v___x_5830_, 1);
lean_dec(v_unused_5846_);
v___x_5836_ = v___x_5830_;
v_isShared_5837_ = v_isSharedCheck_5845_;
goto v_resetjp_5835_;
}
else
{
lean_inc(v_diag_5834_);
lean_inc(v_postponed_5833_);
lean_inc(v_zetaDeltaFVarIds_5832_);
lean_inc(v_mctx_5831_);
lean_dec(v___x_5830_);
v___x_5836_ = lean_box(0);
v_isShared_5837_ = v_isSharedCheck_5845_;
goto v_resetjp_5835_;
}
v_resetjp_5835_:
{
lean_object* v___x_5838_; lean_object* v___x_5840_; 
v___x_5838_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5837_ == 0)
{
lean_ctor_set(v___x_5836_, 1, v___x_5838_);
v___x_5840_ = v___x_5836_;
goto v_reusejp_5839_;
}
else
{
lean_object* v_reuseFailAlloc_5844_; 
v_reuseFailAlloc_5844_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5844_, 0, v_mctx_5831_);
lean_ctor_set(v_reuseFailAlloc_5844_, 1, v___x_5838_);
lean_ctor_set(v_reuseFailAlloc_5844_, 2, v_zetaDeltaFVarIds_5832_);
lean_ctor_set(v_reuseFailAlloc_5844_, 3, v_postponed_5833_);
lean_ctor_set(v_reuseFailAlloc_5844_, 4, v_diag_5834_);
v___x_5840_ = v_reuseFailAlloc_5844_;
goto v_reusejp_5839_;
}
v_reusejp_5839_:
{
lean_object* v___x_5841_; lean_object* v___x_5842_; lean_object* v___x_5843_; 
v___x_5841_ = lean_st_ref_put(v___y_5812_, v___x_5840_);
v___x_5842_ = lean_box(0);
v___x_5843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5843_, 0, v___x_5842_);
return v___x_5843_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5851_, lean_object* v___y_5852_, lean_object* v___y_5853_, lean_object* v___y_5854_){
_start:
{
lean_object* v_res_5855_; 
v_res_5855_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5851_, v___y_5852_, v___y_5853_);
lean_dec(v___y_5853_);
lean_dec(v___y_5852_);
return v_res_5855_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5856_, lean_object* v___y_5857_, lean_object* v___y_5858_, lean_object* v___y_5859_, lean_object* v___y_5860_){
_start:
{
lean_object* v___x_5862_; 
v___x_5862_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5856_, v___y_5858_, v___y_5860_);
return v___x_5862_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5863_, lean_object* v___y_5864_, lean_object* v___y_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_){
_start:
{
lean_object* v_res_5869_; 
v_res_5869_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5863_, v___y_5864_, v___y_5865_, v___y_5866_, v___y_5867_);
lean_dec(v___y_5867_);
lean_dec_ref(v___y_5866_);
lean_dec(v___y_5865_);
lean_dec_ref(v___y_5864_);
return v_res_5869_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5871_; lean_object* v___x_5872_; 
v___x_5871_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5872_ = l_Lean_stringToMessageData(v___x_5871_);
return v___x_5872_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5874_; lean_object* v___x_5875_; 
v___x_5874_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5875_ = l_Lean_stringToMessageData(v___x_5874_);
return v___x_5875_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5877_; lean_object* v___x_5878_; 
v___x_5877_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5878_ = l_Lean_stringToMessageData(v___x_5877_);
return v___x_5878_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5880_; lean_object* v___x_5881_; 
v___x_5880_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5881_ = l_Lean_stringToMessageData(v___x_5880_);
return v___x_5881_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5883_; lean_object* v___x_5884_; 
v___x_5883_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5884_ = l_Lean_stringToMessageData(v___x_5883_);
return v___x_5884_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5885_, lean_object* v_prio_5886_, lean_object* v_x_5887_, lean_object* v_type_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_){
_start:
{
lean_object* v___x_5894_; 
v___x_5894_ = l_Lean_Expr_getAppFn(v_type_5888_);
if (lean_obj_tag(v___x_5894_) == 4)
{
lean_object* v_declName_5895_; lean_object* v___y_5897_; lean_object* v___y_5898_; lean_object* v___y_5899_; lean_object* v___y_5900_; lean_object* v___x_5910_; lean_object* v_env_5911_; uint8_t v___x_5912_; 
v_declName_5895_ = lean_ctor_get(v___x_5894_, 0);
lean_inc(v_declName_5895_);
lean_dec_ref_known(v___x_5894_, 2);
v___x_5910_ = lean_st_ref_get(v___y_5892_);
v_env_5911_ = lean_ctor_get(v___x_5910_, 0);
lean_inc_ref(v_env_5911_);
lean_dec(v___x_5910_);
v___x_5912_ = l_Lean_isClass(v_env_5911_, v_declName_5895_);
if (v___x_5912_ == 0)
{
lean_object* v___x_5913_; lean_object* v___x_5914_; lean_object* v___x_5915_; lean_object* v___x_5916_; lean_object* v___x_5917_; lean_object* v___x_5918_; lean_object* v___x_5919_; lean_object* v___x_5920_; lean_object* v___x_5921_; lean_object* v___x_5922_; lean_object* v___x_5923_; lean_object* v___x_5924_; lean_object* v___x_5925_; lean_object* v___x_5926_; 
lean_dec(v_prio_5886_);
v___x_5913_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5914_ = l_Lean_MessageData_ofConstName(v_declName_5885_, v___x_5912_);
v___x_5915_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5915_, 0, v___x_5913_);
lean_ctor_set(v___x_5915_, 1, v___x_5914_);
v___x_5916_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5917_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5917_, 0, v___x_5915_);
lean_ctor_set(v___x_5917_, 1, v___x_5916_);
lean_inc(v_declName_5895_);
v___x_5918_ = l_Lean_MessageData_ofName(v_declName_5895_);
v___x_5919_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5919_, 0, v___x_5917_);
lean_ctor_set(v___x_5919_, 1, v___x_5918_);
v___x_5920_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5921_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5921_, 0, v___x_5919_);
lean_ctor_set(v___x_5921_, 1, v___x_5920_);
v___x_5922_ = l_Lean_MessageData_ofConstName(v_declName_5895_, v___x_5912_);
v___x_5923_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5923_, 0, v___x_5921_);
lean_ctor_set(v___x_5923_, 1, v___x_5922_);
v___x_5924_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5925_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5925_, 0, v___x_5923_);
lean_ctor_set(v___x_5925_, 1, v___x_5924_);
v___x_5926_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5925_, v___y_5889_, v___y_5890_, v___y_5891_, v___y_5892_);
return v___x_5926_;
}
else
{
v___y_5897_ = v___y_5889_;
v___y_5898_ = v___y_5890_;
v___y_5899_ = v___y_5891_;
v___y_5900_ = v___y_5892_;
goto v___jp_5896_;
}
v___jp_5896_:
{
lean_object* v___x_5901_; lean_object* v_env_5902_; lean_object* v___x_5903_; lean_object* v_toEnvExtension_5904_; lean_object* v_asyncMode_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; 
v___x_5901_ = lean_st_ref_get(v___y_5900_);
v_env_5902_ = lean_ctor_get(v___x_5901_, 0);
lean_inc_ref(v_env_5902_);
lean_dec(v___x_5901_);
v___x_5903_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5904_ = lean_ctor_get(v___x_5903_, 0);
v_asyncMode_5905_ = lean_ctor_get(v_toEnvExtension_5904_, 2);
v___x_5906_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5906_, 0, v_declName_5895_);
lean_ctor_set(v___x_5906_, 1, v_declName_5885_);
lean_ctor_set(v___x_5906_, 2, v_prio_5886_);
v___x_5907_ = lean_box(0);
v___x_5908_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5903_, v_env_5902_, v___x_5906_, v_asyncMode_5905_, v___x_5907_);
v___x_5909_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5908_, v___y_5898_, v___y_5900_);
return v___x_5909_;
}
}
else
{
lean_object* v___x_5927_; uint8_t v___x_5928_; lean_object* v___x_5929_; lean_object* v___x_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; 
lean_dec_ref(v___x_5894_);
lean_dec(v_prio_5886_);
v___x_5927_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5928_ = 0;
v___x_5929_ = l_Lean_MessageData_ofConstName(v_declName_5885_, v___x_5928_);
v___x_5930_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5930_, 0, v___x_5927_);
lean_ctor_set(v___x_5930_, 1, v___x_5929_);
v___x_5931_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5932_, 0, v___x_5930_);
lean_ctor_set(v___x_5932_, 1, v___x_5931_);
v___x_5933_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5932_, v___y_5889_, v___y_5890_, v___y_5891_, v___y_5892_);
return v___x_5933_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5934_, lean_object* v_prio_5935_, lean_object* v_x_5936_, lean_object* v_type_5937_, lean_object* v___y_5938_, lean_object* v___y_5939_, lean_object* v___y_5940_, lean_object* v___y_5941_, lean_object* v___y_5942_){
_start:
{
lean_object* v_res_5943_; 
v_res_5943_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5934_, v_prio_5935_, v_x_5936_, v_type_5937_, v___y_5938_, v___y_5939_, v___y_5940_, v___y_5941_);
lean_dec(v___y_5941_);
lean_dec_ref(v___y_5940_);
lean_dec(v___y_5939_);
lean_dec_ref(v___y_5938_);
lean_dec_ref(v_type_5937_);
lean_dec_ref(v_x_5936_);
return v_res_5943_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5944_, lean_object* v_prio_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_){
_start:
{
lean_object* v___x_5951_; lean_object* v_env_5952_; uint8_t v___x_5953_; lean_object* v___x_5954_; 
v___x_5951_ = lean_st_ref_get(v_a_5949_);
v_env_5952_ = lean_ctor_get(v___x_5951_, 0);
lean_inc_ref(v_env_5952_);
lean_dec(v___x_5951_);
v___x_5953_ = 0;
lean_inc(v_declName_5944_);
v___x_5954_ = l_Lean_Environment_find_x3f(v_env_5952_, v_declName_5944_, v___x_5953_);
if (lean_obj_tag(v___x_5954_) == 0)
{
lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; lean_object* v___x_5959_; lean_object* v___x_5960_; 
lean_dec(v_prio_5945_);
v___x_5955_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5956_ = l_Lean_MessageData_ofConstName(v_declName_5944_, v___x_5953_);
v___x_5957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5955_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
v___x_5958_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5959_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5959_, 0, v___x_5957_);
lean_ctor_set(v___x_5959_, 1, v___x_5958_);
v___x_5960_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5959_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_);
return v___x_5960_;
}
else
{
lean_object* v_val_5961_; lean_object* v___f_5962_; lean_object* v___x_5963_; lean_object* v___x_5964_; 
v_val_5961_ = lean_ctor_get(v___x_5954_, 0);
lean_inc(v_val_5961_);
lean_dec_ref_known(v___x_5954_, 1);
v___f_5962_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5962_, 0, v_declName_5944_);
lean_closure_set(v___f_5962_, 1, v_prio_5945_);
v___x_5963_ = l_Lean_ConstantInfo_type(v_val_5961_);
lean_dec(v_val_5961_);
v___x_5964_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5963_, v___f_5962_, v___x_5953_, v___x_5953_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_);
return v___x_5964_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5965_, lean_object* v_prio_5966_, lean_object* v_a_5967_, lean_object* v_a_5968_, lean_object* v_a_5969_, lean_object* v_a_5970_, lean_object* v_a_5971_){
_start:
{
lean_object* v_res_5972_; 
v_res_5972_ = l_Lean_Meta_addDefaultInstance(v_declName_5965_, v_prio_5966_, v_a_5967_, v_a_5968_, v_a_5969_, v_a_5970_);
lean_dec(v_a_5970_);
lean_dec_ref(v_a_5969_);
lean_dec(v_a_5968_);
lean_dec_ref(v_a_5967_);
return v_res_5972_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5974_; lean_object* v___x_5975_; 
v___x_5974_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5975_ = l_Lean_stringToMessageData(v___x_5974_);
return v___x_5975_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5977_; lean_object* v___x_5978_; 
v___x_5977_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5978_ = l_Lean_stringToMessageData(v___x_5977_);
return v___x_5978_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5982_, uint8_t v_kind_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_){
_start:
{
lean_object* v___x_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; lean_object* v___x_5990_; lean_object* v___x_5991_; lean_object* v___y_5993_; 
v___x_5987_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5988_ = l_Lean_MessageData_ofName(v_name_5982_);
v___x_5989_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5989_, 0, v___x_5987_);
lean_ctor_set(v___x_5989_, 1, v___x_5988_);
v___x_5990_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5991_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5991_, 0, v___x_5989_);
lean_ctor_set(v___x_5991_, 1, v___x_5990_);
switch(v_kind_5983_)
{
case 0:
{
lean_object* v___x_6000_; 
v___x_6000_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5993_ = v___x_6000_;
goto v___jp_5992_;
}
case 1:
{
lean_object* v___x_6001_; 
v___x_6001_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5993_ = v___x_6001_;
goto v___jp_5992_;
}
default: 
{
lean_object* v___x_6002_; 
v___x_6002_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5993_ = v___x_6002_;
goto v___jp_5992_;
}
}
v___jp_5992_:
{
lean_object* v___x_5994_; lean_object* v___x_5995_; lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; 
lean_inc_ref(v___y_5993_);
v___x_5994_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5994_, 0, v___y_5993_);
v___x_5995_ = l_Lean_MessageData_ofFormat(v___x_5994_);
v___x_5996_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5996_, 0, v___x_5991_);
lean_ctor_set(v___x_5996_, 1, v___x_5995_);
v___x_5997_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5998_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5998_, 0, v___x_5996_);
lean_ctor_set(v___x_5998_, 1, v___x_5997_);
v___x_5999_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5998_, v___y_5984_, v___y_5985_);
return v___x_5999_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_6003_, lean_object* v_kind_6004_, lean_object* v___y_6005_, lean_object* v___y_6006_, lean_object* v___y_6007_){
_start:
{
uint8_t v_kind_boxed_6008_; lean_object* v_res_6009_; 
v_kind_boxed_6008_ = lean_unbox(v_kind_6004_);
v_res_6009_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6003_, v_kind_boxed_6008_, v___y_6005_, v___y_6006_);
lean_dec(v___y_6006_);
lean_dec_ref(v___y_6005_);
return v_res_6009_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6010_, lean_object* v___x_6011_, lean_object* v___x_6012_, lean_object* v_declName_6013_, lean_object* v_stx_6014_, uint8_t v_kind_6015_, lean_object* v___y_6016_, lean_object* v___y_6017_){
_start:
{
lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; 
v___x_6019_ = lean_unsigned_to_nat(1u);
v___x_6020_ = l_Lean_Syntax_getArg(v_stx_6014_, v___x_6019_);
v___x_6021_ = l_Lean_getAttrParamOptPrio(v___x_6020_, v___y_6016_, v___y_6017_);
if (lean_obj_tag(v___x_6021_) == 0)
{
lean_object* v_a_6022_; lean_object* v___y_6024_; lean_object* v___y_6025_; uint8_t v___x_6056_; uint8_t v___x_6057_; 
v_a_6022_ = lean_ctor_get(v___x_6021_, 0);
lean_inc(v_a_6022_);
lean_dec_ref_known(v___x_6021_, 1);
v___x_6056_ = 0;
v___x_6057_ = l_Lean_instBEqAttributeKind_beq(v_kind_6015_, v___x_6056_);
if (v___x_6057_ == 0)
{
lean_object* v___x_6058_; 
lean_dec(v_a_6022_);
lean_dec(v_declName_6013_);
lean_dec(v___x_6011_);
lean_dec(v___x_6010_);
v___x_6058_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_6012_, v_kind_6015_, v___y_6016_, v___y_6017_);
return v___x_6058_;
}
else
{
lean_dec(v___x_6012_);
v___y_6024_ = v___y_6016_;
v___y_6025_ = v___y_6017_;
goto v___jp_6023_;
}
v___jp_6023_:
{
uint8_t v___x_6026_; uint8_t v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6030_; lean_object* v___x_6031_; lean_object* v___x_6032_; size_t v___x_6033_; lean_object* v___x_6034_; lean_object* v___x_6035_; lean_object* v___x_6036_; lean_object* v___x_6037_; lean_object* v___x_6038_; lean_object* v___x_6039_; lean_object* v___x_6040_; lean_object* v___x_6041_; lean_object* v___x_6042_; lean_object* v___x_6043_; lean_object* v___x_6044_; lean_object* v___x_6045_; 
v___x_6026_ = 0;
v___x_6027_ = 1;
v___x_6028_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6029_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6030_ = lean_unsigned_to_nat(32u);
v___x_6031_ = lean_mk_empty_array_with_capacity(v___x_6030_);
v___x_6032_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_6033_ = ((size_t)5ULL);
lean_inc_n(v___x_6010_, 6);
v___x_6034_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6034_, 0, v___x_6032_);
lean_ctor_set(v___x_6034_, 1, v___x_6031_);
lean_ctor_set(v___x_6034_, 2, v___x_6010_);
lean_ctor_set(v___x_6034_, 3, v___x_6010_);
lean_ctor_set_usize(v___x_6034_, 4, v___x_6033_);
v___x_6035_ = lean_box(1);
lean_inc_ref(v___x_6034_);
v___x_6036_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6036_, 0, v___x_6029_);
lean_ctor_set(v___x_6036_, 1, v___x_6034_);
lean_ctor_set(v___x_6036_, 2, v___x_6035_);
v___x_6037_ = lean_mk_empty_array_with_capacity(v___x_6010_);
v___x_6038_ = lean_box(0);
lean_inc(v___x_6011_);
v___x_6039_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6039_, 0, v___x_6028_);
lean_ctor_set(v___x_6039_, 1, v___x_6011_);
lean_ctor_set(v___x_6039_, 2, v___x_6036_);
lean_ctor_set(v___x_6039_, 3, v___x_6037_);
lean_ctor_set(v___x_6039_, 4, v___x_6038_);
lean_ctor_set(v___x_6039_, 5, v___x_6010_);
lean_ctor_set(v___x_6039_, 6, v___x_6038_);
lean_ctor_set_uint8(v___x_6039_, sizeof(void*)*7, v___x_6026_);
lean_ctor_set_uint8(v___x_6039_, sizeof(void*)*7 + 1, v___x_6026_);
lean_ctor_set_uint8(v___x_6039_, sizeof(void*)*7 + 2, v___x_6026_);
lean_ctor_set_uint8(v___x_6039_, sizeof(void*)*7 + 3, v___x_6027_);
v___x_6040_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6040_, 0, v___x_6010_);
lean_ctor_set(v___x_6040_, 1, v___x_6010_);
lean_ctor_set(v___x_6040_, 2, v___x_6010_);
lean_ctor_set(v___x_6040_, 3, v___x_6010_);
lean_ctor_set(v___x_6040_, 4, v___x_6029_);
lean_ctor_set(v___x_6040_, 5, v___x_6029_);
lean_ctor_set(v___x_6040_, 6, v___x_6029_);
lean_ctor_set(v___x_6040_, 7, v___x_6029_);
lean_ctor_set(v___x_6040_, 8, v___x_6029_);
lean_ctor_set(v___x_6040_, 9, v___x_6029_);
lean_ctor_set(v___x_6040_, 10, v___x_6029_);
v___x_6041_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6042_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6043_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6043_, 0, v___x_6040_);
lean_ctor_set(v___x_6043_, 1, v___x_6041_);
lean_ctor_set(v___x_6043_, 2, v___x_6011_);
lean_ctor_set(v___x_6043_, 3, v___x_6034_);
lean_ctor_set(v___x_6043_, 4, v___x_6042_);
v___x_6044_ = lean_st_mk_ref(v___x_6043_);
v___x_6045_ = l_Lean_Meta_addDefaultInstance(v_declName_6013_, v_a_6022_, v___x_6039_, v___x_6044_, v___y_6024_, v___y_6025_);
lean_dec_ref_known(v___x_6039_, 7);
if (lean_obj_tag(v___x_6045_) == 0)
{
lean_object* v___x_6047_; uint8_t v_isShared_6048_; uint8_t v_isSharedCheck_6054_; 
v_isSharedCheck_6054_ = !lean_is_exclusive(v___x_6045_);
if (v_isSharedCheck_6054_ == 0)
{
lean_object* v_unused_6055_; 
v_unused_6055_ = lean_ctor_get(v___x_6045_, 0);
lean_dec(v_unused_6055_);
v___x_6047_ = v___x_6045_;
v_isShared_6048_ = v_isSharedCheck_6054_;
goto v_resetjp_6046_;
}
else
{
lean_dec(v___x_6045_);
v___x_6047_ = lean_box(0);
v_isShared_6048_ = v_isSharedCheck_6054_;
goto v_resetjp_6046_;
}
v_resetjp_6046_:
{
lean_object* v___x_6049_; lean_object* v___x_6050_; lean_object* v___x_6052_; 
v___x_6049_ = lean_st_ref_get(v___x_6044_);
lean_dec(v___x_6044_);
lean_dec(v___x_6049_);
v___x_6050_ = lean_box(0);
if (v_isShared_6048_ == 0)
{
lean_ctor_set(v___x_6047_, 0, v___x_6050_);
v___x_6052_ = v___x_6047_;
goto v_reusejp_6051_;
}
else
{
lean_object* v_reuseFailAlloc_6053_; 
v_reuseFailAlloc_6053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6053_, 0, v___x_6050_);
v___x_6052_ = v_reuseFailAlloc_6053_;
goto v_reusejp_6051_;
}
v_reusejp_6051_:
{
return v___x_6052_;
}
}
}
else
{
lean_dec(v___x_6044_);
return v___x_6045_;
}
}
}
else
{
lean_object* v_a_6059_; lean_object* v___x_6061_; uint8_t v_isShared_6062_; uint8_t v_isSharedCheck_6066_; 
lean_dec(v_declName_6013_);
lean_dec(v___x_6012_);
lean_dec(v___x_6011_);
lean_dec(v___x_6010_);
v_a_6059_ = lean_ctor_get(v___x_6021_, 0);
v_isSharedCheck_6066_ = !lean_is_exclusive(v___x_6021_);
if (v_isSharedCheck_6066_ == 0)
{
v___x_6061_ = v___x_6021_;
v_isShared_6062_ = v_isSharedCheck_6066_;
goto v_resetjp_6060_;
}
else
{
lean_inc(v_a_6059_);
lean_dec(v___x_6021_);
v___x_6061_ = lean_box(0);
v_isShared_6062_ = v_isSharedCheck_6066_;
goto v_resetjp_6060_;
}
v_resetjp_6060_:
{
lean_object* v___x_6064_; 
if (v_isShared_6062_ == 0)
{
v___x_6064_ = v___x_6061_;
goto v_reusejp_6063_;
}
else
{
lean_object* v_reuseFailAlloc_6065_; 
v_reuseFailAlloc_6065_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6065_, 0, v_a_6059_);
v___x_6064_ = v_reuseFailAlloc_6065_;
goto v_reusejp_6063_;
}
v_reusejp_6063_:
{
return v___x_6064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6067_, lean_object* v___x_6068_, lean_object* v___x_6069_, lean_object* v_declName_6070_, lean_object* v_stx_6071_, lean_object* v_kind_6072_, lean_object* v___y_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_){
_start:
{
uint8_t v_kind_boxed_6076_; lean_object* v_res_6077_; 
v_kind_boxed_6076_ = lean_unbox(v_kind_6072_);
v_res_6077_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6067_, v___x_6068_, v___x_6069_, v_declName_6070_, v_stx_6071_, v_kind_boxed_6076_, v___y_6073_, v___y_6074_);
lean_dec(v___y_6074_);
lean_dec_ref(v___y_6073_);
lean_dec(v_stx_6071_);
return v_res_6077_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6079_; lean_object* v___x_6080_; 
v___x_6079_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6080_ = l_Lean_stringToMessageData(v___x_6079_);
return v___x_6080_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6082_; lean_object* v___x_6083_; 
v___x_6082_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6083_ = l_Lean_stringToMessageData(v___x_6082_);
return v___x_6083_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6084_, lean_object* v_decl_6085_, lean_object* v___y_6086_, lean_object* v___y_6087_){
_start:
{
lean_object* v___x_6089_; lean_object* v___x_6090_; lean_object* v___x_6091_; lean_object* v___x_6092_; lean_object* v___x_6093_; lean_object* v___x_6094_; 
v___x_6089_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6090_ = l_Lean_MessageData_ofName(v___x_6084_);
v___x_6091_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6091_, 0, v___x_6089_);
lean_ctor_set(v___x_6091_, 1, v___x_6090_);
v___x_6092_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6093_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6093_, 0, v___x_6091_);
lean_ctor_set(v___x_6093_, 1, v___x_6092_);
v___x_6094_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6093_, v___y_6086_, v___y_6087_);
return v___x_6094_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6095_, lean_object* v_decl_6096_, lean_object* v___y_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_){
_start:
{
lean_object* v_res_6100_; 
v_res_6100_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6095_, v_decl_6096_, v___y_6097_, v___y_6098_);
lean_dec(v___y_6098_);
lean_dec_ref(v___y_6097_);
lean_dec(v_decl_6096_);
return v_res_6100_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6133_; lean_object* v___x_6134_; lean_object* v___x_6135_; 
v___x_6133_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6134_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6135_ = l_Lean_registerBuiltinAttribute(v___x_6134_);
if (lean_obj_tag(v___x_6135_) == 0)
{
lean_object* v___x_6136_; uint8_t v___x_6137_; lean_object* v___x_6138_; 
lean_dec_ref_known(v___x_6135_, 1);
v___x_6136_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_6137_ = 0;
v___x_6138_ = l_Lean_registerTraceClass(v___x_6136_, v___x_6137_, v___x_6133_);
return v___x_6138_;
}
else
{
return v___x_6135_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_6139_){
_start:
{
lean_object* v_res_6140_; 
v_res_6140_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_6140_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_6141_, lean_object* v_name_6142_, uint8_t v_kind_6143_, lean_object* v___y_6144_, lean_object* v___y_6145_){
_start:
{
lean_object* v___x_6147_; 
v___x_6147_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6142_, v_kind_6143_, v___y_6144_, v___y_6145_);
return v___x_6147_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_6148_, lean_object* v_name_6149_, lean_object* v_kind_6150_, lean_object* v___y_6151_, lean_object* v___y_6152_, lean_object* v___y_6153_){
_start:
{
uint8_t v_kind_boxed_6154_; lean_object* v_res_6155_; 
v_kind_boxed_6154_ = lean_unbox(v_kind_6150_);
v_res_6155_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_6148_, v_name_6149_, v_kind_boxed_6154_, v___y_6151_, v___y_6152_);
lean_dec(v___y_6152_);
lean_dec_ref(v___y_6151_);
return v_res_6155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_6156_, lean_object* v_toPure_6157_, lean_object* v_____do__lift_6158_){
_start:
{
lean_object* v___x_6159_; lean_object* v_toEnvExtension_6160_; lean_object* v_asyncMode_6161_; lean_object* v___x_6162_; lean_object* v___x_6163_; lean_object* v_priorities_6164_; lean_object* v___x_6165_; 
v___x_6159_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6160_ = lean_ctor_get(v___x_6159_, 0);
v_asyncMode_6161_ = lean_ctor_get(v_toEnvExtension_6160_, 2);
v___x_6162_ = lean_box(0);
v___x_6163_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6156_, v___x_6159_, v_____do__lift_6158_, v_asyncMode_6161_, v___x_6162_);
v_priorities_6164_ = lean_ctor_get(v___x_6163_, 1);
lean_inc(v_priorities_6164_);
lean_dec(v___x_6163_);
v___x_6165_ = lean_apply_2(v_toPure_6157_, lean_box(0), v_priorities_6164_);
return v___x_6165_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_6166_, lean_object* v_inst_6167_){
_start:
{
lean_object* v_toApplicative_6168_; lean_object* v_toBind_6169_; lean_object* v_getEnv_6170_; lean_object* v_toPure_6171_; lean_object* v___x_6172_; lean_object* v___f_6173_; lean_object* v___x_6174_; 
v_toApplicative_6168_ = lean_ctor_get(v_inst_6166_, 0);
lean_inc_ref(v_toApplicative_6168_);
v_toBind_6169_ = lean_ctor_get(v_inst_6166_, 1);
lean_inc(v_toBind_6169_);
lean_dec_ref(v_inst_6166_);
v_getEnv_6170_ = lean_ctor_get(v_inst_6167_, 0);
lean_inc(v_getEnv_6170_);
lean_dec_ref(v_inst_6167_);
v_toPure_6171_ = lean_ctor_get(v_toApplicative_6168_, 1);
lean_inc(v_toPure_6171_);
lean_dec_ref(v_toApplicative_6168_);
v___x_6172_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6173_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6173_, 0, v___x_6172_);
lean_closure_set(v___f_6173_, 1, v_toPure_6171_);
v___x_6174_ = lean_apply_4(v_toBind_6169_, lean_box(0), lean_box(0), v_getEnv_6170_, v___f_6173_);
return v___x_6174_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_6175_, lean_object* v_inst_6176_, lean_object* v_inst_6177_){
_start:
{
lean_object* v___x_6178_; 
v___x_6178_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_6176_, v_inst_6177_);
return v___x_6178_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_6179_, uint8_t v_isExporting_6180_, lean_object* v_x_6181_){
_start:
{
lean_object* v_fst_6182_; uint8_t v___x_6183_; 
v_fst_6182_ = lean_ctor_get(v_x_6181_, 0);
lean_inc(v_fst_6182_);
lean_dec_ref(v_x_6181_);
v___x_6183_ = l_Lean_Environment_contains(v_env_6179_, v_fst_6182_, v_isExporting_6180_);
return v___x_6183_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_6184_, lean_object* v_isExporting_6185_, lean_object* v_x_6186_){
_start:
{
uint8_t v_isExporting_boxed_6187_; uint8_t v_res_6188_; lean_object* v_r_6189_; 
v_isExporting_boxed_6187_ = lean_unbox(v_isExporting_6185_);
v_res_6188_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_6184_, v_isExporting_boxed_6187_, v_x_6186_);
v_r_6189_ = lean_box(v_res_6188_);
return v_r_6189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_6190_, lean_object* v_toPure_6191_, lean_object* v_className_6192_, lean_object* v_env_6193_){
_start:
{
lean_object* v___y_6195_; lean_object* v___x_6203_; lean_object* v_toEnvExtension_6204_; lean_object* v_asyncMode_6205_; lean_object* v___x_6206_; lean_object* v___x_6207_; lean_object* v_defaultInstances_6208_; lean_object* v___x_6209_; 
v___x_6203_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6204_ = lean_ctor_get(v___x_6203_, 0);
v_asyncMode_6205_ = lean_ctor_get(v_toEnvExtension_6204_, 2);
v___x_6206_ = lean_box(0);
lean_inc_ref(v_env_6193_);
v___x_6207_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6190_, v___x_6203_, v_env_6193_, v_asyncMode_6205_, v___x_6206_);
v_defaultInstances_6208_ = lean_ctor_get(v___x_6207_, 0);
lean_inc(v_defaultInstances_6208_);
lean_dec(v___x_6207_);
v___x_6209_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_6208_, v_className_6192_);
lean_dec(v_defaultInstances_6208_);
if (lean_obj_tag(v___x_6209_) == 0)
{
lean_object* v___x_6210_; 
v___x_6210_ = lean_box(0);
v___y_6195_ = v___x_6210_;
goto v___jp_6194_;
}
else
{
lean_object* v_val_6211_; 
v_val_6211_ = lean_ctor_get(v___x_6209_, 0);
lean_inc(v_val_6211_);
lean_dec_ref_known(v___x_6209_, 1);
v___y_6195_ = v_val_6211_;
goto v___jp_6194_;
}
v___jp_6194_:
{
uint8_t v_isExporting_6196_; 
v_isExporting_6196_ = lean_ctor_get_uint8(v_env_6193_, sizeof(void*)*8);
if (v_isExporting_6196_ == 0)
{
lean_object* v___x_6197_; 
lean_dec_ref(v_env_6193_);
v___x_6197_ = lean_apply_2(v_toPure_6191_, lean_box(0), v___y_6195_);
return v___x_6197_;
}
else
{
lean_object* v___x_6198_; lean_object* v___f_6199_; lean_object* v___x_6200_; lean_object* v___x_6201_; lean_object* v___x_6202_; 
v___x_6198_ = lean_box(v_isExporting_6196_);
v___f_6199_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6199_, 0, v_env_6193_);
lean_closure_set(v___f_6199_, 1, v___x_6198_);
v___x_6200_ = lean_box(0);
v___x_6201_ = l_List_filterTR_loop___redArg(v___f_6199_, v___y_6195_, v___x_6200_);
v___x_6202_ = lean_apply_2(v_toPure_6191_, lean_box(0), v___x_6201_);
return v___x_6202_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_6212_, lean_object* v_toPure_6213_, lean_object* v_className_6214_, lean_object* v_env_6215_){
_start:
{
lean_object* v_res_6216_; 
v_res_6216_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_6212_, v_toPure_6213_, v_className_6214_, v_env_6215_);
lean_dec(v_className_6214_);
return v_res_6216_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_6217_, lean_object* v_inst_6218_, lean_object* v_className_6219_){
_start:
{
lean_object* v_toApplicative_6220_; lean_object* v_toBind_6221_; lean_object* v_getEnv_6222_; lean_object* v_toPure_6223_; lean_object* v___x_6224_; lean_object* v___f_6225_; lean_object* v___x_6226_; 
v_toApplicative_6220_ = lean_ctor_get(v_inst_6217_, 0);
lean_inc_ref(v_toApplicative_6220_);
v_toBind_6221_ = lean_ctor_get(v_inst_6217_, 1);
lean_inc(v_toBind_6221_);
lean_dec_ref(v_inst_6217_);
v_getEnv_6222_ = lean_ctor_get(v_inst_6218_, 0);
lean_inc(v_getEnv_6222_);
lean_dec_ref(v_inst_6218_);
v_toPure_6223_ = lean_ctor_get(v_toApplicative_6220_, 1);
lean_inc(v_toPure_6223_);
lean_dec_ref(v_toApplicative_6220_);
v___x_6224_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6225_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_6225_, 0, v___x_6224_);
lean_closure_set(v___f_6225_, 1, v_toPure_6223_);
lean_closure_set(v___f_6225_, 2, v_className_6219_);
v___x_6226_ = lean_apply_4(v_toBind_6221_, lean_box(0), lean_box(0), v_getEnv_6222_, v___f_6225_);
return v___x_6226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6227_, lean_object* v_inst_6228_, lean_object* v_inst_6229_, lean_object* v_className_6230_){
_start:
{
lean_object* v___x_6231_; 
v___x_6231_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6228_, v_inst_6229_, v_className_6230_);
return v___x_6231_;
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
