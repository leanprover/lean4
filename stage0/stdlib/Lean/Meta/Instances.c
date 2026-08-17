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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7;
static const lean_ctor_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_value;
static const lean_ctor_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6_value),((lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__8_value)}};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9_value;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "This instance has "};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = " argument"};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13;
static const lean_string_object l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "s"};
static const lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14 = (const lean_object*)&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14_value;
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
lean_object* v_ks_207_; lean_object* v_vs_208_; lean_object* v___x_210_; uint8_t v_isShared_211_; uint8_t v_isSharedCheck_228_; 
v_ks_207_ = lean_ctor_get(v_x_156_, 0);
v_vs_208_ = lean_ctor_get(v_x_156_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_x_156_);
if (v_isSharedCheck_228_ == 0)
{
v___x_210_ = v_x_156_;
v_isShared_211_ = v_isSharedCheck_228_;
goto v_resetjp_209_;
}
else
{
lean_inc(v_vs_208_);
lean_inc(v_ks_207_);
lean_dec(v_x_156_);
v___x_210_ = lean_box(0);
v_isShared_211_ = v_isSharedCheck_228_;
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
lean_object* v_reuseFailAlloc_227_; 
v_reuseFailAlloc_227_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_227_, 0, v_ks_207_);
lean_ctor_set(v_reuseFailAlloc_227_, 1, v_vs_208_);
v___x_213_ = v_reuseFailAlloc_227_;
goto v_reusejp_212_;
}
v_reusejp_212_:
{
lean_object* v_newNode_214_; uint8_t v___y_216_; size_t v___x_222_; uint8_t v___x_223_; 
v_newNode_214_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9___redArg(v___x_213_, v_x_159_, v_x_160_);
v___x_222_ = ((size_t)7ULL);
v___x_223_ = lean_usize_dec_le(v___x_222_, v_x_158_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
v___x_224_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_214_);
v___x_225_ = lean_unsigned_to_nat(4u);
v___x_226_ = lean_nat_dec_lt(v___x_224_, v___x_225_);
lean_dec(v___x_224_);
v___y_216_ = v___x_226_;
goto v___jp_215_;
}
else
{
v___y_216_ = v___x_223_;
goto v___jp_215_;
}
v___jp_215_:
{
if (v___y_216_ == 0)
{
lean_object* v_ks_217_; lean_object* v_vs_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; 
v_ks_217_ = lean_ctor_get(v_newNode_214_, 0);
lean_inc_ref(v_ks_217_);
v_vs_218_ = lean_ctor_get(v_newNode_214_, 1);
lean_inc_ref(v_vs_218_);
lean_dec_ref(v_newNode_214_);
v___x_219_ = lean_unsigned_to_nat(0u);
v___x_220_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0);
v___x_221_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_x_158_, v_ks_217_, v_vs_218_, v___x_219_, v___x_220_);
lean_dec_ref(v_vs_218_);
lean_dec_ref(v_ks_217_);
return v___x_221_;
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
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(size_t v_depth_229_, lean_object* v_keys_230_, lean_object* v_vals_231_, lean_object* v_i_232_, lean_object* v_entries_233_){
_start:
{
lean_object* v___x_234_; uint8_t v___x_235_; 
v___x_234_ = lean_array_get_size(v_keys_230_);
v___x_235_ = lean_nat_dec_lt(v_i_232_, v___x_234_);
if (v___x_235_ == 0)
{
lean_dec(v_i_232_);
return v_entries_233_;
}
else
{
lean_object* v_k_236_; lean_object* v_v_237_; uint64_t v___y_239_; 
v_k_236_ = lean_array_fget_borrowed(v_keys_230_, v_i_232_);
v_v_237_ = lean_array_fget_borrowed(v_vals_231_, v_i_232_);
if (lean_obj_tag(v_k_236_) == 0)
{
uint64_t v___x_250_; 
v___x_250_ = 1723ULL;
v___y_239_ = v___x_250_;
goto v___jp_238_;
}
else
{
uint64_t v_hash_251_; 
v_hash_251_ = lean_ctor_get_uint64(v_k_236_, sizeof(void*)*2);
v___y_239_ = v_hash_251_;
goto v___jp_238_;
}
v___jp_238_:
{
size_t v_h_240_; size_t v___x_241_; lean_object* v___x_242_; size_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v_h_246_; lean_object* v___x_247_; lean_object* v___x_248_; 
v_h_240_ = lean_uint64_to_usize(v___y_239_);
v___x_241_ = ((size_t)5ULL);
v___x_242_ = lean_unsigned_to_nat(1u);
v___x_243_ = ((size_t)1ULL);
v___x_244_ = lean_usize_sub(v_depth_229_, v___x_243_);
v___x_245_ = lean_usize_mul(v___x_241_, v___x_244_);
v_h_246_ = lean_usize_shift_right(v_h_240_, v___x_245_);
v___x_247_ = lean_nat_add(v_i_232_, v___x_242_);
lean_dec(v_i_232_);
lean_inc(v_v_237_);
lean_inc(v_k_236_);
v___x_248_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_entries_233_, v_h_246_, v_depth_229_, v_k_236_, v_v_237_);
v_i_232_ = v___x_247_;
v_entries_233_ = v___x_248_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_depth_252_, lean_object* v_keys_253_, lean_object* v_vals_254_, lean_object* v_i_255_, lean_object* v_entries_256_){
_start:
{
size_t v_depth_boxed_257_; lean_object* v_res_258_; 
v_depth_boxed_257_ = lean_unbox_usize(v_depth_252_);
lean_dec(v_depth_252_);
v_res_258_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_depth_boxed_257_, v_keys_253_, v_vals_254_, v_i_255_, v_entries_256_);
lean_dec_ref(v_vals_254_);
lean_dec_ref(v_keys_253_);
return v_res_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___boxed(lean_object* v_x_259_, lean_object* v_x_260_, lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_x_263_){
_start:
{
size_t v_x_2094__boxed_264_; size_t v_x_2095__boxed_265_; lean_object* v_res_266_; 
v_x_2094__boxed_264_ = lean_unbox_usize(v_x_260_);
lean_dec(v_x_260_);
v_x_2095__boxed_265_ = lean_unbox_usize(v_x_261_);
lean_dec(v_x_261_);
v_res_266_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_259_, v_x_2094__boxed_264_, v_x_2095__boxed_265_, v_x_262_, v_x_263_);
return v_res_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(lean_object* v_x_267_, lean_object* v_x_268_, lean_object* v_x_269_){
_start:
{
uint64_t v___y_271_; 
if (lean_obj_tag(v_x_268_) == 0)
{
uint64_t v___x_275_; 
v___x_275_ = 1723ULL;
v___y_271_ = v___x_275_;
goto v___jp_270_;
}
else
{
uint64_t v_hash_276_; 
v_hash_276_ = lean_ctor_get_uint64(v_x_268_, sizeof(void*)*2);
v___y_271_ = v_hash_276_;
goto v___jp_270_;
}
v___jp_270_:
{
size_t v___x_272_; size_t v___x_273_; lean_object* v___x_274_; 
v___x_272_ = lean_uint64_to_usize(v___y_271_);
v___x_273_ = ((size_t)1ULL);
v___x_274_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_267_, v___x_272_, v___x_273_, v_x_268_, v_x_269_);
return v___x_274_;
}
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(lean_object* v_msg_278_){
_start:
{
lean_object* v___x_279_; lean_object* v___x_280_; 
v___x_279_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0);
v___x_280_ = lean_panic_fn_borrowed(v___x_279_, v_msg_278_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(lean_object* v_xs_281_, lean_object* v_v_282_, lean_object* v_i_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = lean_array_get_size(v_xs_281_);
v___x_285_ = lean_nat_dec_lt(v_i_283_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; 
lean_dec(v_i_283_);
v___x_286_ = lean_box(0);
return v___x_286_;
}
else
{
lean_object* v___x_287_; uint8_t v___x_288_; 
v___x_287_ = lean_array_fget_borrowed(v_xs_281_, v_i_283_);
v___x_288_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_287_, v_v_282_);
if (v___x_288_ == 0)
{
lean_object* v___x_289_; lean_object* v___x_290_; 
v___x_289_ = lean_unsigned_to_nat(1u);
v___x_290_ = lean_nat_add(v_i_283_, v___x_289_);
lean_dec(v_i_283_);
v_i_283_ = v___x_290_;
goto _start;
}
else
{
lean_object* v___x_292_; 
v___x_292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_292_, 0, v_i_283_);
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_xs_293_, lean_object* v_v_294_, lean_object* v_i_295_){
_start:
{
lean_object* v_res_296_; 
v_res_296_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(v_xs_293_, v_v_294_, v_i_295_);
lean_dec(v_v_294_);
lean_dec_ref(v_xs_293_);
return v_res_296_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(lean_object* v_xs_297_, lean_object* v_v_298_){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = lean_unsigned_to_nat(0u);
v___x_300_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(v_xs_297_, v_v_298_, v___x_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4___boxed(lean_object* v_xs_301_, lean_object* v_v_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(v_xs_301_, v_v_302_);
lean_dec(v_v_302_);
lean_dec_ref(v_xs_301_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(lean_object* v_x_304_, lean_object* v_x_305_, lean_object* v_x_306_, lean_object* v_x_307_){
_start:
{
lean_object* v_ks_308_; lean_object* v_vs_309_; lean_object* v___x_311_; uint8_t v_isShared_312_; uint8_t v_isSharedCheck_333_; 
v_ks_308_ = lean_ctor_get(v_x_304_, 0);
v_vs_309_ = lean_ctor_get(v_x_304_, 1);
v_isSharedCheck_333_ = !lean_is_exclusive(v_x_304_);
if (v_isSharedCheck_333_ == 0)
{
v___x_311_ = v_x_304_;
v_isShared_312_ = v_isSharedCheck_333_;
goto v_resetjp_310_;
}
else
{
lean_inc(v_vs_309_);
lean_inc(v_ks_308_);
lean_dec(v_x_304_);
v___x_311_ = lean_box(0);
v_isShared_312_ = v_isSharedCheck_333_;
goto v_resetjp_310_;
}
v_resetjp_310_:
{
lean_object* v___x_313_; uint8_t v___x_314_; 
v___x_313_ = lean_array_get_size(v_ks_308_);
v___x_314_ = lean_nat_dec_lt(v_x_305_, v___x_313_);
if (v___x_314_ == 0)
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_318_; 
lean_dec(v_x_305_);
v___x_315_ = lean_array_push(v_ks_308_, v_x_306_);
v___x_316_ = lean_array_push(v_vs_309_, v_x_307_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_316_);
lean_ctor_set(v___x_311_, 0, v___x_315_);
v___x_318_ = v___x_311_;
goto v_reusejp_317_;
}
else
{
lean_object* v_reuseFailAlloc_319_; 
v_reuseFailAlloc_319_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_319_, 0, v___x_315_);
lean_ctor_set(v_reuseFailAlloc_319_, 1, v___x_316_);
v___x_318_ = v_reuseFailAlloc_319_;
goto v_reusejp_317_;
}
v_reusejp_317_:
{
return v___x_318_;
}
}
else
{
lean_object* v_k_x27_320_; uint8_t v___x_321_; 
v_k_x27_320_ = lean_array_fget_borrowed(v_ks_308_, v_x_305_);
v___x_321_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_306_, v_k_x27_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_323_; 
if (v_isShared_312_ == 0)
{
v___x_323_ = v___x_311_;
goto v_reusejp_322_;
}
else
{
lean_object* v_reuseFailAlloc_327_; 
v_reuseFailAlloc_327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_327_, 0, v_ks_308_);
lean_ctor_set(v_reuseFailAlloc_327_, 1, v_vs_309_);
v___x_323_ = v_reuseFailAlloc_327_;
goto v_reusejp_322_;
}
v_reusejp_322_:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = lean_nat_add(v_x_305_, v___x_324_);
lean_dec(v_x_305_);
v_x_304_ = v___x_323_;
v_x_305_ = v___x_325_;
goto _start;
}
}
else
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_331_; 
v___x_328_ = lean_array_fset(v_ks_308_, v_x_305_, v_x_306_);
v___x_329_ = lean_array_fset(v_vs_309_, v_x_305_, v_x_307_);
lean_dec(v_x_305_);
if (v_isShared_312_ == 0)
{
lean_ctor_set(v___x_311_, 1, v___x_329_);
lean_ctor_set(v___x_311_, 0, v___x_328_);
v___x_331_ = v___x_311_;
goto v_reusejp_330_;
}
else
{
lean_object* v_reuseFailAlloc_332_; 
v_reuseFailAlloc_332_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_332_, 0, v___x_328_);
lean_ctor_set(v_reuseFailAlloc_332_, 1, v___x_329_);
v___x_331_ = v_reuseFailAlloc_332_;
goto v_reusejp_330_;
}
v_reusejp_330_:
{
return v___x_331_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(lean_object* v_n_334_, lean_object* v_k_335_, lean_object* v_v_336_){
_start:
{
lean_object* v___x_337_; lean_object* v___x_338_; 
v___x_337_ = lean_unsigned_to_nat(0u);
v___x_338_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(v_n_334_, v___x_337_, v_k_335_, v_v_336_);
return v___x_338_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_339_; 
v___x_339_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_x_340_, size_t v_x_341_, size_t v_x_342_, lean_object* v_x_343_, lean_object* v_x_344_){
_start:
{
if (lean_obj_tag(v_x_340_) == 0)
{
lean_object* v_es_345_; size_t v___x_346_; size_t v___x_347_; lean_object* v_j_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v_es_345_ = lean_ctor_get(v_x_340_, 0);
v___x_346_ = ((size_t)31ULL);
v___x_347_ = lean_usize_land(v_x_341_, v___x_346_);
v_j_348_ = lean_usize_to_nat(v___x_347_);
v___x_349_ = lean_array_get_size(v_es_345_);
v___x_350_ = lean_nat_dec_lt(v_j_348_, v___x_349_);
if (v___x_350_ == 0)
{
lean_dec(v_j_348_);
lean_dec(v_x_344_);
lean_dec(v_x_343_);
return v_x_340_;
}
else
{
lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_389_; 
lean_inc_ref(v_es_345_);
v_isSharedCheck_389_ = !lean_is_exclusive(v_x_340_);
if (v_isSharedCheck_389_ == 0)
{
lean_object* v_unused_390_; 
v_unused_390_ = lean_ctor_get(v_x_340_, 0);
lean_dec(v_unused_390_);
v___x_352_ = v_x_340_;
v_isShared_353_ = v_isSharedCheck_389_;
goto v_resetjp_351_;
}
else
{
lean_dec(v_x_340_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_389_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v_v_354_; lean_object* v___x_355_; lean_object* v_xs_x27_356_; lean_object* v___y_358_; 
v_v_354_ = lean_array_fget(v_es_345_, v_j_348_);
v___x_355_ = lean_box(0);
v_xs_x27_356_ = lean_array_fset(v_es_345_, v_j_348_, v___x_355_);
switch(lean_obj_tag(v_v_354_))
{
case 0:
{
lean_object* v_key_363_; lean_object* v_val_364_; lean_object* v___x_366_; uint8_t v_isShared_367_; uint8_t v_isSharedCheck_374_; 
v_key_363_ = lean_ctor_get(v_v_354_, 0);
v_val_364_ = lean_ctor_get(v_v_354_, 1);
v_isSharedCheck_374_ = !lean_is_exclusive(v_v_354_);
if (v_isSharedCheck_374_ == 0)
{
v___x_366_ = v_v_354_;
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
else
{
lean_inc(v_val_364_);
lean_inc(v_key_363_);
lean_dec(v_v_354_);
v___x_366_ = lean_box(0);
v_isShared_367_ = v_isSharedCheck_374_;
goto v_resetjp_365_;
}
v_resetjp_365_:
{
uint8_t v___x_368_; 
v___x_368_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_343_, v_key_363_);
if (v___x_368_ == 0)
{
lean_object* v___x_369_; lean_object* v___x_370_; 
lean_del_object(v___x_366_);
v___x_369_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_363_, v_val_364_, v_x_343_, v_x_344_);
v___x_370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_370_, 0, v___x_369_);
v___y_358_ = v___x_370_;
goto v___jp_357_;
}
else
{
lean_object* v___x_372_; 
lean_dec(v_val_364_);
lean_dec(v_key_363_);
if (v_isShared_367_ == 0)
{
lean_ctor_set(v___x_366_, 1, v_x_344_);
lean_ctor_set(v___x_366_, 0, v_x_343_);
v___x_372_ = v___x_366_;
goto v_reusejp_371_;
}
else
{
lean_object* v_reuseFailAlloc_373_; 
v_reuseFailAlloc_373_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_373_, 0, v_x_343_);
lean_ctor_set(v_reuseFailAlloc_373_, 1, v_x_344_);
v___x_372_ = v_reuseFailAlloc_373_;
goto v_reusejp_371_;
}
v_reusejp_371_:
{
v___y_358_ = v___x_372_;
goto v___jp_357_;
}
}
}
}
case 1:
{
lean_object* v_node_375_; lean_object* v___x_377_; uint8_t v_isShared_378_; uint8_t v_isSharedCheck_387_; 
v_node_375_ = lean_ctor_get(v_v_354_, 0);
v_isSharedCheck_387_ = !lean_is_exclusive(v_v_354_);
if (v_isSharedCheck_387_ == 0)
{
v___x_377_ = v_v_354_;
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
else
{
lean_inc(v_node_375_);
lean_dec(v_v_354_);
v___x_377_ = lean_box(0);
v_isShared_378_ = v_isSharedCheck_387_;
goto v_resetjp_376_;
}
v_resetjp_376_:
{
size_t v___x_379_; size_t v___x_380_; size_t v___x_381_; size_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_385_; 
v___x_379_ = ((size_t)5ULL);
v___x_380_ = lean_usize_shift_right(v_x_341_, v___x_379_);
v___x_381_ = ((size_t)1ULL);
v___x_382_ = lean_usize_add(v_x_342_, v___x_381_);
v___x_383_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_node_375_, v___x_380_, v___x_382_, v_x_343_, v_x_344_);
if (v_isShared_378_ == 0)
{
lean_ctor_set(v___x_377_, 0, v___x_383_);
v___x_385_ = v___x_377_;
goto v_reusejp_384_;
}
else
{
lean_object* v_reuseFailAlloc_386_; 
v_reuseFailAlloc_386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_386_, 0, v___x_383_);
v___x_385_ = v_reuseFailAlloc_386_;
goto v_reusejp_384_;
}
v_reusejp_384_:
{
v___y_358_ = v___x_385_;
goto v___jp_357_;
}
}
}
default: 
{
lean_object* v___x_388_; 
v___x_388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_388_, 0, v_x_343_);
lean_ctor_set(v___x_388_, 1, v_x_344_);
v___y_358_ = v___x_388_;
goto v___jp_357_;
}
}
v___jp_357_:
{
lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_359_ = lean_array_fset(v_xs_x27_356_, v_j_348_, v___y_358_);
lean_dec(v_j_348_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 0, v___x_359_);
v___x_361_ = v___x_352_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
else
{
lean_object* v_ks_391_; lean_object* v_vs_392_; lean_object* v___x_394_; uint8_t v_isShared_395_; uint8_t v_isSharedCheck_412_; 
v_ks_391_ = lean_ctor_get(v_x_340_, 0);
v_vs_392_ = lean_ctor_get(v_x_340_, 1);
v_isSharedCheck_412_ = !lean_is_exclusive(v_x_340_);
if (v_isSharedCheck_412_ == 0)
{
v___x_394_ = v_x_340_;
v_isShared_395_ = v_isSharedCheck_412_;
goto v_resetjp_393_;
}
else
{
lean_inc(v_vs_392_);
lean_inc(v_ks_391_);
lean_dec(v_x_340_);
v___x_394_ = lean_box(0);
v_isShared_395_ = v_isSharedCheck_412_;
goto v_resetjp_393_;
}
v_resetjp_393_:
{
lean_object* v___x_397_; 
if (v_isShared_395_ == 0)
{
v___x_397_ = v___x_394_;
goto v_reusejp_396_;
}
else
{
lean_object* v_reuseFailAlloc_411_; 
v_reuseFailAlloc_411_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_411_, 0, v_ks_391_);
lean_ctor_set(v_reuseFailAlloc_411_, 1, v_vs_392_);
v___x_397_ = v_reuseFailAlloc_411_;
goto v_reusejp_396_;
}
v_reusejp_396_:
{
lean_object* v_newNode_398_; uint8_t v___y_400_; size_t v___x_406_; uint8_t v___x_407_; 
v_newNode_398_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(v___x_397_, v_x_343_, v_x_344_);
v___x_406_ = ((size_t)7ULL);
v___x_407_ = lean_usize_dec_le(v___x_406_, v_x_342_);
if (v___x_407_ == 0)
{
lean_object* v___x_408_; lean_object* v___x_409_; uint8_t v___x_410_; 
v___x_408_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_398_);
v___x_409_ = lean_unsigned_to_nat(4u);
v___x_410_ = lean_nat_dec_lt(v___x_408_, v___x_409_);
lean_dec(v___x_408_);
v___y_400_ = v___x_410_;
goto v___jp_399_;
}
else
{
v___y_400_ = v___x_407_;
goto v___jp_399_;
}
v___jp_399_:
{
if (v___y_400_ == 0)
{
lean_object* v_ks_401_; lean_object* v_vs_402_; lean_object* v___x_403_; lean_object* v___x_404_; lean_object* v___x_405_; 
v_ks_401_ = lean_ctor_get(v_newNode_398_, 0);
lean_inc_ref(v_ks_401_);
v_vs_402_ = lean_ctor_get(v_newNode_398_, 1);
lean_inc_ref(v_vs_402_);
lean_dec_ref(v_newNode_398_);
v___x_403_ = lean_unsigned_to_nat(0u);
v___x_404_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0);
v___x_405_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(v_x_342_, v_ks_401_, v_vs_402_, v___x_403_, v___x_404_);
lean_dec_ref(v_vs_402_);
lean_dec_ref(v_ks_401_);
return v___x_405_;
}
else
{
return v_newNode_398_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(size_t v_depth_413_, lean_object* v_keys_414_, lean_object* v_vals_415_, lean_object* v_i_416_, lean_object* v_entries_417_){
_start:
{
lean_object* v___x_418_; uint8_t v___x_419_; 
v___x_418_ = lean_array_get_size(v_keys_414_);
v___x_419_ = lean_nat_dec_lt(v_i_416_, v___x_418_);
if (v___x_419_ == 0)
{
lean_dec(v_i_416_);
return v_entries_417_;
}
else
{
lean_object* v_k_420_; lean_object* v_v_421_; uint64_t v___x_422_; size_t v_h_423_; size_t v___x_424_; lean_object* v___x_425_; size_t v___x_426_; size_t v___x_427_; size_t v___x_428_; size_t v_h_429_; lean_object* v___x_430_; lean_object* v___x_431_; 
v_k_420_ = lean_array_fget_borrowed(v_keys_414_, v_i_416_);
v_v_421_ = lean_array_fget_borrowed(v_vals_415_, v_i_416_);
v___x_422_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_420_);
v_h_423_ = lean_uint64_to_usize(v___x_422_);
v___x_424_ = ((size_t)5ULL);
v___x_425_ = lean_unsigned_to_nat(1u);
v___x_426_ = ((size_t)1ULL);
v___x_427_ = lean_usize_sub(v_depth_413_, v___x_426_);
v___x_428_ = lean_usize_mul(v___x_424_, v___x_427_);
v_h_429_ = lean_usize_shift_right(v_h_423_, v___x_428_);
v___x_430_ = lean_nat_add(v_i_416_, v___x_425_);
lean_dec(v_i_416_);
lean_inc(v_v_421_);
lean_inc(v_k_420_);
v___x_431_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_entries_417_, v_h_429_, v_depth_413_, v_k_420_, v_v_421_);
v_i_416_ = v___x_430_;
v_entries_417_ = v___x_431_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg___boxed(lean_object* v_depth_433_, lean_object* v_keys_434_, lean_object* v_vals_435_, lean_object* v_i_436_, lean_object* v_entries_437_){
_start:
{
size_t v_depth_boxed_438_; lean_object* v_res_439_; 
v_depth_boxed_438_ = lean_unbox_usize(v_depth_433_);
lean_dec(v_depth_433_);
v_res_439_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(v_depth_boxed_438_, v_keys_434_, v_vals_435_, v_i_436_, v_entries_437_);
lean_dec_ref(v_vals_435_);
lean_dec_ref(v_keys_434_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_x_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_){
_start:
{
size_t v_x_2375__boxed_445_; size_t v_x_2376__boxed_446_; lean_object* v_res_447_; 
v_x_2375__boxed_445_ = lean_unbox_usize(v_x_441_);
lean_dec(v_x_441_);
v_x_2376__boxed_446_ = lean_unbox_usize(v_x_442_);
lean_dec(v_x_442_);
v_res_447_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_x_440_, v_x_2375__boxed_445_, v_x_2376__boxed_446_, v_x_443_, v_x_444_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(lean_object* v_x_448_, lean_object* v_keys_449_, lean_object* v_v_450_, lean_object* v_k_451_, lean_object* v_x_452_){
_start:
{
lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v_c_455_; lean_object* v___x_456_; 
v___x_453_ = lean_unsigned_to_nat(1u);
v___x_454_ = lean_nat_add(v_x_448_, v___x_453_);
v_c_455_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_449_, v_v_450_, v___x_454_);
lean_dec(v___x_454_);
v___x_456_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_456_, 0, v_k_451_);
lean_ctor_set(v___x_456_, 1, v_c_455_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* v_x_457_, lean_object* v_keys_458_, lean_object* v_v_459_, lean_object* v_k_460_, lean_object* v_x_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_457_, v_keys_458_, v_v_459_, v_k_460_, v_x_461_);
lean_dec_ref(v_keys_458_);
lean_dec(v_x_457_);
return v_res_462_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(lean_object* v_a_463_, lean_object* v_b_464_){
_start:
{
lean_object* v_fst_465_; lean_object* v_fst_466_; uint8_t v___x_467_; 
v_fst_465_ = lean_ctor_get(v_a_463_, 0);
v_fst_466_ = lean_ctor_get(v_b_464_, 0);
v___x_467_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_465_, v_fst_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1___boxed(lean_object* v_a_468_, lean_object* v_b_469_){
_start:
{
uint8_t v_res_470_; lean_object* v_r_471_; 
v_res_470_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_a_468_, v_b_469_);
lean_dec_ref(v_b_469_);
lean_dec_ref(v_a_468_);
v_r_471_ = lean_box(v_res_470_);
return v_r_471_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(lean_object* v_vs_472_, lean_object* v_v_473_, lean_object* v_i_474_){
_start:
{
lean_object* v___x_475_; uint8_t v___x_476_; 
v___x_475_ = lean_array_get_size(v_vs_472_);
v___x_476_ = lean_nat_dec_lt(v_i_474_, v___x_475_);
if (v___x_476_ == 0)
{
lean_object* v___x_477_; 
lean_dec(v_i_474_);
v___x_477_ = lean_array_push(v_vs_472_, v_v_473_);
return v___x_477_;
}
else
{
lean_object* v_val_478_; lean_object* v___x_479_; lean_object* v_val_480_; uint8_t v___x_481_; 
v_val_478_ = lean_ctor_get(v_v_473_, 1);
v___x_479_ = lean_array_fget_borrowed(v_vs_472_, v_i_474_);
v_val_480_ = lean_ctor_get(v___x_479_, 1);
v___x_481_ = lean_expr_eqv(v_val_478_, v_val_480_);
if (v___x_481_ == 0)
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = lean_unsigned_to_nat(1u);
v___x_483_ = lean_nat_add(v_i_474_, v___x_482_);
lean_dec(v_i_474_);
v_i_474_ = v___x_483_;
goto _start;
}
else
{
lean_object* v___x_485_; 
v___x_485_ = lean_array_fset(v_vs_472_, v_i_474_, v_v_473_);
lean_dec(v_i_474_);
return v___x_485_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(lean_object* v_vs_486_, lean_object* v_v_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_unsigned_to_nat(0u);
v___x_489_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(v_vs_486_, v_v_487_, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_x_494_, lean_object* v_keys_495_, lean_object* v_v_496_, lean_object* v_k_497_, lean_object* v_as_498_, lean_object* v_k_499_, lean_object* v_x_500_, lean_object* v_x_501_){
_start:
{
lean_object* v___x_502_; lean_object* v___x_503_; lean_object* v_mid_504_; lean_object* v_midVal_505_; uint8_t v___x_506_; 
v___x_502_ = lean_nat_add(v_x_500_, v_x_501_);
v___x_503_ = lean_unsigned_to_nat(1u);
v_mid_504_ = lean_nat_shiftr(v___x_502_, v___x_503_);
lean_dec(v___x_502_);
v_midVal_505_ = lean_array_fget(v_as_498_, v_mid_504_);
v___x_506_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_midVal_505_, v_k_499_);
if (v___x_506_ == 0)
{
uint8_t v___x_507_; 
lean_dec(v_x_501_);
v___x_507_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_499_, v_midVal_505_);
if (v___x_507_ == 0)
{
lean_object* v___x_508_; uint8_t v___x_509_; 
lean_dec(v_x_500_);
v___x_508_ = lean_array_get_size(v_as_498_);
v___x_509_ = lean_nat_dec_lt(v_mid_504_, v___x_508_);
if (v___x_509_ == 0)
{
lean_dec(v_midVal_505_);
lean_dec(v_mid_504_);
lean_dec(v_k_497_);
lean_dec_ref(v_v_496_);
return v_as_498_;
}
else
{
lean_object* v_snd_510_; lean_object* v___x_512_; uint8_t v_isShared_513_; uint8_t v_isSharedCheck_522_; 
v_snd_510_ = lean_ctor_get(v_midVal_505_, 1);
v_isSharedCheck_522_ = !lean_is_exclusive(v_midVal_505_);
if (v_isSharedCheck_522_ == 0)
{
lean_object* v_unused_523_; 
v_unused_523_ = lean_ctor_get(v_midVal_505_, 0);
lean_dec(v_unused_523_);
v___x_512_ = v_midVal_505_;
v_isShared_513_ = v_isSharedCheck_522_;
goto v_resetjp_511_;
}
else
{
lean_inc(v_snd_510_);
lean_dec(v_midVal_505_);
v___x_512_ = lean_box(0);
v_isShared_513_ = v_isSharedCheck_522_;
goto v_resetjp_511_;
}
v_resetjp_511_:
{
lean_object* v___x_514_; lean_object* v_xs_x27_515_; lean_object* v___x_516_; lean_object* v_c_517_; lean_object* v___x_519_; 
v___x_514_ = lean_box(0);
v_xs_x27_515_ = lean_array_fset(v_as_498_, v_mid_504_, v___x_514_);
v___x_516_ = lean_nat_add(v_x_494_, v___x_503_);
v_c_517_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_495_, v_v_496_, v___x_516_, v_snd_510_);
lean_dec(v___x_516_);
if (v_isShared_513_ == 0)
{
lean_ctor_set(v___x_512_, 1, v_c_517_);
lean_ctor_set(v___x_512_, 0, v_k_497_);
v___x_519_ = v___x_512_;
goto v_reusejp_518_;
}
else
{
lean_object* v_reuseFailAlloc_521_; 
v_reuseFailAlloc_521_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_521_, 0, v_k_497_);
lean_ctor_set(v_reuseFailAlloc_521_, 1, v_c_517_);
v___x_519_ = v_reuseFailAlloc_521_;
goto v_reusejp_518_;
}
v_reusejp_518_:
{
lean_object* v___x_520_; 
v___x_520_ = lean_array_fset(v_xs_x27_515_, v_mid_504_, v___x_519_);
lean_dec(v_mid_504_);
return v___x_520_;
}
}
}
}
else
{
lean_dec(v_midVal_505_);
v_x_501_ = v_mid_504_;
goto _start;
}
}
else
{
uint8_t v___x_525_; 
lean_dec(v_midVal_505_);
v___x_525_ = lean_nat_dec_eq(v_mid_504_, v_x_500_);
if (v___x_525_ == 0)
{
lean_dec(v_x_500_);
v_x_500_ = v_mid_504_;
goto _start;
}
else
{
lean_object* v___x_527_; lean_object* v_c_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v_j_531_; lean_object* v_as_532_; lean_object* v___x_533_; 
lean_dec(v_mid_504_);
lean_dec(v_x_501_);
v___x_527_ = lean_nat_add(v_x_494_, v___x_503_);
v_c_528_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_495_, v_v_496_, v___x_527_);
lean_dec(v___x_527_);
v___x_529_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_529_, 0, v_k_497_);
lean_ctor_set(v___x_529_, 1, v_c_528_);
v___x_530_ = lean_nat_add(v_x_500_, v___x_503_);
lean_dec(v_x_500_);
v_j_531_ = lean_array_get_size(v_as_498_);
v_as_532_ = lean_array_push(v_as_498_, v___x_529_);
v___x_533_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_530_, v_as_532_, v_j_531_);
lean_dec(v___x_530_);
return v___x_533_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(lean_object* v_x_534_, lean_object* v_keys_535_, lean_object* v_v_536_, lean_object* v_k_537_, lean_object* v_as_538_, lean_object* v_k_539_){
_start:
{
lean_object* v___x_540_; lean_object* v___x_541_; uint8_t v___x_542_; 
v___x_540_ = lean_array_get_size(v_as_538_);
v___x_541_ = lean_unsigned_to_nat(0u);
v___x_542_ = lean_nat_dec_eq(v___x_540_, v___x_541_);
if (v___x_542_ == 0)
{
lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_543_ = lean_array_fget_borrowed(v_as_538_, v___x_541_);
v___x_544_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_539_, v___x_543_);
if (v___x_544_ == 0)
{
uint8_t v___x_545_; 
v___x_545_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v___x_543_, v_k_539_);
if (v___x_545_ == 0)
{
uint8_t v___x_546_; 
v___x_546_ = lean_nat_dec_lt(v___x_541_, v___x_540_);
if (v___x_546_ == 0)
{
lean_dec(v_k_537_);
lean_dec_ref(v_v_536_);
return v_as_538_;
}
else
{
lean_object* v___x_547_; lean_object* v_xs_x27_548_; lean_object* v___x_549_; lean_object* v___x_550_; 
lean_inc(v___x_543_);
v___x_547_ = lean_box(0);
v_xs_x27_548_ = lean_array_fset(v_as_538_, v___x_541_, v___x_547_);
v___x_549_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_534_, v_keys_535_, v_v_536_, v_k_537_, v___x_543_);
v___x_550_ = lean_array_fset(v_xs_x27_548_, v___x_541_, v___x_549_);
return v___x_550_;
}
}
else
{
lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; uint8_t v___x_554_; 
v___x_551_ = lean_unsigned_to_nat(1u);
v___x_552_ = lean_nat_sub(v___x_540_, v___x_551_);
v___x_553_ = lean_array_fget_borrowed(v_as_538_, v___x_552_);
v___x_554_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v___x_553_, v_k_539_);
if (v___x_554_ == 0)
{
uint8_t v___x_555_; 
v___x_555_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_539_, v___x_553_);
if (v___x_555_ == 0)
{
uint8_t v___x_556_; 
v___x_556_ = lean_nat_dec_lt(v___x_552_, v___x_540_);
if (v___x_556_ == 0)
{
lean_dec(v___x_552_);
lean_dec(v_k_537_);
lean_dec_ref(v_v_536_);
return v_as_538_;
}
else
{
lean_object* v___x_557_; lean_object* v_xs_x27_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_inc(v___x_553_);
v___x_557_ = lean_box(0);
v_xs_x27_558_ = lean_array_fset(v_as_538_, v___x_552_, v___x_557_);
v___x_559_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_534_, v_keys_535_, v_v_536_, v_k_537_, v___x_553_);
v___x_560_ = lean_array_fset(v_xs_x27_558_, v___x_552_, v___x_559_);
lean_dec(v___x_552_);
return v___x_560_;
}
}
else
{
lean_object* v___x_561_; 
v___x_561_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_534_, v_keys_535_, v_v_536_, v_k_537_, v_as_538_, v_k_539_, v___x_541_, v___x_552_);
return v___x_561_;
}
}
else
{
lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; 
lean_dec(v___x_552_);
v___x_562_ = lean_box(0);
v___x_563_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_534_, v_keys_535_, v_v_536_, v_k_537_, v___x_562_);
v___x_564_ = lean_array_push(v_as_538_, v___x_563_);
return v___x_564_;
}
}
}
else
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v_as_567_; lean_object* v___x_568_; 
v___x_565_ = lean_box(0);
v___x_566_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_534_, v_keys_535_, v_v_536_, v_k_537_, v___x_565_);
v_as_567_ = lean_array_push(v_as_538_, v___x_566_);
v___x_568_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_541_, v_as_567_, v___x_540_);
return v___x_568_;
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_569_ = lean_box(0);
v___x_570_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_534_, v_keys_535_, v_v_536_, v_k_537_, v___x_569_);
v___x_571_ = lean_array_push(v_as_538_, v___x_570_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object* v_keys_572_, lean_object* v_v_573_, lean_object* v_x_574_, lean_object* v_x_575_){
_start:
{
lean_object* v_vs_576_; lean_object* v_children_577_; lean_object* v___x_579_; uint8_t v_isShared_580_; uint8_t v_isSharedCheck_594_; 
v_vs_576_ = lean_ctor_get(v_x_575_, 0);
v_children_577_ = lean_ctor_get(v_x_575_, 1);
v_isSharedCheck_594_ = !lean_is_exclusive(v_x_575_);
if (v_isSharedCheck_594_ == 0)
{
v___x_579_ = v_x_575_;
v_isShared_580_ = v_isSharedCheck_594_;
goto v_resetjp_578_;
}
else
{
lean_inc(v_children_577_);
lean_inc(v_vs_576_);
lean_dec(v_x_575_);
v___x_579_ = lean_box(0);
v_isShared_580_ = v_isSharedCheck_594_;
goto v_resetjp_578_;
}
v_resetjp_578_:
{
lean_object* v___x_581_; uint8_t v___x_582_; 
v___x_581_ = lean_array_get_size(v_keys_572_);
v___x_582_ = lean_nat_dec_lt(v_x_574_, v___x_581_);
if (v___x_582_ == 0)
{
lean_object* v___x_583_; lean_object* v___x_585_; 
v___x_583_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(v_vs_576_, v_v_573_);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 0, v___x_583_);
v___x_585_ = v___x_579_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_586_; 
v_reuseFailAlloc_586_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_586_, 0, v___x_583_);
lean_ctor_set(v_reuseFailAlloc_586_, 1, v_children_577_);
v___x_585_ = v_reuseFailAlloc_586_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
return v___x_585_;
}
}
else
{
lean_object* v_k_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v_c_590_; lean_object* v___x_592_; 
v_k_587_ = lean_array_fget_borrowed(v_keys_572_, v_x_574_);
v___x_588_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__1));
lean_inc_n(v_k_587_, 2);
v___x_589_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_589_, 0, v_k_587_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v_c_590_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(v_x_574_, v_keys_572_, v_v_573_, v_k_587_, v_children_577_, v___x_589_);
lean_dec_ref_known(v___x_589_, 2);
if (v_isShared_580_ == 0)
{
lean_ctor_set(v___x_579_, 1, v_c_590_);
v___x_592_ = v___x_579_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_593_; 
v_reuseFailAlloc_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_593_, 0, v_vs_576_);
lean_ctor_set(v_reuseFailAlloc_593_, 1, v_c_590_);
v___x_592_ = v_reuseFailAlloc_593_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
return v___x_592_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(lean_object* v_x_595_, lean_object* v_keys_596_, lean_object* v_v_597_, lean_object* v_k_598_, lean_object* v_x_599_){
_start:
{
lean_object* v_snd_600_; lean_object* v___x_602_; uint8_t v_isShared_603_; uint8_t v_isSharedCheck_610_; 
v_snd_600_ = lean_ctor_get(v_x_599_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_x_599_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v_x_599_, 0);
lean_dec(v_unused_611_);
v___x_602_ = v_x_599_;
v_isShared_603_ = v_isSharedCheck_610_;
goto v_resetjp_601_;
}
else
{
lean_inc(v_snd_600_);
lean_dec(v_x_599_);
v___x_602_ = lean_box(0);
v_isShared_603_ = v_isSharedCheck_610_;
goto v_resetjp_601_;
}
v_resetjp_601_:
{
lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v_c_606_; lean_object* v___x_608_; 
v___x_604_ = lean_unsigned_to_nat(1u);
v___x_605_ = lean_nat_add(v_x_595_, v___x_604_);
v_c_606_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_596_, v_v_597_, v___x_605_, v_snd_600_);
lean_dec(v___x_605_);
if (v_isShared_603_ == 0)
{
lean_ctor_set(v___x_602_, 1, v_c_606_);
lean_ctor_set(v___x_602_, 0, v_k_598_);
v___x_608_ = v___x_602_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_k_598_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_c_606_);
v___x_608_ = v_reuseFailAlloc_609_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
return v___x_608_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* v_x_612_, lean_object* v_keys_613_, lean_object* v_v_614_, lean_object* v_k_615_, lean_object* v_x_616_){
_start:
{
lean_object* v_res_617_; 
v_res_617_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_612_, v_keys_613_, v_v_614_, v_k_615_, v_x_616_);
lean_dec_ref(v_keys_613_);
lean_dec(v_x_612_);
return v_res_617_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object* v_keys_618_, lean_object* v_v_619_, lean_object* v_x_620_, lean_object* v_x_621_){
_start:
{
lean_object* v_res_622_; 
v_res_622_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_618_, v_v_619_, v_x_620_, v_x_621_);
lean_dec(v_x_620_);
lean_dec_ref(v_keys_618_);
return v_res_622_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_x_623_, lean_object* v_keys_624_, lean_object* v_v_625_, lean_object* v_k_626_, lean_object* v_as_627_, lean_object* v_k_628_, lean_object* v_x_629_, lean_object* v_x_630_){
_start:
{
lean_object* v_res_631_; 
v_res_631_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_623_, v_keys_624_, v_v_625_, v_k_626_, v_as_627_, v_k_628_, v_x_629_, v_x_630_);
lean_dec_ref(v_k_628_);
lean_dec_ref(v_keys_624_);
lean_dec(v_x_623_);
return v_res_631_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_x_632_, lean_object* v_keys_633_, lean_object* v_v_634_, lean_object* v_k_635_, lean_object* v_as_636_, lean_object* v_k_637_){
_start:
{
lean_object* v_res_638_; 
v_res_638_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(v_x_632_, v_keys_633_, v_v_634_, v_k_635_, v_as_636_, v_k_637_);
lean_dec_ref(v_k_637_);
lean_dec_ref(v_keys_633_);
lean_dec(v_x_632_);
return v_res_638_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(lean_object* v_keys_639_, lean_object* v_v_640_, lean_object* v_x_641_){
_start:
{
if (lean_obj_tag(v_x_641_) == 0)
{
lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_642_ = lean_unsigned_to_nat(1u);
v___x_643_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_639_, v_v_640_, v___x_642_);
v___x_644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_644_, 0, v___x_643_);
return v___x_644_;
}
else
{
lean_object* v_val_645_; lean_object* v___x_647_; uint8_t v_isShared_648_; uint8_t v_isSharedCheck_654_; 
v_val_645_ = lean_ctor_get(v_x_641_, 0);
v_isSharedCheck_654_ = !lean_is_exclusive(v_x_641_);
if (v_isSharedCheck_654_ == 0)
{
v___x_647_ = v_x_641_;
v_isShared_648_ = v_isSharedCheck_654_;
goto v_resetjp_646_;
}
else
{
lean_inc(v_val_645_);
lean_dec(v_x_641_);
v___x_647_ = lean_box(0);
v_isShared_648_ = v_isSharedCheck_654_;
goto v_resetjp_646_;
}
v_resetjp_646_:
{
lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_652_; 
v___x_649_ = lean_unsigned_to_nat(1u);
v___x_650_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_639_, v_v_640_, v___x_649_, v_val_645_);
if (v_isShared_648_ == 0)
{
lean_ctor_set(v___x_647_, 0, v___x_650_);
v___x_652_ = v___x_647_;
goto v_reusejp_651_;
}
else
{
lean_object* v_reuseFailAlloc_653_; 
v_reuseFailAlloc_653_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_653_, 0, v___x_650_);
v___x_652_ = v_reuseFailAlloc_653_;
goto v_reusejp_651_;
}
v_reusejp_651_:
{
return v___x_652_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0___boxed(lean_object* v_keys_655_, lean_object* v_v_656_, lean_object* v_x_657_){
_start:
{
lean_object* v_res_658_; 
v_res_658_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_655_, v_v_656_, v_x_657_);
lean_dec_ref(v_keys_655_);
return v_res_658_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(lean_object* v_keys_659_, lean_object* v_v_660_, lean_object* v_x_661_, size_t v_x_662_, size_t v_x_663_, lean_object* v_x_664_){
_start:
{
if (lean_obj_tag(v_x_661_) == 0)
{
lean_object* v_es_665_; size_t v___x_666_; size_t v___x_667_; lean_object* v_j_668_; lean_object* v___x_669_; uint8_t v___x_670_; 
v_es_665_ = lean_ctor_get(v_x_661_, 0);
v___x_666_ = ((size_t)31ULL);
v___x_667_ = lean_usize_land(v_x_662_, v___x_666_);
v_j_668_ = lean_usize_to_nat(v___x_667_);
v___x_669_ = lean_array_get_size(v_es_665_);
v___x_670_ = lean_nat_dec_lt(v_j_668_, v___x_669_);
if (v___x_670_ == 0)
{
lean_dec(v_j_668_);
lean_dec(v_x_664_);
lean_dec_ref(v_v_660_);
return v_x_661_;
}
else
{
lean_object* v___x_672_; uint8_t v_isShared_673_; uint8_t v_isSharedCheck_738_; 
lean_inc_ref(v_es_665_);
v_isSharedCheck_738_ = !lean_is_exclusive(v_x_661_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v_x_661_, 0);
lean_dec(v_unused_739_);
v___x_672_ = v_x_661_;
v_isShared_673_ = v_isSharedCheck_738_;
goto v_resetjp_671_;
}
else
{
lean_dec(v_x_661_);
v___x_672_ = lean_box(0);
v_isShared_673_ = v_isSharedCheck_738_;
goto v_resetjp_671_;
}
v_resetjp_671_:
{
lean_object* v_v_674_; lean_object* v___x_675_; lean_object* v_xs_x27_676_; lean_object* v___y_678_; 
v_v_674_ = lean_array_fget(v_es_665_, v_j_668_);
v___x_675_ = lean_box(0);
v_xs_x27_676_ = lean_array_fset(v_es_665_, v_j_668_, v___x_675_);
switch(lean_obj_tag(v_v_674_))
{
case 0:
{
lean_object* v_key_683_; lean_object* v_val_684_; uint8_t v___x_685_; 
v_key_683_ = lean_ctor_get(v_v_674_, 0);
v_val_684_ = lean_ctor_get(v_v_674_, 1);
v___x_685_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_664_, v_key_683_);
if (v___x_685_ == 0)
{
lean_object* v___x_686_; lean_object* v___x_687_; 
v___x_686_ = lean_box(0);
v___x_687_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_659_, v_v_660_, v___x_686_);
if (lean_obj_tag(v___x_687_) == 0)
{
lean_dec(v_x_664_);
v___y_678_ = v_v_674_;
goto v___jp_677_;
}
else
{
lean_object* v_val_688_; lean_object* v___x_690_; uint8_t v_isShared_691_; uint8_t v_isSharedCheck_696_; 
lean_inc(v_val_684_);
lean_inc(v_key_683_);
lean_dec_ref_known(v_v_674_, 2);
v_val_688_ = lean_ctor_get(v___x_687_, 0);
v_isSharedCheck_696_ = !lean_is_exclusive(v___x_687_);
if (v_isSharedCheck_696_ == 0)
{
v___x_690_ = v___x_687_;
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
else
{
lean_inc(v_val_688_);
lean_dec(v___x_687_);
v___x_690_ = lean_box(0);
v_isShared_691_ = v_isSharedCheck_696_;
goto v_resetjp_689_;
}
v_resetjp_689_:
{
lean_object* v___x_692_; lean_object* v___x_694_; 
v___x_692_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_683_, v_val_684_, v_x_664_, v_val_688_);
if (v_isShared_691_ == 0)
{
lean_ctor_set(v___x_690_, 0, v___x_692_);
v___x_694_ = v___x_690_;
goto v_reusejp_693_;
}
else
{
lean_object* v_reuseFailAlloc_695_; 
v_reuseFailAlloc_695_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_695_, 0, v___x_692_);
v___x_694_ = v_reuseFailAlloc_695_;
goto v_reusejp_693_;
}
v_reusejp_693_:
{
v___y_678_ = v___x_694_;
goto v___jp_677_;
}
}
}
}
else
{
lean_object* v___x_698_; uint8_t v_isShared_699_; uint8_t v_isSharedCheck_707_; 
lean_inc(v_val_684_);
v_isSharedCheck_707_ = !lean_is_exclusive(v_v_674_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; lean_object* v_unused_709_; 
v_unused_708_ = lean_ctor_get(v_v_674_, 1);
lean_dec(v_unused_708_);
v_unused_709_ = lean_ctor_get(v_v_674_, 0);
lean_dec(v_unused_709_);
v___x_698_ = v_v_674_;
v_isShared_699_ = v_isSharedCheck_707_;
goto v_resetjp_697_;
}
else
{
lean_dec(v_v_674_);
v___x_698_ = lean_box(0);
v_isShared_699_ = v_isSharedCheck_707_;
goto v_resetjp_697_;
}
v_resetjp_697_:
{
lean_object* v___x_700_; lean_object* v___x_701_; 
v___x_700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_700_, 0, v_val_684_);
v___x_701_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_659_, v_v_660_, v___x_700_);
if (lean_obj_tag(v___x_701_) == 0)
{
lean_object* v___x_702_; 
lean_del_object(v___x_698_);
lean_dec(v_x_664_);
v___x_702_ = lean_box(2);
v___y_678_ = v___x_702_;
goto v___jp_677_;
}
else
{
lean_object* v_val_703_; lean_object* v___x_705_; 
v_val_703_ = lean_ctor_get(v___x_701_, 0);
lean_inc(v_val_703_);
lean_dec_ref_known(v___x_701_, 1);
if (v_isShared_699_ == 0)
{
lean_ctor_set(v___x_698_, 1, v_val_703_);
lean_ctor_set(v___x_698_, 0, v_x_664_);
v___x_705_ = v___x_698_;
goto v_reusejp_704_;
}
else
{
lean_object* v_reuseFailAlloc_706_; 
v_reuseFailAlloc_706_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_706_, 0, v_x_664_);
lean_ctor_set(v_reuseFailAlloc_706_, 1, v_val_703_);
v___x_705_ = v_reuseFailAlloc_706_;
goto v_reusejp_704_;
}
v_reusejp_704_:
{
v___y_678_ = v___x_705_;
goto v___jp_677_;
}
}
}
}
}
case 1:
{
lean_object* v_node_710_; lean_object* v___x_712_; uint8_t v_isShared_713_; uint8_t v_isSharedCheck_733_; 
v_node_710_ = lean_ctor_get(v_v_674_, 0);
v_isSharedCheck_733_ = !lean_is_exclusive(v_v_674_);
if (v_isSharedCheck_733_ == 0)
{
v___x_712_ = v_v_674_;
v_isShared_713_ = v_isSharedCheck_733_;
goto v_resetjp_711_;
}
else
{
lean_inc(v_node_710_);
lean_dec(v_v_674_);
v___x_712_ = lean_box(0);
v_isShared_713_ = v_isSharedCheck_733_;
goto v_resetjp_711_;
}
v_resetjp_711_:
{
size_t v___x_714_; size_t v___x_715_; size_t v___x_716_; size_t v___x_717_; lean_object* v_newNode_718_; lean_object* v___x_719_; 
v___x_714_ = ((size_t)5ULL);
v___x_715_ = lean_usize_shift_right(v_x_662_, v___x_714_);
v___x_716_ = ((size_t)1ULL);
v___x_717_ = lean_usize_add(v_x_663_, v___x_716_);
v_newNode_718_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_659_, v_v_660_, v_node_710_, v___x_715_, v___x_717_, v_x_664_);
lean_inc_ref(v_newNode_718_);
v___x_719_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_718_);
if (lean_obj_tag(v___x_719_) == 0)
{
lean_object* v___x_721_; 
if (v_isShared_713_ == 0)
{
lean_ctor_set(v___x_712_, 0, v_newNode_718_);
v___x_721_ = v___x_712_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v_newNode_718_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
v___y_678_ = v___x_721_;
goto v___jp_677_;
}
}
else
{
lean_object* v_val_723_; lean_object* v_fst_724_; lean_object* v_snd_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_732_; 
lean_dec_ref(v_newNode_718_);
lean_del_object(v___x_712_);
v_val_723_ = lean_ctor_get(v___x_719_, 0);
lean_inc(v_val_723_);
lean_dec_ref_known(v___x_719_, 1);
v_fst_724_ = lean_ctor_get(v_val_723_, 0);
v_snd_725_ = lean_ctor_get(v_val_723_, 1);
v_isSharedCheck_732_ = !lean_is_exclusive(v_val_723_);
if (v_isSharedCheck_732_ == 0)
{
v___x_727_ = v_val_723_;
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_snd_725_);
lean_inc(v_fst_724_);
lean_dec(v_val_723_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_732_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_730_; 
if (v_isShared_728_ == 0)
{
v___x_730_ = v___x_727_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v_fst_724_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_snd_725_);
v___x_730_ = v_reuseFailAlloc_731_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
v___y_678_ = v___x_730_;
goto v___jp_677_;
}
}
}
}
}
default: 
{
lean_object* v___x_734_; lean_object* v___x_735_; 
v___x_734_ = lean_box(0);
v___x_735_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_659_, v_v_660_, v___x_734_);
if (lean_obj_tag(v___x_735_) == 0)
{
lean_dec(v_x_664_);
v___y_678_ = v_v_674_;
goto v___jp_677_;
}
else
{
lean_object* v_val_736_; lean_object* v___x_737_; 
v_val_736_ = lean_ctor_get(v___x_735_, 0);
lean_inc(v_val_736_);
lean_dec_ref_known(v___x_735_, 1);
v___x_737_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_737_, 0, v_x_664_);
lean_ctor_set(v___x_737_, 1, v_val_736_);
v___y_678_ = v___x_737_;
goto v___jp_677_;
}
}
}
v___jp_677_:
{
lean_object* v___x_679_; lean_object* v___x_681_; 
v___x_679_ = lean_array_fset(v_xs_x27_676_, v_j_668_, v___y_678_);
lean_dec(v_j_668_);
if (v_isShared_673_ == 0)
{
lean_ctor_set(v___x_672_, 0, v___x_679_);
v___x_681_ = v___x_672_;
goto v_reusejp_680_;
}
else
{
lean_object* v_reuseFailAlloc_682_; 
v_reuseFailAlloc_682_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_682_, 0, v___x_679_);
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
else
{
lean_object* v_ks_740_; lean_object* v_vs_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_774_; 
v_ks_740_ = lean_ctor_get(v_x_661_, 0);
v_vs_741_ = lean_ctor_get(v_x_661_, 1);
v_isSharedCheck_774_ = !lean_is_exclusive(v_x_661_);
if (v_isSharedCheck_774_ == 0)
{
v___x_743_ = v_x_661_;
v_isShared_744_ = v_isSharedCheck_774_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_vs_741_);
lean_inc(v_ks_740_);
lean_dec(v_x_661_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_774_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; 
v___x_745_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(v_ks_740_, v_x_664_);
if (lean_obj_tag(v___x_745_) == 0)
{
lean_object* v___x_747_; 
if (v_isShared_744_ == 0)
{
v___x_747_ = v___x_743_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v_ks_740_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_vs_741_);
v___x_747_ = v_reuseFailAlloc_752_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_748_; lean_object* v___x_749_; 
v___x_748_ = lean_box(0);
v___x_749_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_659_, v_v_660_, v___x_748_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_dec(v_x_664_);
return v___x_747_;
}
else
{
lean_object* v_val_750_; lean_object* v___x_751_; 
v_val_750_ = lean_ctor_get(v___x_749_, 0);
lean_inc(v_val_750_);
lean_dec_ref_known(v___x_749_, 1);
v___x_751_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v___x_747_, v_x_662_, v_x_663_, v_x_664_, v_val_750_);
return v___x_751_;
}
}
}
else
{
lean_object* v_val_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_773_; 
v_val_753_ = lean_ctor_get(v___x_745_, 0);
v_isSharedCheck_773_ = !lean_is_exclusive(v___x_745_);
if (v_isSharedCheck_773_ == 0)
{
v___x_755_ = v___x_745_;
v_isShared_756_ = v_isSharedCheck_773_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_val_753_);
lean_dec(v___x_745_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_773_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v_v_x27_757_; lean_object* v_keys_758_; lean_object* v_vals_759_; lean_object* v___x_761_; 
v_v_x27_757_ = lean_array_fget(v_vs_741_, v_val_753_);
lean_inc(v_val_753_);
v_keys_758_ = l_Array_eraseIdx___redArg(v_ks_740_, v_val_753_);
v_vals_759_ = l_Array_eraseIdx___redArg(v_vs_741_, v_val_753_);
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 0, v_v_x27_757_);
v___x_761_ = v___x_755_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_772_; 
v_reuseFailAlloc_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_772_, 0, v_v_x27_757_);
v___x_761_ = v_reuseFailAlloc_772_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
lean_object* v___x_762_; 
v___x_762_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_659_, v_v_660_, v___x_761_);
if (lean_obj_tag(v___x_762_) == 0)
{
lean_object* v___x_764_; 
lean_dec(v_x_664_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v_vals_759_);
lean_ctor_set(v___x_743_, 0, v_keys_758_);
v___x_764_ = v___x_743_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_765_; 
v_reuseFailAlloc_765_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_765_, 0, v_keys_758_);
lean_ctor_set(v_reuseFailAlloc_765_, 1, v_vals_759_);
v___x_764_ = v_reuseFailAlloc_765_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
return v___x_764_;
}
}
else
{
lean_object* v_val_766_; lean_object* v_keys_767_; lean_object* v_vals_768_; lean_object* v___x_770_; 
v_val_766_ = lean_ctor_get(v___x_762_, 0);
lean_inc(v_val_766_);
lean_dec_ref_known(v___x_762_, 1);
v_keys_767_ = lean_array_push(v_keys_758_, v_x_664_);
v_vals_768_ = lean_array_push(v_vals_759_, v_val_766_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v_vals_768_);
lean_ctor_set(v___x_743_, 0, v_keys_767_);
v___x_770_ = v___x_743_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_771_; 
v_reuseFailAlloc_771_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_771_, 0, v_keys_767_);
lean_ctor_set(v_reuseFailAlloc_771_, 1, v_vals_768_);
v___x_770_ = v_reuseFailAlloc_771_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
return v___x_770_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___boxed(lean_object* v_keys_775_, lean_object* v_v_776_, lean_object* v_x_777_, lean_object* v_x_778_, lean_object* v_x_779_, lean_object* v_x_780_){
_start:
{
size_t v_x_2800__boxed_781_; size_t v_x_2801__boxed_782_; lean_object* v_res_783_; 
v_x_2800__boxed_781_ = lean_unbox_usize(v_x_778_);
lean_dec(v_x_778_);
v_x_2801__boxed_782_ = lean_unbox_usize(v_x_779_);
lean_dec(v_x_779_);
v_res_783_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_775_, v_v_776_, v_x_777_, v_x_2800__boxed_781_, v_x_2801__boxed_782_, v_x_780_);
lean_dec_ref(v_keys_775_);
return v_res_783_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; 
v___x_787_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2));
v___x_788_ = lean_unsigned_to_nat(23u);
v___x_789_ = lean_unsigned_to_nat(166u);
v___x_790_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1));
v___x_791_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0));
v___x_792_ = l_mkPanicMessageWithDecl(v___x_791_, v___x_790_, v___x_789_, v___x_788_, v___x_787_);
return v___x_792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(lean_object* v_d_793_, lean_object* v_keys_794_, lean_object* v_v_795_){
_start:
{
lean_object* v___x_796_; lean_object* v___x_797_; uint8_t v___x_798_; 
v___x_796_ = lean_array_get_size(v_keys_794_);
v___x_797_ = lean_unsigned_to_nat(0u);
v___x_798_ = lean_nat_dec_eq(v___x_796_, v___x_797_);
if (v___x_798_ == 0)
{
lean_object* v___x_799_; lean_object* v_k_800_; uint64_t v___x_801_; size_t v_h_802_; size_t v___x_803_; lean_object* v___x_804_; 
v___x_799_ = lean_box(0);
v_k_800_ = lean_array_get_borrowed(v___x_799_, v_keys_794_, v___x_797_);
v___x_801_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_800_);
v_h_802_ = lean_uint64_to_usize(v___x_801_);
v___x_803_ = ((size_t)1ULL);
lean_inc(v_k_800_);
v___x_804_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_794_, v_v_795_, v_d_793_, v_h_802_, v___x_803_, v_k_800_);
return v___x_804_;
}
else
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec_ref(v_v_795_);
lean_dec_ref(v_d_793_);
v___x_805_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3);
v___x_806_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v___x_805_);
return v___x_806_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___boxed(lean_object* v_d_807_, lean_object* v_keys_808_, lean_object* v_v_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_d_807_, v_keys_808_, v_v_809_);
lean_dec_ref(v_keys_808_);
return v_res_810_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2071_, lean_object* v_as_2072_, size_t v_i_2073_, size_t v_stop_2074_, lean_object* v_b_2075_){
_start:
{
lean_object* v___y_2077_; uint8_t v___x_2081_; 
v___x_2081_ = lean_usize_dec_eq(v_i_2073_, v_stop_2074_);
if (v___x_2081_ == 0)
{
lean_object* v___x_2082_; uint8_t v___x_2083_; 
v___x_2082_ = lean_array_uget_borrowed(v_as_2072_, v_i_2073_);
v___x_2083_ = lean_nat_dec_eq(v___x_2082_, v_next_2071_);
if (v___x_2083_ == 0)
{
lean_object* v___x_2084_; 
lean_inc(v___x_2082_);
v___x_2084_ = lean_array_push(v_b_2075_, v___x_2082_);
v___y_2077_ = v___x_2084_;
goto v___jp_2076_;
}
else
{
v___y_2077_ = v_b_2075_;
goto v___jp_2076_;
}
}
else
{
return v_b_2075_;
}
v___jp_2076_:
{
size_t v___x_2078_; size_t v___x_2079_; 
v___x_2078_ = ((size_t)1ULL);
v___x_2079_ = lean_usize_add(v_i_2073_, v___x_2078_);
v_i_2073_ = v___x_2079_;
v_b_2075_ = v___y_2077_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2085_, lean_object* v_as_2086_, lean_object* v_i_2087_, lean_object* v_stop_2088_, lean_object* v_b_2089_){
_start:
{
size_t v_i_boxed_2090_; size_t v_stop_boxed_2091_; lean_object* v_res_2092_; 
v_i_boxed_2090_ = lean_unbox_usize(v_i_2087_);
lean_dec(v_i_2087_);
v_stop_boxed_2091_ = lean_unbox_usize(v_stop_2088_);
lean_dec(v_stop_2088_);
v_res_2092_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2085_, v_as_2086_, v_i_boxed_2090_, v_stop_boxed_2091_, v_b_2089_);
lean_dec_ref(v_as_2086_);
lean_dec(v_next_2085_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object* v_fst_2093_, lean_object* v_fst_2094_, lean_object* v_argVars_2095_, lean_object* v_snd_2096_, lean_object* v_next_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_){
_start:
{
lean_object* v___x_2103_; lean_object* v___y_2105_; lean_object* v___x_2146_; lean_object* v___x_2147_; lean_object* v___x_2148_; uint8_t v___x_2149_; 
lean_inc(v_next_2097_);
v___x_2103_ = lean_array_push(v_fst_2093_, v_next_2097_);
v___x_2146_ = lean_unsigned_to_nat(0u);
v___x_2147_ = lean_array_get_size(v_snd_2096_);
v___x_2148_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2149_ = lean_nat_dec_lt(v___x_2146_, v___x_2147_);
if (v___x_2149_ == 0)
{
v___y_2105_ = v___x_2148_;
goto v___jp_2104_;
}
else
{
uint8_t v___x_2150_; 
v___x_2150_ = lean_nat_dec_le(v___x_2147_, v___x_2147_);
if (v___x_2150_ == 0)
{
if (v___x_2149_ == 0)
{
v___y_2105_ = v___x_2148_;
goto v___jp_2104_;
}
else
{
size_t v___x_2151_; size_t v___x_2152_; lean_object* v___x_2153_; 
v___x_2151_ = ((size_t)0ULL);
v___x_2152_ = lean_usize_of_nat(v___x_2147_);
v___x_2153_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2097_, v_snd_2096_, v___x_2151_, v___x_2152_, v___x_2148_);
v___y_2105_ = v___x_2153_;
goto v___jp_2104_;
}
}
else
{
size_t v___x_2154_; size_t v___x_2155_; lean_object* v___x_2156_; 
v___x_2154_ = ((size_t)0ULL);
v___x_2155_ = lean_usize_of_nat(v___x_2147_);
v___x_2156_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2097_, v_snd_2096_, v___x_2154_, v___x_2155_, v___x_2148_);
v___y_2105_ = v___x_2156_;
goto v___jp_2104_;
}
}
v___jp_2104_:
{
lean_object* v___x_2106_; lean_object* v___x_2107_; lean_object* v___x_2108_; 
v___x_2106_ = l_Lean_instInhabitedExpr;
v___x_2107_ = lean_array_get_borrowed(v___x_2106_, v_fst_2094_, v_next_2097_);
lean_dec(v_next_2097_);
lean_inc(v___y_2101_);
lean_inc_ref(v___y_2100_);
lean_inc(v___y_2099_);
lean_inc_ref(v___y_2098_);
lean_inc(v___x_2107_);
v___x_2108_ = lean_infer_type(v___x_2107_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2108_) == 0)
{
lean_object* v_a_2109_; lean_object* v___x_2110_; 
v_a_2109_ = lean_ctor_get(v___x_2108_, 0);
lean_inc(v_a_2109_);
lean_dec_ref_known(v___x_2108_, 1);
v___x_2110_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2094_, v_argVars_2095_, v_a_2109_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v___x_2111_; 
lean_dec_ref_known(v___x_2110_, 1);
lean_inc(v___x_2107_);
v___x_2111_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2094_, v_argVars_2095_, v___x_2107_, v___y_2098_, v___y_2099_, v___y_2100_, v___y_2101_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v___x_2113_; uint8_t v_isShared_2114_; uint8_t v_isSharedCheck_2120_; 
v_isSharedCheck_2120_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2120_ == 0)
{
lean_object* v_unused_2121_; 
v_unused_2121_ = lean_ctor_get(v___x_2111_, 0);
lean_dec(v_unused_2121_);
v___x_2113_ = v___x_2111_;
v_isShared_2114_ = v_isSharedCheck_2120_;
goto v_resetjp_2112_;
}
else
{
lean_dec(v___x_2111_);
v___x_2113_ = lean_box(0);
v_isShared_2114_ = v_isSharedCheck_2120_;
goto v_resetjp_2112_;
}
v_resetjp_2112_:
{
lean_object* v___x_2115_; lean_object* v___x_2116_; lean_object* v___x_2118_; 
v___x_2115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2103_);
lean_ctor_set(v___x_2115_, 1, v___y_2105_);
v___x_2116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2115_);
if (v_isShared_2114_ == 0)
{
lean_ctor_set(v___x_2113_, 0, v___x_2116_);
v___x_2118_ = v___x_2113_;
goto v_reusejp_2117_;
}
else
{
lean_object* v_reuseFailAlloc_2119_; 
v_reuseFailAlloc_2119_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2119_, 0, v___x_2116_);
v___x_2118_ = v_reuseFailAlloc_2119_;
goto v_reusejp_2117_;
}
v_reusejp_2117_:
{
return v___x_2118_;
}
}
}
else
{
lean_object* v_a_2122_; lean_object* v___x_2124_; uint8_t v_isShared_2125_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v___y_2105_);
lean_dec_ref(v___x_2103_);
v_a_2122_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2124_ = v___x_2111_;
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
else
{
lean_inc(v_a_2122_);
lean_dec(v___x_2111_);
v___x_2124_ = lean_box(0);
v_isShared_2125_ = v_isSharedCheck_2129_;
goto v_resetjp_2123_;
}
v_resetjp_2123_:
{
lean_object* v___x_2127_; 
if (v_isShared_2125_ == 0)
{
v___x_2127_ = v___x_2124_;
goto v_reusejp_2126_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_a_2122_);
v___x_2127_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2126_;
}
v_reusejp_2126_:
{
return v___x_2127_;
}
}
}
}
else
{
lean_object* v_a_2130_; lean_object* v___x_2132_; uint8_t v_isShared_2133_; uint8_t v_isSharedCheck_2137_; 
lean_dec_ref(v___y_2105_);
lean_dec_ref(v___x_2103_);
v_a_2130_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2137_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2137_ == 0)
{
v___x_2132_ = v___x_2110_;
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
else
{
lean_inc(v_a_2130_);
lean_dec(v___x_2110_);
v___x_2132_ = lean_box(0);
v_isShared_2133_ = v_isSharedCheck_2137_;
goto v_resetjp_2131_;
}
v_resetjp_2131_:
{
lean_object* v___x_2135_; 
if (v_isShared_2133_ == 0)
{
v___x_2135_ = v___x_2132_;
goto v_reusejp_2134_;
}
else
{
lean_object* v_reuseFailAlloc_2136_; 
v_reuseFailAlloc_2136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2136_, 0, v_a_2130_);
v___x_2135_ = v_reuseFailAlloc_2136_;
goto v_reusejp_2134_;
}
v_reusejp_2134_:
{
return v___x_2135_;
}
}
}
}
else
{
lean_object* v_a_2138_; lean_object* v___x_2140_; uint8_t v_isShared_2141_; uint8_t v_isSharedCheck_2145_; 
lean_dec_ref(v___y_2105_);
lean_dec_ref(v___x_2103_);
v_a_2138_ = lean_ctor_get(v___x_2108_, 0);
v_isSharedCheck_2145_ = !lean_is_exclusive(v___x_2108_);
if (v_isSharedCheck_2145_ == 0)
{
v___x_2140_ = v___x_2108_;
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
else
{
lean_inc(v_a_2138_);
lean_dec(v___x_2108_);
v___x_2140_ = lean_box(0);
v_isShared_2141_ = v_isSharedCheck_2145_;
goto v_resetjp_2139_;
}
v_resetjp_2139_:
{
lean_object* v___x_2143_; 
if (v_isShared_2141_ == 0)
{
v___x_2143_ = v___x_2140_;
goto v_reusejp_2142_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_a_2138_);
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
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object* v_fst_2157_, lean_object* v_fst_2158_, lean_object* v_argVars_2159_, lean_object* v_snd_2160_, lean_object* v_next_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_){
_start:
{
lean_object* v_res_2167_; 
v_res_2167_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2157_, v_fst_2158_, v_argVars_2159_, v_snd_2160_, v_next_2161_, v___y_2162_, v___y_2163_, v___y_2164_, v___y_2165_);
lean_dec(v___y_2165_);
lean_dec_ref(v___y_2164_);
lean_dec(v___y_2163_);
lean_dec_ref(v___y_2162_);
lean_dec(v_snd_2160_);
lean_dec_ref(v_argVars_2159_);
lean_dec_ref(v_fst_2158_);
return v_res_2167_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2168_, lean_object* v___x_2169_, lean_object* v_a_2170_, lean_object* v_a_2171_, lean_object* v_b_2172_){
_start:
{
uint8_t v___x_2174_; 
v___x_2174_ = lean_nat_dec_lt(v_a_2171_, v_upperBound_2168_);
if (v___x_2174_ == 0)
{
lean_object* v___x_2175_; 
lean_dec(v_a_2171_);
v___x_2175_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2175_, 0, v_b_2172_);
return v___x_2175_;
}
else
{
lean_object* v_snd_2176_; lean_object* v___x_2178_; uint8_t v_isShared_2179_; uint8_t v_isSharedCheck_2217_; 
v_snd_2176_ = lean_ctor_get(v_b_2172_, 1);
v_isSharedCheck_2217_ = !lean_is_exclusive(v_b_2172_);
if (v_isSharedCheck_2217_ == 0)
{
lean_object* v_unused_2218_; 
v_unused_2218_ = lean_ctor_get(v_b_2172_, 0);
lean_dec(v_unused_2218_);
v___x_2178_ = v_b_2172_;
v_isShared_2179_ = v_isSharedCheck_2217_;
goto v_resetjp_2177_;
}
else
{
lean_inc(v_snd_2176_);
lean_dec(v_b_2172_);
v___x_2178_ = lean_box(0);
v_isShared_2179_ = v_isSharedCheck_2217_;
goto v_resetjp_2177_;
}
v_resetjp_2177_:
{
lean_object* v_array_2180_; lean_object* v_start_2181_; lean_object* v_stop_2182_; lean_object* v___x_2183_; uint8_t v___x_2184_; 
v_array_2180_ = lean_ctor_get(v_snd_2176_, 0);
v_start_2181_ = lean_ctor_get(v_snd_2176_, 1);
v_stop_2182_ = lean_ctor_get(v_snd_2176_, 2);
v___x_2183_ = lean_box(0);
v___x_2184_ = lean_nat_dec_lt(v_start_2181_, v_stop_2182_);
if (v___x_2184_ == 0)
{
lean_object* v___x_2186_; 
lean_dec(v_a_2171_);
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 0, v___x_2183_);
v___x_2186_ = v___x_2178_;
goto v_reusejp_2185_;
}
else
{
lean_object* v_reuseFailAlloc_2188_; 
v_reuseFailAlloc_2188_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2188_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2188_, 1, v_snd_2176_);
v___x_2186_ = v_reuseFailAlloc_2188_;
goto v_reusejp_2185_;
}
v_reusejp_2185_:
{
lean_object* v___x_2187_; 
v___x_2187_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2187_, 0, v___x_2186_);
return v___x_2187_;
}
}
else
{
lean_object* v___x_2190_; uint8_t v_isShared_2191_; uint8_t v_isSharedCheck_2213_; 
lean_inc(v_stop_2182_);
lean_inc(v_start_2181_);
lean_inc_ref(v_array_2180_);
v_isSharedCheck_2213_ = !lean_is_exclusive(v_snd_2176_);
if (v_isSharedCheck_2213_ == 0)
{
lean_object* v_unused_2214_; lean_object* v_unused_2215_; lean_object* v_unused_2216_; 
v_unused_2214_ = lean_ctor_get(v_snd_2176_, 2);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_snd_2176_, 1);
lean_dec(v_unused_2215_);
v_unused_2216_ = lean_ctor_get(v_snd_2176_, 0);
lean_dec(v_unused_2216_);
v___x_2190_ = v_snd_2176_;
v_isShared_2191_ = v_isSharedCheck_2213_;
goto v_resetjp_2189_;
}
else
{
lean_dec(v_snd_2176_);
v___x_2190_ = lean_box(0);
v_isShared_2191_ = v_isSharedCheck_2213_;
goto v_resetjp_2189_;
}
v_resetjp_2189_:
{
lean_object* v___x_2192_; uint8_t v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2198_; 
v___x_2192_ = lean_unsigned_to_nat(0u);
v___x_2193_ = lean_nat_dec_eq(v___x_2169_, v___x_2192_);
v___x_2194_ = lean_array_fget(v_array_2180_, v_start_2181_);
v___x_2195_ = lean_unsigned_to_nat(1u);
v___x_2196_ = lean_nat_add(v_start_2181_, v___x_2195_);
lean_dec(v_start_2181_);
if (v_isShared_2191_ == 0)
{
lean_ctor_set(v___x_2190_, 1, v___x_2196_);
v___x_2198_ = v___x_2190_;
goto v_reusejp_2197_;
}
else
{
lean_object* v_reuseFailAlloc_2212_; 
v_reuseFailAlloc_2212_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2212_, 0, v_array_2180_);
lean_ctor_set(v_reuseFailAlloc_2212_, 1, v___x_2196_);
lean_ctor_set(v_reuseFailAlloc_2212_, 2, v_stop_2182_);
v___x_2198_ = v_reuseFailAlloc_2212_;
goto v_reusejp_2197_;
}
v_reusejp_2197_:
{
uint8_t v___x_2211_; 
v___x_2211_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2170_, v_a_2171_);
if (v___x_2211_ == 0)
{
goto v___jp_2205_;
}
else
{
if (v___x_2193_ == 0)
{
lean_dec(v___x_2194_);
goto v___jp_2199_;
}
else
{
goto v___jp_2205_;
}
}
v___jp_2199_:
{
lean_object* v___x_2201_; 
if (v_isShared_2179_ == 0)
{
lean_ctor_set(v___x_2178_, 1, v___x_2198_);
lean_ctor_set(v___x_2178_, 0, v___x_2183_);
v___x_2201_ = v___x_2178_;
goto v_reusejp_2200_;
}
else
{
lean_object* v_reuseFailAlloc_2204_; 
v_reuseFailAlloc_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2204_, 0, v___x_2183_);
lean_ctor_set(v_reuseFailAlloc_2204_, 1, v___x_2198_);
v___x_2201_ = v_reuseFailAlloc_2204_;
goto v_reusejp_2200_;
}
v_reusejp_2200_:
{
lean_object* v___x_2202_; 
v___x_2202_ = lean_nat_add(v_a_2171_, v___x_2195_);
lean_dec(v_a_2171_);
v_a_2171_ = v___x_2202_;
v_b_2172_ = v___x_2201_;
goto _start;
}
}
v___jp_2205_:
{
uint8_t v___x_2206_; 
v___x_2206_ = l_Lean_Expr_hasExprMVar(v___x_2194_);
lean_dec(v___x_2194_);
if (v___x_2206_ == 0)
{
goto v___jp_2199_;
}
else
{
lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; 
lean_del_object(v___x_2178_);
lean_dec(v_a_2171_);
v___x_2207_ = lean_box(v___x_2193_);
v___x_2208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
v___x_2209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
lean_ctor_set(v___x_2209_, 1, v___x_2198_);
v___x_2210_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
return v___x_2210_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2219_, lean_object* v___x_2220_, lean_object* v_a_2221_, lean_object* v_a_2222_, lean_object* v_b_2223_, lean_object* v___y_2224_){
_start:
{
lean_object* v_res_2225_; 
v_res_2225_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2219_, v___x_2220_, v_a_2221_, v_a_2222_, v_b_2223_);
lean_dec_ref(v_a_2221_);
lean_dec(v___x_2220_);
lean_dec(v_upperBound_2219_);
return v_res_2225_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2226_; lean_object* v_dummy_2227_; 
v___x_2226_ = lean_box(0);
v_dummy_2227_ = l_Lean_Expr_sort___override(v___x_2226_);
return v_dummy_2227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2228_, lean_object* v___x_2229_, uint8_t v___x_2230_, lean_object* v_x_2231_, lean_object* v_argTy_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_){
_start:
{
lean_object* v___x_2238_; 
lean_inc(v___y_2236_);
lean_inc_ref(v___y_2235_);
lean_inc(v___y_2234_);
lean_inc_ref(v___y_2233_);
v___x_2238_ = lean_whnf(v_argTy_2232_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
if (lean_obj_tag(v___x_2238_) == 0)
{
lean_object* v_a_2239_; lean_object* v___x_2240_; 
v_a_2239_ = lean_ctor_get(v___x_2238_, 0);
lean_inc(v_a_2239_);
lean_dec_ref_known(v___x_2238_, 1);
v___x_2240_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2239_, v___y_2233_, v___y_2234_, v___y_2235_, v___y_2236_);
if (lean_obj_tag(v___x_2240_) == 0)
{
lean_object* v_a_2241_; lean_object* v_dummy_2242_; lean_object* v_nargs_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; 
v_a_2241_ = lean_ctor_get(v___x_2240_, 0);
lean_inc(v_a_2241_);
lean_dec_ref_known(v___x_2240_, 1);
v_dummy_2242_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2243_ = l_Lean_Expr_getAppNumArgs(v_a_2239_);
lean_inc(v_nargs_2243_);
v___x_2244_ = lean_mk_array(v_nargs_2243_, v_dummy_2242_);
v___x_2245_ = lean_unsigned_to_nat(1u);
v___x_2246_ = lean_nat_sub(v_nargs_2243_, v___x_2245_);
lean_dec(v_nargs_2243_);
v___x_2247_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2239_, v___x_2244_, v___x_2246_);
v___x_2248_ = lean_array_get_size(v___x_2247_);
lean_inc(v___x_2228_);
v___x_2249_ = l_Array_toSubarray___redArg(v___x_2247_, v___x_2228_, v___x_2248_);
v___x_2250_ = lean_box(0);
v___x_2251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2251_, 0, v___x_2250_);
lean_ctor_set(v___x_2251_, 1, v___x_2249_);
v___x_2252_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2248_, v___x_2229_, v_a_2241_, v___x_2228_, v___x_2251_);
lean_dec(v_a_2241_);
if (lean_obj_tag(v___x_2252_) == 0)
{
lean_object* v_a_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2266_; 
v_a_2253_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2255_ = v___x_2252_;
v_isShared_2256_ = v_isSharedCheck_2266_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_a_2253_);
lean_dec(v___x_2252_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2266_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v_fst_2257_; 
v_fst_2257_ = lean_ctor_get(v_a_2253_, 0);
lean_inc(v_fst_2257_);
lean_dec(v_a_2253_);
if (lean_obj_tag(v_fst_2257_) == 0)
{
lean_object* v___x_2258_; lean_object* v___x_2260_; 
v___x_2258_ = lean_box(v___x_2230_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v___x_2258_);
v___x_2260_ = v___x_2255_;
goto v_reusejp_2259_;
}
else
{
lean_object* v_reuseFailAlloc_2261_; 
v_reuseFailAlloc_2261_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2261_, 0, v___x_2258_);
v___x_2260_ = v_reuseFailAlloc_2261_;
goto v_reusejp_2259_;
}
v_reusejp_2259_:
{
return v___x_2260_;
}
}
else
{
lean_object* v_val_2262_; lean_object* v___x_2264_; 
v_val_2262_ = lean_ctor_get(v_fst_2257_, 0);
lean_inc(v_val_2262_);
lean_dec_ref_known(v_fst_2257_, 1);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 0, v_val_2262_);
v___x_2264_ = v___x_2255_;
goto v_reusejp_2263_;
}
else
{
lean_object* v_reuseFailAlloc_2265_; 
v_reuseFailAlloc_2265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2265_, 0, v_val_2262_);
v___x_2264_ = v_reuseFailAlloc_2265_;
goto v_reusejp_2263_;
}
v_reusejp_2263_:
{
return v___x_2264_;
}
}
}
}
else
{
lean_object* v_a_2267_; lean_object* v___x_2269_; uint8_t v_isShared_2270_; uint8_t v_isSharedCheck_2274_; 
v_a_2267_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2274_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2274_ == 0)
{
v___x_2269_ = v___x_2252_;
v_isShared_2270_ = v_isSharedCheck_2274_;
goto v_resetjp_2268_;
}
else
{
lean_inc(v_a_2267_);
lean_dec(v___x_2252_);
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
else
{
lean_object* v_a_2275_; lean_object* v___x_2277_; uint8_t v_isShared_2278_; uint8_t v_isSharedCheck_2282_; 
lean_dec(v_a_2239_);
lean_dec(v___x_2228_);
v_a_2275_ = lean_ctor_get(v___x_2240_, 0);
v_isSharedCheck_2282_ = !lean_is_exclusive(v___x_2240_);
if (v_isSharedCheck_2282_ == 0)
{
v___x_2277_ = v___x_2240_;
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
else
{
lean_inc(v_a_2275_);
lean_dec(v___x_2240_);
v___x_2277_ = lean_box(0);
v_isShared_2278_ = v_isSharedCheck_2282_;
goto v_resetjp_2276_;
}
v_resetjp_2276_:
{
lean_object* v___x_2280_; 
if (v_isShared_2278_ == 0)
{
v___x_2280_ = v___x_2277_;
goto v_reusejp_2279_;
}
else
{
lean_object* v_reuseFailAlloc_2281_; 
v_reuseFailAlloc_2281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2281_, 0, v_a_2275_);
v___x_2280_ = v_reuseFailAlloc_2281_;
goto v_reusejp_2279_;
}
v_reusejp_2279_:
{
return v___x_2280_;
}
}
}
}
else
{
lean_object* v_a_2283_; lean_object* v___x_2285_; uint8_t v_isShared_2286_; uint8_t v_isSharedCheck_2290_; 
lean_dec(v___x_2228_);
v_a_2283_ = lean_ctor_get(v___x_2238_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2238_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2285_ = v___x_2238_;
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
else
{
lean_inc(v_a_2283_);
lean_dec(v___x_2238_);
v___x_2285_ = lean_box(0);
v_isShared_2286_ = v_isSharedCheck_2290_;
goto v_resetjp_2284_;
}
v_resetjp_2284_:
{
lean_object* v___x_2288_; 
if (v_isShared_2286_ == 0)
{
v___x_2288_ = v___x_2285_;
goto v_reusejp_2287_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_a_2283_);
v___x_2288_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2287_;
}
v_reusejp_2287_:
{
return v___x_2288_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2291_, lean_object* v___x_2292_, lean_object* v___x_2293_, lean_object* v_x_2294_, lean_object* v_argTy_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_){
_start:
{
uint8_t v___x_26128__boxed_2301_; lean_object* v_res_2302_; 
v___x_26128__boxed_2301_ = lean_unbox(v___x_2293_);
v_res_2302_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2291_, v___x_2292_, v___x_26128__boxed_2301_, v_x_2294_, v_argTy_2295_, v___y_2296_, v___y_2297_, v___y_2298_, v___y_2299_);
lean_dec(v___y_2299_);
lean_dec_ref(v___y_2298_);
lean_dec(v___y_2297_);
lean_dec_ref(v___y_2296_);
lean_dec_ref(v_x_2294_);
lean_dec(v___x_2292_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2306_, lean_object* v_projInfo_x3f_2307_, lean_object* v___x_2308_, lean_object* v_argVars_2309_, lean_object* v_as_2310_, size_t v_sz_2311_, size_t v_i_2312_, lean_object* v_b_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_){
_start:
{
uint8_t v___x_2319_; 
v___x_2319_ = lean_usize_dec_lt(v_i_2312_, v_sz_2311_);
if (v___x_2319_ == 0)
{
lean_object* v___x_2320_; 
lean_dec(v___x_2308_);
v___x_2320_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2320_, 0, v_b_2313_);
return v___x_2320_;
}
else
{
lean_object* v_a_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
lean_dec_ref(v_b_2313_);
v_a_2321_ = lean_array_uget_borrowed(v_as_2310_, v_i_2312_);
v___x_2322_ = l_Lean_instInhabitedExpr;
v___x_2323_ = lean_array_get_borrowed(v___x_2322_, v_fst_2306_, v_a_2321_);
lean_inc(v___y_2317_);
lean_inc_ref(v___y_2316_);
lean_inc(v___y_2315_);
lean_inc_ref(v___y_2314_);
lean_inc(v___x_2323_);
v___x_2324_ = lean_infer_type(v___x_2323_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2324_) == 0)
{
lean_object* v_a_2325_; lean_object* v___x_2326_; 
v_a_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_a_2325_);
lean_dec_ref_known(v___x_2324_, 1);
v___x_2326_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2325_, v___y_2315_);
if (lean_obj_tag(v___x_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2329_; uint8_t v_isShared_2330_; uint8_t v_isSharedCheck_2373_; 
v_a_2327_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2373_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2373_ == 0)
{
v___x_2329_ = v___x_2326_;
v_isShared_2330_ = v_isSharedCheck_2373_;
goto v_resetjp_2328_;
}
else
{
lean_inc(v_a_2327_);
lean_dec(v___x_2326_);
v___x_2329_ = lean_box(0);
v_isShared_2330_ = v_isSharedCheck_2373_;
goto v_resetjp_2328_;
}
v_resetjp_2328_:
{
lean_object* v___x_2331_; lean_object* v___x_2339_; lean_object* v___y_2341_; lean_object* v___x_2355_; lean_object* v___x_2356_; lean_object* v___f_2357_; uint8_t v___x_2358_; 
v___x_2331_ = lean_box(0);
v___x_2339_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2355_ = lean_unsigned_to_nat(0u);
v___x_2356_ = lean_box(v___x_2319_);
lean_inc(v___x_2308_);
v___f_2357_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2357_, 0, v___x_2355_);
lean_closure_set(v___f_2357_, 1, v___x_2308_);
lean_closure_set(v___f_2357_, 2, v___x_2356_);
v___x_2358_ = lean_nat_dec_eq(v___x_2308_, v___x_2355_);
if (lean_obj_tag(v_projInfo_x3f_2307_) == 1)
{
lean_object* v_val_2359_; lean_object* v_numParams_2360_; uint8_t v___x_2361_; 
v_val_2359_ = lean_ctor_get(v_projInfo_x3f_2307_, 0);
v_numParams_2360_ = lean_ctor_get(v_val_2359_, 1);
v___x_2361_ = lean_nat_dec_eq(v_numParams_2360_, v_a_2321_);
if (v___x_2361_ == 0)
{
lean_object* v___x_2362_; 
v___x_2362_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2327_, v___f_2357_, v___x_2358_, v___x_2358_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
v___y_2341_ = v___x_2362_;
goto v___jp_2340_;
}
else
{
lean_object* v___x_2363_; 
lean_dec_ref(v___f_2357_);
lean_dec(v___x_2308_);
v___x_2363_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2306_, v_argVars_2309_, v_a_2327_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
if (lean_obj_tag(v___x_2363_) == 0)
{
lean_dec_ref_known(v___x_2363_, 1);
goto v___jp_2332_;
}
else
{
lean_object* v_a_2364_; lean_object* v___x_2366_; uint8_t v_isShared_2367_; uint8_t v_isSharedCheck_2371_; 
lean_del_object(v___x_2329_);
v_a_2364_ = lean_ctor_get(v___x_2363_, 0);
v_isSharedCheck_2371_ = !lean_is_exclusive(v___x_2363_);
if (v_isSharedCheck_2371_ == 0)
{
v___x_2366_ = v___x_2363_;
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
else
{
lean_inc(v_a_2364_);
lean_dec(v___x_2363_);
v___x_2366_ = lean_box(0);
v_isShared_2367_ = v_isSharedCheck_2371_;
goto v_resetjp_2365_;
}
v_resetjp_2365_:
{
lean_object* v___x_2369_; 
if (v_isShared_2367_ == 0)
{
v___x_2369_ = v___x_2366_;
goto v_reusejp_2368_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_a_2364_);
v___x_2369_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2368_;
}
v_reusejp_2368_:
{
return v___x_2369_;
}
}
}
}
}
else
{
lean_object* v___x_2372_; 
v___x_2372_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2327_, v___f_2357_, v___x_2358_, v___x_2358_, v___y_2314_, v___y_2315_, v___y_2316_, v___y_2317_);
v___y_2341_ = v___x_2372_;
goto v___jp_2340_;
}
v___jp_2332_:
{
lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2337_; 
lean_inc(v_a_2321_);
v___x_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2333_, 0, v_a_2321_);
v___x_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
v___x_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
lean_ctor_set(v___x_2335_, 1, v___x_2331_);
if (v_isShared_2330_ == 0)
{
lean_ctor_set(v___x_2329_, 0, v___x_2335_);
v___x_2337_ = v___x_2329_;
goto v_reusejp_2336_;
}
else
{
lean_object* v_reuseFailAlloc_2338_; 
v_reuseFailAlloc_2338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2338_, 0, v___x_2335_);
v___x_2337_ = v_reuseFailAlloc_2338_;
goto v_reusejp_2336_;
}
v_reusejp_2336_:
{
return v___x_2337_;
}
}
v___jp_2340_:
{
if (lean_obj_tag(v___y_2341_) == 0)
{
lean_object* v_a_2342_; uint8_t v___x_2343_; 
v_a_2342_ = lean_ctor_get(v___y_2341_, 0);
lean_inc(v_a_2342_);
lean_dec_ref_known(v___y_2341_, 1);
v___x_2343_ = lean_unbox(v_a_2342_);
lean_dec(v_a_2342_);
if (v___x_2343_ == 0)
{
size_t v___x_2344_; size_t v___x_2345_; 
lean_del_object(v___x_2329_);
v___x_2344_ = ((size_t)1ULL);
v___x_2345_ = lean_usize_add(v_i_2312_, v___x_2344_);
v_i_2312_ = v___x_2345_;
v_b_2313_ = v___x_2339_;
goto _start;
}
else
{
lean_dec(v___x_2308_);
goto v___jp_2332_;
}
}
else
{
lean_object* v_a_2347_; lean_object* v___x_2349_; uint8_t v_isShared_2350_; uint8_t v_isSharedCheck_2354_; 
lean_del_object(v___x_2329_);
lean_dec(v___x_2308_);
v_a_2347_ = lean_ctor_get(v___y_2341_, 0);
v_isSharedCheck_2354_ = !lean_is_exclusive(v___y_2341_);
if (v_isSharedCheck_2354_ == 0)
{
v___x_2349_ = v___y_2341_;
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
else
{
lean_inc(v_a_2347_);
lean_dec(v___y_2341_);
v___x_2349_ = lean_box(0);
v_isShared_2350_ = v_isSharedCheck_2354_;
goto v_resetjp_2348_;
}
v_resetjp_2348_:
{
lean_object* v___x_2352_; 
if (v_isShared_2350_ == 0)
{
v___x_2352_ = v___x_2349_;
goto v_reusejp_2351_;
}
else
{
lean_object* v_reuseFailAlloc_2353_; 
v_reuseFailAlloc_2353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2353_, 0, v_a_2347_);
v___x_2352_ = v_reuseFailAlloc_2353_;
goto v_reusejp_2351_;
}
v_reusejp_2351_:
{
return v___x_2352_;
}
}
}
}
}
}
else
{
lean_object* v_a_2374_; lean_object* v___x_2376_; uint8_t v_isShared_2377_; uint8_t v_isSharedCheck_2381_; 
lean_dec(v___x_2308_);
v_a_2374_ = lean_ctor_get(v___x_2326_, 0);
v_isSharedCheck_2381_ = !lean_is_exclusive(v___x_2326_);
if (v_isSharedCheck_2381_ == 0)
{
v___x_2376_ = v___x_2326_;
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
else
{
lean_inc(v_a_2374_);
lean_dec(v___x_2326_);
v___x_2376_ = lean_box(0);
v_isShared_2377_ = v_isSharedCheck_2381_;
goto v_resetjp_2375_;
}
v_resetjp_2375_:
{
lean_object* v___x_2379_; 
if (v_isShared_2377_ == 0)
{
v___x_2379_ = v___x_2376_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_a_2374_);
v___x_2379_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
return v___x_2379_;
}
}
}
}
else
{
lean_object* v_a_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2389_; 
lean_dec(v___x_2308_);
v_a_2382_ = lean_ctor_get(v___x_2324_, 0);
v_isSharedCheck_2389_ = !lean_is_exclusive(v___x_2324_);
if (v_isSharedCheck_2389_ == 0)
{
v___x_2384_ = v___x_2324_;
v_isShared_2385_ = v_isSharedCheck_2389_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_a_2382_);
lean_dec(v___x_2324_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2390_, lean_object* v_projInfo_x3f_2391_, lean_object* v___x_2392_, lean_object* v_argVars_2393_, lean_object* v_as_2394_, lean_object* v_sz_2395_, lean_object* v_i_2396_, lean_object* v_b_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_){
_start:
{
size_t v_sz_boxed_2403_; size_t v_i_boxed_2404_; lean_object* v_res_2405_; 
v_sz_boxed_2403_ = lean_unbox_usize(v_sz_2395_);
lean_dec(v_sz_2395_);
v_i_boxed_2404_ = lean_unbox_usize(v_i_2396_);
lean_dec(v_i_2396_);
v_res_2405_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2390_, v_projInfo_x3f_2391_, v___x_2392_, v_argVars_2393_, v_as_2394_, v_sz_boxed_2403_, v_i_boxed_2404_, v_b_2397_, v___y_2398_, v___y_2399_, v___y_2400_, v___y_2401_);
lean_dec(v___y_2401_);
lean_dec_ref(v___y_2400_);
lean_dec(v___y_2399_);
lean_dec_ref(v___y_2398_);
lean_dec_ref(v_as_2394_);
lean_dec_ref(v_argVars_2393_);
lean_dec(v_projInfo_x3f_2391_);
lean_dec_ref(v_fst_2390_);
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
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object* v_k_3235_, lean_object* v_t_3236_){
_start:
{
if (lean_obj_tag(v_t_3236_) == 0)
{
lean_object* v_k_3237_; lean_object* v_l_3238_; lean_object* v_r_3239_; uint8_t v___x_3240_; 
v_k_3237_ = lean_ctor_get(v_t_3236_, 1);
v_l_3238_ = lean_ctor_get(v_t_3236_, 3);
v_r_3239_ = lean_ctor_get(v_t_3236_, 4);
v___x_3240_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3235_, v_k_3237_);
switch(v___x_3240_)
{
case 0:
{
v_t_3236_ = v_l_3238_;
goto _start;
}
case 1:
{
uint8_t v___x_3242_; 
v___x_3242_ = 1;
return v___x_3242_;
}
default: 
{
v_t_3236_ = v_r_3239_;
goto _start;
}
}
}
else
{
uint8_t v___x_3244_; 
v___x_3244_ = 0;
return v___x_3244_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object* v_k_3245_, lean_object* v_t_3246_){
_start:
{
uint8_t v_res_3247_; lean_object* v_r_3248_; 
v_res_3247_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3245_, v_t_3246_);
lean_dec(v_t_3246_);
lean_dec(v_k_3245_);
v_r_3248_ = lean_box(v_res_3247_);
return v_r_3248_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3250_; lean_object* v___x_3251_; 
v___x_3250_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__0));
v___x_3251_ = l_Lean_stringToMessageData(v___x_3250_);
return v___x_3251_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; 
v___x_3253_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__2));
v___x_3254_ = l_Lean_stringToMessageData(v___x_3253_);
return v___x_3254_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(lean_object* v_a_3255_, lean_object* v_as_3256_, size_t v_sz_3257_, size_t v_i_3258_, lean_object* v_b_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_){
_start:
{
lean_object* v_a_3265_; uint8_t v___x_3269_; 
v___x_3269_ = lean_usize_dec_lt(v_i_3258_, v_sz_3257_);
if (v___x_3269_ == 0)
{
lean_object* v___x_3270_; 
v___x_3270_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3270_, 0, v_b_3259_);
return v___x_3270_;
}
else
{
lean_object* v_snd_3271_; 
v_snd_3271_ = lean_ctor_get(v_b_3259_, 1);
lean_inc(v_snd_3271_);
if (lean_obj_tag(v_snd_3271_) == 0)
{
lean_object* v_fst_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3280_; 
v_fst_3272_ = lean_ctor_get(v_b_3259_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v_b_3259_);
if (v_isSharedCheck_3280_ == 0)
{
lean_object* v_unused_3281_; 
v_unused_3281_ = lean_ctor_get(v_b_3259_, 1);
lean_dec(v_unused_3281_);
v___x_3274_ = v_b_3259_;
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_fst_3272_);
lean_dec(v_b_3259_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3277_; 
if (v_isShared_3275_ == 0)
{
v___x_3277_ = v___x_3274_;
goto v_reusejp_3276_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v_fst_3272_);
lean_ctor_set(v_reuseFailAlloc_3279_, 1, v_snd_3271_);
v___x_3277_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3276_;
}
v_reusejp_3276_:
{
lean_object* v___x_3278_; 
v___x_3278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3278_, 0, v___x_3277_);
return v___x_3278_;
}
}
}
else
{
lean_object* v_fst_3282_; lean_object* v___x_3284_; uint8_t v_isShared_3285_; uint8_t v_isSharedCheck_3339_; 
v_fst_3282_ = lean_ctor_get(v_b_3259_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_b_3259_);
if (v_isSharedCheck_3339_ == 0)
{
lean_object* v_unused_3340_; 
v_unused_3340_ = lean_ctor_get(v_b_3259_, 1);
lean_dec(v_unused_3340_);
v___x_3284_ = v_b_3259_;
v_isShared_3285_ = v_isSharedCheck_3339_;
goto v_resetjp_3283_;
}
else
{
lean_inc(v_fst_3282_);
lean_dec(v_b_3259_);
v___x_3284_ = lean_box(0);
v_isShared_3285_ = v_isSharedCheck_3339_;
goto v_resetjp_3283_;
}
v_resetjp_3283_:
{
lean_object* v_val_3286_; lean_object* v___x_3288_; uint8_t v_isShared_3289_; uint8_t v_isSharedCheck_3338_; 
v_val_3286_ = lean_ctor_get(v_snd_3271_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v_snd_3271_);
if (v_isSharedCheck_3338_ == 0)
{
v___x_3288_ = v_snd_3271_;
v_isShared_3289_ = v_isSharedCheck_3338_;
goto v_resetjp_3287_;
}
else
{
lean_inc(v_val_3286_);
lean_dec(v_snd_3271_);
v___x_3288_ = lean_box(0);
v_isShared_3289_ = v_isSharedCheck_3338_;
goto v_resetjp_3287_;
}
v_resetjp_3287_:
{
lean_object* v_fvarSet_3290_; lean_object* v_a_3291_; lean_object* v___x_3292_; lean_object* v___x_3293_; lean_object* v___x_3295_; 
v_fvarSet_3290_ = lean_ctor_get(v_a_3255_, 1);
v_a_3291_ = lean_array_uget_borrowed(v_as_3256_, v_i_3258_);
v___x_3292_ = lean_unsigned_to_nat(1u);
v___x_3293_ = lean_nat_add(v_val_3286_, v___x_3292_);
if (v_isShared_3289_ == 0)
{
lean_ctor_set(v___x_3288_, 0, v___x_3293_);
v___x_3295_ = v___x_3288_;
goto v_reusejp_3294_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v___x_3293_);
v___x_3295_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3294_;
}
v_reusejp_3294_:
{
lean_object* v___x_3296_; uint8_t v___x_3297_; 
v___x_3296_ = l_Lean_Expr_fvarId_x21(v_a_3291_);
v___x_3297_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v___x_3296_, v_fvarSet_3290_);
if (v___x_3297_ == 0)
{
lean_object* v___x_3298_; 
v___x_3298_ = l_Lean_FVarId_getDecl___redArg(v___x_3296_, v___y_3260_, v___y_3261_, v___y_3262_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v_a_3299_; lean_object* v___x_3300_; 
v_a_3299_ = lean_ctor_get(v___x_3298_, 0);
lean_inc(v_a_3299_);
lean_dec_ref_known(v___x_3298_, 1);
v___x_3300_ = l_Lean_LocalDecl_ppAsBinder(v_a_3299_);
if (lean_obj_tag(v___x_3300_) == 1)
{
lean_object* v_val_3301_; lean_object* v___x_3303_; uint8_t v_isShared_3304_; uint8_t v_isSharedCheck_3322_; 
v_val_3301_ = lean_ctor_get(v___x_3300_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3300_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3303_ = v___x_3300_;
v_isShared_3304_ = v_isSharedCheck_3322_;
goto v_resetjp_3302_;
}
else
{
lean_inc(v_val_3301_);
lean_dec(v___x_3300_);
v___x_3303_ = lean_box(0);
v_isShared_3304_ = v_isSharedCheck_3322_;
goto v_resetjp_3302_;
}
v_resetjp_3302_:
{
lean_object* v___x_3305_; lean_object* v___x_3306_; lean_object* v___x_3308_; 
v___x_3305_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1);
v___x_3306_ = l_Nat_reprFast(v_val_3286_);
if (v_isShared_3304_ == 0)
{
lean_ctor_set_tag(v___x_3303_, 3);
lean_ctor_set(v___x_3303_, 0, v___x_3306_);
v___x_3308_ = v___x_3303_;
goto v_reusejp_3307_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3306_);
v___x_3308_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3307_;
}
v_reusejp_3307_:
{
lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3319_; 
v___x_3309_ = l_Lean_MessageData_ofFormat(v___x_3308_);
v___x_3310_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3310_, 0, v___x_3305_);
lean_ctor_set(v___x_3310_, 1, v___x_3309_);
v___x_3311_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3310_);
lean_ctor_set(v___x_3312_, 1, v___x_3311_);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3312_);
lean_ctor_set(v___x_3313_, 1, v_val_3301_);
v___x_3314_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3315_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3315_, 0, v___x_3313_);
lean_ctor_set(v___x_3315_, 1, v___x_3314_);
v___x_3316_ = l_Lean_indentD(v___x_3315_);
v___x_3317_ = lean_array_push(v_fst_3282_, v___x_3316_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v___x_3295_);
lean_ctor_set(v___x_3284_, 0, v___x_3317_);
v___x_3319_ = v___x_3284_;
goto v_reusejp_3318_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3317_);
lean_ctor_set(v_reuseFailAlloc_3320_, 1, v___x_3295_);
v___x_3319_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3318_;
}
v_reusejp_3318_:
{
v_a_3265_ = v___x_3319_;
goto v___jp_3264_;
}
}
}
}
else
{
lean_object* v___x_3324_; 
lean_dec(v___x_3300_);
lean_dec(v_val_3286_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v___x_3295_);
v___x_3324_ = v___x_3284_;
goto v_reusejp_3323_;
}
else
{
lean_object* v_reuseFailAlloc_3325_; 
v_reuseFailAlloc_3325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3325_, 0, v_fst_3282_);
lean_ctor_set(v_reuseFailAlloc_3325_, 1, v___x_3295_);
v___x_3324_ = v_reuseFailAlloc_3325_;
goto v_reusejp_3323_;
}
v_reusejp_3323_:
{
v_a_3265_ = v___x_3324_;
goto v___jp_3264_;
}
}
}
else
{
lean_object* v_a_3326_; lean_object* v___x_3328_; uint8_t v_isShared_3329_; uint8_t v_isSharedCheck_3333_; 
lean_dec_ref(v___x_3295_);
lean_dec(v_val_3286_);
lean_del_object(v___x_3284_);
lean_dec(v_fst_3282_);
v_a_3326_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3333_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3333_ == 0)
{
v___x_3328_ = v___x_3298_;
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
else
{
lean_inc(v_a_3326_);
lean_dec(v___x_3298_);
v___x_3328_ = lean_box(0);
v_isShared_3329_ = v_isSharedCheck_3333_;
goto v_resetjp_3327_;
}
v_resetjp_3327_:
{
lean_object* v___x_3331_; 
if (v_isShared_3329_ == 0)
{
v___x_3331_ = v___x_3328_;
goto v_reusejp_3330_;
}
else
{
lean_object* v_reuseFailAlloc_3332_; 
v_reuseFailAlloc_3332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3332_, 0, v_a_3326_);
v___x_3331_ = v_reuseFailAlloc_3332_;
goto v_reusejp_3330_;
}
v_reusejp_3330_:
{
return v___x_3331_;
}
}
}
}
else
{
lean_object* v___x_3335_; 
lean_dec(v___x_3296_);
lean_dec(v_val_3286_);
if (v_isShared_3285_ == 0)
{
lean_ctor_set(v___x_3284_, 1, v___x_3295_);
v___x_3335_ = v___x_3284_;
goto v_reusejp_3334_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v_fst_3282_);
lean_ctor_set(v_reuseFailAlloc_3336_, 1, v___x_3295_);
v___x_3335_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3334_;
}
v_reusejp_3334_:
{
v_a_3265_ = v___x_3335_;
goto v___jp_3264_;
}
}
}
}
}
}
}
v___jp_3264_:
{
size_t v___x_3266_; size_t v___x_3267_; 
v___x_3266_ = ((size_t)1ULL);
v___x_3267_ = lean_usize_add(v_i_3258_, v___x_3266_);
v_i_3258_ = v___x_3267_;
v_b_3259_ = v_a_3265_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___boxed(lean_object* v_a_3341_, lean_object* v_as_3342_, lean_object* v_sz_3343_, lean_object* v_i_3344_, lean_object* v_b_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_){
_start:
{
size_t v_sz_boxed_3350_; size_t v_i_boxed_3351_; lean_object* v_res_3352_; 
v_sz_boxed_3350_ = lean_unbox_usize(v_sz_3343_);
lean_dec(v_sz_3343_);
v_i_boxed_3351_ = lean_unbox_usize(v_i_3344_);
lean_dec(v_i_3344_);
v_res_3352_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3341_, v_as_3342_, v_sz_boxed_3350_, v_i_boxed_3351_, v_b_3345_, v___y_3346_, v___y_3347_, v___y_3348_);
lean_dec(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec_ref(v_as_3342_);
lean_dec_ref(v_a_3341_);
return v_res_3352_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(uint8_t v___y_3360_, uint8_t v_suppressElabErrors_3361_, lean_object* v_x_3362_){
_start:
{
if (lean_obj_tag(v_x_3362_) == 1)
{
lean_object* v_pre_3363_; 
v_pre_3363_ = lean_ctor_get(v_x_3362_, 0);
switch(lean_obj_tag(v_pre_3363_))
{
case 1:
{
lean_object* v_pre_3364_; 
v_pre_3364_ = lean_ctor_get(v_pre_3363_, 0);
switch(lean_obj_tag(v_pre_3364_))
{
case 0:
{
lean_object* v_str_3365_; lean_object* v_str_3366_; lean_object* v___x_3367_; uint8_t v___x_3368_; 
v_str_3365_ = lean_ctor_get(v_x_3362_, 1);
v_str_3366_ = lean_ctor_get(v_pre_3363_, 1);
v___x_3367_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__0));
v___x_3368_ = lean_string_dec_eq(v_str_3366_, v___x_3367_);
if (v___x_3368_ == 0)
{
lean_object* v___x_3369_; uint8_t v___x_3370_; 
v___x_3369_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__1));
v___x_3370_ = lean_string_dec_eq(v_str_3366_, v___x_3369_);
if (v___x_3370_ == 0)
{
return v___y_3360_;
}
else
{
lean_object* v___x_3371_; uint8_t v___x_3372_; 
v___x_3371_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__2));
v___x_3372_ = lean_string_dec_eq(v_str_3365_, v___x_3371_);
if (v___x_3372_ == 0)
{
return v___y_3360_;
}
else
{
return v_suppressElabErrors_3361_;
}
}
}
else
{
lean_object* v___x_3373_; uint8_t v___x_3374_; 
v___x_3373_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__3));
v___x_3374_ = lean_string_dec_eq(v_str_3365_, v___x_3373_);
if (v___x_3374_ == 0)
{
return v___y_3360_;
}
else
{
return v_suppressElabErrors_3361_;
}
}
}
case 1:
{
lean_object* v_pre_3375_; 
v_pre_3375_ = lean_ctor_get(v_pre_3364_, 0);
if (lean_obj_tag(v_pre_3375_) == 0)
{
lean_object* v_str_3376_; lean_object* v_str_3377_; lean_object* v_str_3378_; lean_object* v___x_3379_; uint8_t v___x_3380_; 
v_str_3376_ = lean_ctor_get(v_x_3362_, 1);
v_str_3377_ = lean_ctor_get(v_pre_3363_, 1);
v_str_3378_ = lean_ctor_get(v_pre_3364_, 1);
v___x_3379_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__4));
v___x_3380_ = lean_string_dec_eq(v_str_3378_, v___x_3379_);
if (v___x_3380_ == 0)
{
return v___y_3360_;
}
else
{
lean_object* v___x_3381_; uint8_t v___x_3382_; 
v___x_3381_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__5));
v___x_3382_ = lean_string_dec_eq(v_str_3377_, v___x_3381_);
if (v___x_3382_ == 0)
{
return v___y_3360_;
}
else
{
lean_object* v___x_3383_; uint8_t v___x_3384_; 
v___x_3383_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__6));
v___x_3384_ = lean_string_dec_eq(v_str_3376_, v___x_3383_);
if (v___x_3384_ == 0)
{
return v___y_3360_;
}
else
{
return v_suppressElabErrors_3361_;
}
}
}
}
else
{
return v___y_3360_;
}
}
default: 
{
return v___y_3360_;
}
}
}
case 0:
{
lean_object* v_str_3385_; lean_object* v___x_3386_; uint8_t v___x_3387_; 
v_str_3385_ = lean_ctor_get(v_x_3362_, 1);
v___x_3386_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3387_ = lean_string_dec_eq(v_str_3385_, v___x_3386_);
if (v___x_3387_ == 0)
{
return v___y_3360_;
}
else
{
return v_suppressElabErrors_3361_;
}
}
default: 
{
return v___y_3360_;
}
}
}
else
{
return v___y_3360_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed(lean_object* v___y_3388_, lean_object* v_suppressElabErrors_3389_, lean_object* v_x_3390_){
_start:
{
uint8_t v___y_11912__boxed_3391_; uint8_t v_suppressElabErrors_boxed_3392_; uint8_t v_res_3393_; lean_object* v_r_3394_; 
v___y_11912__boxed_3391_ = lean_unbox(v___y_3388_);
v_suppressElabErrors_boxed_3392_ = lean_unbox(v_suppressElabErrors_3389_);
v_res_3393_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(v___y_11912__boxed_3391_, v_suppressElabErrors_boxed_3392_, v_x_3390_);
lean_dec(v_x_3390_);
v_r_3394_ = lean_box(v_res_3393_);
return v_r_3394_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(lean_object* v_ref_3395_, lean_object* v_msgData_3396_, uint8_t v_severity_3397_, uint8_t v_isSilent_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_){
_start:
{
lean_object* v___y_3405_; lean_object* v___y_3406_; uint8_t v___y_3407_; lean_object* v___y_3408_; lean_object* v___y_3409_; uint8_t v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3441_; lean_object* v___y_3442_; uint8_t v___y_3443_; lean_object* v___y_3444_; lean_object* v___y_3445_; uint8_t v___y_3446_; uint8_t v___y_3447_; lean_object* v___y_3448_; lean_object* v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; uint8_t v___y_3469_; lean_object* v___y_3470_; uint8_t v___y_3471_; uint8_t v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; uint8_t v___y_3481_; uint8_t v___y_3482_; uint8_t v___y_3483_; uint8_t v___x_3488_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; uint8_t v___y_3494_; uint8_t v___y_3495_; uint8_t v___y_3496_; uint8_t v___y_3498_; uint8_t v___x_3513_; 
v___x_3488_ = 2;
v___x_3513_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3397_, v___x_3488_);
if (v___x_3513_ == 0)
{
v___y_3498_ = v___x_3513_;
goto v___jp_3497_;
}
else
{
uint8_t v___x_3514_; 
lean_inc_ref(v_msgData_3396_);
v___x_3514_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3396_);
v___y_3498_ = v___x_3514_;
goto v___jp_3497_;
}
v___jp_3404_:
{
lean_object* v___x_3414_; lean_object* v_currNamespace_3415_; lean_object* v_openDecls_3416_; lean_object* v_env_3417_; lean_object* v_nextMacroScope_3418_; lean_object* v_ngen_3419_; lean_object* v_auxDeclNGen_3420_; lean_object* v_traceState_3421_; lean_object* v_cache_3422_; lean_object* v_messages_3423_; lean_object* v_infoState_3424_; lean_object* v_snapshotTasks_3425_; lean_object* v___x_3427_; uint8_t v_isShared_3428_; uint8_t v_isSharedCheck_3439_; 
v___x_3414_ = lean_st_ref_take(v___y_3413_);
v_currNamespace_3415_ = lean_ctor_get(v___y_3412_, 6);
v_openDecls_3416_ = lean_ctor_get(v___y_3412_, 7);
v_env_3417_ = lean_ctor_get(v___x_3414_, 0);
v_nextMacroScope_3418_ = lean_ctor_get(v___x_3414_, 1);
v_ngen_3419_ = lean_ctor_get(v___x_3414_, 2);
v_auxDeclNGen_3420_ = lean_ctor_get(v___x_3414_, 3);
v_traceState_3421_ = lean_ctor_get(v___x_3414_, 4);
v_cache_3422_ = lean_ctor_get(v___x_3414_, 5);
v_messages_3423_ = lean_ctor_get(v___x_3414_, 6);
v_infoState_3424_ = lean_ctor_get(v___x_3414_, 7);
v_snapshotTasks_3425_ = lean_ctor_get(v___x_3414_, 8);
v_isSharedCheck_3439_ = !lean_is_exclusive(v___x_3414_);
if (v_isSharedCheck_3439_ == 0)
{
v___x_3427_ = v___x_3414_;
v_isShared_3428_ = v_isSharedCheck_3439_;
goto v_resetjp_3426_;
}
else
{
lean_inc(v_snapshotTasks_3425_);
lean_inc(v_infoState_3424_);
lean_inc(v_messages_3423_);
lean_inc(v_cache_3422_);
lean_inc(v_traceState_3421_);
lean_inc(v_auxDeclNGen_3420_);
lean_inc(v_ngen_3419_);
lean_inc(v_nextMacroScope_3418_);
lean_inc(v_env_3417_);
lean_dec(v___x_3414_);
v___x_3427_ = lean_box(0);
v_isShared_3428_ = v_isSharedCheck_3439_;
goto v_resetjp_3426_;
}
v_resetjp_3426_:
{
lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3434_; 
lean_inc(v_openDecls_3416_);
lean_inc(v_currNamespace_3415_);
v___x_3429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3429_, 0, v_currNamespace_3415_);
lean_ctor_set(v___x_3429_, 1, v_openDecls_3416_);
v___x_3430_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3430_, 0, v___x_3429_);
lean_ctor_set(v___x_3430_, 1, v___y_3408_);
lean_inc_ref(v___y_3411_);
lean_inc_ref(v___y_3409_);
v___x_3431_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3431_, 0, v___y_3409_);
lean_ctor_set(v___x_3431_, 1, v___y_3405_);
lean_ctor_set(v___x_3431_, 2, v___y_3406_);
lean_ctor_set(v___x_3431_, 3, v___y_3411_);
lean_ctor_set(v___x_3431_, 4, v___x_3430_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*5, v___y_3410_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*5 + 1, v___y_3407_);
lean_ctor_set_uint8(v___x_3431_, sizeof(void*)*5 + 2, v_isSilent_3398_);
v___x_3432_ = l_Lean_MessageLog_add(v___x_3431_, v_messages_3423_);
if (v_isShared_3428_ == 0)
{
lean_ctor_set(v___x_3427_, 6, v___x_3432_);
v___x_3434_ = v___x_3427_;
goto v_reusejp_3433_;
}
else
{
lean_object* v_reuseFailAlloc_3438_; 
v_reuseFailAlloc_3438_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3438_, 0, v_env_3417_);
lean_ctor_set(v_reuseFailAlloc_3438_, 1, v_nextMacroScope_3418_);
lean_ctor_set(v_reuseFailAlloc_3438_, 2, v_ngen_3419_);
lean_ctor_set(v_reuseFailAlloc_3438_, 3, v_auxDeclNGen_3420_);
lean_ctor_set(v_reuseFailAlloc_3438_, 4, v_traceState_3421_);
lean_ctor_set(v_reuseFailAlloc_3438_, 5, v_cache_3422_);
lean_ctor_set(v_reuseFailAlloc_3438_, 6, v___x_3432_);
lean_ctor_set(v_reuseFailAlloc_3438_, 7, v_infoState_3424_);
lean_ctor_set(v_reuseFailAlloc_3438_, 8, v_snapshotTasks_3425_);
v___x_3434_ = v_reuseFailAlloc_3438_;
goto v_reusejp_3433_;
}
v_reusejp_3433_:
{
lean_object* v___x_3435_; lean_object* v___x_3436_; lean_object* v___x_3437_; 
v___x_3435_ = lean_st_ref_put(v___y_3413_, v___x_3434_);
v___x_3436_ = lean_box(0);
v___x_3437_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3437_, 0, v___x_3436_);
return v___x_3437_;
}
}
}
v___jp_3440_:
{
lean_object* v___x_3449_; lean_object* v___x_3450_; lean_object* v_a_3451_; lean_object* v___x_3453_; uint8_t v_isShared_3454_; uint8_t v_isSharedCheck_3464_; 
v___x_3449_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3396_);
v___x_3450_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3449_, v___y_3399_, v___y_3400_, v___y_3401_, v___y_3402_);
v_a_3451_ = lean_ctor_get(v___x_3450_, 0);
v_isSharedCheck_3464_ = !lean_is_exclusive(v___x_3450_);
if (v_isSharedCheck_3464_ == 0)
{
v___x_3453_ = v___x_3450_;
v_isShared_3454_ = v_isSharedCheck_3464_;
goto v_resetjp_3452_;
}
else
{
lean_inc(v_a_3451_);
lean_dec(v___x_3450_);
v___x_3453_ = lean_box(0);
v_isShared_3454_ = v_isSharedCheck_3464_;
goto v_resetjp_3452_;
}
v_resetjp_3452_:
{
lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; 
lean_inc_ref_n(v___y_3442_, 2);
v___x_3455_ = l_Lean_FileMap_toPosition(v___y_3442_, v___y_3445_);
lean_dec(v___y_3445_);
v___x_3456_ = l_Lean_FileMap_toPosition(v___y_3442_, v___y_3448_);
lean_dec(v___y_3448_);
v___x_3457_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3457_, 0, v___x_3456_);
v___x_3458_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3447_ == 0)
{
lean_del_object(v___x_3453_);
lean_dec_ref(v___y_3441_);
v___y_3405_ = v___x_3455_;
v___y_3406_ = v___x_3457_;
v___y_3407_ = v___y_3443_;
v___y_3408_ = v_a_3451_;
v___y_3409_ = v___y_3444_;
v___y_3410_ = v___y_3446_;
v___y_3411_ = v___x_3458_;
v___y_3412_ = v___y_3401_;
v___y_3413_ = v___y_3402_;
goto v___jp_3404_;
}
else
{
uint8_t v___x_3459_; 
lean_inc(v_a_3451_);
v___x_3459_ = l_Lean_MessageData_hasTag(v___y_3441_, v_a_3451_);
if (v___x_3459_ == 0)
{
lean_object* v___x_3460_; lean_object* v___x_3462_; 
lean_dec_ref_known(v___x_3457_, 1);
lean_dec_ref(v___x_3455_);
lean_dec(v_a_3451_);
v___x_3460_ = lean_box(0);
if (v_isShared_3454_ == 0)
{
lean_ctor_set(v___x_3453_, 0, v___x_3460_);
v___x_3462_ = v___x_3453_;
goto v_reusejp_3461_;
}
else
{
lean_object* v_reuseFailAlloc_3463_; 
v_reuseFailAlloc_3463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3463_, 0, v___x_3460_);
v___x_3462_ = v_reuseFailAlloc_3463_;
goto v_reusejp_3461_;
}
v_reusejp_3461_:
{
return v___x_3462_;
}
}
else
{
lean_del_object(v___x_3453_);
v___y_3405_ = v___x_3455_;
v___y_3406_ = v___x_3457_;
v___y_3407_ = v___y_3443_;
v___y_3408_ = v_a_3451_;
v___y_3409_ = v___y_3444_;
v___y_3410_ = v___y_3446_;
v___y_3411_ = v___x_3458_;
v___y_3412_ = v___y_3401_;
v___y_3413_ = v___y_3402_;
goto v___jp_3404_;
}
}
}
}
v___jp_3465_:
{
lean_object* v___x_3474_; 
v___x_3474_ = l_Lean_Syntax_getTailPos_x3f(v___y_3467_, v___y_3471_);
lean_dec(v___y_3467_);
if (lean_obj_tag(v___x_3474_) == 0)
{
lean_inc(v___y_3473_);
v___y_3441_ = v___y_3466_;
v___y_3442_ = v___y_3468_;
v___y_3443_ = v___y_3469_;
v___y_3444_ = v___y_3470_;
v___y_3445_ = v___y_3473_;
v___y_3446_ = v___y_3471_;
v___y_3447_ = v___y_3472_;
v___y_3448_ = v___y_3473_;
goto v___jp_3440_;
}
else
{
lean_object* v_val_3475_; 
v_val_3475_ = lean_ctor_get(v___x_3474_, 0);
lean_inc(v_val_3475_);
lean_dec_ref_known(v___x_3474_, 1);
v___y_3441_ = v___y_3466_;
v___y_3442_ = v___y_3468_;
v___y_3443_ = v___y_3469_;
v___y_3444_ = v___y_3470_;
v___y_3445_ = v___y_3473_;
v___y_3446_ = v___y_3471_;
v___y_3447_ = v___y_3472_;
v___y_3448_ = v_val_3475_;
goto v___jp_3440_;
}
}
v___jp_3476_:
{
lean_object* v_ref_3484_; lean_object* v___x_3485_; 
v_ref_3484_ = l_Lean_replaceRef(v_ref_3395_, v___y_3478_);
v___x_3485_ = l_Lean_Syntax_getPos_x3f(v_ref_3484_, v___y_3481_);
if (lean_obj_tag(v___x_3485_) == 0)
{
lean_object* v___x_3486_; 
v___x_3486_ = lean_unsigned_to_nat(0u);
v___y_3466_ = v___y_3477_;
v___y_3467_ = v_ref_3484_;
v___y_3468_ = v___y_3479_;
v___y_3469_ = v___y_3483_;
v___y_3470_ = v___y_3480_;
v___y_3471_ = v___y_3481_;
v___y_3472_ = v___y_3482_;
v___y_3473_ = v___x_3486_;
goto v___jp_3465_;
}
else
{
lean_object* v_val_3487_; 
v_val_3487_ = lean_ctor_get(v___x_3485_, 0);
lean_inc(v_val_3487_);
lean_dec_ref_known(v___x_3485_, 1);
v___y_3466_ = v___y_3477_;
v___y_3467_ = v_ref_3484_;
v___y_3468_ = v___y_3479_;
v___y_3469_ = v___y_3483_;
v___y_3470_ = v___y_3480_;
v___y_3471_ = v___y_3481_;
v___y_3472_ = v___y_3482_;
v___y_3473_ = v_val_3487_;
goto v___jp_3465_;
}
}
v___jp_3489_:
{
if (v___y_3496_ == 0)
{
v___y_3477_ = v___y_3492_;
v___y_3478_ = v___y_3490_;
v___y_3479_ = v___y_3491_;
v___y_3480_ = v___y_3493_;
v___y_3481_ = v___y_3495_;
v___y_3482_ = v___y_3494_;
v___y_3483_ = v_severity_3397_;
goto v___jp_3476_;
}
else
{
v___y_3477_ = v___y_3492_;
v___y_3478_ = v___y_3490_;
v___y_3479_ = v___y_3491_;
v___y_3480_ = v___y_3493_;
v___y_3481_ = v___y_3495_;
v___y_3482_ = v___y_3494_;
v___y_3483_ = v___x_3488_;
goto v___jp_3476_;
}
}
v___jp_3497_:
{
if (v___y_3498_ == 0)
{
lean_object* v_fileName_3499_; lean_object* v_fileMap_3500_; lean_object* v_options_3501_; lean_object* v_ref_3502_; uint8_t v_suppressElabErrors_3503_; lean_object* v___x_3504_; lean_object* v___x_3505_; lean_object* v___f_3506_; uint8_t v___x_3507_; uint8_t v___x_3508_; 
v_fileName_3499_ = lean_ctor_get(v___y_3401_, 0);
v_fileMap_3500_ = lean_ctor_get(v___y_3401_, 1);
v_options_3501_ = lean_ctor_get(v___y_3401_, 2);
v_ref_3502_ = lean_ctor_get(v___y_3401_, 5);
v_suppressElabErrors_3503_ = lean_ctor_get_uint8(v___y_3401_, sizeof(void*)*14 + 1);
v___x_3504_ = lean_box(v___y_3498_);
v___x_3505_ = lean_box(v_suppressElabErrors_3503_);
v___f_3506_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3506_, 0, v___x_3504_);
lean_closure_set(v___f_3506_, 1, v___x_3505_);
v___x_3507_ = 1;
v___x_3508_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3397_, v___x_3507_);
if (v___x_3508_ == 0)
{
v___y_3490_ = v_ref_3502_;
v___y_3491_ = v_fileMap_3500_;
v___y_3492_ = v___f_3506_;
v___y_3493_ = v_fileName_3499_;
v___y_3494_ = v_suppressElabErrors_3503_;
v___y_3495_ = v___y_3498_;
v___y_3496_ = v___x_3508_;
goto v___jp_3489_;
}
else
{
lean_object* v___x_3509_; uint8_t v___x_3510_; 
v___x_3509_ = l_Lean_warningAsError;
v___x_3510_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3501_, v___x_3509_);
v___y_3490_ = v_ref_3502_;
v___y_3491_ = v_fileMap_3500_;
v___y_3492_ = v___f_3506_;
v___y_3493_ = v_fileName_3499_;
v___y_3494_ = v_suppressElabErrors_3503_;
v___y_3495_ = v___y_3498_;
v___y_3496_ = v___x_3510_;
goto v___jp_3489_;
}
}
else
{
lean_object* v___x_3511_; lean_object* v___x_3512_; 
lean_dec_ref(v_msgData_3396_);
v___x_3511_ = lean_box(0);
v___x_3512_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3512_, 0, v___x_3511_);
return v___x_3512_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___boxed(lean_object* v_ref_3515_, lean_object* v_msgData_3516_, lean_object* v_severity_3517_, lean_object* v_isSilent_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_){
_start:
{
uint8_t v_severity_boxed_3524_; uint8_t v_isSilent_boxed_3525_; lean_object* v_res_3526_; 
v_severity_boxed_3524_ = lean_unbox(v_severity_3517_);
v_isSilent_boxed_3525_ = lean_unbox(v_isSilent_3518_);
v_res_3526_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3515_, v_msgData_3516_, v_severity_boxed_3524_, v_isSilent_boxed_3525_, v___y_3519_, v___y_3520_, v___y_3521_, v___y_3522_);
lean_dec(v___y_3522_);
lean_dec_ref(v___y_3521_);
lean_dec(v___y_3520_);
lean_dec_ref(v___y_3519_);
lean_dec(v_ref_3515_);
return v_res_3526_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(lean_object* v_msgData_3527_, uint8_t v_severity_3528_, uint8_t v_isSilent_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_){
_start:
{
lean_object* v_ref_3535_; lean_object* v___x_3536_; 
v_ref_3535_ = lean_ctor_get(v___y_3532_, 5);
v___x_3536_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3535_, v_msgData_3527_, v_severity_3528_, v_isSilent_3529_, v___y_3530_, v___y_3531_, v___y_3532_, v___y_3533_);
return v___x_3536_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3___boxed(lean_object* v_msgData_3537_, lean_object* v_severity_3538_, lean_object* v_isSilent_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_){
_start:
{
uint8_t v_severity_boxed_3545_; uint8_t v_isSilent_boxed_3546_; lean_object* v_res_3547_; 
v_severity_boxed_3545_ = lean_unbox(v_severity_3538_);
v_isSilent_boxed_3546_ = lean_unbox(v_isSilent_3539_);
v_res_3547_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3537_, v_severity_boxed_3545_, v_isSilent_boxed_3546_, v___y_3540_, v___y_3541_, v___y_3542_, v___y_3543_);
lean_dec(v___y_3543_);
lean_dec_ref(v___y_3542_);
lean_dec(v___y_3541_);
lean_dec_ref(v___y_3540_);
return v_res_3547_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object* v_msgData_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_){
_start:
{
uint8_t v___x_3554_; uint8_t v___x_3555_; lean_object* v___x_3556_; 
v___x_3554_ = 1;
v___x_3555_ = 0;
v___x_3556_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3548_, v___x_3554_, v___x_3555_, v___y_3549_, v___y_3550_, v___y_3551_, v___y_3552_);
return v___x_3556_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object* v_msgData_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_){
_start:
{
lean_object* v_res_3563_; 
v_res_3563_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v_msgData_3557_, v___y_3558_, v___y_3559_, v___y_3560_, v___y_3561_);
lean_dec(v___y_3561_);
lean_dec_ref(v___y_3560_);
lean_dec(v___y_3559_);
lean_dec_ref(v___y_3558_);
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
lean_object* v___x_3570_; lean_object* v___x_3571_; lean_object* v___x_3572_; 
v___x_3570_ = lean_box(0);
v___x_3571_ = lean_unsigned_to_nat(16u);
v___x_3572_ = lean_mk_array(v___x_3571_, v___x_3570_);
return v___x_3572_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3573_; lean_object* v___x_3574_; lean_object* v___x_3575_; 
v___x_3573_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4);
v___x_3574_ = lean_unsigned_to_nat(0u);
v___x_3575_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3575_, 0, v___x_3574_);
lean_ctor_set(v___x_3575_, 1, v___x_3573_);
return v___x_3575_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; 
v___x_3578_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6));
v___x_3579_ = lean_box(1);
v___x_3580_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5);
v___x_3581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3581_, 0, v___x_3580_);
lean_ctor_set(v___x_3581_, 1, v___x_3579_);
lean_ctor_set(v___x_3581_, 2, v___x_3578_);
return v___x_3581_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3588_; lean_object* v___x_3589_; 
v___x_3588_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10));
v___x_3589_ = l_Lean_stringToMessageData(v___x_3588_);
return v___x_3589_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13(void){
_start:
{
lean_object* v___x_3591_; lean_object* v___x_3592_; 
v___x_3591_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12));
v___x_3592_ = l_Lean_stringToMessageData(v___x_3591_);
return v___x_3592_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v___x_3594_, lean_object* v_args_3595_, lean_object* v_ty_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_){
_start:
{
lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___y_3677_; lean_object* v___x_3678_; 
v___x_3619_ = lean_unsigned_to_nat(0u);
v___x_3620_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7);
v___x_3621_ = lean_st_mk_ref(v___x_3620_);
v___x_3678_ = l_Lean_Expr_collectFVars(v_ty_3596_, v___x_3621_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
if (lean_obj_tag(v___x_3678_) == 0)
{
lean_object* v___x_3679_; size_t v_sz_3680_; size_t v___x_3681_; lean_object* v___x_3682_; 
lean_dec_ref_known(v___x_3678_, 1);
v___x_3679_ = lean_box(0);
v_sz_3680_ = lean_array_size(v_args_3595_);
v___x_3681_ = ((size_t)0ULL);
v___x_3682_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_args_3595_, v_sz_3680_, v___x_3681_, v___x_3679_, v___x_3621_, v___y_3597_, v___y_3599_, v___y_3600_);
if (lean_obj_tag(v___x_3682_) == 0)
{
lean_dec_ref_known(v___x_3682_, 1);
goto v___jp_3622_;
}
else
{
v___y_3677_ = v___x_3682_;
goto v___jp_3676_;
}
}
else
{
v___y_3677_ = v___x_3678_;
goto v___jp_3676_;
}
v___jp_3602_:
{
lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; uint8_t v___x_3616_; 
lean_inc_ref(v___y_3605_);
v___x_3606_ = l_Lean_stringToMessageData(v___y_3605_);
v___x_3607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3607_, 0, v___y_3603_);
lean_ctor_set(v___x_3607_, 1, v___x_3606_);
v___x_3608_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1);
v___x_3609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3609_, 0, v___x_3607_);
lean_ctor_set(v___x_3609_, 1, v___x_3608_);
v___x_3610_ = lean_array_to_list(v___y_3604_);
v___x_3611_ = l_Lean_MessageData_nil;
v___x_3612_ = l_Lean_MessageData_joinSep(v___x_3610_, v___x_3611_);
v___x_3613_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3613_, 0, v___x_3609_);
lean_ctor_set(v___x_3613_, 1, v___x_3612_);
v___x_3614_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3);
v___x_3615_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3615_, 0, v___x_3613_);
lean_ctor_set(v___x_3615_, 1, v___x_3614_);
v___x_3616_ = l_Lean_Expr_hasSorry(v___x_3594_);
if (v___x_3616_ == 0)
{
lean_object* v___x_3617_; 
v___x_3617_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3615_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
return v___x_3617_;
}
else
{
lean_object* v___x_3618_; 
v___x_3618_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_3615_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
return v___x_3618_;
}
}
v___jp_3622_:
{
lean_object* v___x_3623_; lean_object* v___x_3624_; 
v___x_3623_ = lean_st_ref_get(v___x_3621_);
lean_dec(v___x_3621_);
v___x_3624_ = l_Lean_CollectFVars_State_addDependencies(v___x_3623_, v___y_3597_, v___y_3598_, v___y_3599_, v___y_3600_);
if (lean_obj_tag(v___x_3624_) == 0)
{
lean_object* v_a_3625_; lean_object* v___x_3626_; lean_object* v___x_3627_; size_t v_sz_3628_; size_t v___x_3629_; lean_object* v___x_3630_; 
v_a_3625_ = lean_ctor_get(v___x_3624_, 0);
lean_inc(v_a_3625_);
lean_dec_ref_known(v___x_3624_, 1);
v___x_3626_ = lean_unsigned_to_nat(1u);
v___x_3627_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9));
v_sz_3628_ = lean_array_size(v_args_3595_);
v___x_3629_ = ((size_t)0ULL);
v___x_3630_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3625_, v_args_3595_, v_sz_3628_, v___x_3629_, v___x_3627_, v___y_3597_, v___y_3599_, v___y_3600_);
lean_dec(v_a_3625_);
if (lean_obj_tag(v___x_3630_) == 0)
{
lean_object* v_a_3631_; lean_object* v___x_3633_; uint8_t v_isShared_3634_; uint8_t v_isSharedCheck_3659_; 
v_a_3631_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3659_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3659_ == 0)
{
v___x_3633_ = v___x_3630_;
v_isShared_3634_ = v_isSharedCheck_3659_;
goto v_resetjp_3632_;
}
else
{
lean_inc(v_a_3631_);
lean_dec(v___x_3630_);
v___x_3633_ = lean_box(0);
v_isShared_3634_ = v_isSharedCheck_3659_;
goto v_resetjp_3632_;
}
v_resetjp_3632_:
{
lean_object* v_fst_3635_; lean_object* v___x_3637_; uint8_t v_isShared_3638_; uint8_t v_isSharedCheck_3657_; 
v_fst_3635_ = lean_ctor_get(v_a_3631_, 0);
v_isSharedCheck_3657_ = !lean_is_exclusive(v_a_3631_);
if (v_isSharedCheck_3657_ == 0)
{
lean_object* v_unused_3658_; 
v_unused_3658_ = lean_ctor_get(v_a_3631_, 1);
lean_dec(v_unused_3658_);
v___x_3637_ = v_a_3631_;
v_isShared_3638_ = v_isSharedCheck_3657_;
goto v_resetjp_3636_;
}
else
{
lean_inc(v_fst_3635_);
lean_dec(v_a_3631_);
v___x_3637_ = lean_box(0);
v_isShared_3638_ = v_isSharedCheck_3657_;
goto v_resetjp_3636_;
}
v_resetjp_3636_:
{
lean_object* v___x_3639_; uint8_t v___x_3640_; 
v___x_3639_ = lean_array_get_size(v_fst_3635_);
v___x_3640_ = lean_nat_dec_eq(v___x_3639_, v___x_3619_);
if (v___x_3640_ == 0)
{
lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3646_; 
lean_del_object(v___x_3633_);
v___x_3641_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11);
v___x_3642_ = l_Nat_reprFast(v___x_3639_);
v___x_3643_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3643_, 0, v___x_3642_);
v___x_3644_ = l_Lean_MessageData_ofFormat(v___x_3643_);
if (v_isShared_3638_ == 0)
{
lean_ctor_set_tag(v___x_3637_, 7);
lean_ctor_set(v___x_3637_, 1, v___x_3644_);
lean_ctor_set(v___x_3637_, 0, v___x_3641_);
v___x_3646_ = v___x_3637_;
goto v_reusejp_3645_;
}
else
{
lean_object* v_reuseFailAlloc_3652_; 
v_reuseFailAlloc_3652_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3652_, 0, v___x_3641_);
lean_ctor_set(v_reuseFailAlloc_3652_, 1, v___x_3644_);
v___x_3646_ = v_reuseFailAlloc_3652_;
goto v_reusejp_3645_;
}
v_reusejp_3645_:
{
lean_object* v___x_3647_; lean_object* v___x_3648_; uint8_t v___x_3649_; 
v___x_3647_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13);
v___x_3648_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3648_, 0, v___x_3646_);
lean_ctor_set(v___x_3648_, 1, v___x_3647_);
v___x_3649_ = lean_nat_dec_eq(v___x_3639_, v___x_3626_);
if (v___x_3649_ == 0)
{
lean_object* v___x_3650_; 
v___x_3650_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14));
v___y_3603_ = v___x_3648_;
v___y_3604_ = v_fst_3635_;
v___y_3605_ = v___x_3650_;
goto v___jp_3602_;
}
else
{
lean_object* v___x_3651_; 
v___x_3651_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___y_3603_ = v___x_3648_;
v___y_3604_ = v_fst_3635_;
v___y_3605_ = v___x_3651_;
goto v___jp_3602_;
}
}
}
else
{
lean_object* v___x_3653_; lean_object* v___x_3655_; 
lean_del_object(v___x_3637_);
lean_dec(v_fst_3635_);
v___x_3653_ = lean_box(0);
if (v_isShared_3634_ == 0)
{
lean_ctor_set(v___x_3633_, 0, v___x_3653_);
v___x_3655_ = v___x_3633_;
goto v_reusejp_3654_;
}
else
{
lean_object* v_reuseFailAlloc_3656_; 
v_reuseFailAlloc_3656_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3656_, 0, v___x_3653_);
v___x_3655_ = v_reuseFailAlloc_3656_;
goto v_reusejp_3654_;
}
v_reusejp_3654_:
{
return v___x_3655_;
}
}
}
}
}
else
{
lean_object* v_a_3660_; lean_object* v___x_3662_; uint8_t v_isShared_3663_; uint8_t v_isSharedCheck_3667_; 
v_a_3660_ = lean_ctor_get(v___x_3630_, 0);
v_isSharedCheck_3667_ = !lean_is_exclusive(v___x_3630_);
if (v_isSharedCheck_3667_ == 0)
{
v___x_3662_ = v___x_3630_;
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
else
{
lean_inc(v_a_3660_);
lean_dec(v___x_3630_);
v___x_3662_ = lean_box(0);
v_isShared_3663_ = v_isSharedCheck_3667_;
goto v_resetjp_3661_;
}
v_resetjp_3661_:
{
lean_object* v___x_3665_; 
if (v_isShared_3663_ == 0)
{
v___x_3665_ = v___x_3662_;
goto v_reusejp_3664_;
}
else
{
lean_object* v_reuseFailAlloc_3666_; 
v_reuseFailAlloc_3666_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3666_, 0, v_a_3660_);
v___x_3665_ = v_reuseFailAlloc_3666_;
goto v_reusejp_3664_;
}
v_reusejp_3664_:
{
return v___x_3665_;
}
}
}
}
else
{
lean_object* v_a_3668_; lean_object* v___x_3670_; uint8_t v_isShared_3671_; uint8_t v_isSharedCheck_3675_; 
v_a_3668_ = lean_ctor_get(v___x_3624_, 0);
v_isSharedCheck_3675_ = !lean_is_exclusive(v___x_3624_);
if (v_isSharedCheck_3675_ == 0)
{
v___x_3670_ = v___x_3624_;
v_isShared_3671_ = v_isSharedCheck_3675_;
goto v_resetjp_3669_;
}
else
{
lean_inc(v_a_3668_);
lean_dec(v___x_3624_);
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
v___jp_3676_:
{
if (lean_obj_tag(v___y_3677_) == 0)
{
lean_dec_ref_known(v___y_3677_, 1);
goto v___jp_3622_;
}
else
{
lean_dec(v___x_3621_);
return v___y_3677_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v___x_3683_, lean_object* v_args_3684_, lean_object* v_ty_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_){
_start:
{
lean_object* v_res_3691_; 
v_res_3691_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v___x_3683_, v_args_3684_, v_ty_3685_, v___y_3686_, v___y_3687_, v___y_3688_, v___y_3689_);
lean_dec(v___y_3689_);
lean_dec_ref(v___y_3688_);
lean_dec(v___y_3687_);
lean_dec_ref(v___y_3686_);
lean_dec_ref(v_args_3684_);
lean_dec_ref(v___x_3683_);
return v_res_3691_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object* v_e_3692_){
_start:
{
lean_object* v___x_3693_; 
v___x_3693_ = l_Lean_Expr_cleanupAnnotations(v_e_3692_);
switch(lean_obj_tag(v___x_3693_))
{
case 7:
{
lean_object* v_body_3694_; uint8_t v_binderInfo_3695_; uint8_t v___x_3696_; 
v_body_3694_ = lean_ctor_get(v___x_3693_, 2);
lean_inc_ref(v_body_3694_);
v_binderInfo_3695_ = lean_ctor_get_uint8(v___x_3693_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3693_, 3);
v___x_3696_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3695_);
if (v___x_3696_ == 0)
{
lean_object* v___x_3697_; uint8_t v___x_3698_; 
v___x_3697_ = lean_unsigned_to_nat(0u);
v___x_3698_ = lean_expr_has_loose_bvar(v_body_3694_, v___x_3697_);
if (v___x_3698_ == 0)
{
uint8_t v___x_3699_; 
lean_dec_ref(v_body_3694_);
v___x_3699_ = 1;
return v___x_3699_;
}
else
{
v_e_3692_ = v_body_3694_;
goto _start;
}
}
else
{
v_e_3692_ = v_body_3694_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3702_; 
v_body_3702_ = lean_ctor_get(v___x_3693_, 3);
lean_inc_ref(v_body_3702_);
lean_dec_ref_known(v___x_3693_, 4);
v_e_3692_ = v_body_3702_;
goto _start;
}
default: 
{
uint8_t v___x_3704_; 
lean_dec_ref(v___x_3693_);
v___x_3704_ = 0;
return v___x_3704_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_e_3705_){
_start:
{
uint8_t v_res_3706_; lean_object* v_r_3707_; 
v_res_3706_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_e_3705_);
v_r_3707_ = lean_box(v_res_3706_);
return v_r_3707_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_cinfo_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_){
_start:
{
lean_object* v___x_3714_; uint8_t v___x_3715_; 
v___x_3714_ = l_Lean_ConstantInfo_type(v_cinfo_3708_);
lean_inc_ref(v___x_3714_);
v___x_3715_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(v___x_3714_);
if (v___x_3715_ == 0)
{
lean_object* v___x_3716_; lean_object* v___x_3717_; 
lean_dec_ref(v___x_3714_);
v___x_3716_ = lean_box(0);
v___x_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3717_, 0, v___x_3716_);
return v___x_3717_;
}
else
{
lean_object* v___f_3718_; uint8_t v___x_3719_; lean_object* v___x_3720_; 
lean_inc_ref(v___x_3714_);
v___f_3718_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3718_, 0, v___x_3714_);
v___x_3719_ = 0;
v___x_3720_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v___x_3714_, v___f_3718_, v___x_3719_, v_a_3709_, v_a_3710_, v_a_3711_, v_a_3712_);
return v___x_3720_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_cinfo_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_){
_start:
{
lean_object* v_res_3727_; 
v_res_3727_ = l_Lean_Meta_checkImpossibleInstance(v_cinfo_3721_, v_a_3722_, v_a_3723_, v_a_3724_, v_a_3725_);
lean_dec(v_a_3725_);
lean_dec_ref(v_a_3724_);
lean_dec(v_a_3723_);
lean_dec_ref(v_a_3722_);
lean_dec_ref(v_cinfo_3721_);
return v_res_3727_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v_00_u03b2_3728_, lean_object* v_k_3729_, lean_object* v_t_3730_){
_start:
{
uint8_t v___x_3731_; 
v___x_3731_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3729_, v_t_3730_);
return v___x_3731_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v_00_u03b2_3732_, lean_object* v_k_3733_, lean_object* v_t_3734_){
_start:
{
uint8_t v_res_3735_; lean_object* v_r_3736_; 
v_res_3735_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(v_00_u03b2_3732_, v_k_3733_, v_t_3734_);
lean_dec(v_t_3734_);
lean_dec(v_k_3733_);
v_r_3736_ = lean_box(v_res_3735_);
return v_r_3736_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_a_3737_, lean_object* v_as_3738_, size_t v_sz_3739_, size_t v_i_3740_, lean_object* v_b_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_){
_start:
{
lean_object* v___x_3747_; 
v___x_3747_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3737_, v_as_3738_, v_sz_3739_, v_i_3740_, v_b_3741_, v___y_3742_, v___y_3744_, v___y_3745_);
return v___x_3747_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_a_3748_, lean_object* v_as_3749_, lean_object* v_sz_3750_, lean_object* v_i_3751_, lean_object* v_b_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_){
_start:
{
size_t v_sz_boxed_3758_; size_t v_i_boxed_3759_; lean_object* v_res_3760_; 
v_sz_boxed_3758_ = lean_unbox_usize(v_sz_3750_);
lean_dec(v_sz_3750_);
v_i_boxed_3759_ = lean_unbox_usize(v_i_3751_);
lean_dec(v_i_3751_);
v_res_3760_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_a_3748_, v_as_3749_, v_sz_boxed_3758_, v_i_boxed_3759_, v_b_3752_, v___y_3753_, v___y_3754_, v___y_3755_, v___y_3756_);
lean_dec(v___y_3756_);
lean_dec_ref(v___y_3755_);
lean_dec(v___y_3754_);
lean_dec_ref(v___y_3753_);
lean_dec_ref(v_as_3749_);
lean_dec_ref(v_a_3748_);
return v_res_3760_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object* v_as_3761_, size_t v_sz_3762_, size_t v_i_3763_, lean_object* v_b_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_){
_start:
{
lean_object* v___x_3771_; 
v___x_3771_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_as_3761_, v_sz_3762_, v_i_3763_, v_b_3764_, v___y_3765_, v___y_3766_, v___y_3768_, v___y_3769_);
return v___x_3771_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object* v_as_3772_, lean_object* v_sz_3773_, lean_object* v_i_3774_, lean_object* v_b_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_){
_start:
{
size_t v_sz_boxed_3782_; size_t v_i_boxed_3783_; lean_object* v_res_3784_; 
v_sz_boxed_3782_ = lean_unbox_usize(v_sz_3773_);
lean_dec(v_sz_3773_);
v_i_boxed_3783_ = lean_unbox_usize(v_i_3774_);
lean_dec(v_i_3774_);
v_res_3784_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(v_as_3772_, v_sz_boxed_3782_, v_i_boxed_3783_, v_b_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_);
lean_dec(v___y_3780_);
lean_dec_ref(v___y_3779_);
lean_dec(v___y_3778_);
lean_dec_ref(v___y_3777_);
lean_dec(v___y_3776_);
lean_dec_ref(v_as_3772_);
return v_res_3784_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3786_; lean_object* v___x_3787_; 
v___x_3786_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3787_ = l_Lean_stringToMessageData(v___x_3786_);
return v___x_3787_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3789_; lean_object* v___x_3790_; 
v___x_3789_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3790_ = l_Lean_stringToMessageData(v___x_3789_);
return v___x_3790_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3792_; lean_object* v___x_3793_; 
v___x_3792_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3793_ = l_Lean_stringToMessageData(v___x_3792_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_c_3794_, lean_object* v_x_3795_, lean_object* v_target_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_){
_start:
{
lean_object* v___x_3802_; 
lean_inc_ref(v_target_3796_);
v___x_3802_ = l_Lean_Meta_isClass_x3f(v_target_3796_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
if (lean_obj_tag(v___x_3802_) == 0)
{
lean_object* v_a_3803_; lean_object* v___x_3805_; uint8_t v_isShared_3806_; uint8_t v_isSharedCheck_3821_; 
v_a_3803_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3821_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3821_ == 0)
{
v___x_3805_ = v___x_3802_;
v_isShared_3806_ = v_isSharedCheck_3821_;
goto v_resetjp_3804_;
}
else
{
lean_inc(v_a_3803_);
lean_dec(v___x_3802_);
v___x_3805_ = lean_box(0);
v_isShared_3806_ = v_isSharedCheck_3821_;
goto v_resetjp_3804_;
}
v_resetjp_3804_:
{
if (lean_obj_tag(v_a_3803_) == 0)
{
lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; 
lean_del_object(v___x_3805_);
v___x_3807_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3808_ = l_Lean_MessageData_ofExpr(v_c_3794_);
v___x_3809_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3809_, 0, v___x_3807_);
lean_ctor_set(v___x_3809_, 1, v___x_3808_);
v___x_3810_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3811_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3811_, 0, v___x_3809_);
lean_ctor_set(v___x_3811_, 1, v___x_3810_);
v___x_3812_ = l_Lean_MessageData_ofExpr(v_target_3796_);
v___x_3813_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3813_, 0, v___x_3811_);
lean_ctor_set(v___x_3813_, 1, v___x_3812_);
v___x_3814_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3815_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3815_, 0, v___x_3813_);
lean_ctor_set(v___x_3815_, 1, v___x_3814_);
v___x_3816_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3815_, v___y_3797_, v___y_3798_, v___y_3799_, v___y_3800_);
return v___x_3816_;
}
else
{
lean_object* v___x_3817_; lean_object* v___x_3819_; 
lean_dec_ref_known(v_a_3803_, 1);
lean_dec_ref(v_target_3796_);
lean_dec_ref(v_c_3794_);
v___x_3817_ = lean_box(0);
if (v_isShared_3806_ == 0)
{
lean_ctor_set(v___x_3805_, 0, v___x_3817_);
v___x_3819_ = v___x_3805_;
goto v_reusejp_3818_;
}
else
{
lean_object* v_reuseFailAlloc_3820_; 
v_reuseFailAlloc_3820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3820_, 0, v___x_3817_);
v___x_3819_ = v_reuseFailAlloc_3820_;
goto v_reusejp_3818_;
}
v_reusejp_3818_:
{
return v___x_3819_;
}
}
}
}
else
{
lean_object* v_a_3822_; lean_object* v___x_3824_; uint8_t v_isShared_3825_; uint8_t v_isSharedCheck_3829_; 
lean_dec_ref(v_target_3796_);
lean_dec_ref(v_c_3794_);
v_a_3822_ = lean_ctor_get(v___x_3802_, 0);
v_isSharedCheck_3829_ = !lean_is_exclusive(v___x_3802_);
if (v_isSharedCheck_3829_ == 0)
{
v___x_3824_ = v___x_3802_;
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
else
{
lean_inc(v_a_3822_);
lean_dec(v___x_3802_);
v___x_3824_ = lean_box(0);
v_isShared_3825_ = v_isSharedCheck_3829_;
goto v_resetjp_3823_;
}
v_resetjp_3823_:
{
lean_object* v___x_3827_; 
if (v_isShared_3825_ == 0)
{
v___x_3827_ = v___x_3824_;
goto v_reusejp_3826_;
}
else
{
lean_object* v_reuseFailAlloc_3828_; 
v_reuseFailAlloc_3828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3828_, 0, v_a_3822_);
v___x_3827_ = v_reuseFailAlloc_3828_;
goto v_reusejp_3826_;
}
v_reusejp_3826_:
{
return v___x_3827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_c_3830_, lean_object* v_x_3831_, lean_object* v_target_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_){
_start:
{
lean_object* v_res_3838_; 
v_res_3838_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_c_3830_, v_x_3831_, v_target_3832_, v___y_3833_, v___y_3834_, v___y_3835_, v___y_3836_);
lean_dec(v___y_3836_);
lean_dec_ref(v___y_3835_);
lean_dec(v___y_3834_);
lean_dec_ref(v___y_3833_);
lean_dec_ref(v_x_3831_);
return v_res_3838_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_c_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_){
_start:
{
lean_object* v___x_3845_; 
lean_inc(v_a_3843_);
lean_inc_ref(v_a_3842_);
lean_inc(v_a_3841_);
lean_inc_ref(v_a_3840_);
lean_inc_ref(v_c_3839_);
v___x_3845_ = lean_infer_type(v_c_3839_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
if (lean_obj_tag(v___x_3845_) == 0)
{
lean_object* v_a_3846_; lean_object* v___f_3847_; uint8_t v___x_3848_; lean_object* v___x_3849_; 
v_a_3846_ = lean_ctor_get(v___x_3845_, 0);
lean_inc(v_a_3846_);
lean_dec_ref_known(v___x_3845_, 1);
v___f_3847_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3847_, 0, v_c_3839_);
v___x_3848_ = 0;
v___x_3849_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3846_, v___f_3847_, v___x_3848_, v___x_3848_, v_a_3840_, v_a_3841_, v_a_3842_, v_a_3843_);
return v___x_3849_;
}
else
{
lean_object* v_a_3850_; lean_object* v___x_3852_; uint8_t v_isShared_3853_; uint8_t v_isSharedCheck_3857_; 
lean_dec_ref(v_c_3839_);
v_a_3850_ = lean_ctor_get(v___x_3845_, 0);
v_isSharedCheck_3857_ = !lean_is_exclusive(v___x_3845_);
if (v_isSharedCheck_3857_ == 0)
{
v___x_3852_ = v___x_3845_;
v_isShared_3853_ = v_isSharedCheck_3857_;
goto v_resetjp_3851_;
}
else
{
lean_inc(v_a_3850_);
lean_dec(v___x_3845_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_c_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_){
_start:
{
lean_object* v_res_3864_; 
v_res_3864_ = l_Lean_Meta_checkNonClassInstance(v_c_3858_, v_a_3859_, v_a_3860_, v_a_3861_, v_a_3862_);
lean_dec(v_a_3862_);
lean_dec_ref(v_a_3861_);
lean_dec(v_a_3860_);
lean_dec_ref(v_a_3859_);
return v_res_3864_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3875_, lean_object* v___y_3876_){
_start:
{
lean_object* v___x_3878_; lean_object* v_env_3879_; lean_object* v___x_3880_; lean_object* v___x_3881_; 
v___x_3878_ = lean_st_ref_get(v___y_3876_);
v_env_3879_ = lean_ctor_get(v___x_3878_, 0);
lean_inc_ref(v_env_3879_);
lean_dec(v___x_3878_);
v___x_3880_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3879_, v_declName_3875_);
v___x_3881_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3881_, 0, v___x_3880_);
return v___x_3881_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3882_, lean_object* v___y_3883_, lean_object* v___y_3884_){
_start:
{
lean_object* v_res_3885_; 
v_res_3885_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3882_, v___y_3883_);
lean_dec(v___y_3883_);
return v_res_3885_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_){
_start:
{
lean_object* v___x_3892_; 
v___x_3892_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3886_, v___y_3890_);
return v___x_3892_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_){
_start:
{
lean_object* v_res_3899_; 
v_res_3899_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3893_, v___y_3894_, v___y_3895_, v___y_3896_, v___y_3897_);
lean_dec(v___y_3897_);
lean_dec_ref(v___y_3896_);
lean_dec(v___y_3895_);
lean_dec_ref(v___y_3894_);
return v_res_3899_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3900_; 
v___x_3900_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3900_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3901_; lean_object* v___x_3902_; 
v___x_3901_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3902_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3902_, 0, v___x_3901_);
return v___x_3902_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3903_; lean_object* v___x_3904_; 
v___x_3903_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3904_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3904_, 0, v___x_3903_);
lean_ctor_set(v___x_3904_, 1, v___x_3903_);
return v___x_3904_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3905_; lean_object* v___x_3906_; 
v___x_3905_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3906_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3906_, 0, v___x_3905_);
lean_ctor_set(v___x_3906_, 1, v___x_3905_);
lean_ctor_set(v___x_3906_, 2, v___x_3905_);
lean_ctor_set(v___x_3906_, 3, v___x_3905_);
lean_ctor_set(v___x_3906_, 4, v___x_3905_);
lean_ctor_set(v___x_3906_, 5, v___x_3905_);
return v___x_3906_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3907_, lean_object* v_b_3908_, uint8_t v_kind_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_){
_start:
{
lean_object* v_currNamespace_3914_; lean_object* v___x_3915_; lean_object* v_env_3916_; lean_object* v_nextMacroScope_3917_; lean_object* v_ngen_3918_; lean_object* v_auxDeclNGen_3919_; lean_object* v_traceState_3920_; lean_object* v_messages_3921_; lean_object* v_infoState_3922_; lean_object* v_snapshotTasks_3923_; lean_object* v___x_3925_; uint8_t v_isShared_3926_; uint8_t v_isSharedCheck_3950_; 
v_currNamespace_3914_ = lean_ctor_get(v___y_3911_, 6);
v___x_3915_ = lean_st_ref_take(v___y_3912_);
v_env_3916_ = lean_ctor_get(v___x_3915_, 0);
v_nextMacroScope_3917_ = lean_ctor_get(v___x_3915_, 1);
v_ngen_3918_ = lean_ctor_get(v___x_3915_, 2);
v_auxDeclNGen_3919_ = lean_ctor_get(v___x_3915_, 3);
v_traceState_3920_ = lean_ctor_get(v___x_3915_, 4);
v_messages_3921_ = lean_ctor_get(v___x_3915_, 6);
v_infoState_3922_ = lean_ctor_get(v___x_3915_, 7);
v_snapshotTasks_3923_ = lean_ctor_get(v___x_3915_, 8);
v_isSharedCheck_3950_ = !lean_is_exclusive(v___x_3915_);
if (v_isSharedCheck_3950_ == 0)
{
lean_object* v_unused_3951_; 
v_unused_3951_ = lean_ctor_get(v___x_3915_, 5);
lean_dec(v_unused_3951_);
v___x_3925_ = v___x_3915_;
v_isShared_3926_ = v_isSharedCheck_3950_;
goto v_resetjp_3924_;
}
else
{
lean_inc(v_snapshotTasks_3923_);
lean_inc(v_infoState_3922_);
lean_inc(v_messages_3921_);
lean_inc(v_traceState_3920_);
lean_inc(v_auxDeclNGen_3919_);
lean_inc(v_ngen_3918_);
lean_inc(v_nextMacroScope_3917_);
lean_inc(v_env_3916_);
lean_dec(v___x_3915_);
v___x_3925_ = lean_box(0);
v_isShared_3926_ = v_isSharedCheck_3950_;
goto v_resetjp_3924_;
}
v_resetjp_3924_:
{
lean_object* v___x_3927_; lean_object* v___x_3928_; lean_object* v___x_3930_; 
lean_inc(v_currNamespace_3914_);
v___x_3927_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3916_, v_ext_3907_, v_b_3908_, v_kind_3909_, v_currNamespace_3914_);
v___x_3928_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3926_ == 0)
{
lean_ctor_set(v___x_3925_, 5, v___x_3928_);
lean_ctor_set(v___x_3925_, 0, v___x_3927_);
v___x_3930_ = v___x_3925_;
goto v_reusejp_3929_;
}
else
{
lean_object* v_reuseFailAlloc_3949_; 
v_reuseFailAlloc_3949_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3949_, 0, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3949_, 1, v_nextMacroScope_3917_);
lean_ctor_set(v_reuseFailAlloc_3949_, 2, v_ngen_3918_);
lean_ctor_set(v_reuseFailAlloc_3949_, 3, v_auxDeclNGen_3919_);
lean_ctor_set(v_reuseFailAlloc_3949_, 4, v_traceState_3920_);
lean_ctor_set(v_reuseFailAlloc_3949_, 5, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_3949_, 6, v_messages_3921_);
lean_ctor_set(v_reuseFailAlloc_3949_, 7, v_infoState_3922_);
lean_ctor_set(v_reuseFailAlloc_3949_, 8, v_snapshotTasks_3923_);
v___x_3930_ = v_reuseFailAlloc_3949_;
goto v_reusejp_3929_;
}
v_reusejp_3929_:
{
lean_object* v___x_3931_; lean_object* v___x_3932_; lean_object* v_mctx_3933_; lean_object* v_zetaDeltaFVarIds_3934_; lean_object* v_postponed_3935_; lean_object* v_diag_3936_; lean_object* v___x_3938_; uint8_t v_isShared_3939_; uint8_t v_isSharedCheck_3947_; 
v___x_3931_ = lean_st_ref_put(v___y_3912_, v___x_3930_);
v___x_3932_ = lean_st_ref_take(v___y_3910_);
v_mctx_3933_ = lean_ctor_get(v___x_3932_, 0);
v_zetaDeltaFVarIds_3934_ = lean_ctor_get(v___x_3932_, 2);
v_postponed_3935_ = lean_ctor_get(v___x_3932_, 3);
v_diag_3936_ = lean_ctor_get(v___x_3932_, 4);
v_isSharedCheck_3947_ = !lean_is_exclusive(v___x_3932_);
if (v_isSharedCheck_3947_ == 0)
{
lean_object* v_unused_3948_; 
v_unused_3948_ = lean_ctor_get(v___x_3932_, 1);
lean_dec(v_unused_3948_);
v___x_3938_ = v___x_3932_;
v_isShared_3939_ = v_isSharedCheck_3947_;
goto v_resetjp_3937_;
}
else
{
lean_inc(v_diag_3936_);
lean_inc(v_postponed_3935_);
lean_inc(v_zetaDeltaFVarIds_3934_);
lean_inc(v_mctx_3933_);
lean_dec(v___x_3932_);
v___x_3938_ = lean_box(0);
v_isShared_3939_ = v_isSharedCheck_3947_;
goto v_resetjp_3937_;
}
v_resetjp_3937_:
{
lean_object* v___x_3940_; lean_object* v___x_3942_; 
v___x_3940_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3939_ == 0)
{
lean_ctor_set(v___x_3938_, 1, v___x_3940_);
v___x_3942_ = v___x_3938_;
goto v_reusejp_3941_;
}
else
{
lean_object* v_reuseFailAlloc_3946_; 
v_reuseFailAlloc_3946_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3946_, 0, v_mctx_3933_);
lean_ctor_set(v_reuseFailAlloc_3946_, 1, v___x_3940_);
lean_ctor_set(v_reuseFailAlloc_3946_, 2, v_zetaDeltaFVarIds_3934_);
lean_ctor_set(v_reuseFailAlloc_3946_, 3, v_postponed_3935_);
lean_ctor_set(v_reuseFailAlloc_3946_, 4, v_diag_3936_);
v___x_3942_ = v_reuseFailAlloc_3946_;
goto v_reusejp_3941_;
}
v_reusejp_3941_:
{
lean_object* v___x_3943_; lean_object* v___x_3944_; lean_object* v___x_3945_; 
v___x_3943_ = lean_st_ref_put(v___y_3910_, v___x_3942_);
v___x_3944_ = lean_box(0);
v___x_3945_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3945_, 0, v___x_3944_);
return v___x_3945_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3952_, lean_object* v_b_3953_, lean_object* v_kind_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_){
_start:
{
uint8_t v_kind_boxed_3959_; lean_object* v_res_3960_; 
v_kind_boxed_3959_ = lean_unbox(v_kind_3954_);
v_res_3960_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3952_, v_b_3953_, v_kind_boxed_3959_, v___y_3955_, v___y_3956_, v___y_3957_);
lean_dec(v___y_3957_);
lean_dec_ref(v___y_3956_);
lean_dec(v___y_3955_);
return v_res_3960_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3961_, lean_object* v_00_u03b2_3962_, lean_object* v_00_u03c3_3963_, lean_object* v_ext_3964_, lean_object* v_b_3965_, uint8_t v_kind_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_){
_start:
{
lean_object* v___x_3972_; 
v___x_3972_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3964_, v_b_3965_, v_kind_3966_, v___y_3968_, v___y_3969_, v___y_3970_);
return v___x_3972_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_3973_, lean_object* v_00_u03b2_3974_, lean_object* v_00_u03c3_3975_, lean_object* v_ext_3976_, lean_object* v_b_3977_, lean_object* v_kind_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_){
_start:
{
uint8_t v_kind_boxed_3984_; lean_object* v_res_3985_; 
v_kind_boxed_3984_ = lean_unbox(v_kind_3978_);
v_res_3985_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_3973_, v_00_u03b2_3974_, v_00_u03c3_3975_, v_ext_3976_, v_b_3977_, v_kind_boxed_3984_, v___y_3979_, v___y_3980_, v___y_3981_, v___y_3982_);
lean_dec(v___y_3982_);
lean_dec_ref(v___y_3981_);
lean_dec(v___y_3980_);
lean_dec_ref(v___y_3979_);
return v_res_3985_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_3986_, lean_object* v___y_3987_){
_start:
{
lean_object* v___x_3989_; lean_object* v_env_3990_; uint8_t v___x_3991_; lean_object* v___x_3992_; lean_object* v___x_3993_; 
v___x_3989_ = lean_st_ref_get(v___y_3987_);
v_env_3990_ = lean_ctor_get(v___x_3989_, 0);
lean_inc_ref(v_env_3990_);
lean_dec(v___x_3989_);
v___x_3991_ = l_Lean_getReducibilityStatusCore(v_env_3990_, v_declName_3986_);
v___x_3992_ = lean_box(v___x_3991_);
v___x_3993_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3993_, 0, v___x_3992_);
return v___x_3993_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_3994_, lean_object* v___y_3995_, lean_object* v___y_3996_){
_start:
{
lean_object* v_res_3997_; 
v_res_3997_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3994_, v___y_3995_);
lean_dec(v___y_3995_);
return v_res_3997_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_){
_start:
{
lean_object* v___x_4004_; 
v___x_4004_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3998_, v___y_4002_);
return v___x_4004_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
lean_object* v_res_4011_; 
v_res_4011_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_4005_, v___y_4006_, v___y_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
lean_dec_ref(v___y_4006_);
return v_res_4011_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_4012_, lean_object* v_msg_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_){
_start:
{
lean_object* v_fileName_4019_; lean_object* v_fileMap_4020_; lean_object* v_options_4021_; lean_object* v_currRecDepth_4022_; lean_object* v_maxRecDepth_4023_; lean_object* v_ref_4024_; lean_object* v_currNamespace_4025_; lean_object* v_openDecls_4026_; lean_object* v_initHeartbeats_4027_; lean_object* v_maxHeartbeats_4028_; lean_object* v_quotContext_4029_; lean_object* v_currMacroScope_4030_; uint8_t v_diag_4031_; lean_object* v_cancelTk_x3f_4032_; uint8_t v_suppressElabErrors_4033_; lean_object* v_inheritedTraceOptions_4034_; lean_object* v_ref_4035_; lean_object* v___x_4036_; lean_object* v___x_4037_; 
v_fileName_4019_ = lean_ctor_get(v___y_4016_, 0);
v_fileMap_4020_ = lean_ctor_get(v___y_4016_, 1);
v_options_4021_ = lean_ctor_get(v___y_4016_, 2);
v_currRecDepth_4022_ = lean_ctor_get(v___y_4016_, 3);
v_maxRecDepth_4023_ = lean_ctor_get(v___y_4016_, 4);
v_ref_4024_ = lean_ctor_get(v___y_4016_, 5);
v_currNamespace_4025_ = lean_ctor_get(v___y_4016_, 6);
v_openDecls_4026_ = lean_ctor_get(v___y_4016_, 7);
v_initHeartbeats_4027_ = lean_ctor_get(v___y_4016_, 8);
v_maxHeartbeats_4028_ = lean_ctor_get(v___y_4016_, 9);
v_quotContext_4029_ = lean_ctor_get(v___y_4016_, 10);
v_currMacroScope_4030_ = lean_ctor_get(v___y_4016_, 11);
v_diag_4031_ = lean_ctor_get_uint8(v___y_4016_, sizeof(void*)*14);
v_cancelTk_x3f_4032_ = lean_ctor_get(v___y_4016_, 12);
v_suppressElabErrors_4033_ = lean_ctor_get_uint8(v___y_4016_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4034_ = lean_ctor_get(v___y_4016_, 13);
v_ref_4035_ = l_Lean_replaceRef(v_ref_4012_, v_ref_4024_);
lean_inc_ref(v_inheritedTraceOptions_4034_);
lean_inc(v_cancelTk_x3f_4032_);
lean_inc(v_currMacroScope_4030_);
lean_inc(v_quotContext_4029_);
lean_inc(v_maxHeartbeats_4028_);
lean_inc(v_initHeartbeats_4027_);
lean_inc(v_openDecls_4026_);
lean_inc(v_currNamespace_4025_);
lean_inc(v_maxRecDepth_4023_);
lean_inc(v_currRecDepth_4022_);
lean_inc_ref(v_options_4021_);
lean_inc_ref(v_fileMap_4020_);
lean_inc_ref(v_fileName_4019_);
v___x_4036_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4036_, 0, v_fileName_4019_);
lean_ctor_set(v___x_4036_, 1, v_fileMap_4020_);
lean_ctor_set(v___x_4036_, 2, v_options_4021_);
lean_ctor_set(v___x_4036_, 3, v_currRecDepth_4022_);
lean_ctor_set(v___x_4036_, 4, v_maxRecDepth_4023_);
lean_ctor_set(v___x_4036_, 5, v_ref_4035_);
lean_ctor_set(v___x_4036_, 6, v_currNamespace_4025_);
lean_ctor_set(v___x_4036_, 7, v_openDecls_4026_);
lean_ctor_set(v___x_4036_, 8, v_initHeartbeats_4027_);
lean_ctor_set(v___x_4036_, 9, v_maxHeartbeats_4028_);
lean_ctor_set(v___x_4036_, 10, v_quotContext_4029_);
lean_ctor_set(v___x_4036_, 11, v_currMacroScope_4030_);
lean_ctor_set(v___x_4036_, 12, v_cancelTk_x3f_4032_);
lean_ctor_set(v___x_4036_, 13, v_inheritedTraceOptions_4034_);
lean_ctor_set_uint8(v___x_4036_, sizeof(void*)*14, v_diag_4031_);
lean_ctor_set_uint8(v___x_4036_, sizeof(void*)*14 + 1, v_suppressElabErrors_4033_);
v___x_4037_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_4013_, v___y_4014_, v___y_4015_, v___x_4036_, v___y_4017_);
lean_dec_ref_known(v___x_4036_, 14);
return v___x_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_4038_, lean_object* v_msg_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_){
_start:
{
lean_object* v_res_4045_; 
v_res_4045_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4038_, v_msg_4039_, v___y_4040_, v___y_4041_, v___y_4042_, v___y_4043_);
lean_dec(v___y_4043_);
lean_dec_ref(v___y_4042_);
lean_dec(v___y_4041_);
lean_dec_ref(v___y_4040_);
lean_dec(v_ref_4038_);
return v_res_4045_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_4046_; 
v___x_4046_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4046_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_4047_; lean_object* v___x_4048_; 
v___x_4047_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4048_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4048_, 0, v___x_4047_);
return v___x_4048_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_4049_; lean_object* v___x_4050_; lean_object* v___x_4051_; 
v___x_4049_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4050_ = lean_unsigned_to_nat(0u);
v___x_4051_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4051_, 0, v___x_4050_);
lean_ctor_set(v___x_4051_, 1, v___x_4050_);
lean_ctor_set(v___x_4051_, 2, v___x_4050_);
lean_ctor_set(v___x_4051_, 3, v___x_4050_);
lean_ctor_set(v___x_4051_, 4, v___x_4049_);
lean_ctor_set(v___x_4051_, 5, v___x_4049_);
lean_ctor_set(v___x_4051_, 6, v___x_4049_);
lean_ctor_set(v___x_4051_, 7, v___x_4049_);
lean_ctor_set(v___x_4051_, 8, v___x_4049_);
lean_ctor_set(v___x_4051_, 9, v___x_4049_);
lean_ctor_set(v___x_4051_, 10, v___x_4049_);
return v___x_4051_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_4052_; lean_object* v___x_4053_; lean_object* v___x_4054_; 
v___x_4052_ = lean_unsigned_to_nat(32u);
v___x_4053_ = lean_mk_empty_array_with_capacity(v___x_4052_);
v___x_4054_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4054_, 0, v___x_4053_);
return v___x_4054_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; 
v___x_4055_ = ((size_t)5ULL);
v___x_4056_ = lean_unsigned_to_nat(0u);
v___x_4057_ = lean_unsigned_to_nat(32u);
v___x_4058_ = lean_mk_empty_array_with_capacity(v___x_4057_);
v___x_4059_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4060_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4060_, 0, v___x_4059_);
lean_ctor_set(v___x_4060_, 1, v___x_4058_);
lean_ctor_set(v___x_4060_, 2, v___x_4056_);
lean_ctor_set(v___x_4060_, 3, v___x_4056_);
lean_ctor_set_usize(v___x_4060_, 4, v___x_4055_);
return v___x_4060_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; 
v___x_4061_ = lean_box(1);
v___x_4062_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_4063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4064_, 0, v___x_4063_);
lean_ctor_set(v___x_4064_, 1, v___x_4062_);
lean_ctor_set(v___x_4064_, 2, v___x_4061_);
return v___x_4064_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_4066_; lean_object* v___x_4067_; 
v___x_4066_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_4067_ = l_Lean_stringToMessageData(v___x_4066_);
return v___x_4067_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_4069_; lean_object* v___x_4070_; 
v___x_4069_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_4070_ = l_Lean_stringToMessageData(v___x_4069_);
return v___x_4070_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_4072_; lean_object* v___x_4073_; 
v___x_4072_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_4073_ = l_Lean_stringToMessageData(v___x_4072_);
return v___x_4073_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_4075_; lean_object* v___x_4076_; 
v___x_4075_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_4076_ = l_Lean_stringToMessageData(v___x_4075_);
return v___x_4076_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_4078_; lean_object* v___x_4079_; 
v___x_4078_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_4079_ = l_Lean_stringToMessageData(v___x_4078_);
return v___x_4079_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_4081_; lean_object* v___x_4082_; 
v___x_4081_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_4082_ = l_Lean_stringToMessageData(v___x_4081_);
return v___x_4082_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_4084_; lean_object* v___x_4085_; 
v___x_4084_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_4085_ = l_Lean_stringToMessageData(v___x_4084_);
return v___x_4085_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_4086_, lean_object* v_declHint_4087_, lean_object* v___y_4088_){
_start:
{
lean_object* v___x_4090_; lean_object* v_env_4091_; uint8_t v___x_4092_; 
v___x_4090_ = lean_st_ref_get(v___y_4088_);
v_env_4091_ = lean_ctor_get(v___x_4090_, 0);
lean_inc_ref(v_env_4091_);
lean_dec(v___x_4090_);
v___x_4092_ = l_Lean_Name_isAnonymous(v_declHint_4087_);
if (v___x_4092_ == 0)
{
uint8_t v_isExporting_4093_; 
v_isExporting_4093_ = lean_ctor_get_uint8(v_env_4091_, sizeof(void*)*8);
if (v_isExporting_4093_ == 0)
{
lean_object* v___x_4094_; 
lean_dec_ref(v_env_4091_);
lean_dec(v_declHint_4087_);
v___x_4094_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4094_, 0, v_msg_4086_);
return v___x_4094_;
}
else
{
lean_object* v___x_4095_; uint8_t v___x_4096_; 
lean_inc_ref(v_env_4091_);
v___x_4095_ = l_Lean_Environment_setExporting(v_env_4091_, v___x_4092_);
lean_inc(v_declHint_4087_);
lean_inc_ref(v___x_4095_);
v___x_4096_ = l_Lean_Environment_contains(v___x_4095_, v_declHint_4087_, v_isExporting_4093_);
if (v___x_4096_ == 0)
{
lean_object* v___x_4097_; 
lean_dec_ref(v___x_4095_);
lean_dec_ref(v_env_4091_);
lean_dec(v_declHint_4087_);
v___x_4097_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4097_, 0, v_msg_4086_);
return v___x_4097_;
}
else
{
lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v_c_4103_; lean_object* v___x_4104_; 
v___x_4098_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_4100_ = l_Lean_Options_empty;
v___x_4101_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4101_, 0, v___x_4095_);
lean_ctor_set(v___x_4101_, 1, v___x_4098_);
lean_ctor_set(v___x_4101_, 2, v___x_4099_);
lean_ctor_set(v___x_4101_, 3, v___x_4100_);
lean_inc(v_declHint_4087_);
v___x_4102_ = l_Lean_MessageData_ofConstName(v_declHint_4087_, v___x_4092_);
v_c_4103_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4103_, 0, v___x_4101_);
lean_ctor_set(v_c_4103_, 1, v___x_4102_);
v___x_4104_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4091_, v_declHint_4087_);
if (lean_obj_tag(v___x_4104_) == 0)
{
lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; 
lean_dec_ref(v_env_4091_);
lean_dec(v_declHint_4087_);
v___x_4105_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4106_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4105_);
lean_ctor_set(v___x_4106_, 1, v_c_4103_);
v___x_4107_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_4108_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4108_, 0, v___x_4106_);
lean_ctor_set(v___x_4108_, 1, v___x_4107_);
v___x_4109_ = l_Lean_MessageData_note(v___x_4108_);
v___x_4110_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4110_, 0, v_msg_4086_);
lean_ctor_set(v___x_4110_, 1, v___x_4109_);
v___x_4111_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4111_, 0, v___x_4110_);
return v___x_4111_;
}
else
{
lean_object* v_val_4112_; lean_object* v___x_4114_; uint8_t v_isShared_4115_; uint8_t v_isSharedCheck_4147_; 
v_val_4112_ = lean_ctor_get(v___x_4104_, 0);
v_isSharedCheck_4147_ = !lean_is_exclusive(v___x_4104_);
if (v_isSharedCheck_4147_ == 0)
{
v___x_4114_ = v___x_4104_;
v_isShared_4115_ = v_isSharedCheck_4147_;
goto v_resetjp_4113_;
}
else
{
lean_inc(v_val_4112_);
lean_dec(v___x_4104_);
v___x_4114_ = lean_box(0);
v_isShared_4115_ = v_isSharedCheck_4147_;
goto v_resetjp_4113_;
}
v_resetjp_4113_:
{
lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v_mod_4119_; uint8_t v___x_4120_; 
v___x_4116_ = lean_box(0);
v___x_4117_ = l_Lean_Environment_header(v_env_4091_);
lean_dec_ref(v_env_4091_);
v___x_4118_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4117_);
v_mod_4119_ = lean_array_get(v___x_4116_, v___x_4118_, v_val_4112_);
lean_dec(v_val_4112_);
lean_dec_ref(v___x_4118_);
v___x_4120_ = l_Lean_isPrivateName(v_declHint_4087_);
lean_dec(v_declHint_4087_);
if (v___x_4120_ == 0)
{
lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4132_; 
v___x_4121_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_4122_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4122_, 0, v___x_4121_);
lean_ctor_set(v___x_4122_, 1, v_c_4103_);
v___x_4123_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_4124_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4124_, 0, v___x_4122_);
lean_ctor_set(v___x_4124_, 1, v___x_4123_);
v___x_4125_ = l_Lean_MessageData_ofName(v_mod_4119_);
v___x_4126_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4126_, 0, v___x_4124_);
lean_ctor_set(v___x_4126_, 1, v___x_4125_);
v___x_4127_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_4128_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4128_, 0, v___x_4126_);
lean_ctor_set(v___x_4128_, 1, v___x_4127_);
v___x_4129_ = l_Lean_MessageData_note(v___x_4128_);
v___x_4130_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4130_, 0, v_msg_4086_);
lean_ctor_set(v___x_4130_, 1, v___x_4129_);
if (v_isShared_4115_ == 0)
{
lean_ctor_set_tag(v___x_4114_, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4130_);
v___x_4132_ = v___x_4114_;
goto v_reusejp_4131_;
}
else
{
lean_object* v_reuseFailAlloc_4133_; 
v_reuseFailAlloc_4133_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4133_, 0, v___x_4130_);
v___x_4132_ = v_reuseFailAlloc_4133_;
goto v_reusejp_4131_;
}
v_reusejp_4131_:
{
return v___x_4132_;
}
}
else
{
lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4145_; 
v___x_4134_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4135_, 0, v___x_4134_);
lean_ctor_set(v___x_4135_, 1, v_c_4103_);
v___x_4136_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_4137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4137_, 0, v___x_4135_);
lean_ctor_set(v___x_4137_, 1, v___x_4136_);
v___x_4138_ = l_Lean_MessageData_ofName(v_mod_4119_);
v___x_4139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4139_, 0, v___x_4137_);
lean_ctor_set(v___x_4139_, 1, v___x_4138_);
v___x_4140_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_4141_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4141_, 0, v___x_4139_);
lean_ctor_set(v___x_4141_, 1, v___x_4140_);
v___x_4142_ = l_Lean_MessageData_note(v___x_4141_);
v___x_4143_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4143_, 0, v_msg_4086_);
lean_ctor_set(v___x_4143_, 1, v___x_4142_);
if (v_isShared_4115_ == 0)
{
lean_ctor_set_tag(v___x_4114_, 0);
lean_ctor_set(v___x_4114_, 0, v___x_4143_);
v___x_4145_ = v___x_4114_;
goto v_reusejp_4144_;
}
else
{
lean_object* v_reuseFailAlloc_4146_; 
v_reuseFailAlloc_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4146_, 0, v___x_4143_);
v___x_4145_ = v_reuseFailAlloc_4146_;
goto v_reusejp_4144_;
}
v_reusejp_4144_:
{
return v___x_4145_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4148_; 
lean_dec_ref(v_env_4091_);
lean_dec(v_declHint_4087_);
v___x_4148_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4148_, 0, v_msg_4086_);
return v___x_4148_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_4149_, lean_object* v_declHint_4150_, lean_object* v___y_4151_, lean_object* v___y_4152_){
_start:
{
lean_object* v_res_4153_; 
v_res_4153_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4149_, v_declHint_4150_, v___y_4151_);
lean_dec(v___y_4151_);
return v_res_4153_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(lean_object* v_msg_4154_, lean_object* v_declHint_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_){
_start:
{
lean_object* v___x_4161_; lean_object* v_a_4162_; lean_object* v___x_4164_; uint8_t v_isShared_4165_; uint8_t v_isSharedCheck_4171_; 
v___x_4161_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4154_, v_declHint_4155_, v___y_4159_);
v_a_4162_ = lean_ctor_get(v___x_4161_, 0);
v_isSharedCheck_4171_ = !lean_is_exclusive(v___x_4161_);
if (v_isSharedCheck_4171_ == 0)
{
v___x_4164_ = v___x_4161_;
v_isShared_4165_ = v_isSharedCheck_4171_;
goto v_resetjp_4163_;
}
else
{
lean_inc(v_a_4162_);
lean_dec(v___x_4161_);
v___x_4164_ = lean_box(0);
v_isShared_4165_ = v_isSharedCheck_4171_;
goto v_resetjp_4163_;
}
v_resetjp_4163_:
{
lean_object* v___x_4166_; lean_object* v___x_4167_; lean_object* v___x_4169_; 
v___x_4166_ = l_Lean_unknownIdentifierMessageTag;
v___x_4167_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4166_);
lean_ctor_set(v___x_4167_, 1, v_a_4162_);
if (v_isShared_4165_ == 0)
{
lean_ctor_set(v___x_4164_, 0, v___x_4167_);
v___x_4169_ = v___x_4164_;
goto v_reusejp_4168_;
}
else
{
lean_object* v_reuseFailAlloc_4170_; 
v_reuseFailAlloc_4170_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4170_, 0, v___x_4167_);
v___x_4169_ = v_reuseFailAlloc_4170_;
goto v_reusejp_4168_;
}
v_reusejp_4168_:
{
return v___x_4169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_4172_, lean_object* v_declHint_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_){
_start:
{
lean_object* v_res_4179_; 
v_res_4179_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4172_, v_declHint_4173_, v___y_4174_, v___y_4175_, v___y_4176_, v___y_4177_);
lean_dec(v___y_4177_);
lean_dec_ref(v___y_4176_);
lean_dec(v___y_4175_);
lean_dec_ref(v___y_4174_);
return v_res_4179_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_ref_4180_, lean_object* v_msg_4181_, lean_object* v_declHint_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_){
_start:
{
lean_object* v___x_4188_; lean_object* v_a_4189_; lean_object* v___x_4190_; 
v___x_4188_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4181_, v_declHint_4182_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
v_a_4189_ = lean_ctor_get(v___x_4188_, 0);
lean_inc(v_a_4189_);
lean_dec_ref(v___x_4188_);
v___x_4190_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4180_, v_a_4189_, v___y_4183_, v___y_4184_, v___y_4185_, v___y_4186_);
return v___x_4190_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_ref_4191_, lean_object* v_msg_4192_, lean_object* v_declHint_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_){
_start:
{
lean_object* v_res_4199_; 
v_res_4199_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4191_, v_msg_4192_, v_declHint_4193_, v___y_4194_, v___y_4195_, v___y_4196_, v___y_4197_);
lean_dec(v___y_4197_);
lean_dec_ref(v___y_4196_);
lean_dec(v___y_4195_);
lean_dec_ref(v___y_4194_);
lean_dec(v_ref_4191_);
return v_res_4199_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_4201_; lean_object* v___x_4202_; 
v___x_4201_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_4202_ = l_Lean_stringToMessageData(v___x_4201_);
return v___x_4202_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_4203_, lean_object* v_constName_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_){
_start:
{
lean_object* v___x_4210_; uint8_t v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; 
v___x_4210_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_4211_ = 0;
lean_inc(v_constName_4204_);
v___x_4212_ = l_Lean_MessageData_ofConstName(v_constName_4204_, v___x_4211_);
v___x_4213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4213_, 0, v___x_4210_);
lean_ctor_set(v___x_4213_, 1, v___x_4212_);
v___x_4214_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4215_, 0, v___x_4213_);
lean_ctor_set(v___x_4215_, 1, v___x_4214_);
v___x_4216_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4203_, v___x_4215_, v_constName_4204_, v___y_4205_, v___y_4206_, v___y_4207_, v___y_4208_);
return v___x_4216_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_4217_, lean_object* v_constName_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_){
_start:
{
lean_object* v_res_4224_; 
v_res_4224_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4217_, v_constName_4218_, v___y_4219_, v___y_4220_, v___y_4221_, v___y_4222_);
lean_dec(v___y_4222_);
lean_dec_ref(v___y_4221_);
lean_dec(v___y_4220_);
lean_dec_ref(v___y_4219_);
lean_dec(v_ref_4217_);
return v_res_4224_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_){
_start:
{
lean_object* v_ref_4231_; lean_object* v___x_4232_; 
v_ref_4231_ = lean_ctor_get(v___y_4228_, 5);
v___x_4232_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4231_, v_constName_4225_, v___y_4226_, v___y_4227_, v___y_4228_, v___y_4229_);
return v___x_4232_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_){
_start:
{
lean_object* v_res_4239_; 
v_res_4239_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4233_, v___y_4234_, v___y_4235_, v___y_4236_, v___y_4237_);
lean_dec(v___y_4237_);
lean_dec_ref(v___y_4236_);
lean_dec(v___y_4235_);
lean_dec_ref(v___y_4234_);
return v_res_4239_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_){
_start:
{
lean_object* v___x_4246_; lean_object* v_env_4247_; uint8_t v___x_4248_; lean_object* v___x_4249_; 
v___x_4246_ = lean_st_ref_get(v___y_4244_);
v_env_4247_ = lean_ctor_get(v___x_4246_, 0);
lean_inc_ref(v_env_4247_);
lean_dec(v___x_4246_);
v___x_4248_ = 0;
lean_inc(v_constName_4240_);
v___x_4249_ = l_Lean_Environment_find_x3f(v_env_4247_, v_constName_4240_, v___x_4248_);
if (lean_obj_tag(v___x_4249_) == 0)
{
lean_object* v___x_4250_; 
v___x_4250_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4240_, v___y_4241_, v___y_4242_, v___y_4243_, v___y_4244_);
return v___x_4250_;
}
else
{
lean_object* v_val_4251_; lean_object* v___x_4253_; uint8_t v_isShared_4254_; uint8_t v_isSharedCheck_4258_; 
lean_dec(v_constName_4240_);
v_val_4251_ = lean_ctor_get(v___x_4249_, 0);
v_isSharedCheck_4258_ = !lean_is_exclusive(v___x_4249_);
if (v_isSharedCheck_4258_ == 0)
{
v___x_4253_ = v___x_4249_;
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
else
{
lean_inc(v_val_4251_);
lean_dec(v___x_4249_);
v___x_4253_ = lean_box(0);
v_isShared_4254_ = v_isSharedCheck_4258_;
goto v_resetjp_4252_;
}
v_resetjp_4252_:
{
lean_object* v___x_4256_; 
if (v_isShared_4254_ == 0)
{
lean_ctor_set_tag(v___x_4253_, 0);
v___x_4256_ = v___x_4253_;
goto v_reusejp_4255_;
}
else
{
lean_object* v_reuseFailAlloc_4257_; 
v_reuseFailAlloc_4257_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4257_, 0, v_val_4251_);
v___x_4256_ = v_reuseFailAlloc_4257_;
goto v_reusejp_4255_;
}
v_reusejp_4255_:
{
return v___x_4256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_){
_start:
{
lean_object* v_res_4265_; 
v_res_4265_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
lean_dec(v___y_4263_);
lean_dec_ref(v___y_4262_);
lean_dec(v___y_4261_);
lean_dec_ref(v___y_4260_);
return v_res_4265_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_){
_start:
{
lean_object* v___x_4272_; lean_object* v_env_4273_; uint8_t v___x_4274_; lean_object* v___x_4275_; 
v___x_4272_ = lean_st_ref_get(v___y_4270_);
v_env_4273_ = lean_ctor_get(v___x_4272_, 0);
lean_inc_ref(v_env_4273_);
lean_dec(v___x_4272_);
v___x_4274_ = 0;
lean_inc(v_constName_4266_);
v___x_4275_ = l_Lean_Environment_findConstVal_x3f(v_env_4273_, v_constName_4266_, v___x_4274_);
if (lean_obj_tag(v___x_4275_) == 0)
{
lean_object* v___x_4276_; 
v___x_4276_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4266_, v___y_4267_, v___y_4268_, v___y_4269_, v___y_4270_);
return v___x_4276_;
}
else
{
lean_object* v_val_4277_; lean_object* v___x_4279_; uint8_t v_isShared_4280_; uint8_t v_isSharedCheck_4284_; 
lean_dec(v_constName_4266_);
v_val_4277_ = lean_ctor_get(v___x_4275_, 0);
v_isSharedCheck_4284_ = !lean_is_exclusive(v___x_4275_);
if (v_isSharedCheck_4284_ == 0)
{
v___x_4279_ = v___x_4275_;
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
else
{
lean_inc(v_val_4277_);
lean_dec(v___x_4275_);
v___x_4279_ = lean_box(0);
v_isShared_4280_ = v_isSharedCheck_4284_;
goto v_resetjp_4278_;
}
v_resetjp_4278_:
{
lean_object* v___x_4282_; 
if (v_isShared_4280_ == 0)
{
lean_ctor_set_tag(v___x_4279_, 0);
v___x_4282_ = v___x_4279_;
goto v_reusejp_4281_;
}
else
{
lean_object* v_reuseFailAlloc_4283_; 
v_reuseFailAlloc_4283_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4283_, 0, v_val_4277_);
v___x_4282_ = v_reuseFailAlloc_4283_;
goto v_reusejp_4281_;
}
v_reusejp_4281_:
{
return v___x_4282_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_){
_start:
{
lean_object* v_res_4291_; 
v_res_4291_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4285_, v___y_4286_, v___y_4287_, v___y_4288_, v___y_4289_);
lean_dec(v___y_4289_);
lean_dec_ref(v___y_4288_);
lean_dec(v___y_4287_);
lean_dec_ref(v___y_4286_);
return v_res_4291_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4292_, lean_object* v_a_4293_){
_start:
{
if (lean_obj_tag(v_a_4292_) == 0)
{
lean_object* v___x_4294_; 
v___x_4294_ = l_List_reverse___redArg(v_a_4293_);
return v___x_4294_;
}
else
{
lean_object* v_head_4295_; lean_object* v_tail_4296_; lean_object* v___x_4298_; uint8_t v_isShared_4299_; uint8_t v_isSharedCheck_4305_; 
v_head_4295_ = lean_ctor_get(v_a_4292_, 0);
v_tail_4296_ = lean_ctor_get(v_a_4292_, 1);
v_isSharedCheck_4305_ = !lean_is_exclusive(v_a_4292_);
if (v_isSharedCheck_4305_ == 0)
{
v___x_4298_ = v_a_4292_;
v_isShared_4299_ = v_isSharedCheck_4305_;
goto v_resetjp_4297_;
}
else
{
lean_inc(v_tail_4296_);
lean_inc(v_head_4295_);
lean_dec(v_a_4292_);
v___x_4298_ = lean_box(0);
v_isShared_4299_ = v_isSharedCheck_4305_;
goto v_resetjp_4297_;
}
v_resetjp_4297_:
{
lean_object* v___x_4300_; lean_object* v___x_4302_; 
v___x_4300_ = l_Lean_mkLevelParam(v_head_4295_);
if (v_isShared_4299_ == 0)
{
lean_ctor_set(v___x_4298_, 1, v_a_4293_);
lean_ctor_set(v___x_4298_, 0, v___x_4300_);
v___x_4302_ = v___x_4298_;
goto v_reusejp_4301_;
}
else
{
lean_object* v_reuseFailAlloc_4304_; 
v_reuseFailAlloc_4304_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4304_, 0, v___x_4300_);
lean_ctor_set(v_reuseFailAlloc_4304_, 1, v_a_4293_);
v___x_4302_ = v_reuseFailAlloc_4304_;
goto v_reusejp_4301_;
}
v_reusejp_4301_:
{
v_a_4292_ = v_tail_4296_;
v_a_4293_ = v___x_4302_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_){
_start:
{
lean_object* v___x_4312_; 
lean_inc(v_constName_4306_);
v___x_4312_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4306_, v___y_4307_, v___y_4308_, v___y_4309_, v___y_4310_);
if (lean_obj_tag(v___x_4312_) == 0)
{
lean_object* v_a_4313_; lean_object* v___x_4315_; uint8_t v_isShared_4316_; uint8_t v_isSharedCheck_4324_; 
v_a_4313_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4324_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4324_ == 0)
{
v___x_4315_ = v___x_4312_;
v_isShared_4316_ = v_isSharedCheck_4324_;
goto v_resetjp_4314_;
}
else
{
lean_inc(v_a_4313_);
lean_dec(v___x_4312_);
v___x_4315_ = lean_box(0);
v_isShared_4316_ = v_isSharedCheck_4324_;
goto v_resetjp_4314_;
}
v_resetjp_4314_:
{
lean_object* v_levelParams_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4322_; 
v_levelParams_4317_ = lean_ctor_get(v_a_4313_, 1);
lean_inc(v_levelParams_4317_);
lean_dec(v_a_4313_);
v___x_4318_ = lean_box(0);
v___x_4319_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4317_, v___x_4318_);
v___x_4320_ = l_Lean_mkConst(v_constName_4306_, v___x_4319_);
if (v_isShared_4316_ == 0)
{
lean_ctor_set(v___x_4315_, 0, v___x_4320_);
v___x_4322_ = v___x_4315_;
goto v_reusejp_4321_;
}
else
{
lean_object* v_reuseFailAlloc_4323_; 
v_reuseFailAlloc_4323_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4323_, 0, v___x_4320_);
v___x_4322_ = v_reuseFailAlloc_4323_;
goto v_reusejp_4321_;
}
v_reusejp_4321_:
{
return v___x_4322_;
}
}
}
else
{
lean_object* v_a_4325_; lean_object* v___x_4327_; uint8_t v_isShared_4328_; uint8_t v_isSharedCheck_4332_; 
lean_dec(v_constName_4306_);
v_a_4325_ = lean_ctor_get(v___x_4312_, 0);
v_isSharedCheck_4332_ = !lean_is_exclusive(v___x_4312_);
if (v_isSharedCheck_4332_ == 0)
{
v___x_4327_ = v___x_4312_;
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
else
{
lean_inc(v_a_4325_);
lean_dec(v___x_4312_);
v___x_4327_ = lean_box(0);
v_isShared_4328_ = v_isSharedCheck_4332_;
goto v_resetjp_4326_;
}
v_resetjp_4326_:
{
lean_object* v___x_4330_; 
if (v_isShared_4328_ == 0)
{
v___x_4330_ = v___x_4327_;
goto v_reusejp_4329_;
}
else
{
lean_object* v_reuseFailAlloc_4331_; 
v_reuseFailAlloc_4331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4331_, 0, v_a_4325_);
v___x_4330_ = v_reuseFailAlloc_4331_;
goto v_reusejp_4329_;
}
v_reusejp_4329_:
{
return v___x_4330_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_){
_start:
{
lean_object* v_res_4339_; 
v_res_4339_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4333_, v___y_4334_, v___y_4335_, v___y_4336_, v___y_4337_);
lean_dec(v___y_4337_);
lean_dec_ref(v___y_4336_);
lean_dec(v___y_4335_);
lean_dec_ref(v___y_4334_);
return v_res_4339_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4341_; lean_object* v___x_4342_; 
v___x_4341_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4342_ = l_Lean_stringToMessageData(v___x_4341_);
return v___x_4342_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4344_; lean_object* v___x_4345_; 
v___x_4344_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4345_ = l_Lean_stringToMessageData(v___x_4344_);
return v___x_4345_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_4347_; lean_object* v___x_4348_; 
v___x_4347_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_4348_ = l_Lean_stringToMessageData(v___x_4347_);
return v___x_4348_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__7(void){
_start:
{
lean_object* v___x_4350_; lean_object* v___x_4351_; 
v___x_4350_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__6));
v___x_4351_ = l_Lean_stringToMessageData(v___x_4350_);
return v___x_4351_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4352_, uint8_t v_attrKind_4353_, lean_object* v_prio_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_){
_start:
{
lean_object* v___x_4360_; 
lean_inc(v_declName_4352_);
v___x_4360_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4352_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
if (lean_obj_tag(v___x_4360_) == 0)
{
lean_object* v_a_4361_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___x_4439_; 
v_a_4361_ = lean_ctor_get(v___x_4360_, 0);
lean_inc(v_a_4361_);
lean_dec_ref_known(v___x_4360_, 1);
lean_inc(v_declName_4352_);
v___x_4439_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4352_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
if (lean_obj_tag(v___x_4439_) == 0)
{
lean_object* v_a_4440_; lean_object* v___x_4441_; uint8_t v___x_4442_; 
v_a_4440_ = lean_ctor_get(v___x_4439_, 0);
lean_inc(v_a_4440_);
lean_dec_ref_known(v___x_4439_, 1);
v___x_4441_ = l_Lean_ConstantInfo_type(v_a_4440_);
v___x_4442_ = l_Lean_Expr_hasSorry(v___x_4441_);
lean_dec_ref(v___x_4441_);
if (v___x_4442_ == 0)
{
lean_object* v___x_4443_; 
lean_inc(v_a_4361_);
v___x_4443_ = l_Lean_Meta_checkNonClassInstance(v_a_4361_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_object* v___x_4444_; 
lean_dec_ref_known(v___x_4443_, 1);
v___x_4444_ = l_Lean_Meta_checkImpossibleInstance(v_a_4440_, v_a_4355_, v_a_4356_, v_a_4357_, v_a_4358_);
lean_dec(v_a_4440_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_dec_ref_known(v___x_4444_, 1);
v___y_4391_ = v_a_4355_;
v___y_4392_ = v_a_4356_;
v___y_4393_ = v_a_4357_;
v___y_4394_ = v_a_4358_;
goto v___jp_4390_;
}
else
{
lean_dec(v_a_4361_);
lean_dec(v_prio_4354_);
lean_dec(v_declName_4352_);
return v___x_4444_;
}
}
else
{
lean_dec(v_a_4440_);
lean_dec(v_a_4361_);
lean_dec(v_prio_4354_);
lean_dec(v_declName_4352_);
return v___x_4443_;
}
}
else
{
lean_dec(v_a_4440_);
v___y_4391_ = v_a_4355_;
v___y_4392_ = v_a_4356_;
v___y_4393_ = v_a_4357_;
v___y_4394_ = v_a_4358_;
goto v___jp_4390_;
}
}
else
{
lean_object* v_a_4445_; lean_object* v___x_4447_; uint8_t v_isShared_4448_; uint8_t v_isSharedCheck_4452_; 
lean_dec(v_a_4361_);
lean_dec(v_prio_4354_);
lean_dec(v_declName_4352_);
v_a_4445_ = lean_ctor_get(v___x_4439_, 0);
v_isSharedCheck_4452_ = !lean_is_exclusive(v___x_4439_);
if (v_isSharedCheck_4452_ == 0)
{
v___x_4447_ = v___x_4439_;
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
else
{
lean_inc(v_a_4445_);
lean_dec(v___x_4439_);
v___x_4447_ = lean_box(0);
v_isShared_4448_ = v_isSharedCheck_4452_;
goto v_resetjp_4446_;
}
v_resetjp_4446_:
{
lean_object* v___x_4450_; 
if (v_isShared_4448_ == 0)
{
v___x_4450_ = v___x_4447_;
goto v_reusejp_4449_;
}
else
{
lean_object* v_reuseFailAlloc_4451_; 
v_reuseFailAlloc_4451_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4451_, 0, v_a_4445_);
v___x_4450_ = v_reuseFailAlloc_4451_;
goto v_reusejp_4449_;
}
v_reusejp_4449_:
{
return v___x_4450_;
}
}
}
v___jp_4362_:
{
lean_object* v___x_4368_; lean_object* v_a_4369_; lean_object* v___x_4371_; uint8_t v_isShared_4372_; uint8_t v_isSharedCheck_4389_; 
lean_inc(v_declName_4352_);
v___x_4368_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4352_, v___y_4367_);
v_a_4369_ = lean_ctor_get(v___x_4368_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4368_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4371_ = v___x_4368_;
v_isShared_4372_ = v_isSharedCheck_4389_;
goto v_resetjp_4370_;
}
else
{
lean_inc(v_a_4369_);
lean_dec(v___x_4368_);
v___x_4371_ = lean_box(0);
v_isShared_4372_ = v_isSharedCheck_4389_;
goto v_resetjp_4370_;
}
v_resetjp_4370_:
{
lean_object* v___x_4373_; 
lean_inc(v_a_4361_);
v___x_4373_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4361_, v_a_4369_, v___y_4364_, v___y_4365_, v___y_4366_, v___y_4367_);
if (lean_obj_tag(v___x_4373_) == 0)
{
lean_object* v_a_4374_; lean_object* v___x_4375_; lean_object* v___x_4377_; 
v_a_4374_ = lean_ctor_get(v___x_4373_, 0);
lean_inc(v_a_4374_);
lean_dec_ref_known(v___x_4373_, 1);
v___x_4375_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4372_ == 0)
{
lean_ctor_set_tag(v___x_4371_, 1);
lean_ctor_set(v___x_4371_, 0, v_declName_4352_);
v___x_4377_ = v___x_4371_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4380_; 
v_reuseFailAlloc_4380_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4380_, 0, v_declName_4352_);
v___x_4377_ = v_reuseFailAlloc_4380_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
lean_object* v___x_4378_; lean_object* v___x_4379_; 
v___x_4378_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4378_, 0, v___y_4363_);
lean_ctor_set(v___x_4378_, 1, v_a_4361_);
lean_ctor_set(v___x_4378_, 2, v_prio_4354_);
lean_ctor_set(v___x_4378_, 3, v___x_4377_);
lean_ctor_set(v___x_4378_, 4, v_a_4374_);
lean_ctor_set_uint8(v___x_4378_, sizeof(void*)*5, v_attrKind_4353_);
v___x_4379_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4375_, v___x_4378_, v_attrKind_4353_, v___y_4365_, v___y_4366_, v___y_4367_);
return v___x_4379_;
}
}
else
{
lean_object* v_a_4381_; lean_object* v___x_4383_; uint8_t v_isShared_4384_; uint8_t v_isSharedCheck_4388_; 
lean_del_object(v___x_4371_);
lean_dec_ref(v___y_4363_);
lean_dec(v_a_4361_);
lean_dec(v_prio_4354_);
lean_dec(v_declName_4352_);
v_a_4381_ = lean_ctor_get(v___x_4373_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4373_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4383_ = v___x_4373_;
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
else
{
lean_inc(v_a_4381_);
lean_dec(v___x_4373_);
v___x_4383_ = lean_box(0);
v_isShared_4384_ = v_isSharedCheck_4388_;
goto v_resetjp_4382_;
}
v_resetjp_4382_:
{
lean_object* v___x_4386_; 
if (v_isShared_4384_ == 0)
{
v___x_4386_ = v___x_4383_;
goto v_reusejp_4385_;
}
else
{
lean_object* v_reuseFailAlloc_4387_; 
v_reuseFailAlloc_4387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4387_, 0, v_a_4381_);
v___x_4386_ = v_reuseFailAlloc_4387_;
goto v_reusejp_4385_;
}
v_reusejp_4385_:
{
return v___x_4386_;
}
}
}
}
}
v___jp_4390_:
{
lean_object* v___x_4395_; 
lean_inc(v_a_4361_);
v___x_4395_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4361_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4395_) == 0)
{
lean_object* v_a_4396_; lean_object* v___x_4397_; lean_object* v_a_4398_; uint8_t v___x_4399_; uint8_t v___x_4400_; uint8_t v___x_4401_; 
v_a_4396_ = lean_ctor_get(v___x_4395_, 0);
lean_inc(v_a_4396_);
lean_dec_ref_known(v___x_4395_, 1);
lean_inc(v_declName_4352_);
v___x_4397_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4352_, v___y_4394_);
v_a_4398_ = lean_ctor_get(v___x_4397_, 0);
lean_inc(v_a_4398_);
lean_dec_ref(v___x_4397_);
v___x_4399_ = 1;
v___x_4400_ = lean_unbox(v_a_4398_);
lean_dec(v_a_4398_);
v___x_4401_ = l_Lean_instBEqReducibilityStatus_beq(v___x_4400_, v___x_4399_);
if (v___x_4401_ == 0)
{
v___y_4363_ = v_a_4396_;
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
goto v___jp_4362_;
}
else
{
lean_object* v___x_4402_; 
lean_inc(v_declName_4352_);
v___x_4402_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4352_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4402_) == 0)
{
lean_object* v_a_4403_; uint8_t v___x_4404_; 
v_a_4403_ = lean_ctor_get(v___x_4402_, 0);
lean_inc(v_a_4403_);
lean_dec_ref_known(v___x_4402_, 1);
v___x_4404_ = l_Lean_ConstantInfo_isDefinition(v_a_4403_);
lean_dec(v_a_4403_);
if (v___x_4404_ == 0)
{
lean_object* v___x_4405_; lean_object* v_env_4406_; uint8_t v___x_4407_; 
v___x_4405_ = lean_st_ref_get(v___y_4394_);
v_env_4406_ = lean_ctor_get(v___x_4405_, 0);
lean_inc_ref(v_env_4406_);
lean_dec(v___x_4405_);
lean_inc(v_declName_4352_);
v___x_4407_ = l_Lean_wasOriginallyDefn(v_env_4406_, v_declName_4352_);
if (v___x_4407_ == 0)
{
v___y_4363_ = v_a_4396_;
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
goto v___jp_4362_;
}
else
{
lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; 
v___x_4408_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4352_);
v___x_4409_ = l_Lean_MessageData_ofName(v_declName_4352_);
v___x_4410_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4410_, 0, v___x_4408_);
lean_ctor_set(v___x_4410_, 1, v___x_4409_);
v___x_4411_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4412_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4412_, 0, v___x_4410_);
lean_ctor_set(v___x_4412_, 1, v___x_4411_);
v___x_4413_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4412_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4413_) == 0)
{
lean_dec_ref_known(v___x_4413_, 1);
v___y_4363_ = v_a_4396_;
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
goto v___jp_4362_;
}
else
{
lean_dec(v_a_4396_);
lean_dec(v_a_4361_);
lean_dec(v_prio_4354_);
lean_dec(v_declName_4352_);
return v___x_4413_;
}
}
}
else
{
lean_object* v_options_4414_; lean_object* v___x_4415_; uint8_t v___x_4416_; 
v_options_4414_ = lean_ctor_get(v___y_4393_, 2);
v___x_4415_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility));
v___x_4416_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_4414_, v___x_4415_);
if (v___x_4416_ == 0)
{
v___y_4363_ = v_a_4396_;
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
goto v___jp_4362_;
}
else
{
lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; 
v___x_4417_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
lean_inc(v_declName_4352_);
v___x_4418_ = l_Lean_MessageData_ofName(v_declName_4352_);
v___x_4419_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4419_, 0, v___x_4417_);
lean_ctor_set(v___x_4419_, 1, v___x_4418_);
v___x_4420_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__7, &l_Lean_Meta_addInstance___closed__7_once, _init_l_Lean_Meta_addInstance___closed__7);
v___x_4421_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4421_, 0, v___x_4419_);
lean_ctor_set(v___x_4421_, 1, v___x_4420_);
v___x_4422_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4421_, v___y_4391_, v___y_4392_, v___y_4393_, v___y_4394_);
if (lean_obj_tag(v___x_4422_) == 0)
{
lean_dec_ref_known(v___x_4422_, 1);
v___y_4363_ = v_a_4396_;
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
goto v___jp_4362_;
}
else
{
lean_dec(v_a_4396_);
lean_dec(v_a_4361_);
lean_dec(v_prio_4354_);
lean_dec(v_declName_4352_);
return v___x_4422_;
}
}
}
}
else
{
lean_object* v_a_4423_; lean_object* v___x_4425_; uint8_t v_isShared_4426_; uint8_t v_isSharedCheck_4430_; 
lean_dec(v_a_4396_);
lean_dec(v_a_4361_);
lean_dec(v_prio_4354_);
lean_dec(v_declName_4352_);
v_a_4423_ = lean_ctor_get(v___x_4402_, 0);
v_isSharedCheck_4430_ = !lean_is_exclusive(v___x_4402_);
if (v_isSharedCheck_4430_ == 0)
{
v___x_4425_ = v___x_4402_;
v_isShared_4426_ = v_isSharedCheck_4430_;
goto v_resetjp_4424_;
}
else
{
lean_inc(v_a_4423_);
lean_dec(v___x_4402_);
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
else
{
lean_object* v_a_4431_; lean_object* v___x_4433_; uint8_t v_isShared_4434_; uint8_t v_isSharedCheck_4438_; 
lean_dec(v_a_4361_);
lean_dec(v_prio_4354_);
lean_dec(v_declName_4352_);
v_a_4431_ = lean_ctor_get(v___x_4395_, 0);
v_isSharedCheck_4438_ = !lean_is_exclusive(v___x_4395_);
if (v_isSharedCheck_4438_ == 0)
{
v___x_4433_ = v___x_4395_;
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
else
{
lean_inc(v_a_4431_);
lean_dec(v___x_4395_);
v___x_4433_ = lean_box(0);
v_isShared_4434_ = v_isSharedCheck_4438_;
goto v_resetjp_4432_;
}
v_resetjp_4432_:
{
lean_object* v___x_4436_; 
if (v_isShared_4434_ == 0)
{
v___x_4436_ = v___x_4433_;
goto v_reusejp_4435_;
}
else
{
lean_object* v_reuseFailAlloc_4437_; 
v_reuseFailAlloc_4437_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4437_, 0, v_a_4431_);
v___x_4436_ = v_reuseFailAlloc_4437_;
goto v_reusejp_4435_;
}
v_reusejp_4435_:
{
return v___x_4436_;
}
}
}
}
}
else
{
lean_object* v_a_4453_; lean_object* v___x_4455_; uint8_t v_isShared_4456_; uint8_t v_isSharedCheck_4460_; 
lean_dec(v_prio_4354_);
lean_dec(v_declName_4352_);
v_a_4453_ = lean_ctor_get(v___x_4360_, 0);
v_isSharedCheck_4460_ = !lean_is_exclusive(v___x_4360_);
if (v_isSharedCheck_4460_ == 0)
{
v___x_4455_ = v___x_4360_;
v_isShared_4456_ = v_isSharedCheck_4460_;
goto v_resetjp_4454_;
}
else
{
lean_inc(v_a_4453_);
lean_dec(v___x_4360_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4461_, lean_object* v_attrKind_4462_, lean_object* v_prio_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_){
_start:
{
uint8_t v_attrKind_boxed_4469_; lean_object* v_res_4470_; 
v_attrKind_boxed_4469_ = lean_unbox(v_attrKind_4462_);
v_res_4470_ = l_Lean_Meta_addInstance(v_declName_4461_, v_attrKind_boxed_4469_, v_prio_4463_, v_a_4464_, v_a_4465_, v_a_4466_, v_a_4467_);
lean_dec(v_a_4467_);
lean_dec_ref(v_a_4466_);
lean_dec(v_a_4465_);
lean_dec_ref(v_a_4464_);
return v_res_4470_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_4471_, lean_object* v_constName_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_){
_start:
{
lean_object* v___x_4478_; 
v___x_4478_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4472_, v___y_4473_, v___y_4474_, v___y_4475_, v___y_4476_);
return v___x_4478_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4479_, lean_object* v_constName_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_){
_start:
{
lean_object* v_res_4486_; 
v_res_4486_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_4479_, v_constName_4480_, v___y_4481_, v___y_4482_, v___y_4483_, v___y_4484_);
lean_dec(v___y_4484_);
lean_dec_ref(v___y_4483_);
lean_dec(v___y_4482_);
lean_dec_ref(v___y_4481_);
return v_res_4486_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_4487_, lean_object* v_ref_4488_, lean_object* v_constName_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_){
_start:
{
lean_object* v___x_4495_; 
v___x_4495_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4488_, v_constName_4489_, v___y_4490_, v___y_4491_, v___y_4492_, v___y_4493_);
return v___x_4495_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4496_, lean_object* v_ref_4497_, lean_object* v_constName_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_){
_start:
{
lean_object* v_res_4504_; 
v_res_4504_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_4496_, v_ref_4497_, v_constName_4498_, v___y_4499_, v___y_4500_, v___y_4501_, v___y_4502_);
lean_dec(v___y_4502_);
lean_dec_ref(v___y_4501_);
lean_dec(v___y_4500_);
lean_dec_ref(v___y_4499_);
lean_dec(v_ref_4497_);
return v_res_4504_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b1_4505_, lean_object* v_ref_4506_, lean_object* v_msg_4507_, lean_object* v_declHint_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_){
_start:
{
lean_object* v___x_4514_; 
v___x_4514_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4506_, v_msg_4507_, v_declHint_4508_, v___y_4509_, v___y_4510_, v___y_4511_, v___y_4512_);
return v___x_4514_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4515_, lean_object* v_ref_4516_, lean_object* v_msg_4517_, lean_object* v_declHint_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v_res_4524_; 
v_res_4524_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(v_00_u03b1_4515_, v_ref_4516_, v_msg_4517_, v_declHint_4518_, v___y_4519_, v___y_4520_, v___y_4521_, v___y_4522_);
lean_dec(v___y_4522_);
lean_dec_ref(v___y_4521_);
lean_dec(v___y_4520_);
lean_dec_ref(v___y_4519_);
lean_dec(v_ref_4516_);
return v_res_4524_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_4525_, lean_object* v_declHint_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_){
_start:
{
lean_object* v___x_4532_; 
v___x_4532_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4525_, v_declHint_4526_, v___y_4530_);
return v___x_4532_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_4533_, lean_object* v_declHint_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_){
_start:
{
lean_object* v_res_4540_; 
v_res_4540_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(v_msg_4533_, v_declHint_4534_, v___y_4535_, v___y_4536_, v___y_4537_, v___y_4538_);
lean_dec(v___y_4538_);
lean_dec_ref(v___y_4537_);
lean_dec(v___y_4536_);
lean_dec_ref(v___y_4535_);
return v_res_4540_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_4541_, lean_object* v_ref_4542_, lean_object* v_msg_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_){
_start:
{
lean_object* v___x_4549_; 
v___x_4549_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4542_, v_msg_4543_, v___y_4544_, v___y_4545_, v___y_4546_, v___y_4547_);
return v___x_4549_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4550_, lean_object* v_ref_4551_, lean_object* v_msg_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_){
_start:
{
lean_object* v_res_4558_; 
v_res_4558_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_4550_, v_ref_4551_, v_msg_4552_, v___y_4553_, v___y_4554_, v___y_4555_, v___y_4556_);
lean_dec(v___y_4556_);
lean_dec_ref(v___y_4555_);
lean_dec(v___y_4554_);
lean_dec_ref(v___y_4553_);
lean_dec(v_ref_4551_);
return v_res_4558_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4559_, uint8_t v_s_4560_, lean_object* v___y_4561_, lean_object* v___y_4562_){
_start:
{
lean_object* v___x_4564_; lean_object* v_env_4565_; lean_object* v_nextMacroScope_4566_; lean_object* v_ngen_4567_; lean_object* v_auxDeclNGen_4568_; lean_object* v_traceState_4569_; lean_object* v_messages_4570_; lean_object* v_infoState_4571_; lean_object* v_snapshotTasks_4572_; lean_object* v___x_4574_; uint8_t v_isShared_4575_; uint8_t v_isSharedCheck_4601_; 
v___x_4564_ = lean_st_ref_take(v___y_4562_);
v_env_4565_ = lean_ctor_get(v___x_4564_, 0);
v_nextMacroScope_4566_ = lean_ctor_get(v___x_4564_, 1);
v_ngen_4567_ = lean_ctor_get(v___x_4564_, 2);
v_auxDeclNGen_4568_ = lean_ctor_get(v___x_4564_, 3);
v_traceState_4569_ = lean_ctor_get(v___x_4564_, 4);
v_messages_4570_ = lean_ctor_get(v___x_4564_, 6);
v_infoState_4571_ = lean_ctor_get(v___x_4564_, 7);
v_snapshotTasks_4572_ = lean_ctor_get(v___x_4564_, 8);
v_isSharedCheck_4601_ = !lean_is_exclusive(v___x_4564_);
if (v_isSharedCheck_4601_ == 0)
{
lean_object* v_unused_4602_; 
v_unused_4602_ = lean_ctor_get(v___x_4564_, 5);
lean_dec(v_unused_4602_);
v___x_4574_ = v___x_4564_;
v_isShared_4575_ = v_isSharedCheck_4601_;
goto v_resetjp_4573_;
}
else
{
lean_inc(v_snapshotTasks_4572_);
lean_inc(v_infoState_4571_);
lean_inc(v_messages_4570_);
lean_inc(v_traceState_4569_);
lean_inc(v_auxDeclNGen_4568_);
lean_inc(v_ngen_4567_);
lean_inc(v_nextMacroScope_4566_);
lean_inc(v_env_4565_);
lean_dec(v___x_4564_);
v___x_4574_ = lean_box(0);
v_isShared_4575_ = v_isSharedCheck_4601_;
goto v_resetjp_4573_;
}
v_resetjp_4573_:
{
uint8_t v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4581_; 
v___x_4576_ = 0;
v___x_4577_ = lean_box(0);
v___x_4578_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4565_, v_declName_4559_, v_s_4560_, v___x_4576_, v___x_4577_);
v___x_4579_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4575_ == 0)
{
lean_ctor_set(v___x_4574_, 5, v___x_4579_);
lean_ctor_set(v___x_4574_, 0, v___x_4578_);
v___x_4581_ = v___x_4574_;
goto v_reusejp_4580_;
}
else
{
lean_object* v_reuseFailAlloc_4600_; 
v_reuseFailAlloc_4600_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4600_, 0, v___x_4578_);
lean_ctor_set(v_reuseFailAlloc_4600_, 1, v_nextMacroScope_4566_);
lean_ctor_set(v_reuseFailAlloc_4600_, 2, v_ngen_4567_);
lean_ctor_set(v_reuseFailAlloc_4600_, 3, v_auxDeclNGen_4568_);
lean_ctor_set(v_reuseFailAlloc_4600_, 4, v_traceState_4569_);
lean_ctor_set(v_reuseFailAlloc_4600_, 5, v___x_4579_);
lean_ctor_set(v_reuseFailAlloc_4600_, 6, v_messages_4570_);
lean_ctor_set(v_reuseFailAlloc_4600_, 7, v_infoState_4571_);
lean_ctor_set(v_reuseFailAlloc_4600_, 8, v_snapshotTasks_4572_);
v___x_4581_ = v_reuseFailAlloc_4600_;
goto v_reusejp_4580_;
}
v_reusejp_4580_:
{
lean_object* v___x_4582_; lean_object* v___x_4583_; lean_object* v_mctx_4584_; lean_object* v_zetaDeltaFVarIds_4585_; lean_object* v_postponed_4586_; lean_object* v_diag_4587_; lean_object* v___x_4589_; uint8_t v_isShared_4590_; uint8_t v_isSharedCheck_4598_; 
v___x_4582_ = lean_st_ref_put(v___y_4562_, v___x_4581_);
v___x_4583_ = lean_st_ref_take(v___y_4561_);
v_mctx_4584_ = lean_ctor_get(v___x_4583_, 0);
v_zetaDeltaFVarIds_4585_ = lean_ctor_get(v___x_4583_, 2);
v_postponed_4586_ = lean_ctor_get(v___x_4583_, 3);
v_diag_4587_ = lean_ctor_get(v___x_4583_, 4);
v_isSharedCheck_4598_ = !lean_is_exclusive(v___x_4583_);
if (v_isSharedCheck_4598_ == 0)
{
lean_object* v_unused_4599_; 
v_unused_4599_ = lean_ctor_get(v___x_4583_, 1);
lean_dec(v_unused_4599_);
v___x_4589_ = v___x_4583_;
v_isShared_4590_ = v_isSharedCheck_4598_;
goto v_resetjp_4588_;
}
else
{
lean_inc(v_diag_4587_);
lean_inc(v_postponed_4586_);
lean_inc(v_zetaDeltaFVarIds_4585_);
lean_inc(v_mctx_4584_);
lean_dec(v___x_4583_);
v___x_4589_ = lean_box(0);
v_isShared_4590_ = v_isSharedCheck_4598_;
goto v_resetjp_4588_;
}
v_resetjp_4588_:
{
lean_object* v___x_4591_; lean_object* v___x_4593_; 
v___x_4591_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_4590_ == 0)
{
lean_ctor_set(v___x_4589_, 1, v___x_4591_);
v___x_4593_ = v___x_4589_;
goto v_reusejp_4592_;
}
else
{
lean_object* v_reuseFailAlloc_4597_; 
v_reuseFailAlloc_4597_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4597_, 0, v_mctx_4584_);
lean_ctor_set(v_reuseFailAlloc_4597_, 1, v___x_4591_);
lean_ctor_set(v_reuseFailAlloc_4597_, 2, v_zetaDeltaFVarIds_4585_);
lean_ctor_set(v_reuseFailAlloc_4597_, 3, v_postponed_4586_);
lean_ctor_set(v_reuseFailAlloc_4597_, 4, v_diag_4587_);
v___x_4593_ = v_reuseFailAlloc_4597_;
goto v_reusejp_4592_;
}
v_reusejp_4592_:
{
lean_object* v___x_4594_; lean_object* v___x_4595_; lean_object* v___x_4596_; 
v___x_4594_ = lean_st_ref_put(v___y_4561_, v___x_4593_);
v___x_4595_ = lean_box(0);
v___x_4596_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4596_, 0, v___x_4595_);
return v___x_4596_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4603_, lean_object* v_s_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_){
_start:
{
uint8_t v_s_boxed_4608_; lean_object* v_res_4609_; 
v_s_boxed_4608_ = lean_unbox(v_s_4604_);
v_res_4609_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4603_, v_s_boxed_4608_, v___y_4605_, v___y_4606_);
lean_dec(v___y_4606_);
lean_dec(v___y_4605_);
return v_res_4609_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4610_, uint8_t v_s_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_){
_start:
{
lean_object* v___x_4617_; 
v___x_4617_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4610_, v_s_4611_, v___y_4613_, v___y_4615_);
return v___x_4617_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4618_, lean_object* v_s_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_){
_start:
{
uint8_t v_s_boxed_4625_; lean_object* v_res_4626_; 
v_s_boxed_4625_ = lean_unbox(v_s_4619_);
v_res_4626_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4618_, v_s_boxed_4625_, v___y_4620_, v___y_4621_, v___y_4622_, v___y_4623_);
lean_dec(v___y_4623_);
lean_dec_ref(v___y_4622_);
lean_dec(v___y_4621_);
lean_dec_ref(v___y_4620_);
return v_res_4626_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4627_, uint8_t v_attrKind_4628_, lean_object* v_prio_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_){
_start:
{
uint8_t v___x_4635_; lean_object* v___x_4636_; lean_object* v___x_4637_; 
v___x_4635_ = 4;
lean_inc(v_declName_4627_);
v___x_4636_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4627_, v___x_4635_, v_a_4631_, v_a_4633_);
lean_dec_ref(v___x_4636_);
v___x_4637_ = l_Lean_Meta_addInstance(v_declName_4627_, v_attrKind_4628_, v_prio_4629_, v_a_4630_, v_a_4631_, v_a_4632_, v_a_4633_);
return v___x_4637_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4638_, lean_object* v_attrKind_4639_, lean_object* v_prio_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_){
_start:
{
uint8_t v_attrKind_boxed_4646_; lean_object* v_res_4647_; 
v_attrKind_boxed_4646_ = lean_unbox(v_attrKind_4639_);
v_res_4647_ = l_Lean_Meta_registerInstance(v_declName_4638_, v_attrKind_boxed_4646_, v_prio_4640_, v_a_4641_, v_a_4642_, v_a_4643_, v_a_4644_);
lean_dec(v_a_4644_);
lean_dec_ref(v_a_4643_);
lean_dec(v_a_4642_);
lean_dec_ref(v_a_4641_);
return v_res_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4648_, lean_object* v_x_4649_){
_start:
{
lean_inc_ref(v_a_4648_);
return v_a_4648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4650_, lean_object* v_x_4651_){
_start:
{
lean_object* v_res_4652_; 
v_res_4652_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4650_, v_x_4651_);
lean_dec_ref(v_x_4651_);
lean_dec_ref(v_a_4650_);
return v_res_4652_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4653_, lean_object* v___y_4654_, lean_object* v___y_4655_){
_start:
{
lean_object* v___x_4657_; lean_object* v_env_4658_; lean_object* v_options_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; 
v___x_4657_ = lean_st_ref_get(v___y_4655_);
v_env_4658_ = lean_ctor_get(v___x_4657_, 0);
lean_inc_ref(v_env_4658_);
lean_dec(v___x_4657_);
v_options_4659_ = lean_ctor_get(v___y_4654_, 2);
v___x_4660_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4661_ = lean_unsigned_to_nat(32u);
v___x_4662_ = lean_mk_empty_array_with_capacity(v___x_4661_);
lean_dec_ref(v___x_4662_);
v___x_4663_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_4659_);
v___x_4664_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4664_, 0, v_env_4658_);
lean_ctor_set(v___x_4664_, 1, v___x_4660_);
lean_ctor_set(v___x_4664_, 2, v___x_4663_);
lean_ctor_set(v___x_4664_, 3, v_options_4659_);
v___x_4665_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4665_, 0, v___x_4664_);
lean_ctor_set(v___x_4665_, 1, v_msgData_4653_);
v___x_4666_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4665_);
return v___x_4666_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_){
_start:
{
lean_object* v_res_4671_; 
v_res_4671_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4667_, v___y_4668_, v___y_4669_);
lean_dec(v___y_4669_);
lean_dec_ref(v___y_4668_);
return v_res_4671_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4672_, lean_object* v___y_4673_, lean_object* v___y_4674_){
_start:
{
lean_object* v_ref_4676_; lean_object* v___x_4677_; lean_object* v_a_4678_; lean_object* v___x_4680_; uint8_t v_isShared_4681_; uint8_t v_isSharedCheck_4686_; 
v_ref_4676_ = lean_ctor_get(v___y_4673_, 5);
v___x_4677_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4672_, v___y_4673_, v___y_4674_);
v_a_4678_ = lean_ctor_get(v___x_4677_, 0);
v_isSharedCheck_4686_ = !lean_is_exclusive(v___x_4677_);
if (v_isSharedCheck_4686_ == 0)
{
v___x_4680_ = v___x_4677_;
v_isShared_4681_ = v_isSharedCheck_4686_;
goto v_resetjp_4679_;
}
else
{
lean_inc(v_a_4678_);
lean_dec(v___x_4677_);
v___x_4680_ = lean_box(0);
v_isShared_4681_ = v_isSharedCheck_4686_;
goto v_resetjp_4679_;
}
v_resetjp_4679_:
{
lean_object* v___x_4682_; lean_object* v___x_4684_; 
lean_inc(v_ref_4676_);
v___x_4682_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4682_, 0, v_ref_4676_);
lean_ctor_set(v___x_4682_, 1, v_a_4678_);
if (v_isShared_4681_ == 0)
{
lean_ctor_set_tag(v___x_4680_, 1);
lean_ctor_set(v___x_4680_, 0, v___x_4682_);
v___x_4684_ = v___x_4680_;
goto v_reusejp_4683_;
}
else
{
lean_object* v_reuseFailAlloc_4685_; 
v_reuseFailAlloc_4685_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4685_, 0, v___x_4682_);
v___x_4684_ = v_reuseFailAlloc_4685_;
goto v_reusejp_4683_;
}
v_reusejp_4683_:
{
return v___x_4684_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_){
_start:
{
lean_object* v_res_4691_; 
v_res_4691_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4687_, v___y_4688_, v___y_4689_);
lean_dec(v___y_4689_);
lean_dec_ref(v___y_4688_);
return v_res_4691_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4692_, lean_object* v_i_4693_, lean_object* v_k_4694_){
_start:
{
lean_object* v___x_4695_; uint8_t v___x_4696_; 
v___x_4695_ = lean_array_get_size(v_keys_4692_);
v___x_4696_ = lean_nat_dec_lt(v_i_4693_, v___x_4695_);
if (v___x_4696_ == 0)
{
lean_dec(v_i_4693_);
return v___x_4696_;
}
else
{
lean_object* v_k_x27_4697_; uint8_t v___x_4698_; 
v_k_x27_4697_ = lean_array_fget_borrowed(v_keys_4692_, v_i_4693_);
v___x_4698_ = lean_name_eq(v_k_4694_, v_k_x27_4697_);
if (v___x_4698_ == 0)
{
lean_object* v___x_4699_; lean_object* v___x_4700_; 
v___x_4699_ = lean_unsigned_to_nat(1u);
v___x_4700_ = lean_nat_add(v_i_4693_, v___x_4699_);
lean_dec(v_i_4693_);
v_i_4693_ = v___x_4700_;
goto _start;
}
else
{
lean_dec(v_i_4693_);
return v___x_4698_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4702_, lean_object* v_i_4703_, lean_object* v_k_4704_){
_start:
{
uint8_t v_res_4705_; lean_object* v_r_4706_; 
v_res_4705_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4702_, v_i_4703_, v_k_4704_);
lean_dec(v_k_4704_);
lean_dec_ref(v_keys_4702_);
v_r_4706_ = lean_box(v_res_4705_);
return v_r_4706_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4707_, size_t v_x_4708_, lean_object* v_x_4709_){
_start:
{
if (lean_obj_tag(v_x_4707_) == 0)
{
lean_object* v_es_4710_; lean_object* v___x_4711_; size_t v___x_4712_; size_t v___x_4713_; lean_object* v_j_4714_; lean_object* v___x_4715_; 
v_es_4710_ = lean_ctor_get(v_x_4707_, 0);
v___x_4711_ = lean_box(2);
v___x_4712_ = ((size_t)31ULL);
v___x_4713_ = lean_usize_land(v_x_4708_, v___x_4712_);
v_j_4714_ = lean_usize_to_nat(v___x_4713_);
v___x_4715_ = lean_array_get_borrowed(v___x_4711_, v_es_4710_, v_j_4714_);
lean_dec(v_j_4714_);
switch(lean_obj_tag(v___x_4715_))
{
case 0:
{
lean_object* v_key_4716_; uint8_t v___x_4717_; 
v_key_4716_ = lean_ctor_get(v___x_4715_, 0);
v___x_4717_ = lean_name_eq(v_x_4709_, v_key_4716_);
return v___x_4717_;
}
case 1:
{
lean_object* v_node_4718_; size_t v___x_4719_; size_t v___x_4720_; 
v_node_4718_ = lean_ctor_get(v___x_4715_, 0);
v___x_4719_ = ((size_t)5ULL);
v___x_4720_ = lean_usize_shift_right(v_x_4708_, v___x_4719_);
v_x_4707_ = v_node_4718_;
v_x_4708_ = v___x_4720_;
goto _start;
}
default: 
{
uint8_t v___x_4722_; 
v___x_4722_ = 0;
return v___x_4722_;
}
}
}
else
{
lean_object* v_ks_4723_; lean_object* v___x_4724_; uint8_t v___x_4725_; 
v_ks_4723_ = lean_ctor_get(v_x_4707_, 0);
v___x_4724_ = lean_unsigned_to_nat(0u);
v___x_4725_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4723_, v___x_4724_, v_x_4709_);
return v___x_4725_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4726_, lean_object* v_x_4727_, lean_object* v_x_4728_){
_start:
{
size_t v_x_2375__boxed_4729_; uint8_t v_res_4730_; lean_object* v_r_4731_; 
v_x_2375__boxed_4729_ = lean_unbox_usize(v_x_4727_);
lean_dec(v_x_4727_);
v_res_4730_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4726_, v_x_2375__boxed_4729_, v_x_4728_);
lean_dec(v_x_4728_);
lean_dec_ref(v_x_4726_);
v_r_4731_ = lean_box(v_res_4730_);
return v_r_4731_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4732_, lean_object* v_x_4733_){
_start:
{
uint64_t v___y_4735_; 
if (lean_obj_tag(v_x_4733_) == 0)
{
uint64_t v___x_4738_; 
v___x_4738_ = 1723ULL;
v___y_4735_ = v___x_4738_;
goto v___jp_4734_;
}
else
{
uint64_t v_hash_4739_; 
v_hash_4739_ = lean_ctor_get_uint64(v_x_4733_, sizeof(void*)*2);
v___y_4735_ = v_hash_4739_;
goto v___jp_4734_;
}
v___jp_4734_:
{
size_t v___x_4736_; uint8_t v___x_4737_; 
v___x_4736_ = lean_uint64_to_usize(v___y_4735_);
v___x_4737_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4732_, v___x_4736_, v_x_4733_);
return v___x_4737_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4740_, lean_object* v_x_4741_){
_start:
{
uint8_t v_res_4742_; lean_object* v_r_4743_; 
v_res_4742_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4740_, v_x_4741_);
lean_dec(v_x_4741_);
lean_dec_ref(v_x_4740_);
v_r_4743_ = lean_box(v_res_4742_);
return v_r_4743_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4744_, lean_object* v_declName_4745_, lean_object* v___y_4746_, lean_object* v___y_4747_){
_start:
{
lean_object* v_instanceNames_4752_; uint8_t v___x_4753_; 
v_instanceNames_4752_ = lean_ctor_get(v_d_4744_, 1);
v___x_4753_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4752_, v_declName_4745_);
if (v___x_4753_ == 0)
{
lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v_a_4760_; lean_object* v___x_4762_; uint8_t v_isShared_4763_; uint8_t v_isSharedCheck_4767_; 
lean_dec_ref(v_d_4744_);
v___x_4754_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4755_ = l_Lean_MessageData_ofConstName(v_declName_4745_, v___x_4753_);
v___x_4756_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4756_, 0, v___x_4754_);
lean_ctor_set(v___x_4756_, 1, v___x_4755_);
v___x_4757_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4758_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4758_, 0, v___x_4756_);
lean_ctor_set(v___x_4758_, 1, v___x_4757_);
v___x_4759_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4758_, v___y_4746_, v___y_4747_);
v_a_4760_ = lean_ctor_get(v___x_4759_, 0);
v_isSharedCheck_4767_ = !lean_is_exclusive(v___x_4759_);
if (v_isSharedCheck_4767_ == 0)
{
v___x_4762_ = v___x_4759_;
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
else
{
lean_inc(v_a_4760_);
lean_dec(v___x_4759_);
v___x_4762_ = lean_box(0);
v_isShared_4763_ = v_isSharedCheck_4767_;
goto v_resetjp_4761_;
}
v_resetjp_4761_:
{
lean_object* v___x_4765_; 
if (v_isShared_4763_ == 0)
{
v___x_4765_ = v___x_4762_;
goto v_reusejp_4764_;
}
else
{
lean_object* v_reuseFailAlloc_4766_; 
v_reuseFailAlloc_4766_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4766_, 0, v_a_4760_);
v___x_4765_ = v_reuseFailAlloc_4766_;
goto v_reusejp_4764_;
}
v_reusejp_4764_:
{
return v___x_4765_;
}
}
}
else
{
goto v___jp_4749_;
}
v___jp_4749_:
{
lean_object* v___x_4750_; lean_object* v___x_4751_; 
v___x_4750_ = l_Lean_Meta_Instances_eraseCore(v_d_4744_, v_declName_4745_);
v___x_4751_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4751_, 0, v___x_4750_);
return v___x_4751_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4768_, lean_object* v_declName_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_){
_start:
{
lean_object* v_res_4773_; 
v_res_4773_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4768_, v_declName_4769_, v___y_4770_, v___y_4771_);
lean_dec(v___y_4771_);
lean_dec_ref(v___y_4770_);
return v_res_4773_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4774_, lean_object* v_declName_4775_, lean_object* v___y_4776_, lean_object* v___y_4777_){
_start:
{
lean_object* v___x_4779_; lean_object* v_env_4780_; lean_object* v___x_4781_; lean_object* v_ext_4782_; lean_object* v_toEnvExtension_4783_; lean_object* v_asyncMode_4784_; lean_object* v___x_4785_; lean_object* v___x_4786_; 
v___x_4779_ = lean_st_ref_get(v___y_4777_);
v_env_4780_ = lean_ctor_get(v___x_4779_, 0);
lean_inc_ref(v_env_4780_);
lean_dec(v___x_4779_);
v___x_4781_ = l_Lean_Meta_instanceExtension;
v_ext_4782_ = lean_ctor_get(v___x_4781_, 1);
v_toEnvExtension_4783_ = lean_ctor_get(v_ext_4782_, 0);
v_asyncMode_4784_ = lean_ctor_get(v_toEnvExtension_4783_, 2);
v___x_4785_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4774_, v___x_4781_, v_env_4780_, v_asyncMode_4784_);
v___x_4786_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4785_, v_declName_4775_, v___y_4776_, v___y_4777_);
if (lean_obj_tag(v___x_4786_) == 0)
{
lean_object* v_a_4787_; lean_object* v___x_4789_; uint8_t v_isShared_4790_; uint8_t v_isSharedCheck_4816_; 
v_a_4787_ = lean_ctor_get(v___x_4786_, 0);
v_isSharedCheck_4816_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4816_ == 0)
{
v___x_4789_ = v___x_4786_;
v_isShared_4790_ = v_isSharedCheck_4816_;
goto v_resetjp_4788_;
}
else
{
lean_inc(v_a_4787_);
lean_dec(v___x_4786_);
v___x_4789_ = lean_box(0);
v_isShared_4790_ = v_isSharedCheck_4816_;
goto v_resetjp_4788_;
}
v_resetjp_4788_:
{
lean_object* v___x_4791_; lean_object* v_env_4792_; lean_object* v_nextMacroScope_4793_; lean_object* v_ngen_4794_; lean_object* v_auxDeclNGen_4795_; lean_object* v_traceState_4796_; lean_object* v_messages_4797_; lean_object* v_infoState_4798_; lean_object* v_snapshotTasks_4799_; lean_object* v___x_4801_; uint8_t v_isShared_4802_; uint8_t v_isSharedCheck_4814_; 
v___x_4791_ = lean_st_ref_take(v___y_4777_);
v_env_4792_ = lean_ctor_get(v___x_4791_, 0);
v_nextMacroScope_4793_ = lean_ctor_get(v___x_4791_, 1);
v_ngen_4794_ = lean_ctor_get(v___x_4791_, 2);
v_auxDeclNGen_4795_ = lean_ctor_get(v___x_4791_, 3);
v_traceState_4796_ = lean_ctor_get(v___x_4791_, 4);
v_messages_4797_ = lean_ctor_get(v___x_4791_, 6);
v_infoState_4798_ = lean_ctor_get(v___x_4791_, 7);
v_snapshotTasks_4799_ = lean_ctor_get(v___x_4791_, 8);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4791_);
if (v_isSharedCheck_4814_ == 0)
{
lean_object* v_unused_4815_; 
v_unused_4815_ = lean_ctor_get(v___x_4791_, 5);
lean_dec(v_unused_4815_);
v___x_4801_ = v___x_4791_;
v_isShared_4802_ = v_isSharedCheck_4814_;
goto v_resetjp_4800_;
}
else
{
lean_inc(v_snapshotTasks_4799_);
lean_inc(v_infoState_4798_);
lean_inc(v_messages_4797_);
lean_inc(v_traceState_4796_);
lean_inc(v_auxDeclNGen_4795_);
lean_inc(v_ngen_4794_);
lean_inc(v_nextMacroScope_4793_);
lean_inc(v_env_4792_);
lean_dec(v___x_4791_);
v___x_4801_ = lean_box(0);
v_isShared_4802_ = v_isSharedCheck_4814_;
goto v_resetjp_4800_;
}
v_resetjp_4800_:
{
lean_object* v___f_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4807_; 
v___f_4803_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4803_, 0, v_a_4787_);
v___x_4804_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4781_, v_env_4792_, v___f_4803_);
v___x_4805_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4802_ == 0)
{
lean_ctor_set(v___x_4801_, 5, v___x_4805_);
lean_ctor_set(v___x_4801_, 0, v___x_4804_);
v___x_4807_ = v___x_4801_;
goto v_reusejp_4806_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v___x_4804_);
lean_ctor_set(v_reuseFailAlloc_4813_, 1, v_nextMacroScope_4793_);
lean_ctor_set(v_reuseFailAlloc_4813_, 2, v_ngen_4794_);
lean_ctor_set(v_reuseFailAlloc_4813_, 3, v_auxDeclNGen_4795_);
lean_ctor_set(v_reuseFailAlloc_4813_, 4, v_traceState_4796_);
lean_ctor_set(v_reuseFailAlloc_4813_, 5, v___x_4805_);
lean_ctor_set(v_reuseFailAlloc_4813_, 6, v_messages_4797_);
lean_ctor_set(v_reuseFailAlloc_4813_, 7, v_infoState_4798_);
lean_ctor_set(v_reuseFailAlloc_4813_, 8, v_snapshotTasks_4799_);
v___x_4807_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4806_;
}
v_reusejp_4806_:
{
lean_object* v___x_4808_; lean_object* v___x_4809_; lean_object* v___x_4811_; 
v___x_4808_ = lean_st_ref_put(v___y_4777_, v___x_4807_);
v___x_4809_ = lean_box(0);
if (v_isShared_4790_ == 0)
{
lean_ctor_set(v___x_4789_, 0, v___x_4809_);
v___x_4811_ = v___x_4789_;
goto v_reusejp_4810_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v___x_4809_);
v___x_4811_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4810_;
}
v_reusejp_4810_:
{
return v___x_4811_;
}
}
}
}
}
else
{
lean_object* v_a_4817_; lean_object* v___x_4819_; uint8_t v_isShared_4820_; uint8_t v_isSharedCheck_4824_; 
v_a_4817_ = lean_ctor_get(v___x_4786_, 0);
v_isSharedCheck_4824_ = !lean_is_exclusive(v___x_4786_);
if (v_isSharedCheck_4824_ == 0)
{
v___x_4819_ = v___x_4786_;
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
else
{
lean_inc(v_a_4817_);
lean_dec(v___x_4786_);
v___x_4819_ = lean_box(0);
v_isShared_4820_ = v_isSharedCheck_4824_;
goto v_resetjp_4818_;
}
v_resetjp_4818_:
{
lean_object* v___x_4822_; 
if (v_isShared_4820_ == 0)
{
v___x_4822_ = v___x_4819_;
goto v_reusejp_4821_;
}
else
{
lean_object* v_reuseFailAlloc_4823_; 
v_reuseFailAlloc_4823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4823_, 0, v_a_4817_);
v___x_4822_ = v_reuseFailAlloc_4823_;
goto v_reusejp_4821_;
}
v_reusejp_4821_:
{
return v___x_4822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4825_, lean_object* v_declName_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_){
_start:
{
lean_object* v_res_4830_; 
v_res_4830_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4825_, v_declName_4826_, v___y_4827_, v___y_4828_);
lean_dec(v___y_4828_);
lean_dec_ref(v___y_4827_);
lean_dec_ref(v___x_4825_);
return v_res_4830_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4837_; uint64_t v___x_4838_; 
v___x_4837_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4838_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4837_);
return v___x_4838_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4839_; lean_object* v___x_4840_; lean_object* v___x_4841_; 
v___x_4839_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4840_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4841_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4841_, 0, v___x_4840_);
lean_ctor_set_uint64(v___x_4841_, sizeof(void*)*1, v___x_4839_);
return v___x_4841_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4842_; 
v___x_4842_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4842_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4843_; lean_object* v___x_4844_; 
v___x_4843_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4844_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4844_, 0, v___x_4843_);
return v___x_4844_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4845_; lean_object* v___x_4846_; 
v___x_4845_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4846_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4846_, 0, v___x_4845_);
lean_ctor_set(v___x_4846_, 1, v___x_4845_);
lean_ctor_set(v___x_4846_, 2, v___x_4845_);
lean_ctor_set(v___x_4846_, 3, v___x_4845_);
lean_ctor_set(v___x_4846_, 4, v___x_4845_);
lean_ctor_set(v___x_4846_, 5, v___x_4845_);
return v___x_4846_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4847_; lean_object* v___x_4848_; 
v___x_4847_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4848_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4848_, 0, v___x_4847_);
lean_ctor_set(v___x_4848_, 1, v___x_4847_);
lean_ctor_set(v___x_4848_, 2, v___x_4847_);
lean_ctor_set(v___x_4848_, 3, v___x_4847_);
lean_ctor_set(v___x_4848_, 4, v___x_4847_);
return v___x_4848_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4849_, lean_object* v___x_4850_, lean_object* v_declName_4851_, lean_object* v_stx_4852_, uint8_t v_attrKind_4853_, lean_object* v___y_4854_, lean_object* v___y_4855_){
_start:
{
lean_object* v___x_4857_; lean_object* v___x_4858_; lean_object* v___x_4859_; 
v___x_4857_ = lean_unsigned_to_nat(1u);
v___x_4858_ = l_Lean_Syntax_getArg(v_stx_4852_, v___x_4857_);
v___x_4859_ = l_Lean_getAttrParamOptPrio(v___x_4858_, v___y_4854_, v___y_4855_);
if (lean_obj_tag(v___x_4859_) == 0)
{
lean_object* v_a_4860_; uint8_t v___x_4861_; uint8_t v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; size_t v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; 
v_a_4860_ = lean_ctor_get(v___x_4859_, 0);
lean_inc(v_a_4860_);
lean_dec_ref_known(v___x_4859_, 1);
v___x_4861_ = 0;
v___x_4862_ = 1;
v___x_4863_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4864_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4865_ = lean_unsigned_to_nat(32u);
v___x_4866_ = lean_mk_empty_array_with_capacity(v___x_4865_);
v___x_4867_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4868_ = ((size_t)5ULL);
lean_inc_n(v___x_4849_, 6);
v___x_4869_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4869_, 0, v___x_4867_);
lean_ctor_set(v___x_4869_, 1, v___x_4866_);
lean_ctor_set(v___x_4869_, 2, v___x_4849_);
lean_ctor_set(v___x_4869_, 3, v___x_4849_);
lean_ctor_set_usize(v___x_4869_, 4, v___x_4868_);
v___x_4870_ = lean_box(1);
lean_inc_ref(v___x_4869_);
v___x_4871_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4871_, 0, v___x_4864_);
lean_ctor_set(v___x_4871_, 1, v___x_4869_);
lean_ctor_set(v___x_4871_, 2, v___x_4870_);
v___x_4872_ = lean_mk_empty_array_with_capacity(v___x_4849_);
v___x_4873_ = lean_box(0);
lean_inc(v___x_4850_);
v___x_4874_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4874_, 0, v___x_4863_);
lean_ctor_set(v___x_4874_, 1, v___x_4850_);
lean_ctor_set(v___x_4874_, 2, v___x_4871_);
lean_ctor_set(v___x_4874_, 3, v___x_4872_);
lean_ctor_set(v___x_4874_, 4, v___x_4873_);
lean_ctor_set(v___x_4874_, 5, v___x_4849_);
lean_ctor_set(v___x_4874_, 6, v___x_4873_);
lean_ctor_set_uint8(v___x_4874_, sizeof(void*)*7, v___x_4861_);
lean_ctor_set_uint8(v___x_4874_, sizeof(void*)*7 + 1, v___x_4861_);
lean_ctor_set_uint8(v___x_4874_, sizeof(void*)*7 + 2, v___x_4861_);
lean_ctor_set_uint8(v___x_4874_, sizeof(void*)*7 + 3, v___x_4862_);
v___x_4875_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_4875_, 0, v___x_4849_);
lean_ctor_set(v___x_4875_, 1, v___x_4849_);
lean_ctor_set(v___x_4875_, 2, v___x_4849_);
lean_ctor_set(v___x_4875_, 3, v___x_4849_);
lean_ctor_set(v___x_4875_, 4, v___x_4864_);
lean_ctor_set(v___x_4875_, 5, v___x_4864_);
lean_ctor_set(v___x_4875_, 6, v___x_4864_);
lean_ctor_set(v___x_4875_, 7, v___x_4864_);
lean_ctor_set(v___x_4875_, 8, v___x_4864_);
lean_ctor_set(v___x_4875_, 9, v___x_4864_);
lean_ctor_set(v___x_4875_, 10, v___x_4864_);
v___x_4876_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4877_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4878_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4878_, 0, v___x_4875_);
lean_ctor_set(v___x_4878_, 1, v___x_4876_);
lean_ctor_set(v___x_4878_, 2, v___x_4850_);
lean_ctor_set(v___x_4878_, 3, v___x_4869_);
lean_ctor_set(v___x_4878_, 4, v___x_4877_);
v___x_4879_ = lean_st_mk_ref(v___x_4878_);
v___x_4880_ = l_Lean_Meta_addInstance(v_declName_4851_, v_attrKind_4853_, v_a_4860_, v___x_4874_, v___x_4879_, v___y_4854_, v___y_4855_);
lean_dec_ref_known(v___x_4874_, 7);
if (lean_obj_tag(v___x_4880_) == 0)
{
lean_object* v___x_4882_; uint8_t v_isShared_4883_; uint8_t v_isSharedCheck_4889_; 
v_isSharedCheck_4889_ = !lean_is_exclusive(v___x_4880_);
if (v_isSharedCheck_4889_ == 0)
{
lean_object* v_unused_4890_; 
v_unused_4890_ = lean_ctor_get(v___x_4880_, 0);
lean_dec(v_unused_4890_);
v___x_4882_ = v___x_4880_;
v_isShared_4883_ = v_isSharedCheck_4889_;
goto v_resetjp_4881_;
}
else
{
lean_dec(v___x_4880_);
v___x_4882_ = lean_box(0);
v_isShared_4883_ = v_isSharedCheck_4889_;
goto v_resetjp_4881_;
}
v_resetjp_4881_:
{
lean_object* v___x_4884_; lean_object* v___x_4885_; lean_object* v___x_4887_; 
v___x_4884_ = lean_st_ref_get(v___x_4879_);
lean_dec(v___x_4879_);
lean_dec(v___x_4884_);
v___x_4885_ = lean_box(0);
if (v_isShared_4883_ == 0)
{
lean_ctor_set(v___x_4882_, 0, v___x_4885_);
v___x_4887_ = v___x_4882_;
goto v_reusejp_4886_;
}
else
{
lean_object* v_reuseFailAlloc_4888_; 
v_reuseFailAlloc_4888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4888_, 0, v___x_4885_);
v___x_4887_ = v_reuseFailAlloc_4888_;
goto v_reusejp_4886_;
}
v_reusejp_4886_:
{
return v___x_4887_;
}
}
}
else
{
lean_dec(v___x_4879_);
return v___x_4880_;
}
}
else
{
lean_object* v_a_4891_; lean_object* v___x_4893_; uint8_t v_isShared_4894_; uint8_t v_isSharedCheck_4898_; 
lean_dec(v_declName_4851_);
lean_dec(v___x_4850_);
lean_dec(v___x_4849_);
v_a_4891_ = lean_ctor_get(v___x_4859_, 0);
v_isSharedCheck_4898_ = !lean_is_exclusive(v___x_4859_);
if (v_isSharedCheck_4898_ == 0)
{
v___x_4893_ = v___x_4859_;
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
else
{
lean_inc(v_a_4891_);
lean_dec(v___x_4859_);
v___x_4893_ = lean_box(0);
v_isShared_4894_ = v_isSharedCheck_4898_;
goto v_resetjp_4892_;
}
v_resetjp_4892_:
{
lean_object* v___x_4896_; 
if (v_isShared_4894_ == 0)
{
v___x_4896_ = v___x_4893_;
goto v_reusejp_4895_;
}
else
{
lean_object* v_reuseFailAlloc_4897_; 
v_reuseFailAlloc_4897_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4897_, 0, v_a_4891_);
v___x_4896_ = v_reuseFailAlloc_4897_;
goto v_reusejp_4895_;
}
v_reusejp_4895_:
{
return v___x_4896_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4899_, lean_object* v___x_4900_, lean_object* v_declName_4901_, lean_object* v_stx_4902_, lean_object* v_attrKind_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_){
_start:
{
uint8_t v_attrKind_boxed_4907_; lean_object* v_res_4908_; 
v_attrKind_boxed_4907_ = lean_unbox(v_attrKind_4903_);
v_res_4908_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4899_, v___x_4900_, v_declName_4901_, v_stx_4902_, v_attrKind_boxed_4907_, v___y_4904_, v___y_4905_);
lean_dec(v___y_4905_);
lean_dec_ref(v___y_4904_);
lean_dec(v_stx_4902_);
return v_res_4908_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4909_; lean_object* v___f_4910_; 
v___x_4909_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4910_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4910_, 0, v___x_4909_);
return v___f_4910_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4977_; lean_object* v___f_4978_; lean_object* v___x_4979_; lean_object* v___x_4980_; 
v___f_4977_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_4978_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4979_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4980_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4980_, 0, v___x_4979_);
lean_ctor_set(v___x_4980_, 1, v___f_4978_);
lean_ctor_set(v___x_4980_, 2, v___f_4977_);
return v___x_4980_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4982_; lean_object* v___x_4983_; 
v___x_4982_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4983_ = l_Lean_registerBuiltinAttribute(v___x_4982_);
return v___x_4983_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4984_){
_start:
{
lean_object* v_res_4985_; 
v_res_4985_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4985_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4986_, lean_object* v_x_4987_, lean_object* v_x_4988_){
_start:
{
uint8_t v___x_4989_; 
v___x_4989_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4987_, v_x_4988_);
return v___x_4989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_4990_, lean_object* v_x_4991_, lean_object* v_x_4992_){
_start:
{
uint8_t v_res_4993_; lean_object* v_r_4994_; 
v_res_4993_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_4990_, v_x_4991_, v_x_4992_);
lean_dec(v_x_4992_);
lean_dec_ref(v_x_4991_);
v_r_4994_ = lean_box(v_res_4993_);
return v_r_4994_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_4995_, lean_object* v_msg_4996_, lean_object* v___y_4997_, lean_object* v___y_4998_){
_start:
{
lean_object* v___x_5000_; 
v___x_5000_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4996_, v___y_4997_, v___y_4998_);
return v___x_5000_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_5001_, lean_object* v_msg_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_){
_start:
{
lean_object* v_res_5006_; 
v_res_5006_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_5001_, v_msg_5002_, v___y_5003_, v___y_5004_);
lean_dec(v___y_5004_);
lean_dec_ref(v___y_5003_);
return v_res_5006_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5007_, lean_object* v_x_5008_, size_t v_x_5009_, lean_object* v_x_5010_){
_start:
{
uint8_t v___x_5011_; 
v___x_5011_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5008_, v_x_5009_, v_x_5010_);
return v___x_5011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5012_, lean_object* v_x_5013_, lean_object* v_x_5014_, lean_object* v_x_5015_){
_start:
{
size_t v_x_3024__boxed_5016_; uint8_t v_res_5017_; lean_object* v_r_5018_; 
v_x_3024__boxed_5016_ = lean_unbox_usize(v_x_5014_);
lean_dec(v_x_5014_);
v_res_5017_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_5012_, v_x_5013_, v_x_3024__boxed_5016_, v_x_5015_);
lean_dec(v_x_5015_);
lean_dec_ref(v_x_5013_);
v_r_5018_ = lean_box(v_res_5017_);
return v_r_5018_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5019_, lean_object* v_keys_5020_, lean_object* v_vals_5021_, lean_object* v_heq_5022_, lean_object* v_i_5023_, lean_object* v_k_5024_){
_start:
{
uint8_t v___x_5025_; 
v___x_5025_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_5020_, v_i_5023_, v_k_5024_);
return v___x_5025_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5026_, lean_object* v_keys_5027_, lean_object* v_vals_5028_, lean_object* v_heq_5029_, lean_object* v_i_5030_, lean_object* v_k_5031_){
_start:
{
uint8_t v_res_5032_; lean_object* v_r_5033_; 
v_res_5032_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_5026_, v_keys_5027_, v_vals_5028_, v_heq_5029_, v_i_5030_, v_k_5031_);
lean_dec(v_k_5031_);
lean_dec_ref(v_vals_5028_);
lean_dec_ref(v_keys_5027_);
v_r_5033_ = lean_box(v_res_5032_);
return v_r_5033_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5036_; lean_object* v___x_5037_; lean_object* v___x_5038_; 
v___x_5036_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5037_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5038_ = l_Lean_addBuiltinDocString(v___x_5036_, v___x_5037_);
return v___x_5038_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5039_){
_start:
{
lean_object* v_res_5040_; 
v_res_5040_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5040_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_5041_){
_start:
{
lean_object* v___x_5043_; lean_object* v_env_5044_; lean_object* v___x_5045_; lean_object* v_ext_5046_; lean_object* v_toEnvExtension_5047_; lean_object* v_asyncMode_5048_; lean_object* v___x_5049_; lean_object* v___x_5050_; lean_object* v_discrTree_5051_; lean_object* v___x_5052_; 
v___x_5043_ = lean_st_ref_get(v_a_5041_);
v_env_5044_ = lean_ctor_get(v___x_5043_, 0);
lean_inc_ref(v_env_5044_);
lean_dec(v___x_5043_);
v___x_5045_ = l_Lean_Meta_instanceExtension;
v_ext_5046_ = lean_ctor_get(v___x_5045_, 1);
v_toEnvExtension_5047_ = lean_ctor_get(v_ext_5046_, 0);
v_asyncMode_5048_ = lean_ctor_get(v_toEnvExtension_5047_, 2);
v___x_5049_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5050_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5049_, v___x_5045_, v_env_5044_, v_asyncMode_5048_);
v_discrTree_5051_ = lean_ctor_get(v___x_5050_, 0);
lean_inc_ref(v_discrTree_5051_);
lean_dec(v___x_5050_);
v___x_5052_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5052_, 0, v_discrTree_5051_);
return v___x_5052_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_5053_, lean_object* v_a_5054_){
_start:
{
lean_object* v_res_5055_; 
v_res_5055_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5053_);
lean_dec(v_a_5053_);
return v_res_5055_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_5056_, lean_object* v_a_5057_){
_start:
{
lean_object* v___x_5059_; 
v___x_5059_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5057_);
return v___x_5059_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_5060_, lean_object* v_a_5061_, lean_object* v_a_5062_){
_start:
{
lean_object* v_res_5063_; 
v_res_5063_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_5060_, v_a_5061_);
lean_dec(v_a_5061_);
lean_dec_ref(v_a_5060_);
return v_res_5063_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_5064_){
_start:
{
lean_object* v___x_5066_; lean_object* v_env_5067_; lean_object* v___x_5068_; lean_object* v_ext_5069_; lean_object* v_toEnvExtension_5070_; lean_object* v_asyncMode_5071_; lean_object* v___x_5072_; lean_object* v___x_5073_; lean_object* v_erased_5074_; lean_object* v___x_5075_; 
v___x_5066_ = lean_st_ref_get(v_a_5064_);
v_env_5067_ = lean_ctor_get(v___x_5066_, 0);
lean_inc_ref(v_env_5067_);
lean_dec(v___x_5066_);
v___x_5068_ = l_Lean_Meta_instanceExtension;
v_ext_5069_ = lean_ctor_get(v___x_5068_, 1);
v_toEnvExtension_5070_ = lean_ctor_get(v_ext_5069_, 0);
v_asyncMode_5071_ = lean_ctor_get(v_toEnvExtension_5070_, 2);
v___x_5072_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5073_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5072_, v___x_5068_, v_env_5067_, v_asyncMode_5071_);
v_erased_5074_ = lean_ctor_get(v___x_5073_, 2);
lean_inc_ref(v_erased_5074_);
lean_dec(v___x_5073_);
v___x_5075_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5075_, 0, v_erased_5074_);
return v___x_5075_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_5076_, lean_object* v_a_5077_){
_start:
{
lean_object* v_res_5078_; 
v_res_5078_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5076_);
lean_dec(v_a_5076_);
return v_res_5078_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_5079_, lean_object* v_a_5080_){
_start:
{
lean_object* v___x_5082_; 
v___x_5082_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5080_);
return v___x_5082_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_5083_, lean_object* v_a_5084_, lean_object* v_a_5085_){
_start:
{
lean_object* v_res_5086_; 
v_res_5086_ = l_Lean_Meta_getErasedInstances(v_a_5083_, v_a_5084_);
lean_dec(v_a_5084_);
lean_dec_ref(v_a_5083_);
return v_res_5086_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_5087_, lean_object* v_declName_5088_){
_start:
{
lean_object* v___x_5089_; lean_object* v_ext_5090_; lean_object* v_toEnvExtension_5091_; lean_object* v_asyncMode_5092_; lean_object* v___x_5093_; lean_object* v___x_5094_; lean_object* v_instanceNames_5095_; uint8_t v___x_5096_; 
v___x_5089_ = l_Lean_Meta_instanceExtension;
v_ext_5090_ = lean_ctor_get(v___x_5089_, 1);
v_toEnvExtension_5091_ = lean_ctor_get(v_ext_5090_, 0);
v_asyncMode_5092_ = lean_ctor_get(v_toEnvExtension_5091_, 2);
v___x_5093_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5094_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5093_, v___x_5089_, v_env_5087_, v_asyncMode_5092_);
v_instanceNames_5095_ = lean_ctor_get(v___x_5094_, 1);
lean_inc_ref(v_instanceNames_5095_);
lean_dec(v___x_5094_);
v___x_5096_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_5095_, v_declName_5088_);
lean_dec_ref(v_instanceNames_5095_);
return v___x_5096_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_5097_, lean_object* v_declName_5098_){
_start:
{
uint8_t v_res_5099_; lean_object* v_r_5100_; 
v_res_5099_ = l_Lean_Meta_isInstanceCore(v_env_5097_, v_declName_5098_);
lean_dec(v_declName_5098_);
v_r_5100_ = lean_box(v_res_5099_);
return v_r_5100_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_5101_, lean_object* v_a_5102_){
_start:
{
lean_object* v___x_5104_; lean_object* v_env_5105_; uint8_t v___x_5106_; lean_object* v___x_5107_; lean_object* v___x_5108_; 
v___x_5104_ = lean_st_ref_get(v_a_5102_);
v_env_5105_ = lean_ctor_get(v___x_5104_, 0);
lean_inc_ref(v_env_5105_);
lean_dec(v___x_5104_);
v___x_5106_ = l_Lean_Meta_isInstanceCore(v_env_5105_, v_declName_5101_);
v___x_5107_ = lean_box(v___x_5106_);
v___x_5108_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5108_, 0, v___x_5107_);
return v___x_5108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_5109_, lean_object* v_a_5110_, lean_object* v_a_5111_){
_start:
{
lean_object* v_res_5112_; 
v_res_5112_ = l_Lean_Meta_isInstance___redArg(v_declName_5109_, v_a_5110_);
lean_dec(v_a_5110_);
lean_dec(v_declName_5109_);
return v_res_5112_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_5113_, lean_object* v_a_5114_, lean_object* v_a_5115_){
_start:
{
lean_object* v___x_5117_; 
v___x_5117_ = l_Lean_Meta_isInstance___redArg(v_declName_5113_, v_a_5115_);
return v___x_5117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_){
_start:
{
lean_object* v_res_5122_; 
v_res_5122_ = l_Lean_Meta_isInstance(v_declName_5118_, v_a_5119_, v_a_5120_);
lean_dec(v_a_5120_);
lean_dec_ref(v_a_5119_);
lean_dec(v_declName_5118_);
return v_res_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5123_, lean_object* v_vals_5124_, lean_object* v_i_5125_, lean_object* v_k_5126_){
_start:
{
lean_object* v___x_5127_; uint8_t v___x_5128_; 
v___x_5127_ = lean_array_get_size(v_keys_5123_);
v___x_5128_ = lean_nat_dec_lt(v_i_5125_, v___x_5127_);
if (v___x_5128_ == 0)
{
lean_object* v___x_5129_; 
lean_dec(v_i_5125_);
v___x_5129_ = lean_box(0);
return v___x_5129_;
}
else
{
lean_object* v_k_x27_5130_; uint8_t v___x_5131_; 
v_k_x27_5130_ = lean_array_fget_borrowed(v_keys_5123_, v_i_5125_);
v___x_5131_ = lean_name_eq(v_k_5126_, v_k_x27_5130_);
if (v___x_5131_ == 0)
{
lean_object* v___x_5132_; lean_object* v___x_5133_; 
v___x_5132_ = lean_unsigned_to_nat(1u);
v___x_5133_ = lean_nat_add(v_i_5125_, v___x_5132_);
lean_dec(v_i_5125_);
v_i_5125_ = v___x_5133_;
goto _start;
}
else
{
lean_object* v___x_5135_; lean_object* v___x_5136_; 
v___x_5135_ = lean_array_fget_borrowed(v_vals_5124_, v_i_5125_);
lean_dec(v_i_5125_);
lean_inc(v___x_5135_);
v___x_5136_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5136_, 0, v___x_5135_);
return v___x_5136_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5137_, lean_object* v_vals_5138_, lean_object* v_i_5139_, lean_object* v_k_5140_){
_start:
{
lean_object* v_res_5141_; 
v_res_5141_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5137_, v_vals_5138_, v_i_5139_, v_k_5140_);
lean_dec(v_k_5140_);
lean_dec_ref(v_vals_5138_);
lean_dec_ref(v_keys_5137_);
return v_res_5141_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_5142_, size_t v_x_5143_, lean_object* v_x_5144_){
_start:
{
if (lean_obj_tag(v_x_5142_) == 0)
{
lean_object* v_es_5145_; lean_object* v___x_5146_; size_t v___x_5147_; size_t v___x_5148_; lean_object* v_j_5149_; lean_object* v___x_5150_; 
v_es_5145_ = lean_ctor_get(v_x_5142_, 0);
v___x_5146_ = lean_box(2);
v___x_5147_ = ((size_t)31ULL);
v___x_5148_ = lean_usize_land(v_x_5143_, v___x_5147_);
v_j_5149_ = lean_usize_to_nat(v___x_5148_);
v___x_5150_ = lean_array_get_borrowed(v___x_5146_, v_es_5145_, v_j_5149_);
lean_dec(v_j_5149_);
switch(lean_obj_tag(v___x_5150_))
{
case 0:
{
lean_object* v_key_5151_; lean_object* v_val_5152_; uint8_t v___x_5153_; 
v_key_5151_ = lean_ctor_get(v___x_5150_, 0);
v_val_5152_ = lean_ctor_get(v___x_5150_, 1);
v___x_5153_ = lean_name_eq(v_x_5144_, v_key_5151_);
if (v___x_5153_ == 0)
{
lean_object* v___x_5154_; 
v___x_5154_ = lean_box(0);
return v___x_5154_;
}
else
{
lean_object* v___x_5155_; 
lean_inc(v_val_5152_);
v___x_5155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5155_, 0, v_val_5152_);
return v___x_5155_;
}
}
case 1:
{
lean_object* v_node_5156_; size_t v___x_5157_; size_t v___x_5158_; 
v_node_5156_ = lean_ctor_get(v___x_5150_, 0);
v___x_5157_ = ((size_t)5ULL);
v___x_5158_ = lean_usize_shift_right(v_x_5143_, v___x_5157_);
v_x_5142_ = v_node_5156_;
v_x_5143_ = v___x_5158_;
goto _start;
}
default: 
{
lean_object* v___x_5160_; 
v___x_5160_ = lean_box(0);
return v___x_5160_;
}
}
}
else
{
lean_object* v_ks_5161_; lean_object* v_vs_5162_; lean_object* v___x_5163_; lean_object* v___x_5164_; 
v_ks_5161_ = lean_ctor_get(v_x_5142_, 0);
v_vs_5162_ = lean_ctor_get(v_x_5142_, 1);
v___x_5163_ = lean_unsigned_to_nat(0u);
v___x_5164_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5161_, v_vs_5162_, v___x_5163_, v_x_5144_);
return v___x_5164_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5165_, lean_object* v_x_5166_, lean_object* v_x_5167_){
_start:
{
size_t v_x_478__boxed_5168_; lean_object* v_res_5169_; 
v_x_478__boxed_5168_ = lean_unbox_usize(v_x_5166_);
lean_dec(v_x_5166_);
v_res_5169_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5165_, v_x_478__boxed_5168_, v_x_5167_);
lean_dec(v_x_5167_);
lean_dec_ref(v_x_5165_);
return v_res_5169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_5170_, lean_object* v_x_5171_){
_start:
{
uint64_t v___y_5173_; 
if (lean_obj_tag(v_x_5171_) == 0)
{
uint64_t v___x_5176_; 
v___x_5176_ = 1723ULL;
v___y_5173_ = v___x_5176_;
goto v___jp_5172_;
}
else
{
uint64_t v_hash_5177_; 
v_hash_5177_ = lean_ctor_get_uint64(v_x_5171_, sizeof(void*)*2);
v___y_5173_ = v_hash_5177_;
goto v___jp_5172_;
}
v___jp_5172_:
{
size_t v___x_5174_; lean_object* v___x_5175_; 
v___x_5174_ = lean_uint64_to_usize(v___y_5173_);
v___x_5175_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5170_, v___x_5174_, v_x_5171_);
return v___x_5175_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_5178_, lean_object* v_x_5179_){
_start:
{
lean_object* v_res_5180_; 
v_res_5180_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5178_, v_x_5179_);
lean_dec(v_x_5179_);
lean_dec_ref(v_x_5178_);
return v_res_5180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_5181_, lean_object* v_a_5182_){
_start:
{
lean_object* v___x_5184_; lean_object* v_env_5185_; lean_object* v___x_5186_; lean_object* v_ext_5187_; lean_object* v_toEnvExtension_5188_; lean_object* v_asyncMode_5189_; lean_object* v___x_5190_; lean_object* v___x_5191_; lean_object* v_instanceNames_5192_; lean_object* v___x_5193_; 
v___x_5184_ = lean_st_ref_get(v_a_5182_);
v_env_5185_ = lean_ctor_get(v___x_5184_, 0);
lean_inc_ref(v_env_5185_);
lean_dec(v___x_5184_);
v___x_5186_ = l_Lean_Meta_instanceExtension;
v_ext_5187_ = lean_ctor_get(v___x_5186_, 1);
v_toEnvExtension_5188_ = lean_ctor_get(v_ext_5187_, 0);
v_asyncMode_5189_ = lean_ctor_get(v_toEnvExtension_5188_, 2);
v___x_5190_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5191_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5190_, v___x_5186_, v_env_5185_, v_asyncMode_5189_);
v_instanceNames_5192_ = lean_ctor_get(v___x_5191_, 1);
lean_inc_ref(v_instanceNames_5192_);
lean_dec(v___x_5191_);
v___x_5193_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5192_, v_declName_5181_);
lean_dec_ref(v_instanceNames_5192_);
if (lean_obj_tag(v___x_5193_) == 1)
{
lean_object* v_val_5194_; lean_object* v___x_5196_; uint8_t v_isShared_5197_; uint8_t v_isSharedCheck_5203_; 
v_val_5194_ = lean_ctor_get(v___x_5193_, 0);
v_isSharedCheck_5203_ = !lean_is_exclusive(v___x_5193_);
if (v_isSharedCheck_5203_ == 0)
{
v___x_5196_ = v___x_5193_;
v_isShared_5197_ = v_isSharedCheck_5203_;
goto v_resetjp_5195_;
}
else
{
lean_inc(v_val_5194_);
lean_dec(v___x_5193_);
v___x_5196_ = lean_box(0);
v_isShared_5197_ = v_isSharedCheck_5203_;
goto v_resetjp_5195_;
}
v_resetjp_5195_:
{
lean_object* v_priority_5198_; lean_object* v___x_5200_; 
v_priority_5198_ = lean_ctor_get(v_val_5194_, 2);
lean_inc(v_priority_5198_);
lean_dec(v_val_5194_);
if (v_isShared_5197_ == 0)
{
lean_ctor_set(v___x_5196_, 0, v_priority_5198_);
v___x_5200_ = v___x_5196_;
goto v_reusejp_5199_;
}
else
{
lean_object* v_reuseFailAlloc_5202_; 
v_reuseFailAlloc_5202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5202_, 0, v_priority_5198_);
v___x_5200_ = v_reuseFailAlloc_5202_;
goto v_reusejp_5199_;
}
v_reusejp_5199_:
{
lean_object* v___x_5201_; 
v___x_5201_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5201_, 0, v___x_5200_);
return v___x_5201_;
}
}
}
else
{
lean_object* v___x_5204_; lean_object* v___x_5205_; 
lean_dec(v___x_5193_);
v___x_5204_ = lean_box(0);
v___x_5205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5205_, 0, v___x_5204_);
return v___x_5205_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_5206_, lean_object* v_a_5207_, lean_object* v_a_5208_){
_start:
{
lean_object* v_res_5209_; 
v_res_5209_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5206_, v_a_5207_);
lean_dec(v_a_5207_);
lean_dec(v_declName_5206_);
return v_res_5209_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_5210_, lean_object* v_a_5211_, lean_object* v_a_5212_){
_start:
{
lean_object* v___x_5214_; 
v___x_5214_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5210_, v_a_5212_);
return v___x_5214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_){
_start:
{
lean_object* v_res_5219_; 
v_res_5219_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_5215_, v_a_5216_, v_a_5217_);
lean_dec(v_a_5217_);
lean_dec_ref(v_a_5216_);
lean_dec(v_declName_5215_);
return v_res_5219_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_5220_, lean_object* v_x_5221_, lean_object* v_x_5222_){
_start:
{
lean_object* v___x_5223_; 
v___x_5223_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5221_, v_x_5222_);
return v___x_5223_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_5224_, lean_object* v_x_5225_, lean_object* v_x_5226_){
_start:
{
lean_object* v_res_5227_; 
v_res_5227_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_5224_, v_x_5225_, v_x_5226_);
lean_dec(v_x_5226_);
lean_dec_ref(v_x_5225_);
return v_res_5227_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5228_, lean_object* v_x_5229_, size_t v_x_5230_, lean_object* v_x_5231_){
_start:
{
lean_object* v___x_5232_; 
v___x_5232_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5229_, v_x_5230_, v_x_5231_);
return v___x_5232_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5233_, lean_object* v_x_5234_, lean_object* v_x_5235_, lean_object* v_x_5236_){
_start:
{
size_t v_x_589__boxed_5237_; lean_object* v_res_5238_; 
v_x_589__boxed_5237_ = lean_unbox_usize(v_x_5235_);
lean_dec(v_x_5235_);
v_res_5238_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_5233_, v_x_5234_, v_x_589__boxed_5237_, v_x_5236_);
lean_dec(v_x_5236_);
lean_dec_ref(v_x_5234_);
return v_res_5238_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5239_, lean_object* v_keys_5240_, lean_object* v_vals_5241_, lean_object* v_heq_5242_, lean_object* v_i_5243_, lean_object* v_k_5244_){
_start:
{
lean_object* v___x_5245_; 
v___x_5245_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5240_, v_vals_5241_, v_i_5243_, v_k_5244_);
return v___x_5245_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5246_, lean_object* v_keys_5247_, lean_object* v_vals_5248_, lean_object* v_heq_5249_, lean_object* v_i_5250_, lean_object* v_k_5251_){
_start:
{
lean_object* v_res_5252_; 
v_res_5252_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5246_, v_keys_5247_, v_vals_5248_, v_heq_5249_, v_i_5250_, v_k_5251_);
lean_dec(v_k_5251_);
lean_dec_ref(v_vals_5248_);
lean_dec_ref(v_keys_5247_);
return v_res_5252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_5253_, lean_object* v_a_5254_){
_start:
{
lean_object* v___x_5256_; lean_object* v_env_5257_; lean_object* v___x_5258_; lean_object* v_ext_5259_; lean_object* v_toEnvExtension_5260_; lean_object* v_asyncMode_5261_; lean_object* v___x_5262_; lean_object* v___x_5263_; lean_object* v_instanceNames_5264_; lean_object* v___x_5265_; 
v___x_5256_ = lean_st_ref_get(v_a_5254_);
v_env_5257_ = lean_ctor_get(v___x_5256_, 0);
lean_inc_ref(v_env_5257_);
lean_dec(v___x_5256_);
v___x_5258_ = l_Lean_Meta_instanceExtension;
v_ext_5259_ = lean_ctor_get(v___x_5258_, 1);
v_toEnvExtension_5260_ = lean_ctor_get(v_ext_5259_, 0);
v_asyncMode_5261_ = lean_ctor_get(v_toEnvExtension_5260_, 2);
v___x_5262_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5263_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5262_, v___x_5258_, v_env_5257_, v_asyncMode_5261_);
v_instanceNames_5264_ = lean_ctor_get(v___x_5263_, 1);
lean_inc_ref(v_instanceNames_5264_);
lean_dec(v___x_5263_);
v___x_5265_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5264_, v_declName_5253_);
lean_dec_ref(v_instanceNames_5264_);
if (lean_obj_tag(v___x_5265_) == 1)
{
lean_object* v_val_5266_; lean_object* v___x_5268_; uint8_t v_isShared_5269_; uint8_t v_isSharedCheck_5276_; 
v_val_5266_ = lean_ctor_get(v___x_5265_, 0);
v_isSharedCheck_5276_ = !lean_is_exclusive(v___x_5265_);
if (v_isSharedCheck_5276_ == 0)
{
v___x_5268_ = v___x_5265_;
v_isShared_5269_ = v_isSharedCheck_5276_;
goto v_resetjp_5267_;
}
else
{
lean_inc(v_val_5266_);
lean_dec(v___x_5265_);
v___x_5268_ = lean_box(0);
v_isShared_5269_ = v_isSharedCheck_5276_;
goto v_resetjp_5267_;
}
v_resetjp_5267_:
{
uint8_t v_attrKind_5270_; lean_object* v___x_5271_; lean_object* v___x_5273_; 
v_attrKind_5270_ = lean_ctor_get_uint8(v_val_5266_, sizeof(void*)*5);
lean_dec(v_val_5266_);
v___x_5271_ = lean_box(v_attrKind_5270_);
if (v_isShared_5269_ == 0)
{
lean_ctor_set(v___x_5268_, 0, v___x_5271_);
v___x_5273_ = v___x_5268_;
goto v_reusejp_5272_;
}
else
{
lean_object* v_reuseFailAlloc_5275_; 
v_reuseFailAlloc_5275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5275_, 0, v___x_5271_);
v___x_5273_ = v_reuseFailAlloc_5275_;
goto v_reusejp_5272_;
}
v_reusejp_5272_:
{
lean_object* v___x_5274_; 
v___x_5274_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5274_, 0, v___x_5273_);
return v___x_5274_;
}
}
}
else
{
lean_object* v___x_5277_; lean_object* v___x_5278_; 
lean_dec(v___x_5265_);
v___x_5277_ = lean_box(0);
v___x_5278_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5278_, 0, v___x_5277_);
return v___x_5278_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_5279_, lean_object* v_a_5280_, lean_object* v_a_5281_){
_start:
{
lean_object* v_res_5282_; 
v_res_5282_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5279_, v_a_5280_);
lean_dec(v_a_5280_);
lean_dec(v_declName_5279_);
return v_res_5282_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_5283_, lean_object* v_a_5284_, lean_object* v_a_5285_){
_start:
{
lean_object* v___x_5287_; 
v___x_5287_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5283_, v_a_5285_);
return v___x_5287_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_){
_start:
{
lean_object* v_res_5292_; 
v_res_5292_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_5288_, v_a_5289_, v_a_5290_);
lean_dec(v_a_5290_);
lean_dec_ref(v_a_5289_);
lean_dec(v_declName_5288_);
return v_res_5292_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5297_, lean_object* v_v_5298_, lean_object* v_t_5299_){
_start:
{
if (lean_obj_tag(v_t_5299_) == 0)
{
lean_object* v_size_5300_; lean_object* v_k_5301_; lean_object* v_v_5302_; lean_object* v_l_5303_; lean_object* v_r_5304_; lean_object* v___x_5306_; uint8_t v_isShared_5307_; uint8_t v_isSharedCheck_5585_; 
v_size_5300_ = lean_ctor_get(v_t_5299_, 0);
v_k_5301_ = lean_ctor_get(v_t_5299_, 1);
v_v_5302_ = lean_ctor_get(v_t_5299_, 2);
v_l_5303_ = lean_ctor_get(v_t_5299_, 3);
v_r_5304_ = lean_ctor_get(v_t_5299_, 4);
v_isSharedCheck_5585_ = !lean_is_exclusive(v_t_5299_);
if (v_isSharedCheck_5585_ == 0)
{
v___x_5306_ = v_t_5299_;
v_isShared_5307_ = v_isSharedCheck_5585_;
goto v_resetjp_5305_;
}
else
{
lean_inc(v_r_5304_);
lean_inc(v_l_5303_);
lean_inc(v_v_5302_);
lean_inc(v_k_5301_);
lean_inc(v_size_5300_);
lean_dec(v_t_5299_);
v___x_5306_ = lean_box(0);
v_isShared_5307_ = v_isSharedCheck_5585_;
goto v_resetjp_5305_;
}
v_resetjp_5305_:
{
uint8_t v___x_5308_; 
v___x_5308_ = lean_nat_dec_lt(v_k_5301_, v_k_5297_);
if (v___x_5308_ == 0)
{
uint8_t v___x_5309_; 
v___x_5309_ = lean_nat_dec_eq(v_k_5301_, v_k_5297_);
if (v___x_5309_ == 0)
{
lean_object* v_impl_5310_; lean_object* v___x_5311_; 
lean_dec(v_size_5300_);
v_impl_5310_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5297_, v_v_5298_, v_r_5304_);
v___x_5311_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5303_) == 0)
{
lean_object* v_size_5312_; lean_object* v_size_5313_; lean_object* v_k_5314_; lean_object* v_v_5315_; lean_object* v_l_5316_; lean_object* v_r_5317_; lean_object* v___x_5318_; lean_object* v___x_5319_; uint8_t v___x_5320_; 
v_size_5312_ = lean_ctor_get(v_l_5303_, 0);
v_size_5313_ = lean_ctor_get(v_impl_5310_, 0);
lean_inc(v_size_5313_);
v_k_5314_ = lean_ctor_get(v_impl_5310_, 1);
lean_inc(v_k_5314_);
v_v_5315_ = lean_ctor_get(v_impl_5310_, 2);
lean_inc(v_v_5315_);
v_l_5316_ = lean_ctor_get(v_impl_5310_, 3);
lean_inc(v_l_5316_);
v_r_5317_ = lean_ctor_get(v_impl_5310_, 4);
lean_inc(v_r_5317_);
v___x_5318_ = lean_unsigned_to_nat(3u);
v___x_5319_ = lean_nat_mul(v___x_5318_, v_size_5312_);
v___x_5320_ = lean_nat_dec_lt(v___x_5319_, v_size_5313_);
lean_dec(v___x_5319_);
if (v___x_5320_ == 0)
{
lean_object* v___x_5321_; lean_object* v___x_5322_; lean_object* v___x_5324_; 
lean_dec(v_r_5317_);
lean_dec(v_l_5316_);
lean_dec(v_v_5315_);
lean_dec(v_k_5314_);
v___x_5321_ = lean_nat_add(v___x_5311_, v_size_5312_);
v___x_5322_ = lean_nat_add(v___x_5321_, v_size_5313_);
lean_dec(v_size_5313_);
lean_dec(v___x_5321_);
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 4, v_impl_5310_);
lean_ctor_set(v___x_5306_, 0, v___x_5322_);
v___x_5324_ = v___x_5306_;
goto v_reusejp_5323_;
}
else
{
lean_object* v_reuseFailAlloc_5325_; 
v_reuseFailAlloc_5325_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5325_, 0, v___x_5322_);
lean_ctor_set(v_reuseFailAlloc_5325_, 1, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5325_, 2, v_v_5302_);
lean_ctor_set(v_reuseFailAlloc_5325_, 3, v_l_5303_);
lean_ctor_set(v_reuseFailAlloc_5325_, 4, v_impl_5310_);
v___x_5324_ = v_reuseFailAlloc_5325_;
goto v_reusejp_5323_;
}
v_reusejp_5323_:
{
return v___x_5324_;
}
}
else
{
lean_object* v___x_5327_; uint8_t v_isShared_5328_; uint8_t v_isSharedCheck_5389_; 
v_isSharedCheck_5389_ = !lean_is_exclusive(v_impl_5310_);
if (v_isSharedCheck_5389_ == 0)
{
lean_object* v_unused_5390_; lean_object* v_unused_5391_; lean_object* v_unused_5392_; lean_object* v_unused_5393_; lean_object* v_unused_5394_; 
v_unused_5390_ = lean_ctor_get(v_impl_5310_, 4);
lean_dec(v_unused_5390_);
v_unused_5391_ = lean_ctor_get(v_impl_5310_, 3);
lean_dec(v_unused_5391_);
v_unused_5392_ = lean_ctor_get(v_impl_5310_, 2);
lean_dec(v_unused_5392_);
v_unused_5393_ = lean_ctor_get(v_impl_5310_, 1);
lean_dec(v_unused_5393_);
v_unused_5394_ = lean_ctor_get(v_impl_5310_, 0);
lean_dec(v_unused_5394_);
v___x_5327_ = v_impl_5310_;
v_isShared_5328_ = v_isSharedCheck_5389_;
goto v_resetjp_5326_;
}
else
{
lean_dec(v_impl_5310_);
v___x_5327_ = lean_box(0);
v_isShared_5328_ = v_isSharedCheck_5389_;
goto v_resetjp_5326_;
}
v_resetjp_5326_:
{
lean_object* v_size_5329_; lean_object* v_k_5330_; lean_object* v_v_5331_; lean_object* v_l_5332_; lean_object* v_r_5333_; lean_object* v_size_5334_; lean_object* v___x_5335_; lean_object* v___x_5336_; uint8_t v___x_5337_; 
v_size_5329_ = lean_ctor_get(v_l_5316_, 0);
v_k_5330_ = lean_ctor_get(v_l_5316_, 1);
v_v_5331_ = lean_ctor_get(v_l_5316_, 2);
v_l_5332_ = lean_ctor_get(v_l_5316_, 3);
v_r_5333_ = lean_ctor_get(v_l_5316_, 4);
v_size_5334_ = lean_ctor_get(v_r_5317_, 0);
v___x_5335_ = lean_unsigned_to_nat(2u);
v___x_5336_ = lean_nat_mul(v___x_5335_, v_size_5334_);
v___x_5337_ = lean_nat_dec_lt(v_size_5329_, v___x_5336_);
lean_dec(v___x_5336_);
if (v___x_5337_ == 0)
{
lean_object* v___x_5339_; uint8_t v_isShared_5340_; uint8_t v_isSharedCheck_5365_; 
lean_inc(v_r_5333_);
lean_inc(v_l_5332_);
lean_inc(v_v_5331_);
lean_inc(v_k_5330_);
v_isSharedCheck_5365_ = !lean_is_exclusive(v_l_5316_);
if (v_isSharedCheck_5365_ == 0)
{
lean_object* v_unused_5366_; lean_object* v_unused_5367_; lean_object* v_unused_5368_; lean_object* v_unused_5369_; lean_object* v_unused_5370_; 
v_unused_5366_ = lean_ctor_get(v_l_5316_, 4);
lean_dec(v_unused_5366_);
v_unused_5367_ = lean_ctor_get(v_l_5316_, 3);
lean_dec(v_unused_5367_);
v_unused_5368_ = lean_ctor_get(v_l_5316_, 2);
lean_dec(v_unused_5368_);
v_unused_5369_ = lean_ctor_get(v_l_5316_, 1);
lean_dec(v_unused_5369_);
v_unused_5370_ = lean_ctor_get(v_l_5316_, 0);
lean_dec(v_unused_5370_);
v___x_5339_ = v_l_5316_;
v_isShared_5340_ = v_isSharedCheck_5365_;
goto v_resetjp_5338_;
}
else
{
lean_dec(v_l_5316_);
v___x_5339_ = lean_box(0);
v_isShared_5340_ = v_isSharedCheck_5365_;
goto v_resetjp_5338_;
}
v_resetjp_5338_:
{
lean_object* v___x_5341_; lean_object* v___x_5342_; lean_object* v___y_5344_; lean_object* v___y_5345_; lean_object* v___y_5346_; lean_object* v___y_5355_; 
v___x_5341_ = lean_nat_add(v___x_5311_, v_size_5312_);
v___x_5342_ = lean_nat_add(v___x_5341_, v_size_5313_);
lean_dec(v_size_5313_);
if (lean_obj_tag(v_l_5332_) == 0)
{
lean_object* v_size_5363_; 
v_size_5363_ = lean_ctor_get(v_l_5332_, 0);
lean_inc(v_size_5363_);
v___y_5355_ = v_size_5363_;
goto v___jp_5354_;
}
else
{
lean_object* v___x_5364_; 
v___x_5364_ = lean_unsigned_to_nat(0u);
v___y_5355_ = v___x_5364_;
goto v___jp_5354_;
}
v___jp_5343_:
{
lean_object* v___x_5347_; lean_object* v___x_5349_; 
v___x_5347_ = lean_nat_add(v___y_5344_, v___y_5346_);
lean_dec(v___y_5346_);
lean_dec(v___y_5344_);
if (v_isShared_5340_ == 0)
{
lean_ctor_set(v___x_5339_, 4, v_r_5317_);
lean_ctor_set(v___x_5339_, 3, v_r_5333_);
lean_ctor_set(v___x_5339_, 2, v_v_5315_);
lean_ctor_set(v___x_5339_, 1, v_k_5314_);
lean_ctor_set(v___x_5339_, 0, v___x_5347_);
v___x_5349_ = v___x_5339_;
goto v_reusejp_5348_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v___x_5347_);
lean_ctor_set(v_reuseFailAlloc_5353_, 1, v_k_5314_);
lean_ctor_set(v_reuseFailAlloc_5353_, 2, v_v_5315_);
lean_ctor_set(v_reuseFailAlloc_5353_, 3, v_r_5333_);
lean_ctor_set(v_reuseFailAlloc_5353_, 4, v_r_5317_);
v___x_5349_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5348_;
}
v_reusejp_5348_:
{
lean_object* v___x_5351_; 
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 4, v___x_5349_);
lean_ctor_set(v___x_5327_, 3, v___y_5345_);
lean_ctor_set(v___x_5327_, 2, v_v_5331_);
lean_ctor_set(v___x_5327_, 1, v_k_5330_);
lean_ctor_set(v___x_5327_, 0, v___x_5342_);
v___x_5351_ = v___x_5327_;
goto v_reusejp_5350_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5342_);
lean_ctor_set(v_reuseFailAlloc_5352_, 1, v_k_5330_);
lean_ctor_set(v_reuseFailAlloc_5352_, 2, v_v_5331_);
lean_ctor_set(v_reuseFailAlloc_5352_, 3, v___y_5345_);
lean_ctor_set(v_reuseFailAlloc_5352_, 4, v___x_5349_);
v___x_5351_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5350_;
}
v_reusejp_5350_:
{
return v___x_5351_;
}
}
}
v___jp_5354_:
{
lean_object* v___x_5356_; lean_object* v___x_5358_; 
v___x_5356_ = lean_nat_add(v___x_5341_, v___y_5355_);
lean_dec(v___y_5355_);
lean_dec(v___x_5341_);
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 4, v_l_5332_);
lean_ctor_set(v___x_5306_, 0, v___x_5356_);
v___x_5358_ = v___x_5306_;
goto v_reusejp_5357_;
}
else
{
lean_object* v_reuseFailAlloc_5362_; 
v_reuseFailAlloc_5362_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5362_, 0, v___x_5356_);
lean_ctor_set(v_reuseFailAlloc_5362_, 1, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5362_, 2, v_v_5302_);
lean_ctor_set(v_reuseFailAlloc_5362_, 3, v_l_5303_);
lean_ctor_set(v_reuseFailAlloc_5362_, 4, v_l_5332_);
v___x_5358_ = v_reuseFailAlloc_5362_;
goto v_reusejp_5357_;
}
v_reusejp_5357_:
{
lean_object* v___x_5359_; 
v___x_5359_ = lean_nat_add(v___x_5311_, v_size_5334_);
if (lean_obj_tag(v_r_5333_) == 0)
{
lean_object* v_size_5360_; 
v_size_5360_ = lean_ctor_get(v_r_5333_, 0);
lean_inc(v_size_5360_);
v___y_5344_ = v___x_5359_;
v___y_5345_ = v___x_5358_;
v___y_5346_ = v_size_5360_;
goto v___jp_5343_;
}
else
{
lean_object* v___x_5361_; 
v___x_5361_ = lean_unsigned_to_nat(0u);
v___y_5344_ = v___x_5359_;
v___y_5345_ = v___x_5358_;
v___y_5346_ = v___x_5361_;
goto v___jp_5343_;
}
}
}
}
}
else
{
lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5375_; 
lean_del_object(v___x_5306_);
v___x_5371_ = lean_nat_add(v___x_5311_, v_size_5312_);
v___x_5372_ = lean_nat_add(v___x_5371_, v_size_5313_);
lean_dec(v_size_5313_);
v___x_5373_ = lean_nat_add(v___x_5371_, v_size_5329_);
lean_dec(v___x_5371_);
lean_inc_ref(v_l_5303_);
if (v_isShared_5328_ == 0)
{
lean_ctor_set(v___x_5327_, 4, v_l_5316_);
lean_ctor_set(v___x_5327_, 3, v_l_5303_);
lean_ctor_set(v___x_5327_, 2, v_v_5302_);
lean_ctor_set(v___x_5327_, 1, v_k_5301_);
lean_ctor_set(v___x_5327_, 0, v___x_5373_);
v___x_5375_ = v___x_5327_;
goto v_reusejp_5374_;
}
else
{
lean_object* v_reuseFailAlloc_5388_; 
v_reuseFailAlloc_5388_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5388_, 0, v___x_5373_);
lean_ctor_set(v_reuseFailAlloc_5388_, 1, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5388_, 2, v_v_5302_);
lean_ctor_set(v_reuseFailAlloc_5388_, 3, v_l_5303_);
lean_ctor_set(v_reuseFailAlloc_5388_, 4, v_l_5316_);
v___x_5375_ = v_reuseFailAlloc_5388_;
goto v_reusejp_5374_;
}
v_reusejp_5374_:
{
lean_object* v___x_5377_; uint8_t v_isShared_5378_; uint8_t v_isSharedCheck_5382_; 
v_isSharedCheck_5382_ = !lean_is_exclusive(v_l_5303_);
if (v_isSharedCheck_5382_ == 0)
{
lean_object* v_unused_5383_; lean_object* v_unused_5384_; lean_object* v_unused_5385_; lean_object* v_unused_5386_; lean_object* v_unused_5387_; 
v_unused_5383_ = lean_ctor_get(v_l_5303_, 4);
lean_dec(v_unused_5383_);
v_unused_5384_ = lean_ctor_get(v_l_5303_, 3);
lean_dec(v_unused_5384_);
v_unused_5385_ = lean_ctor_get(v_l_5303_, 2);
lean_dec(v_unused_5385_);
v_unused_5386_ = lean_ctor_get(v_l_5303_, 1);
lean_dec(v_unused_5386_);
v_unused_5387_ = lean_ctor_get(v_l_5303_, 0);
lean_dec(v_unused_5387_);
v___x_5377_ = v_l_5303_;
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
else
{
lean_dec(v_l_5303_);
v___x_5377_ = lean_box(0);
v_isShared_5378_ = v_isSharedCheck_5382_;
goto v_resetjp_5376_;
}
v_resetjp_5376_:
{
lean_object* v___x_5380_; 
if (v_isShared_5378_ == 0)
{
lean_ctor_set(v___x_5377_, 4, v_r_5317_);
lean_ctor_set(v___x_5377_, 3, v___x_5375_);
lean_ctor_set(v___x_5377_, 2, v_v_5315_);
lean_ctor_set(v___x_5377_, 1, v_k_5314_);
lean_ctor_set(v___x_5377_, 0, v___x_5372_);
v___x_5380_ = v___x_5377_;
goto v_reusejp_5379_;
}
else
{
lean_object* v_reuseFailAlloc_5381_; 
v_reuseFailAlloc_5381_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5381_, 0, v___x_5372_);
lean_ctor_set(v_reuseFailAlloc_5381_, 1, v_k_5314_);
lean_ctor_set(v_reuseFailAlloc_5381_, 2, v_v_5315_);
lean_ctor_set(v_reuseFailAlloc_5381_, 3, v___x_5375_);
lean_ctor_set(v_reuseFailAlloc_5381_, 4, v_r_5317_);
v___x_5380_ = v_reuseFailAlloc_5381_;
goto v_reusejp_5379_;
}
v_reusejp_5379_:
{
return v___x_5380_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5395_; 
v_l_5395_ = lean_ctor_get(v_impl_5310_, 3);
lean_inc(v_l_5395_);
if (lean_obj_tag(v_l_5395_) == 0)
{
lean_object* v_r_5396_; lean_object* v_k_5397_; lean_object* v_v_5398_; lean_object* v___x_5400_; uint8_t v_isShared_5401_; uint8_t v_isSharedCheck_5421_; 
v_r_5396_ = lean_ctor_get(v_impl_5310_, 4);
v_k_5397_ = lean_ctor_get(v_impl_5310_, 1);
v_v_5398_ = lean_ctor_get(v_impl_5310_, 2);
v_isSharedCheck_5421_ = !lean_is_exclusive(v_impl_5310_);
if (v_isSharedCheck_5421_ == 0)
{
lean_object* v_unused_5422_; lean_object* v_unused_5423_; 
v_unused_5422_ = lean_ctor_get(v_impl_5310_, 3);
lean_dec(v_unused_5422_);
v_unused_5423_ = lean_ctor_get(v_impl_5310_, 0);
lean_dec(v_unused_5423_);
v___x_5400_ = v_impl_5310_;
v_isShared_5401_ = v_isSharedCheck_5421_;
goto v_resetjp_5399_;
}
else
{
lean_inc(v_r_5396_);
lean_inc(v_v_5398_);
lean_inc(v_k_5397_);
lean_dec(v_impl_5310_);
v___x_5400_ = lean_box(0);
v_isShared_5401_ = v_isSharedCheck_5421_;
goto v_resetjp_5399_;
}
v_resetjp_5399_:
{
lean_object* v_k_5402_; lean_object* v_v_5403_; lean_object* v___x_5405_; uint8_t v_isShared_5406_; uint8_t v_isSharedCheck_5417_; 
v_k_5402_ = lean_ctor_get(v_l_5395_, 1);
v_v_5403_ = lean_ctor_get(v_l_5395_, 2);
v_isSharedCheck_5417_ = !lean_is_exclusive(v_l_5395_);
if (v_isSharedCheck_5417_ == 0)
{
lean_object* v_unused_5418_; lean_object* v_unused_5419_; lean_object* v_unused_5420_; 
v_unused_5418_ = lean_ctor_get(v_l_5395_, 4);
lean_dec(v_unused_5418_);
v_unused_5419_ = lean_ctor_get(v_l_5395_, 3);
lean_dec(v_unused_5419_);
v_unused_5420_ = lean_ctor_get(v_l_5395_, 0);
lean_dec(v_unused_5420_);
v___x_5405_ = v_l_5395_;
v_isShared_5406_ = v_isSharedCheck_5417_;
goto v_resetjp_5404_;
}
else
{
lean_inc(v_v_5403_);
lean_inc(v_k_5402_);
lean_dec(v_l_5395_);
v___x_5405_ = lean_box(0);
v_isShared_5406_ = v_isSharedCheck_5417_;
goto v_resetjp_5404_;
}
v_resetjp_5404_:
{
lean_object* v___x_5407_; lean_object* v___x_5409_; 
v___x_5407_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5396_, 2);
if (v_isShared_5406_ == 0)
{
lean_ctor_set(v___x_5405_, 4, v_r_5396_);
lean_ctor_set(v___x_5405_, 3, v_r_5396_);
lean_ctor_set(v___x_5405_, 2, v_v_5302_);
lean_ctor_set(v___x_5405_, 1, v_k_5301_);
lean_ctor_set(v___x_5405_, 0, v___x_5311_);
v___x_5409_ = v___x_5405_;
goto v_reusejp_5408_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v___x_5311_);
lean_ctor_set(v_reuseFailAlloc_5416_, 1, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5416_, 2, v_v_5302_);
lean_ctor_set(v_reuseFailAlloc_5416_, 3, v_r_5396_);
lean_ctor_set(v_reuseFailAlloc_5416_, 4, v_r_5396_);
v___x_5409_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5408_;
}
v_reusejp_5408_:
{
lean_object* v___x_5411_; 
lean_inc(v_r_5396_);
if (v_isShared_5401_ == 0)
{
lean_ctor_set(v___x_5400_, 3, v_r_5396_);
lean_ctor_set(v___x_5400_, 0, v___x_5311_);
v___x_5411_ = v___x_5400_;
goto v_reusejp_5410_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v___x_5311_);
lean_ctor_set(v_reuseFailAlloc_5415_, 1, v_k_5397_);
lean_ctor_set(v_reuseFailAlloc_5415_, 2, v_v_5398_);
lean_ctor_set(v_reuseFailAlloc_5415_, 3, v_r_5396_);
lean_ctor_set(v_reuseFailAlloc_5415_, 4, v_r_5396_);
v___x_5411_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5410_;
}
v_reusejp_5410_:
{
lean_object* v___x_5413_; 
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 4, v___x_5411_);
lean_ctor_set(v___x_5306_, 3, v___x_5409_);
lean_ctor_set(v___x_5306_, 2, v_v_5403_);
lean_ctor_set(v___x_5306_, 1, v_k_5402_);
lean_ctor_set(v___x_5306_, 0, v___x_5407_);
v___x_5413_ = v___x_5306_;
goto v_reusejp_5412_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v___x_5407_);
lean_ctor_set(v_reuseFailAlloc_5414_, 1, v_k_5402_);
lean_ctor_set(v_reuseFailAlloc_5414_, 2, v_v_5403_);
lean_ctor_set(v_reuseFailAlloc_5414_, 3, v___x_5409_);
lean_ctor_set(v_reuseFailAlloc_5414_, 4, v___x_5411_);
v___x_5413_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5412_;
}
v_reusejp_5412_:
{
return v___x_5413_;
}
}
}
}
}
}
else
{
lean_object* v_r_5424_; 
v_r_5424_ = lean_ctor_get(v_impl_5310_, 4);
lean_inc(v_r_5424_);
if (lean_obj_tag(v_r_5424_) == 0)
{
lean_object* v_k_5425_; lean_object* v_v_5426_; lean_object* v___x_5428_; uint8_t v_isShared_5429_; uint8_t v_isSharedCheck_5437_; 
v_k_5425_ = lean_ctor_get(v_impl_5310_, 1);
v_v_5426_ = lean_ctor_get(v_impl_5310_, 2);
v_isSharedCheck_5437_ = !lean_is_exclusive(v_impl_5310_);
if (v_isSharedCheck_5437_ == 0)
{
lean_object* v_unused_5438_; lean_object* v_unused_5439_; lean_object* v_unused_5440_; 
v_unused_5438_ = lean_ctor_get(v_impl_5310_, 4);
lean_dec(v_unused_5438_);
v_unused_5439_ = lean_ctor_get(v_impl_5310_, 3);
lean_dec(v_unused_5439_);
v_unused_5440_ = lean_ctor_get(v_impl_5310_, 0);
lean_dec(v_unused_5440_);
v___x_5428_ = v_impl_5310_;
v_isShared_5429_ = v_isSharedCheck_5437_;
goto v_resetjp_5427_;
}
else
{
lean_inc(v_v_5426_);
lean_inc(v_k_5425_);
lean_dec(v_impl_5310_);
v___x_5428_ = lean_box(0);
v_isShared_5429_ = v_isSharedCheck_5437_;
goto v_resetjp_5427_;
}
v_resetjp_5427_:
{
lean_object* v___x_5430_; lean_object* v___x_5432_; 
v___x_5430_ = lean_unsigned_to_nat(3u);
if (v_isShared_5429_ == 0)
{
lean_ctor_set(v___x_5428_, 4, v_l_5395_);
lean_ctor_set(v___x_5428_, 2, v_v_5302_);
lean_ctor_set(v___x_5428_, 1, v_k_5301_);
lean_ctor_set(v___x_5428_, 0, v___x_5311_);
v___x_5432_ = v___x_5428_;
goto v_reusejp_5431_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v___x_5311_);
lean_ctor_set(v_reuseFailAlloc_5436_, 1, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5436_, 2, v_v_5302_);
lean_ctor_set(v_reuseFailAlloc_5436_, 3, v_l_5395_);
lean_ctor_set(v_reuseFailAlloc_5436_, 4, v_l_5395_);
v___x_5432_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5431_;
}
v_reusejp_5431_:
{
lean_object* v___x_5434_; 
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 4, v_r_5424_);
lean_ctor_set(v___x_5306_, 3, v___x_5432_);
lean_ctor_set(v___x_5306_, 2, v_v_5426_);
lean_ctor_set(v___x_5306_, 1, v_k_5425_);
lean_ctor_set(v___x_5306_, 0, v___x_5430_);
v___x_5434_ = v___x_5306_;
goto v_reusejp_5433_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v___x_5430_);
lean_ctor_set(v_reuseFailAlloc_5435_, 1, v_k_5425_);
lean_ctor_set(v_reuseFailAlloc_5435_, 2, v_v_5426_);
lean_ctor_set(v_reuseFailAlloc_5435_, 3, v___x_5432_);
lean_ctor_set(v_reuseFailAlloc_5435_, 4, v_r_5424_);
v___x_5434_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5433_;
}
v_reusejp_5433_:
{
return v___x_5434_;
}
}
}
}
else
{
lean_object* v___x_5441_; lean_object* v___x_5443_; 
v___x_5441_ = lean_unsigned_to_nat(2u);
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 4, v_impl_5310_);
lean_ctor_set(v___x_5306_, 3, v_r_5424_);
lean_ctor_set(v___x_5306_, 0, v___x_5441_);
v___x_5443_ = v___x_5306_;
goto v_reusejp_5442_;
}
else
{
lean_object* v_reuseFailAlloc_5444_; 
v_reuseFailAlloc_5444_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5444_, 0, v___x_5441_);
lean_ctor_set(v_reuseFailAlloc_5444_, 1, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5444_, 2, v_v_5302_);
lean_ctor_set(v_reuseFailAlloc_5444_, 3, v_r_5424_);
lean_ctor_set(v_reuseFailAlloc_5444_, 4, v_impl_5310_);
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
else
{
lean_object* v___x_5446_; 
lean_dec(v_v_5302_);
lean_dec(v_k_5301_);
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 2, v_v_5298_);
lean_ctor_set(v___x_5306_, 1, v_k_5297_);
v___x_5446_ = v___x_5306_;
goto v_reusejp_5445_;
}
else
{
lean_object* v_reuseFailAlloc_5447_; 
v_reuseFailAlloc_5447_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5447_, 0, v_size_5300_);
lean_ctor_set(v_reuseFailAlloc_5447_, 1, v_k_5297_);
lean_ctor_set(v_reuseFailAlloc_5447_, 2, v_v_5298_);
lean_ctor_set(v_reuseFailAlloc_5447_, 3, v_l_5303_);
lean_ctor_set(v_reuseFailAlloc_5447_, 4, v_r_5304_);
v___x_5446_ = v_reuseFailAlloc_5447_;
goto v_reusejp_5445_;
}
v_reusejp_5445_:
{
return v___x_5446_;
}
}
}
else
{
lean_object* v_impl_5448_; lean_object* v___x_5449_; 
lean_dec(v_size_5300_);
v_impl_5448_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5297_, v_v_5298_, v_l_5303_);
v___x_5449_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5304_) == 0)
{
lean_object* v_size_5450_; lean_object* v_size_5451_; lean_object* v_k_5452_; lean_object* v_v_5453_; lean_object* v_l_5454_; lean_object* v_r_5455_; lean_object* v___x_5456_; lean_object* v___x_5457_; uint8_t v___x_5458_; 
v_size_5450_ = lean_ctor_get(v_r_5304_, 0);
v_size_5451_ = lean_ctor_get(v_impl_5448_, 0);
lean_inc(v_size_5451_);
v_k_5452_ = lean_ctor_get(v_impl_5448_, 1);
lean_inc(v_k_5452_);
v_v_5453_ = lean_ctor_get(v_impl_5448_, 2);
lean_inc(v_v_5453_);
v_l_5454_ = lean_ctor_get(v_impl_5448_, 3);
lean_inc(v_l_5454_);
v_r_5455_ = lean_ctor_get(v_impl_5448_, 4);
lean_inc(v_r_5455_);
v___x_5456_ = lean_unsigned_to_nat(3u);
v___x_5457_ = lean_nat_mul(v___x_5456_, v_size_5450_);
v___x_5458_ = lean_nat_dec_lt(v___x_5457_, v_size_5451_);
lean_dec(v___x_5457_);
if (v___x_5458_ == 0)
{
lean_object* v___x_5459_; lean_object* v___x_5460_; lean_object* v___x_5462_; 
lean_dec(v_r_5455_);
lean_dec(v_l_5454_);
lean_dec(v_v_5453_);
lean_dec(v_k_5452_);
v___x_5459_ = lean_nat_add(v___x_5449_, v_size_5451_);
lean_dec(v_size_5451_);
v___x_5460_ = lean_nat_add(v___x_5459_, v_size_5450_);
lean_dec(v___x_5459_);
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 3, v_impl_5448_);
lean_ctor_set(v___x_5306_, 0, v___x_5460_);
v___x_5462_ = v___x_5306_;
goto v_reusejp_5461_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v___x_5460_);
lean_ctor_set(v_reuseFailAlloc_5463_, 1, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5463_, 2, v_v_5302_);
lean_ctor_set(v_reuseFailAlloc_5463_, 3, v_impl_5448_);
lean_ctor_set(v_reuseFailAlloc_5463_, 4, v_r_5304_);
v___x_5462_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5461_;
}
v_reusejp_5461_:
{
return v___x_5462_;
}
}
else
{
lean_object* v___x_5465_; uint8_t v_isShared_5466_; uint8_t v_isSharedCheck_5529_; 
v_isSharedCheck_5529_ = !lean_is_exclusive(v_impl_5448_);
if (v_isSharedCheck_5529_ == 0)
{
lean_object* v_unused_5530_; lean_object* v_unused_5531_; lean_object* v_unused_5532_; lean_object* v_unused_5533_; lean_object* v_unused_5534_; 
v_unused_5530_ = lean_ctor_get(v_impl_5448_, 4);
lean_dec(v_unused_5530_);
v_unused_5531_ = lean_ctor_get(v_impl_5448_, 3);
lean_dec(v_unused_5531_);
v_unused_5532_ = lean_ctor_get(v_impl_5448_, 2);
lean_dec(v_unused_5532_);
v_unused_5533_ = lean_ctor_get(v_impl_5448_, 1);
lean_dec(v_unused_5533_);
v_unused_5534_ = lean_ctor_get(v_impl_5448_, 0);
lean_dec(v_unused_5534_);
v___x_5465_ = v_impl_5448_;
v_isShared_5466_ = v_isSharedCheck_5529_;
goto v_resetjp_5464_;
}
else
{
lean_dec(v_impl_5448_);
v___x_5465_ = lean_box(0);
v_isShared_5466_ = v_isSharedCheck_5529_;
goto v_resetjp_5464_;
}
v_resetjp_5464_:
{
lean_object* v_size_5467_; lean_object* v_size_5468_; lean_object* v_k_5469_; lean_object* v_v_5470_; lean_object* v_l_5471_; lean_object* v_r_5472_; lean_object* v___x_5473_; lean_object* v___x_5474_; uint8_t v___x_5475_; 
v_size_5467_ = lean_ctor_get(v_l_5454_, 0);
v_size_5468_ = lean_ctor_get(v_r_5455_, 0);
v_k_5469_ = lean_ctor_get(v_r_5455_, 1);
v_v_5470_ = lean_ctor_get(v_r_5455_, 2);
v_l_5471_ = lean_ctor_get(v_r_5455_, 3);
v_r_5472_ = lean_ctor_get(v_r_5455_, 4);
v___x_5473_ = lean_unsigned_to_nat(2u);
v___x_5474_ = lean_nat_mul(v___x_5473_, v_size_5467_);
v___x_5475_ = lean_nat_dec_lt(v_size_5468_, v___x_5474_);
lean_dec(v___x_5474_);
if (v___x_5475_ == 0)
{
lean_object* v___x_5477_; uint8_t v_isShared_5478_; uint8_t v_isSharedCheck_5504_; 
lean_inc(v_r_5472_);
lean_inc(v_l_5471_);
lean_inc(v_v_5470_);
lean_inc(v_k_5469_);
v_isSharedCheck_5504_ = !lean_is_exclusive(v_r_5455_);
if (v_isSharedCheck_5504_ == 0)
{
lean_object* v_unused_5505_; lean_object* v_unused_5506_; lean_object* v_unused_5507_; lean_object* v_unused_5508_; lean_object* v_unused_5509_; 
v_unused_5505_ = lean_ctor_get(v_r_5455_, 4);
lean_dec(v_unused_5505_);
v_unused_5506_ = lean_ctor_get(v_r_5455_, 3);
lean_dec(v_unused_5506_);
v_unused_5507_ = lean_ctor_get(v_r_5455_, 2);
lean_dec(v_unused_5507_);
v_unused_5508_ = lean_ctor_get(v_r_5455_, 1);
lean_dec(v_unused_5508_);
v_unused_5509_ = lean_ctor_get(v_r_5455_, 0);
lean_dec(v_unused_5509_);
v___x_5477_ = v_r_5455_;
v_isShared_5478_ = v_isSharedCheck_5504_;
goto v_resetjp_5476_;
}
else
{
lean_dec(v_r_5455_);
v___x_5477_ = lean_box(0);
v_isShared_5478_ = v_isSharedCheck_5504_;
goto v_resetjp_5476_;
}
v_resetjp_5476_:
{
lean_object* v___x_5479_; lean_object* v___x_5480_; lean_object* v___y_5482_; lean_object* v___y_5483_; lean_object* v___y_5484_; lean_object* v___x_5492_; lean_object* v___y_5494_; 
v___x_5479_ = lean_nat_add(v___x_5449_, v_size_5451_);
lean_dec(v_size_5451_);
v___x_5480_ = lean_nat_add(v___x_5479_, v_size_5450_);
lean_dec(v___x_5479_);
v___x_5492_ = lean_nat_add(v___x_5449_, v_size_5467_);
if (lean_obj_tag(v_l_5471_) == 0)
{
lean_object* v_size_5502_; 
v_size_5502_ = lean_ctor_get(v_l_5471_, 0);
lean_inc(v_size_5502_);
v___y_5494_ = v_size_5502_;
goto v___jp_5493_;
}
else
{
lean_object* v___x_5503_; 
v___x_5503_ = lean_unsigned_to_nat(0u);
v___y_5494_ = v___x_5503_;
goto v___jp_5493_;
}
v___jp_5481_:
{
lean_object* v___x_5485_; lean_object* v___x_5487_; 
v___x_5485_ = lean_nat_add(v___y_5482_, v___y_5484_);
lean_dec(v___y_5484_);
lean_dec(v___y_5482_);
if (v_isShared_5478_ == 0)
{
lean_ctor_set(v___x_5477_, 4, v_r_5304_);
lean_ctor_set(v___x_5477_, 3, v_r_5472_);
lean_ctor_set(v___x_5477_, 2, v_v_5302_);
lean_ctor_set(v___x_5477_, 1, v_k_5301_);
lean_ctor_set(v___x_5477_, 0, v___x_5485_);
v___x_5487_ = v___x_5477_;
goto v_reusejp_5486_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5485_);
lean_ctor_set(v_reuseFailAlloc_5491_, 1, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5491_, 2, v_v_5302_);
lean_ctor_set(v_reuseFailAlloc_5491_, 3, v_r_5472_);
lean_ctor_set(v_reuseFailAlloc_5491_, 4, v_r_5304_);
v___x_5487_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5486_;
}
v_reusejp_5486_:
{
lean_object* v___x_5489_; 
if (v_isShared_5466_ == 0)
{
lean_ctor_set(v___x_5465_, 4, v___x_5487_);
lean_ctor_set(v___x_5465_, 3, v___y_5483_);
lean_ctor_set(v___x_5465_, 2, v_v_5470_);
lean_ctor_set(v___x_5465_, 1, v_k_5469_);
lean_ctor_set(v___x_5465_, 0, v___x_5480_);
v___x_5489_ = v___x_5465_;
goto v_reusejp_5488_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v___x_5480_);
lean_ctor_set(v_reuseFailAlloc_5490_, 1, v_k_5469_);
lean_ctor_set(v_reuseFailAlloc_5490_, 2, v_v_5470_);
lean_ctor_set(v_reuseFailAlloc_5490_, 3, v___y_5483_);
lean_ctor_set(v_reuseFailAlloc_5490_, 4, v___x_5487_);
v___x_5489_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5488_;
}
v_reusejp_5488_:
{
return v___x_5489_;
}
}
}
v___jp_5493_:
{
lean_object* v___x_5495_; lean_object* v___x_5497_; 
v___x_5495_ = lean_nat_add(v___x_5492_, v___y_5494_);
lean_dec(v___y_5494_);
lean_dec(v___x_5492_);
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 4, v_l_5471_);
lean_ctor_set(v___x_5306_, 3, v_l_5454_);
lean_ctor_set(v___x_5306_, 2, v_v_5453_);
lean_ctor_set(v___x_5306_, 1, v_k_5452_);
lean_ctor_set(v___x_5306_, 0, v___x_5495_);
v___x_5497_ = v___x_5306_;
goto v_reusejp_5496_;
}
else
{
lean_object* v_reuseFailAlloc_5501_; 
v_reuseFailAlloc_5501_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5501_, 0, v___x_5495_);
lean_ctor_set(v_reuseFailAlloc_5501_, 1, v_k_5452_);
lean_ctor_set(v_reuseFailAlloc_5501_, 2, v_v_5453_);
lean_ctor_set(v_reuseFailAlloc_5501_, 3, v_l_5454_);
lean_ctor_set(v_reuseFailAlloc_5501_, 4, v_l_5471_);
v___x_5497_ = v_reuseFailAlloc_5501_;
goto v_reusejp_5496_;
}
v_reusejp_5496_:
{
lean_object* v___x_5498_; 
v___x_5498_ = lean_nat_add(v___x_5449_, v_size_5450_);
if (lean_obj_tag(v_r_5472_) == 0)
{
lean_object* v_size_5499_; 
v_size_5499_ = lean_ctor_get(v_r_5472_, 0);
lean_inc(v_size_5499_);
v___y_5482_ = v___x_5498_;
v___y_5483_ = v___x_5497_;
v___y_5484_ = v_size_5499_;
goto v___jp_5481_;
}
else
{
lean_object* v___x_5500_; 
v___x_5500_ = lean_unsigned_to_nat(0u);
v___y_5482_ = v___x_5498_;
v___y_5483_ = v___x_5497_;
v___y_5484_ = v___x_5500_;
goto v___jp_5481_;
}
}
}
}
}
else
{
lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5515_; 
lean_del_object(v___x_5306_);
v___x_5510_ = lean_nat_add(v___x_5449_, v_size_5451_);
lean_dec(v_size_5451_);
v___x_5511_ = lean_nat_add(v___x_5510_, v_size_5450_);
lean_dec(v___x_5510_);
v___x_5512_ = lean_nat_add(v___x_5449_, v_size_5450_);
v___x_5513_ = lean_nat_add(v___x_5512_, v_size_5468_);
lean_dec(v___x_5512_);
lean_inc_ref(v_r_5304_);
if (v_isShared_5466_ == 0)
{
lean_ctor_set(v___x_5465_, 4, v_r_5304_);
lean_ctor_set(v___x_5465_, 3, v_r_5455_);
lean_ctor_set(v___x_5465_, 2, v_v_5302_);
lean_ctor_set(v___x_5465_, 1, v_k_5301_);
lean_ctor_set(v___x_5465_, 0, v___x_5513_);
v___x_5515_ = v___x_5465_;
goto v_reusejp_5514_;
}
else
{
lean_object* v_reuseFailAlloc_5528_; 
v_reuseFailAlloc_5528_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5528_, 0, v___x_5513_);
lean_ctor_set(v_reuseFailAlloc_5528_, 1, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5528_, 2, v_v_5302_);
lean_ctor_set(v_reuseFailAlloc_5528_, 3, v_r_5455_);
lean_ctor_set(v_reuseFailAlloc_5528_, 4, v_r_5304_);
v___x_5515_ = v_reuseFailAlloc_5528_;
goto v_reusejp_5514_;
}
v_reusejp_5514_:
{
lean_object* v___x_5517_; uint8_t v_isShared_5518_; uint8_t v_isSharedCheck_5522_; 
v_isSharedCheck_5522_ = !lean_is_exclusive(v_r_5304_);
if (v_isSharedCheck_5522_ == 0)
{
lean_object* v_unused_5523_; lean_object* v_unused_5524_; lean_object* v_unused_5525_; lean_object* v_unused_5526_; lean_object* v_unused_5527_; 
v_unused_5523_ = lean_ctor_get(v_r_5304_, 4);
lean_dec(v_unused_5523_);
v_unused_5524_ = lean_ctor_get(v_r_5304_, 3);
lean_dec(v_unused_5524_);
v_unused_5525_ = lean_ctor_get(v_r_5304_, 2);
lean_dec(v_unused_5525_);
v_unused_5526_ = lean_ctor_get(v_r_5304_, 1);
lean_dec(v_unused_5526_);
v_unused_5527_ = lean_ctor_get(v_r_5304_, 0);
lean_dec(v_unused_5527_);
v___x_5517_ = v_r_5304_;
v_isShared_5518_ = v_isSharedCheck_5522_;
goto v_resetjp_5516_;
}
else
{
lean_dec(v_r_5304_);
v___x_5517_ = lean_box(0);
v_isShared_5518_ = v_isSharedCheck_5522_;
goto v_resetjp_5516_;
}
v_resetjp_5516_:
{
lean_object* v___x_5520_; 
if (v_isShared_5518_ == 0)
{
lean_ctor_set(v___x_5517_, 4, v___x_5515_);
lean_ctor_set(v___x_5517_, 3, v_l_5454_);
lean_ctor_set(v___x_5517_, 2, v_v_5453_);
lean_ctor_set(v___x_5517_, 1, v_k_5452_);
lean_ctor_set(v___x_5517_, 0, v___x_5511_);
v___x_5520_ = v___x_5517_;
goto v_reusejp_5519_;
}
else
{
lean_object* v_reuseFailAlloc_5521_; 
v_reuseFailAlloc_5521_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5521_, 0, v___x_5511_);
lean_ctor_set(v_reuseFailAlloc_5521_, 1, v_k_5452_);
lean_ctor_set(v_reuseFailAlloc_5521_, 2, v_v_5453_);
lean_ctor_set(v_reuseFailAlloc_5521_, 3, v_l_5454_);
lean_ctor_set(v_reuseFailAlloc_5521_, 4, v___x_5515_);
v___x_5520_ = v_reuseFailAlloc_5521_;
goto v_reusejp_5519_;
}
v_reusejp_5519_:
{
return v___x_5520_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5535_; 
v_l_5535_ = lean_ctor_get(v_impl_5448_, 3);
lean_inc(v_l_5535_);
if (lean_obj_tag(v_l_5535_) == 0)
{
lean_object* v_r_5536_; lean_object* v_k_5537_; lean_object* v_v_5538_; lean_object* v___x_5540_; uint8_t v_isShared_5541_; uint8_t v_isSharedCheck_5549_; 
v_r_5536_ = lean_ctor_get(v_impl_5448_, 4);
v_k_5537_ = lean_ctor_get(v_impl_5448_, 1);
v_v_5538_ = lean_ctor_get(v_impl_5448_, 2);
v_isSharedCheck_5549_ = !lean_is_exclusive(v_impl_5448_);
if (v_isSharedCheck_5549_ == 0)
{
lean_object* v_unused_5550_; lean_object* v_unused_5551_; 
v_unused_5550_ = lean_ctor_get(v_impl_5448_, 3);
lean_dec(v_unused_5550_);
v_unused_5551_ = lean_ctor_get(v_impl_5448_, 0);
lean_dec(v_unused_5551_);
v___x_5540_ = v_impl_5448_;
v_isShared_5541_ = v_isSharedCheck_5549_;
goto v_resetjp_5539_;
}
else
{
lean_inc(v_r_5536_);
lean_inc(v_v_5538_);
lean_inc(v_k_5537_);
lean_dec(v_impl_5448_);
v___x_5540_ = lean_box(0);
v_isShared_5541_ = v_isSharedCheck_5549_;
goto v_resetjp_5539_;
}
v_resetjp_5539_:
{
lean_object* v___x_5542_; lean_object* v___x_5544_; 
v___x_5542_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5536_);
if (v_isShared_5541_ == 0)
{
lean_ctor_set(v___x_5540_, 3, v_r_5536_);
lean_ctor_set(v___x_5540_, 2, v_v_5302_);
lean_ctor_set(v___x_5540_, 1, v_k_5301_);
lean_ctor_set(v___x_5540_, 0, v___x_5449_);
v___x_5544_ = v___x_5540_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v___x_5449_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5548_, 2, v_v_5302_);
lean_ctor_set(v_reuseFailAlloc_5548_, 3, v_r_5536_);
lean_ctor_set(v_reuseFailAlloc_5548_, 4, v_r_5536_);
v___x_5544_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
lean_object* v___x_5546_; 
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 4, v___x_5544_);
lean_ctor_set(v___x_5306_, 3, v_l_5535_);
lean_ctor_set(v___x_5306_, 2, v_v_5538_);
lean_ctor_set(v___x_5306_, 1, v_k_5537_);
lean_ctor_set(v___x_5306_, 0, v___x_5542_);
v___x_5546_ = v___x_5306_;
goto v_reusejp_5545_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v___x_5542_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v_k_5537_);
lean_ctor_set(v_reuseFailAlloc_5547_, 2, v_v_5538_);
lean_ctor_set(v_reuseFailAlloc_5547_, 3, v_l_5535_);
lean_ctor_set(v_reuseFailAlloc_5547_, 4, v___x_5544_);
v___x_5546_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5545_;
}
v_reusejp_5545_:
{
return v___x_5546_;
}
}
}
}
else
{
lean_object* v_r_5552_; 
v_r_5552_ = lean_ctor_get(v_impl_5448_, 4);
lean_inc(v_r_5552_);
if (lean_obj_tag(v_r_5552_) == 0)
{
lean_object* v_k_5553_; lean_object* v_v_5554_; lean_object* v___x_5556_; uint8_t v_isShared_5557_; uint8_t v_isSharedCheck_5577_; 
v_k_5553_ = lean_ctor_get(v_impl_5448_, 1);
v_v_5554_ = lean_ctor_get(v_impl_5448_, 2);
v_isSharedCheck_5577_ = !lean_is_exclusive(v_impl_5448_);
if (v_isSharedCheck_5577_ == 0)
{
lean_object* v_unused_5578_; lean_object* v_unused_5579_; lean_object* v_unused_5580_; 
v_unused_5578_ = lean_ctor_get(v_impl_5448_, 4);
lean_dec(v_unused_5578_);
v_unused_5579_ = lean_ctor_get(v_impl_5448_, 3);
lean_dec(v_unused_5579_);
v_unused_5580_ = lean_ctor_get(v_impl_5448_, 0);
lean_dec(v_unused_5580_);
v___x_5556_ = v_impl_5448_;
v_isShared_5557_ = v_isSharedCheck_5577_;
goto v_resetjp_5555_;
}
else
{
lean_inc(v_v_5554_);
lean_inc(v_k_5553_);
lean_dec(v_impl_5448_);
v___x_5556_ = lean_box(0);
v_isShared_5557_ = v_isSharedCheck_5577_;
goto v_resetjp_5555_;
}
v_resetjp_5555_:
{
lean_object* v_k_5558_; lean_object* v_v_5559_; lean_object* v___x_5561_; uint8_t v_isShared_5562_; uint8_t v_isSharedCheck_5573_; 
v_k_5558_ = lean_ctor_get(v_r_5552_, 1);
v_v_5559_ = lean_ctor_get(v_r_5552_, 2);
v_isSharedCheck_5573_ = !lean_is_exclusive(v_r_5552_);
if (v_isSharedCheck_5573_ == 0)
{
lean_object* v_unused_5574_; lean_object* v_unused_5575_; lean_object* v_unused_5576_; 
v_unused_5574_ = lean_ctor_get(v_r_5552_, 4);
lean_dec(v_unused_5574_);
v_unused_5575_ = lean_ctor_get(v_r_5552_, 3);
lean_dec(v_unused_5575_);
v_unused_5576_ = lean_ctor_get(v_r_5552_, 0);
lean_dec(v_unused_5576_);
v___x_5561_ = v_r_5552_;
v_isShared_5562_ = v_isSharedCheck_5573_;
goto v_resetjp_5560_;
}
else
{
lean_inc(v_v_5559_);
lean_inc(v_k_5558_);
lean_dec(v_r_5552_);
v___x_5561_ = lean_box(0);
v_isShared_5562_ = v_isSharedCheck_5573_;
goto v_resetjp_5560_;
}
v_resetjp_5560_:
{
lean_object* v___x_5563_; lean_object* v___x_5565_; 
v___x_5563_ = lean_unsigned_to_nat(3u);
if (v_isShared_5562_ == 0)
{
lean_ctor_set(v___x_5561_, 4, v_l_5535_);
lean_ctor_set(v___x_5561_, 3, v_l_5535_);
lean_ctor_set(v___x_5561_, 2, v_v_5554_);
lean_ctor_set(v___x_5561_, 1, v_k_5553_);
lean_ctor_set(v___x_5561_, 0, v___x_5449_);
v___x_5565_ = v___x_5561_;
goto v_reusejp_5564_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v___x_5449_);
lean_ctor_set(v_reuseFailAlloc_5572_, 1, v_k_5553_);
lean_ctor_set(v_reuseFailAlloc_5572_, 2, v_v_5554_);
lean_ctor_set(v_reuseFailAlloc_5572_, 3, v_l_5535_);
lean_ctor_set(v_reuseFailAlloc_5572_, 4, v_l_5535_);
v___x_5565_ = v_reuseFailAlloc_5572_;
goto v_reusejp_5564_;
}
v_reusejp_5564_:
{
lean_object* v___x_5567_; 
if (v_isShared_5557_ == 0)
{
lean_ctor_set(v___x_5556_, 4, v_l_5535_);
lean_ctor_set(v___x_5556_, 2, v_v_5302_);
lean_ctor_set(v___x_5556_, 1, v_k_5301_);
lean_ctor_set(v___x_5556_, 0, v___x_5449_);
v___x_5567_ = v___x_5556_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5449_);
lean_ctor_set(v_reuseFailAlloc_5571_, 1, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5571_, 2, v_v_5302_);
lean_ctor_set(v_reuseFailAlloc_5571_, 3, v_l_5535_);
lean_ctor_set(v_reuseFailAlloc_5571_, 4, v_l_5535_);
v___x_5567_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
lean_object* v___x_5569_; 
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 4, v___x_5567_);
lean_ctor_set(v___x_5306_, 3, v___x_5565_);
lean_ctor_set(v___x_5306_, 2, v_v_5559_);
lean_ctor_set(v___x_5306_, 1, v_k_5558_);
lean_ctor_set(v___x_5306_, 0, v___x_5563_);
v___x_5569_ = v___x_5306_;
goto v_reusejp_5568_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v___x_5563_);
lean_ctor_set(v_reuseFailAlloc_5570_, 1, v_k_5558_);
lean_ctor_set(v_reuseFailAlloc_5570_, 2, v_v_5559_);
lean_ctor_set(v_reuseFailAlloc_5570_, 3, v___x_5565_);
lean_ctor_set(v_reuseFailAlloc_5570_, 4, v___x_5567_);
v___x_5569_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5568_;
}
v_reusejp_5568_:
{
return v___x_5569_;
}
}
}
}
}
}
else
{
lean_object* v___x_5581_; lean_object* v___x_5583_; 
v___x_5581_ = lean_unsigned_to_nat(2u);
if (v_isShared_5307_ == 0)
{
lean_ctor_set(v___x_5306_, 4, v_r_5552_);
lean_ctor_set(v___x_5306_, 3, v_impl_5448_);
lean_ctor_set(v___x_5306_, 0, v___x_5581_);
v___x_5583_ = v___x_5306_;
goto v_reusejp_5582_;
}
else
{
lean_object* v_reuseFailAlloc_5584_; 
v_reuseFailAlloc_5584_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5584_, 0, v___x_5581_);
lean_ctor_set(v_reuseFailAlloc_5584_, 1, v_k_5301_);
lean_ctor_set(v_reuseFailAlloc_5584_, 2, v_v_5302_);
lean_ctor_set(v_reuseFailAlloc_5584_, 3, v_impl_5448_);
lean_ctor_set(v_reuseFailAlloc_5584_, 4, v_r_5552_);
v___x_5583_ = v_reuseFailAlloc_5584_;
goto v_reusejp_5582_;
}
v_reusejp_5582_:
{
return v___x_5583_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5586_; lean_object* v___x_5587_; 
v___x_5586_ = lean_unsigned_to_nat(1u);
v___x_5587_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5587_, 0, v___x_5586_);
lean_ctor_set(v___x_5587_, 1, v_k_5297_);
lean_ctor_set(v___x_5587_, 2, v_v_5298_);
lean_ctor_set(v___x_5587_, 3, v_t_5299_);
lean_ctor_set(v___x_5587_, 4, v_t_5299_);
return v___x_5587_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5588_, lean_object* v_t_5589_){
_start:
{
if (lean_obj_tag(v_t_5589_) == 0)
{
lean_object* v_k_5590_; lean_object* v_l_5591_; lean_object* v_r_5592_; uint8_t v___x_5593_; 
v_k_5590_ = lean_ctor_get(v_t_5589_, 1);
v_l_5591_ = lean_ctor_get(v_t_5589_, 3);
v_r_5592_ = lean_ctor_get(v_t_5589_, 4);
v___x_5593_ = lean_nat_dec_lt(v_k_5590_, v_k_5588_);
if (v___x_5593_ == 0)
{
uint8_t v___x_5594_; 
v___x_5594_ = lean_nat_dec_eq(v_k_5590_, v_k_5588_);
if (v___x_5594_ == 0)
{
v_t_5589_ = v_r_5592_;
goto _start;
}
else
{
return v___x_5594_;
}
}
else
{
v_t_5589_ = v_l_5591_;
goto _start;
}
}
else
{
uint8_t v___x_5597_; 
v___x_5597_ = 0;
return v___x_5597_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5598_, lean_object* v_t_5599_){
_start:
{
uint8_t v_res_5600_; lean_object* v_r_5601_; 
v_res_5600_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5598_, v_t_5599_);
lean_dec(v_t_5599_);
lean_dec(v_k_5598_);
v_r_5601_ = lean_box(v_res_5600_);
return v_r_5601_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5602_, lean_object* v_e_5603_){
_start:
{
lean_object* v_defaultInstances_5604_; lean_object* v_priorities_5605_; lean_object* v___x_5607_; uint8_t v_isShared_5608_; uint8_t v_isSharedCheck_5632_; 
v_defaultInstances_5604_ = lean_ctor_get(v_d_5602_, 0);
v_priorities_5605_ = lean_ctor_get(v_d_5602_, 1);
v_isSharedCheck_5632_ = !lean_is_exclusive(v_d_5602_);
if (v_isSharedCheck_5632_ == 0)
{
v___x_5607_ = v_d_5602_;
v_isShared_5608_ = v_isSharedCheck_5632_;
goto v_resetjp_5606_;
}
else
{
lean_inc(v_priorities_5605_);
lean_inc(v_defaultInstances_5604_);
lean_dec(v_d_5602_);
v___x_5607_ = lean_box(0);
v_isShared_5608_ = v_isSharedCheck_5632_;
goto v_resetjp_5606_;
}
v_resetjp_5606_:
{
lean_object* v_className_5609_; lean_object* v_instanceName_5610_; lean_object* v_priority_5611_; lean_object* v___y_5613_; uint8_t v___x_5629_; 
v_className_5609_ = lean_ctor_get(v_e_5603_, 0);
lean_inc(v_className_5609_);
v_instanceName_5610_ = lean_ctor_get(v_e_5603_, 1);
lean_inc(v_instanceName_5610_);
v_priority_5611_ = lean_ctor_get(v_e_5603_, 2);
lean_inc(v_priority_5611_);
lean_dec_ref(v_e_5603_);
v___x_5629_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5611_, v_priorities_5605_);
if (v___x_5629_ == 0)
{
lean_object* v___x_5630_; lean_object* v___x_5631_; 
v___x_5630_ = lean_box(0);
lean_inc(v_priority_5611_);
v___x_5631_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5611_, v___x_5630_, v_priorities_5605_);
v___y_5613_ = v___x_5631_;
goto v___jp_5612_;
}
else
{
v___y_5613_ = v_priorities_5605_;
goto v___jp_5612_;
}
v___jp_5612_:
{
lean_object* v___x_5614_; 
v___x_5614_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5604_, v_className_5609_);
if (lean_obj_tag(v___x_5614_) == 0)
{
lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5620_; 
v___x_5615_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5615_, 0, v_instanceName_5610_);
lean_ctor_set(v___x_5615_, 1, v_priority_5611_);
v___x_5616_ = lean_box(0);
v___x_5617_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5617_, 0, v___x_5615_);
lean_ctor_set(v___x_5617_, 1, v___x_5616_);
v___x_5618_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5609_, v___x_5617_, v_defaultInstances_5604_);
if (v_isShared_5608_ == 0)
{
lean_ctor_set(v___x_5607_, 1, v___y_5613_);
lean_ctor_set(v___x_5607_, 0, v___x_5618_);
v___x_5620_ = v___x_5607_;
goto v_reusejp_5619_;
}
else
{
lean_object* v_reuseFailAlloc_5621_; 
v_reuseFailAlloc_5621_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5621_, 0, v___x_5618_);
lean_ctor_set(v_reuseFailAlloc_5621_, 1, v___y_5613_);
v___x_5620_ = v_reuseFailAlloc_5621_;
goto v_reusejp_5619_;
}
v_reusejp_5619_:
{
return v___x_5620_;
}
}
else
{
lean_object* v_val_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5627_; 
v_val_5622_ = lean_ctor_get(v___x_5614_, 0);
lean_inc(v_val_5622_);
lean_dec_ref_known(v___x_5614_, 1);
v___x_5623_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5623_, 0, v_instanceName_5610_);
lean_ctor_set(v___x_5623_, 1, v_priority_5611_);
v___x_5624_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5624_, 0, v___x_5623_);
lean_ctor_set(v___x_5624_, 1, v_val_5622_);
v___x_5625_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5609_, v___x_5624_, v_defaultInstances_5604_);
if (v_isShared_5608_ == 0)
{
lean_ctor_set(v___x_5607_, 1, v___y_5613_);
lean_ctor_set(v___x_5607_, 0, v___x_5625_);
v___x_5627_ = v___x_5607_;
goto v_reusejp_5626_;
}
else
{
lean_object* v_reuseFailAlloc_5628_; 
v_reuseFailAlloc_5628_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5628_, 0, v___x_5625_);
lean_ctor_set(v_reuseFailAlloc_5628_, 1, v___y_5613_);
v___x_5627_ = v_reuseFailAlloc_5628_;
goto v_reusejp_5626_;
}
v_reusejp_5626_:
{
return v___x_5627_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5633_, lean_object* v_k_5634_, lean_object* v_t_5635_){
_start:
{
uint8_t v___x_5636_; 
v___x_5636_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5634_, v_t_5635_);
return v___x_5636_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5637_, lean_object* v_k_5638_, lean_object* v_t_5639_){
_start:
{
uint8_t v_res_5640_; lean_object* v_r_5641_; 
v_res_5640_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5637_, v_k_5638_, v_t_5639_);
lean_dec(v_t_5639_);
lean_dec(v_k_5638_);
v_r_5641_ = lean_box(v_res_5640_);
return v_r_5641_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5642_, lean_object* v_k_5643_, lean_object* v_v_5644_, lean_object* v_t_5645_, lean_object* v_hl_5646_){
_start:
{
lean_object* v___x_5647_; 
v___x_5647_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5643_, v_v_5644_, v_t_5645_);
return v___x_5647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object* v_env_5648_, lean_object* v_as_5649_, size_t v_i_5650_, size_t v_stop_5651_, lean_object* v_b_5652_){
_start:
{
lean_object* v___y_5654_; uint8_t v___x_5658_; 
v___x_5658_ = lean_usize_dec_eq(v_i_5650_, v_stop_5651_);
if (v___x_5658_ == 0)
{
lean_object* v___x_5659_; lean_object* v_instanceName_5660_; uint8_t v___x_5661_; lean_object* v___x_5662_; uint8_t v___x_5663_; 
v___x_5659_ = lean_array_uget_borrowed(v_as_5649_, v_i_5650_);
v_instanceName_5660_ = lean_ctor_get(v___x_5659_, 1);
v___x_5661_ = 1;
lean_inc_ref(v_env_5648_);
v___x_5662_ = l_Lean_Environment_setExporting(v_env_5648_, v___x_5661_);
lean_inc(v_instanceName_5660_);
v___x_5663_ = l_Lean_Environment_contains(v___x_5662_, v_instanceName_5660_, v___x_5658_);
if (v___x_5663_ == 0)
{
v___y_5654_ = v_b_5652_;
goto v___jp_5653_;
}
else
{
lean_object* v___x_5664_; 
lean_inc(v___x_5659_);
v___x_5664_ = lean_array_push(v_b_5652_, v___x_5659_);
v___y_5654_ = v___x_5664_;
goto v___jp_5653_;
}
}
else
{
lean_dec_ref(v_env_5648_);
return v_b_5652_;
}
v___jp_5653_:
{
size_t v___x_5655_; size_t v___x_5656_; 
v___x_5655_ = ((size_t)1ULL);
v___x_5656_ = lean_usize_add(v_i_5650_, v___x_5655_);
v_i_5650_ = v___x_5656_;
v_b_5652_ = v___y_5654_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_5665_, lean_object* v_as_5666_, lean_object* v_i_5667_, lean_object* v_stop_5668_, lean_object* v_b_5669_){
_start:
{
size_t v_i_boxed_5670_; size_t v_stop_boxed_5671_; lean_object* v_res_5672_; 
v_i_boxed_5670_ = lean_unbox_usize(v_i_5667_);
lean_dec(v_i_5667_);
v_stop_boxed_5671_ = lean_unbox_usize(v_stop_5668_);
lean_dec(v_stop_5668_);
v_res_5672_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5665_, v_as_5666_, v_i_boxed_5670_, v_stop_boxed_5671_, v_b_5669_);
lean_dec_ref(v_as_5666_);
return v_res_5672_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_env_5675_, lean_object* v_x_5676_, lean_object* v_entries_5677_){
_start:
{
lean_object* v_all_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; uint8_t v___x_5682_; 
v_all_5678_ = lean_array_mk(v_entries_5677_);
v___x_5679_ = lean_unsigned_to_nat(0u);
v___x_5680_ = lean_array_get_size(v_all_5678_);
v___x_5681_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5682_ = lean_nat_dec_lt(v___x_5679_, v___x_5680_);
if (v___x_5682_ == 0)
{
lean_object* v___x_5683_; 
lean_dec_ref(v_env_5675_);
v___x_5683_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5683_, 0, v___x_5681_);
lean_ctor_set(v___x_5683_, 1, v___x_5681_);
lean_ctor_set(v___x_5683_, 2, v_all_5678_);
return v___x_5683_;
}
else
{
uint8_t v___x_5684_; 
v___x_5684_ = lean_nat_dec_le(v___x_5680_, v___x_5680_);
if (v___x_5684_ == 0)
{
if (v___x_5682_ == 0)
{
lean_object* v___x_5685_; 
lean_dec_ref(v_env_5675_);
v___x_5685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5685_, 0, v___x_5681_);
lean_ctor_set(v___x_5685_, 1, v___x_5681_);
lean_ctor_set(v___x_5685_, 2, v_all_5678_);
return v___x_5685_;
}
else
{
size_t v___x_5686_; size_t v___x_5687_; lean_object* v___x_5688_; lean_object* v___x_5689_; 
v___x_5686_ = ((size_t)0ULL);
v___x_5687_ = lean_usize_of_nat(v___x_5680_);
v___x_5688_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5675_, v_all_5678_, v___x_5686_, v___x_5687_, v___x_5681_);
lean_inc_ref(v___x_5688_);
v___x_5689_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5689_, 0, v___x_5688_);
lean_ctor_set(v___x_5689_, 1, v___x_5688_);
lean_ctor_set(v___x_5689_, 2, v_all_5678_);
return v___x_5689_;
}
}
else
{
size_t v___x_5690_; size_t v___x_5691_; lean_object* v___x_5692_; lean_object* v___x_5693_; 
v___x_5690_ = ((size_t)0ULL);
v___x_5691_ = lean_usize_of_nat(v___x_5680_);
v___x_5692_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5675_, v_all_5678_, v___x_5690_, v___x_5691_, v___x_5681_);
lean_inc_ref(v___x_5692_);
v___x_5693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5693_, 0, v___x_5692_);
lean_ctor_set(v___x_5693_, 1, v___x_5692_);
lean_ctor_set(v___x_5693_, 2, v_all_5678_);
return v___x_5693_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5694_, lean_object* v_x_5695_, lean_object* v_entries_5696_){
_start:
{
lean_object* v_res_5697_; 
v_res_5697_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5694_, v_x_5695_, v_entries_5696_);
lean_dec_ref(v_x_5695_);
return v_res_5697_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5698_){
_start:
{
lean_object* v___x_5699_; 
v___x_5699_ = lean_array_mk(v_es_5698_);
return v___x_5699_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5700_, size_t v_i_5701_, size_t v_stop_5702_, lean_object* v_b_5703_){
_start:
{
uint8_t v___x_5704_; 
v___x_5704_ = lean_usize_dec_eq(v_i_5701_, v_stop_5702_);
if (v___x_5704_ == 0)
{
lean_object* v___x_5705_; lean_object* v___x_5706_; size_t v___x_5707_; size_t v___x_5708_; 
v___x_5705_ = lean_array_uget_borrowed(v_as_5700_, v_i_5701_);
lean_inc(v___x_5705_);
v___x_5706_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5703_, v___x_5705_);
v___x_5707_ = ((size_t)1ULL);
v___x_5708_ = lean_usize_add(v_i_5701_, v___x_5707_);
v_i_5701_ = v___x_5708_;
v_b_5703_ = v___x_5706_;
goto _start;
}
else
{
return v_b_5703_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5710_, lean_object* v_i_5711_, lean_object* v_stop_5712_, lean_object* v_b_5713_){
_start:
{
size_t v_i_boxed_5714_; size_t v_stop_boxed_5715_; lean_object* v_res_5716_; 
v_i_boxed_5714_ = lean_unbox_usize(v_i_5711_);
lean_dec(v_i_5711_);
v_stop_boxed_5715_ = lean_unbox_usize(v_stop_5712_);
lean_dec(v_stop_5712_);
v_res_5716_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5710_, v_i_boxed_5714_, v_stop_boxed_5715_, v_b_5713_);
lean_dec_ref(v_as_5710_);
return v_res_5716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5717_, size_t v_i_5718_, size_t v_stop_5719_, lean_object* v_b_5720_){
_start:
{
lean_object* v___y_5722_; uint8_t v___x_5726_; 
v___x_5726_ = lean_usize_dec_eq(v_i_5718_, v_stop_5719_);
if (v___x_5726_ == 0)
{
lean_object* v___x_5727_; lean_object* v___x_5728_; lean_object* v___x_5729_; uint8_t v___x_5730_; 
v___x_5727_ = lean_array_uget_borrowed(v_as_5717_, v_i_5718_);
v___x_5728_ = lean_unsigned_to_nat(0u);
v___x_5729_ = lean_array_get_size(v___x_5727_);
v___x_5730_ = lean_nat_dec_lt(v___x_5728_, v___x_5729_);
if (v___x_5730_ == 0)
{
v___y_5722_ = v_b_5720_;
goto v___jp_5721_;
}
else
{
uint8_t v___x_5731_; 
v___x_5731_ = lean_nat_dec_le(v___x_5729_, v___x_5729_);
if (v___x_5731_ == 0)
{
if (v___x_5730_ == 0)
{
v___y_5722_ = v_b_5720_;
goto v___jp_5721_;
}
else
{
size_t v___x_5732_; size_t v___x_5733_; lean_object* v___x_5734_; 
v___x_5732_ = ((size_t)0ULL);
v___x_5733_ = lean_usize_of_nat(v___x_5729_);
v___x_5734_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5727_, v___x_5732_, v___x_5733_, v_b_5720_);
v___y_5722_ = v___x_5734_;
goto v___jp_5721_;
}
}
else
{
size_t v___x_5735_; size_t v___x_5736_; lean_object* v___x_5737_; 
v___x_5735_ = ((size_t)0ULL);
v___x_5736_ = lean_usize_of_nat(v___x_5729_);
v___x_5737_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5727_, v___x_5735_, v___x_5736_, v_b_5720_);
v___y_5722_ = v___x_5737_;
goto v___jp_5721_;
}
}
}
else
{
return v_b_5720_;
}
v___jp_5721_:
{
size_t v___x_5723_; size_t v___x_5724_; 
v___x_5723_ = ((size_t)1ULL);
v___x_5724_ = lean_usize_add(v_i_5718_, v___x_5723_);
v_i_5718_ = v___x_5724_;
v_b_5720_ = v___y_5722_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5738_, lean_object* v_i_5739_, lean_object* v_stop_5740_, lean_object* v_b_5741_){
_start:
{
size_t v_i_boxed_5742_; size_t v_stop_boxed_5743_; lean_object* v_res_5744_; 
v_i_boxed_5742_ = lean_unbox_usize(v_i_5739_);
lean_dec(v_i_5739_);
v_stop_boxed_5743_ = lean_unbox_usize(v_stop_5740_);
lean_dec(v_stop_5740_);
v_res_5744_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5738_, v_i_boxed_5742_, v_stop_boxed_5743_, v_b_5741_);
lean_dec_ref(v_as_5738_);
return v_res_5744_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_5745_, lean_object* v_as_5746_){
_start:
{
lean_object* v___x_5747_; lean_object* v___x_5748_; uint8_t v___x_5749_; 
v___x_5747_ = lean_unsigned_to_nat(0u);
v___x_5748_ = lean_array_get_size(v_as_5746_);
v___x_5749_ = lean_nat_dec_lt(v___x_5747_, v___x_5748_);
if (v___x_5749_ == 0)
{
return v_initState_5745_;
}
else
{
uint8_t v___x_5750_; 
v___x_5750_ = lean_nat_dec_le(v___x_5748_, v___x_5748_);
if (v___x_5750_ == 0)
{
if (v___x_5749_ == 0)
{
return v_initState_5745_;
}
else
{
size_t v___x_5751_; size_t v___x_5752_; lean_object* v___x_5753_; 
v___x_5751_ = ((size_t)0ULL);
v___x_5752_ = lean_usize_of_nat(v___x_5748_);
v___x_5753_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5746_, v___x_5751_, v___x_5752_, v_initState_5745_);
return v___x_5753_;
}
}
else
{
size_t v___x_5754_; size_t v___x_5755_; lean_object* v___x_5756_; 
v___x_5754_ = ((size_t)0ULL);
v___x_5755_ = lean_usize_of_nat(v___x_5748_);
v___x_5756_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5746_, v___x_5754_, v___x_5755_, v_initState_5745_);
return v___x_5756_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_5757_, lean_object* v_as_5758_){
_start:
{
lean_object* v_res_5759_; 
v_res_5759_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_5757_, v_as_5758_);
lean_dec_ref(v_as_5758_);
return v_res_5759_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5760_){
_start:
{
lean_object* v___x_5761_; lean_object* v___x_5762_; 
v___x_5761_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5762_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_5761_, v_es_5760_);
return v___x_5762_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_5763_){
_start:
{
lean_object* v_res_5764_; 
v_res_5764_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_5763_);
lean_dec_ref(v_es_5763_);
return v_res_5764_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5785_; lean_object* v___x_5786_; 
v___x_5785_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5786_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5785_);
return v___x_5786_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_5787_){
_start:
{
lean_object* v_res_5788_; 
v_res_5788_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_5788_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5789_, lean_object* v___y_5790_, lean_object* v___y_5791_){
_start:
{
lean_object* v___x_5793_; lean_object* v_nextMacroScope_5794_; lean_object* v_ngen_5795_; lean_object* v_auxDeclNGen_5796_; lean_object* v_traceState_5797_; lean_object* v_messages_5798_; lean_object* v_infoState_5799_; lean_object* v_snapshotTasks_5800_; lean_object* v___x_5802_; uint8_t v_isShared_5803_; uint8_t v_isSharedCheck_5826_; 
v___x_5793_ = lean_st_ref_take(v___y_5791_);
v_nextMacroScope_5794_ = lean_ctor_get(v___x_5793_, 1);
v_ngen_5795_ = lean_ctor_get(v___x_5793_, 2);
v_auxDeclNGen_5796_ = lean_ctor_get(v___x_5793_, 3);
v_traceState_5797_ = lean_ctor_get(v___x_5793_, 4);
v_messages_5798_ = lean_ctor_get(v___x_5793_, 6);
v_infoState_5799_ = lean_ctor_get(v___x_5793_, 7);
v_snapshotTasks_5800_ = lean_ctor_get(v___x_5793_, 8);
v_isSharedCheck_5826_ = !lean_is_exclusive(v___x_5793_);
if (v_isSharedCheck_5826_ == 0)
{
lean_object* v_unused_5827_; lean_object* v_unused_5828_; 
v_unused_5827_ = lean_ctor_get(v___x_5793_, 5);
lean_dec(v_unused_5827_);
v_unused_5828_ = lean_ctor_get(v___x_5793_, 0);
lean_dec(v_unused_5828_);
v___x_5802_ = v___x_5793_;
v_isShared_5803_ = v_isSharedCheck_5826_;
goto v_resetjp_5801_;
}
else
{
lean_inc(v_snapshotTasks_5800_);
lean_inc(v_infoState_5799_);
lean_inc(v_messages_5798_);
lean_inc(v_traceState_5797_);
lean_inc(v_auxDeclNGen_5796_);
lean_inc(v_ngen_5795_);
lean_inc(v_nextMacroScope_5794_);
lean_dec(v___x_5793_);
v___x_5802_ = lean_box(0);
v_isShared_5803_ = v_isSharedCheck_5826_;
goto v_resetjp_5801_;
}
v_resetjp_5801_:
{
lean_object* v___x_5804_; lean_object* v___x_5806_; 
v___x_5804_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5803_ == 0)
{
lean_ctor_set(v___x_5802_, 5, v___x_5804_);
lean_ctor_set(v___x_5802_, 0, v_env_5789_);
v___x_5806_ = v___x_5802_;
goto v_reusejp_5805_;
}
else
{
lean_object* v_reuseFailAlloc_5825_; 
v_reuseFailAlloc_5825_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5825_, 0, v_env_5789_);
lean_ctor_set(v_reuseFailAlloc_5825_, 1, v_nextMacroScope_5794_);
lean_ctor_set(v_reuseFailAlloc_5825_, 2, v_ngen_5795_);
lean_ctor_set(v_reuseFailAlloc_5825_, 3, v_auxDeclNGen_5796_);
lean_ctor_set(v_reuseFailAlloc_5825_, 4, v_traceState_5797_);
lean_ctor_set(v_reuseFailAlloc_5825_, 5, v___x_5804_);
lean_ctor_set(v_reuseFailAlloc_5825_, 6, v_messages_5798_);
lean_ctor_set(v_reuseFailAlloc_5825_, 7, v_infoState_5799_);
lean_ctor_set(v_reuseFailAlloc_5825_, 8, v_snapshotTasks_5800_);
v___x_5806_ = v_reuseFailAlloc_5825_;
goto v_reusejp_5805_;
}
v_reusejp_5805_:
{
lean_object* v___x_5807_; lean_object* v___x_5808_; lean_object* v_mctx_5809_; lean_object* v_zetaDeltaFVarIds_5810_; lean_object* v_postponed_5811_; lean_object* v_diag_5812_; lean_object* v___x_5814_; uint8_t v_isShared_5815_; uint8_t v_isSharedCheck_5823_; 
v___x_5807_ = lean_st_ref_put(v___y_5791_, v___x_5806_);
v___x_5808_ = lean_st_ref_take(v___y_5790_);
v_mctx_5809_ = lean_ctor_get(v___x_5808_, 0);
v_zetaDeltaFVarIds_5810_ = lean_ctor_get(v___x_5808_, 2);
v_postponed_5811_ = lean_ctor_get(v___x_5808_, 3);
v_diag_5812_ = lean_ctor_get(v___x_5808_, 4);
v_isSharedCheck_5823_ = !lean_is_exclusive(v___x_5808_);
if (v_isSharedCheck_5823_ == 0)
{
lean_object* v_unused_5824_; 
v_unused_5824_ = lean_ctor_get(v___x_5808_, 1);
lean_dec(v_unused_5824_);
v___x_5814_ = v___x_5808_;
v_isShared_5815_ = v_isSharedCheck_5823_;
goto v_resetjp_5813_;
}
else
{
lean_inc(v_diag_5812_);
lean_inc(v_postponed_5811_);
lean_inc(v_zetaDeltaFVarIds_5810_);
lean_inc(v_mctx_5809_);
lean_dec(v___x_5808_);
v___x_5814_ = lean_box(0);
v_isShared_5815_ = v_isSharedCheck_5823_;
goto v_resetjp_5813_;
}
v_resetjp_5813_:
{
lean_object* v___x_5816_; lean_object* v___x_5818_; 
v___x_5816_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5815_ == 0)
{
lean_ctor_set(v___x_5814_, 1, v___x_5816_);
v___x_5818_ = v___x_5814_;
goto v_reusejp_5817_;
}
else
{
lean_object* v_reuseFailAlloc_5822_; 
v_reuseFailAlloc_5822_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5822_, 0, v_mctx_5809_);
lean_ctor_set(v_reuseFailAlloc_5822_, 1, v___x_5816_);
lean_ctor_set(v_reuseFailAlloc_5822_, 2, v_zetaDeltaFVarIds_5810_);
lean_ctor_set(v_reuseFailAlloc_5822_, 3, v_postponed_5811_);
lean_ctor_set(v_reuseFailAlloc_5822_, 4, v_diag_5812_);
v___x_5818_ = v_reuseFailAlloc_5822_;
goto v_reusejp_5817_;
}
v_reusejp_5817_:
{
lean_object* v___x_5819_; lean_object* v___x_5820_; lean_object* v___x_5821_; 
v___x_5819_ = lean_st_ref_put(v___y_5790_, v___x_5818_);
v___x_5820_ = lean_box(0);
v___x_5821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5821_, 0, v___x_5820_);
return v___x_5821_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_){
_start:
{
lean_object* v_res_5833_; 
v_res_5833_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5829_, v___y_5830_, v___y_5831_);
lean_dec(v___y_5831_);
lean_dec(v___y_5830_);
return v_res_5833_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_){
_start:
{
lean_object* v___x_5840_; 
v___x_5840_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5834_, v___y_5836_, v___y_5838_);
return v___x_5840_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_){
_start:
{
lean_object* v_res_5847_; 
v_res_5847_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5841_, v___y_5842_, v___y_5843_, v___y_5844_, v___y_5845_);
lean_dec(v___y_5845_);
lean_dec_ref(v___y_5844_);
lean_dec(v___y_5843_);
lean_dec_ref(v___y_5842_);
return v_res_5847_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5849_; lean_object* v___x_5850_; 
v___x_5849_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5850_ = l_Lean_stringToMessageData(v___x_5849_);
return v___x_5850_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5852_; lean_object* v___x_5853_; 
v___x_5852_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5853_ = l_Lean_stringToMessageData(v___x_5852_);
return v___x_5853_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5855_; lean_object* v___x_5856_; 
v___x_5855_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5856_ = l_Lean_stringToMessageData(v___x_5855_);
return v___x_5856_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5858_; lean_object* v___x_5859_; 
v___x_5858_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5859_ = l_Lean_stringToMessageData(v___x_5858_);
return v___x_5859_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5861_; lean_object* v___x_5862_; 
v___x_5861_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5862_ = l_Lean_stringToMessageData(v___x_5861_);
return v___x_5862_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5863_, lean_object* v_prio_5864_, lean_object* v_x_5865_, lean_object* v_type_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_){
_start:
{
lean_object* v___x_5872_; 
v___x_5872_ = l_Lean_Expr_getAppFn(v_type_5866_);
if (lean_obj_tag(v___x_5872_) == 4)
{
lean_object* v_declName_5873_; lean_object* v___y_5875_; lean_object* v___y_5876_; lean_object* v___y_5877_; lean_object* v___y_5878_; lean_object* v___x_5888_; lean_object* v_env_5889_; uint8_t v___x_5890_; 
v_declName_5873_ = lean_ctor_get(v___x_5872_, 0);
lean_inc(v_declName_5873_);
lean_dec_ref_known(v___x_5872_, 2);
v___x_5888_ = lean_st_ref_get(v___y_5870_);
v_env_5889_ = lean_ctor_get(v___x_5888_, 0);
lean_inc_ref(v_env_5889_);
lean_dec(v___x_5888_);
v___x_5890_ = l_Lean_isClass(v_env_5889_, v_declName_5873_);
if (v___x_5890_ == 0)
{
lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; 
lean_dec(v_prio_5864_);
v___x_5891_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5892_ = l_Lean_MessageData_ofConstName(v_declName_5863_, v___x_5890_);
v___x_5893_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5893_, 0, v___x_5891_);
lean_ctor_set(v___x_5893_, 1, v___x_5892_);
v___x_5894_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5895_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5895_, 0, v___x_5893_);
lean_ctor_set(v___x_5895_, 1, v___x_5894_);
lean_inc(v_declName_5873_);
v___x_5896_ = l_Lean_MessageData_ofName(v_declName_5873_);
v___x_5897_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5897_, 0, v___x_5895_);
lean_ctor_set(v___x_5897_, 1, v___x_5896_);
v___x_5898_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5899_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5899_, 0, v___x_5897_);
lean_ctor_set(v___x_5899_, 1, v___x_5898_);
v___x_5900_ = l_Lean_MessageData_ofConstName(v_declName_5873_, v___x_5890_);
v___x_5901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5901_, 0, v___x_5899_);
lean_ctor_set(v___x_5901_, 1, v___x_5900_);
v___x_5902_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5903_, 0, v___x_5901_);
lean_ctor_set(v___x_5903_, 1, v___x_5902_);
v___x_5904_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5903_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
return v___x_5904_;
}
else
{
v___y_5875_ = v___y_5867_;
v___y_5876_ = v___y_5868_;
v___y_5877_ = v___y_5869_;
v___y_5878_ = v___y_5870_;
goto v___jp_5874_;
}
v___jp_5874_:
{
lean_object* v___x_5879_; lean_object* v_env_5880_; lean_object* v___x_5881_; lean_object* v_toEnvExtension_5882_; lean_object* v_asyncMode_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; 
v___x_5879_ = lean_st_ref_get(v___y_5878_);
v_env_5880_ = lean_ctor_get(v___x_5879_, 0);
lean_inc_ref(v_env_5880_);
lean_dec(v___x_5879_);
v___x_5881_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5882_ = lean_ctor_get(v___x_5881_, 0);
v_asyncMode_5883_ = lean_ctor_get(v_toEnvExtension_5882_, 2);
v___x_5884_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5884_, 0, v_declName_5873_);
lean_ctor_set(v___x_5884_, 1, v_declName_5863_);
lean_ctor_set(v___x_5884_, 2, v_prio_5864_);
v___x_5885_ = lean_box(0);
v___x_5886_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5881_, v_env_5880_, v___x_5884_, v_asyncMode_5883_, v___x_5885_);
v___x_5887_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5886_, v___y_5876_, v___y_5878_);
return v___x_5887_;
}
}
else
{
lean_object* v___x_5905_; uint8_t v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; 
lean_dec_ref(v___x_5872_);
lean_dec(v_prio_5864_);
v___x_5905_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5906_ = 0;
v___x_5907_ = l_Lean_MessageData_ofConstName(v_declName_5863_, v___x_5906_);
v___x_5908_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5908_, 0, v___x_5905_);
lean_ctor_set(v___x_5908_, 1, v___x_5907_);
v___x_5909_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5910_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5910_, 0, v___x_5908_);
lean_ctor_set(v___x_5910_, 1, v___x_5909_);
v___x_5911_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5910_, v___y_5867_, v___y_5868_, v___y_5869_, v___y_5870_);
return v___x_5911_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5912_, lean_object* v_prio_5913_, lean_object* v_x_5914_, lean_object* v_type_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_){
_start:
{
lean_object* v_res_5921_; 
v_res_5921_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5912_, v_prio_5913_, v_x_5914_, v_type_5915_, v___y_5916_, v___y_5917_, v___y_5918_, v___y_5919_);
lean_dec(v___y_5919_);
lean_dec_ref(v___y_5918_);
lean_dec(v___y_5917_);
lean_dec_ref(v___y_5916_);
lean_dec_ref(v_type_5915_);
lean_dec_ref(v_x_5914_);
return v_res_5921_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5922_, lean_object* v_prio_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_){
_start:
{
lean_object* v___x_5929_; lean_object* v_env_5930_; uint8_t v___x_5931_; lean_object* v___x_5932_; 
v___x_5929_ = lean_st_ref_get(v_a_5927_);
v_env_5930_ = lean_ctor_get(v___x_5929_, 0);
lean_inc_ref(v_env_5930_);
lean_dec(v___x_5929_);
v___x_5931_ = 0;
lean_inc(v_declName_5922_);
v___x_5932_ = l_Lean_Environment_find_x3f(v_env_5930_, v_declName_5922_, v___x_5931_);
if (lean_obj_tag(v___x_5932_) == 0)
{
lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; 
lean_dec(v_prio_5923_);
v___x_5933_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5934_ = l_Lean_MessageData_ofConstName(v_declName_5922_, v___x_5931_);
v___x_5935_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5935_, 0, v___x_5933_);
lean_ctor_set(v___x_5935_, 1, v___x_5934_);
v___x_5936_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5937_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5937_, 0, v___x_5935_);
lean_ctor_set(v___x_5937_, 1, v___x_5936_);
v___x_5938_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5937_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_);
return v___x_5938_;
}
else
{
lean_object* v_val_5939_; lean_object* v___f_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; 
v_val_5939_ = lean_ctor_get(v___x_5932_, 0);
lean_inc(v_val_5939_);
lean_dec_ref_known(v___x_5932_, 1);
v___f_5940_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5940_, 0, v_declName_5922_);
lean_closure_set(v___f_5940_, 1, v_prio_5923_);
v___x_5941_ = l_Lean_ConstantInfo_type(v_val_5939_);
lean_dec(v_val_5939_);
v___x_5942_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5941_, v___f_5940_, v___x_5931_, v___x_5931_, v_a_5924_, v_a_5925_, v_a_5926_, v_a_5927_);
return v___x_5942_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5943_, lean_object* v_prio_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_){
_start:
{
lean_object* v_res_5950_; 
v_res_5950_ = l_Lean_Meta_addDefaultInstance(v_declName_5943_, v_prio_5944_, v_a_5945_, v_a_5946_, v_a_5947_, v_a_5948_);
lean_dec(v_a_5948_);
lean_dec_ref(v_a_5947_);
lean_dec(v_a_5946_);
lean_dec_ref(v_a_5945_);
return v_res_5950_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5952_; lean_object* v___x_5953_; 
v___x_5952_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5953_ = l_Lean_stringToMessageData(v___x_5952_);
return v___x_5953_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5955_; lean_object* v___x_5956_; 
v___x_5955_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5956_ = l_Lean_stringToMessageData(v___x_5955_);
return v___x_5956_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5960_, uint8_t v_kind_5961_, lean_object* v___y_5962_, lean_object* v___y_5963_){
_start:
{
lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___y_5971_; 
v___x_5965_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5966_ = l_Lean_MessageData_ofName(v_name_5960_);
v___x_5967_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5967_, 0, v___x_5965_);
lean_ctor_set(v___x_5967_, 1, v___x_5966_);
v___x_5968_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5969_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5969_, 0, v___x_5967_);
lean_ctor_set(v___x_5969_, 1, v___x_5968_);
switch(v_kind_5961_)
{
case 0:
{
lean_object* v___x_5978_; 
v___x_5978_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5971_ = v___x_5978_;
goto v___jp_5970_;
}
case 1:
{
lean_object* v___x_5979_; 
v___x_5979_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5971_ = v___x_5979_;
goto v___jp_5970_;
}
default: 
{
lean_object* v___x_5980_; 
v___x_5980_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5971_ = v___x_5980_;
goto v___jp_5970_;
}
}
v___jp_5970_:
{
lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; 
lean_inc_ref(v___y_5971_);
v___x_5972_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5972_, 0, v___y_5971_);
v___x_5973_ = l_Lean_MessageData_ofFormat(v___x_5972_);
v___x_5974_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5974_, 0, v___x_5969_);
lean_ctor_set(v___x_5974_, 1, v___x_5973_);
v___x_5975_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5976_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5976_, 0, v___x_5974_);
lean_ctor_set(v___x_5976_, 1, v___x_5975_);
v___x_5977_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5976_, v___y_5962_, v___y_5963_);
return v___x_5977_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_5981_, lean_object* v_kind_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_){
_start:
{
uint8_t v_kind_boxed_5986_; lean_object* v_res_5987_; 
v_kind_boxed_5986_ = lean_unbox(v_kind_5982_);
v_res_5987_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5981_, v_kind_boxed_5986_, v___y_5983_, v___y_5984_);
lean_dec(v___y_5984_);
lean_dec_ref(v___y_5983_);
return v_res_5987_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5988_, lean_object* v___x_5989_, lean_object* v___x_5990_, lean_object* v_declName_5991_, lean_object* v_stx_5992_, uint8_t v_kind_5993_, lean_object* v___y_5994_, lean_object* v___y_5995_){
_start:
{
lean_object* v___x_5997_; lean_object* v___x_5998_; lean_object* v___x_5999_; 
v___x_5997_ = lean_unsigned_to_nat(1u);
v___x_5998_ = l_Lean_Syntax_getArg(v_stx_5992_, v___x_5997_);
v___x_5999_ = l_Lean_getAttrParamOptPrio(v___x_5998_, v___y_5994_, v___y_5995_);
if (lean_obj_tag(v___x_5999_) == 0)
{
lean_object* v_a_6000_; lean_object* v___y_6002_; lean_object* v___y_6003_; uint8_t v___x_6034_; uint8_t v___x_6035_; 
v_a_6000_ = lean_ctor_get(v___x_5999_, 0);
lean_inc(v_a_6000_);
lean_dec_ref_known(v___x_5999_, 1);
v___x_6034_ = 0;
v___x_6035_ = l_Lean_instBEqAttributeKind_beq(v_kind_5993_, v___x_6034_);
if (v___x_6035_ == 0)
{
lean_object* v___x_6036_; 
lean_dec(v_a_6000_);
lean_dec(v_declName_5991_);
lean_dec(v___x_5989_);
lean_dec(v___x_5988_);
v___x_6036_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_5990_, v_kind_5993_, v___y_5994_, v___y_5995_);
return v___x_6036_;
}
else
{
lean_dec(v___x_5990_);
v___y_6002_ = v___y_5994_;
v___y_6003_ = v___y_5995_;
goto v___jp_6001_;
}
v___jp_6001_:
{
uint8_t v___x_6004_; uint8_t v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; size_t v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; 
v___x_6004_ = 0;
v___x_6005_ = 1;
v___x_6006_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6007_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6008_ = lean_unsigned_to_nat(32u);
v___x_6009_ = lean_mk_empty_array_with_capacity(v___x_6008_);
v___x_6010_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_6011_ = ((size_t)5ULL);
lean_inc_n(v___x_5988_, 6);
v___x_6012_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6012_, 0, v___x_6010_);
lean_ctor_set(v___x_6012_, 1, v___x_6009_);
lean_ctor_set(v___x_6012_, 2, v___x_5988_);
lean_ctor_set(v___x_6012_, 3, v___x_5988_);
lean_ctor_set_usize(v___x_6012_, 4, v___x_6011_);
v___x_6013_ = lean_box(1);
lean_inc_ref(v___x_6012_);
v___x_6014_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6007_);
lean_ctor_set(v___x_6014_, 1, v___x_6012_);
lean_ctor_set(v___x_6014_, 2, v___x_6013_);
v___x_6015_ = lean_mk_empty_array_with_capacity(v___x_5988_);
v___x_6016_ = lean_box(0);
lean_inc(v___x_5989_);
v___x_6017_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6017_, 0, v___x_6006_);
lean_ctor_set(v___x_6017_, 1, v___x_5989_);
lean_ctor_set(v___x_6017_, 2, v___x_6014_);
lean_ctor_set(v___x_6017_, 3, v___x_6015_);
lean_ctor_set(v___x_6017_, 4, v___x_6016_);
lean_ctor_set(v___x_6017_, 5, v___x_5988_);
lean_ctor_set(v___x_6017_, 6, v___x_6016_);
lean_ctor_set_uint8(v___x_6017_, sizeof(void*)*7, v___x_6004_);
lean_ctor_set_uint8(v___x_6017_, sizeof(void*)*7 + 1, v___x_6004_);
lean_ctor_set_uint8(v___x_6017_, sizeof(void*)*7 + 2, v___x_6004_);
lean_ctor_set_uint8(v___x_6017_, sizeof(void*)*7 + 3, v___x_6005_);
v___x_6018_ = lean_alloc_ctor(0, 11, 0);
lean_ctor_set(v___x_6018_, 0, v___x_5988_);
lean_ctor_set(v___x_6018_, 1, v___x_5988_);
lean_ctor_set(v___x_6018_, 2, v___x_5988_);
lean_ctor_set(v___x_6018_, 3, v___x_5988_);
lean_ctor_set(v___x_6018_, 4, v___x_6007_);
lean_ctor_set(v___x_6018_, 5, v___x_6007_);
lean_ctor_set(v___x_6018_, 6, v___x_6007_);
lean_ctor_set(v___x_6018_, 7, v___x_6007_);
lean_ctor_set(v___x_6018_, 8, v___x_6007_);
lean_ctor_set(v___x_6018_, 9, v___x_6007_);
lean_ctor_set(v___x_6018_, 10, v___x_6007_);
v___x_6019_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6020_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6021_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6021_, 0, v___x_6018_);
lean_ctor_set(v___x_6021_, 1, v___x_6019_);
lean_ctor_set(v___x_6021_, 2, v___x_5989_);
lean_ctor_set(v___x_6021_, 3, v___x_6012_);
lean_ctor_set(v___x_6021_, 4, v___x_6020_);
v___x_6022_ = lean_st_mk_ref(v___x_6021_);
v___x_6023_ = l_Lean_Meta_addDefaultInstance(v_declName_5991_, v_a_6000_, v___x_6017_, v___x_6022_, v___y_6002_, v___y_6003_);
lean_dec_ref_known(v___x_6017_, 7);
if (lean_obj_tag(v___x_6023_) == 0)
{
lean_object* v___x_6025_; uint8_t v_isShared_6026_; uint8_t v_isSharedCheck_6032_; 
v_isSharedCheck_6032_ = !lean_is_exclusive(v___x_6023_);
if (v_isSharedCheck_6032_ == 0)
{
lean_object* v_unused_6033_; 
v_unused_6033_ = lean_ctor_get(v___x_6023_, 0);
lean_dec(v_unused_6033_);
v___x_6025_ = v___x_6023_;
v_isShared_6026_ = v_isSharedCheck_6032_;
goto v_resetjp_6024_;
}
else
{
lean_dec(v___x_6023_);
v___x_6025_ = lean_box(0);
v_isShared_6026_ = v_isSharedCheck_6032_;
goto v_resetjp_6024_;
}
v_resetjp_6024_:
{
lean_object* v___x_6027_; lean_object* v___x_6028_; lean_object* v___x_6030_; 
v___x_6027_ = lean_st_ref_get(v___x_6022_);
lean_dec(v___x_6022_);
lean_dec(v___x_6027_);
v___x_6028_ = lean_box(0);
if (v_isShared_6026_ == 0)
{
lean_ctor_set(v___x_6025_, 0, v___x_6028_);
v___x_6030_ = v___x_6025_;
goto v_reusejp_6029_;
}
else
{
lean_object* v_reuseFailAlloc_6031_; 
v_reuseFailAlloc_6031_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6031_, 0, v___x_6028_);
v___x_6030_ = v_reuseFailAlloc_6031_;
goto v_reusejp_6029_;
}
v_reusejp_6029_:
{
return v___x_6030_;
}
}
}
else
{
lean_dec(v___x_6022_);
return v___x_6023_;
}
}
}
else
{
lean_object* v_a_6037_; lean_object* v___x_6039_; uint8_t v_isShared_6040_; uint8_t v_isSharedCheck_6044_; 
lean_dec(v_declName_5991_);
lean_dec(v___x_5990_);
lean_dec(v___x_5989_);
lean_dec(v___x_5988_);
v_a_6037_ = lean_ctor_get(v___x_5999_, 0);
v_isSharedCheck_6044_ = !lean_is_exclusive(v___x_5999_);
if (v_isSharedCheck_6044_ == 0)
{
v___x_6039_ = v___x_5999_;
v_isShared_6040_ = v_isSharedCheck_6044_;
goto v_resetjp_6038_;
}
else
{
lean_inc(v_a_6037_);
lean_dec(v___x_5999_);
v___x_6039_ = lean_box(0);
v_isShared_6040_ = v_isSharedCheck_6044_;
goto v_resetjp_6038_;
}
v_resetjp_6038_:
{
lean_object* v___x_6042_; 
if (v_isShared_6040_ == 0)
{
v___x_6042_ = v___x_6039_;
goto v_reusejp_6041_;
}
else
{
lean_object* v_reuseFailAlloc_6043_; 
v_reuseFailAlloc_6043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6043_, 0, v_a_6037_);
v___x_6042_ = v_reuseFailAlloc_6043_;
goto v_reusejp_6041_;
}
v_reusejp_6041_:
{
return v___x_6042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6045_, lean_object* v___x_6046_, lean_object* v___x_6047_, lean_object* v_declName_6048_, lean_object* v_stx_6049_, lean_object* v_kind_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_){
_start:
{
uint8_t v_kind_boxed_6054_; lean_object* v_res_6055_; 
v_kind_boxed_6054_ = lean_unbox(v_kind_6050_);
v_res_6055_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6045_, v___x_6046_, v___x_6047_, v_declName_6048_, v_stx_6049_, v_kind_boxed_6054_, v___y_6051_, v___y_6052_);
lean_dec(v___y_6052_);
lean_dec_ref(v___y_6051_);
lean_dec(v_stx_6049_);
return v_res_6055_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6057_; lean_object* v___x_6058_; 
v___x_6057_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6058_ = l_Lean_stringToMessageData(v___x_6057_);
return v___x_6058_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6060_; lean_object* v___x_6061_; 
v___x_6060_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6061_ = l_Lean_stringToMessageData(v___x_6060_);
return v___x_6061_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6062_, lean_object* v_decl_6063_, lean_object* v___y_6064_, lean_object* v___y_6065_){
_start:
{
lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; 
v___x_6067_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6068_ = l_Lean_MessageData_ofName(v___x_6062_);
v___x_6069_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6069_, 0, v___x_6067_);
lean_ctor_set(v___x_6069_, 1, v___x_6068_);
v___x_6070_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6071_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6071_, 0, v___x_6069_);
lean_ctor_set(v___x_6071_, 1, v___x_6070_);
v___x_6072_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6071_, v___y_6064_, v___y_6065_);
return v___x_6072_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6073_, lean_object* v_decl_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_){
_start:
{
lean_object* v_res_6078_; 
v_res_6078_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6073_, v_decl_6074_, v___y_6075_, v___y_6076_);
lean_dec(v___y_6076_);
lean_dec_ref(v___y_6075_);
lean_dec(v_decl_6074_);
return v_res_6078_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6111_; lean_object* v___x_6112_; lean_object* v___x_6113_; 
v___x_6111_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6112_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6113_ = l_Lean_registerBuiltinAttribute(v___x_6112_);
if (lean_obj_tag(v___x_6113_) == 0)
{
lean_object* v___x_6114_; uint8_t v___x_6115_; lean_object* v___x_6116_; 
lean_dec_ref_known(v___x_6113_, 1);
v___x_6114_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_6115_ = 0;
v___x_6116_ = l_Lean_registerTraceClass(v___x_6114_, v___x_6115_, v___x_6111_);
return v___x_6116_;
}
else
{
return v___x_6113_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_6117_){
_start:
{
lean_object* v_res_6118_; 
v_res_6118_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_6118_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_6119_, lean_object* v_name_6120_, uint8_t v_kind_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_){
_start:
{
lean_object* v___x_6125_; 
v___x_6125_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6120_, v_kind_6121_, v___y_6122_, v___y_6123_);
return v___x_6125_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_6126_, lean_object* v_name_6127_, lean_object* v_kind_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_){
_start:
{
uint8_t v_kind_boxed_6132_; lean_object* v_res_6133_; 
v_kind_boxed_6132_ = lean_unbox(v_kind_6128_);
v_res_6133_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_6126_, v_name_6127_, v_kind_boxed_6132_, v___y_6129_, v___y_6130_);
lean_dec(v___y_6130_);
lean_dec_ref(v___y_6129_);
return v_res_6133_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_6134_, lean_object* v_toPure_6135_, lean_object* v_____do__lift_6136_){
_start:
{
lean_object* v___x_6137_; lean_object* v_toEnvExtension_6138_; lean_object* v_asyncMode_6139_; lean_object* v___x_6140_; lean_object* v___x_6141_; lean_object* v_priorities_6142_; lean_object* v___x_6143_; 
v___x_6137_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6138_ = lean_ctor_get(v___x_6137_, 0);
v_asyncMode_6139_ = lean_ctor_get(v_toEnvExtension_6138_, 2);
v___x_6140_ = lean_box(0);
v___x_6141_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6134_, v___x_6137_, v_____do__lift_6136_, v_asyncMode_6139_, v___x_6140_);
v_priorities_6142_ = lean_ctor_get(v___x_6141_, 1);
lean_inc(v_priorities_6142_);
lean_dec(v___x_6141_);
v___x_6143_ = lean_apply_2(v_toPure_6135_, lean_box(0), v_priorities_6142_);
return v___x_6143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_6144_, lean_object* v_inst_6145_){
_start:
{
lean_object* v_toApplicative_6146_; lean_object* v_toBind_6147_; lean_object* v_getEnv_6148_; lean_object* v_toPure_6149_; lean_object* v___x_6150_; lean_object* v___f_6151_; lean_object* v___x_6152_; 
v_toApplicative_6146_ = lean_ctor_get(v_inst_6144_, 0);
lean_inc_ref(v_toApplicative_6146_);
v_toBind_6147_ = lean_ctor_get(v_inst_6144_, 1);
lean_inc(v_toBind_6147_);
lean_dec_ref(v_inst_6144_);
v_getEnv_6148_ = lean_ctor_get(v_inst_6145_, 0);
lean_inc(v_getEnv_6148_);
lean_dec_ref(v_inst_6145_);
v_toPure_6149_ = lean_ctor_get(v_toApplicative_6146_, 1);
lean_inc(v_toPure_6149_);
lean_dec_ref(v_toApplicative_6146_);
v___x_6150_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6151_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6151_, 0, v___x_6150_);
lean_closure_set(v___f_6151_, 1, v_toPure_6149_);
v___x_6152_ = lean_apply_4(v_toBind_6147_, lean_box(0), lean_box(0), v_getEnv_6148_, v___f_6151_);
return v___x_6152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_6153_, lean_object* v_inst_6154_, lean_object* v_inst_6155_){
_start:
{
lean_object* v___x_6156_; 
v___x_6156_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_6154_, v_inst_6155_);
return v___x_6156_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_6157_, uint8_t v_isExporting_6158_, lean_object* v_x_6159_){
_start:
{
lean_object* v_fst_6160_; uint8_t v___x_6161_; 
v_fst_6160_ = lean_ctor_get(v_x_6159_, 0);
lean_inc(v_fst_6160_);
lean_dec_ref(v_x_6159_);
v___x_6161_ = l_Lean_Environment_contains(v_env_6157_, v_fst_6160_, v_isExporting_6158_);
return v___x_6161_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_6162_, lean_object* v_isExporting_6163_, lean_object* v_x_6164_){
_start:
{
uint8_t v_isExporting_boxed_6165_; uint8_t v_res_6166_; lean_object* v_r_6167_; 
v_isExporting_boxed_6165_ = lean_unbox(v_isExporting_6163_);
v_res_6166_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_6162_, v_isExporting_boxed_6165_, v_x_6164_);
v_r_6167_ = lean_box(v_res_6166_);
return v_r_6167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_6168_, lean_object* v_toApplicative_6169_, lean_object* v_className_6170_, lean_object* v_env_6171_){
_start:
{
lean_object* v___y_6173_; lean_object* v___x_6183_; lean_object* v_toEnvExtension_6184_; lean_object* v_asyncMode_6185_; lean_object* v___x_6186_; lean_object* v___x_6187_; lean_object* v_defaultInstances_6188_; lean_object* v___x_6189_; 
v___x_6183_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6184_ = lean_ctor_get(v___x_6183_, 0);
v_asyncMode_6185_ = lean_ctor_get(v_toEnvExtension_6184_, 2);
v___x_6186_ = lean_box(0);
lean_inc_ref(v_env_6171_);
v___x_6187_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6168_, v___x_6183_, v_env_6171_, v_asyncMode_6185_, v___x_6186_);
v_defaultInstances_6188_ = lean_ctor_get(v___x_6187_, 0);
lean_inc(v_defaultInstances_6188_);
lean_dec(v___x_6187_);
v___x_6189_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_6188_, v_className_6170_);
lean_dec(v_defaultInstances_6188_);
if (lean_obj_tag(v___x_6189_) == 0)
{
lean_object* v___x_6190_; 
v___x_6190_ = lean_box(0);
v___y_6173_ = v___x_6190_;
goto v___jp_6172_;
}
else
{
lean_object* v_val_6191_; 
v_val_6191_ = lean_ctor_get(v___x_6189_, 0);
lean_inc(v_val_6191_);
lean_dec_ref_known(v___x_6189_, 1);
v___y_6173_ = v_val_6191_;
goto v___jp_6172_;
}
v___jp_6172_:
{
uint8_t v_isExporting_6174_; 
v_isExporting_6174_ = lean_ctor_get_uint8(v_env_6171_, sizeof(void*)*8);
if (v_isExporting_6174_ == 0)
{
lean_object* v_toPure_6175_; lean_object* v___x_6176_; 
lean_dec_ref(v_env_6171_);
v_toPure_6175_ = lean_ctor_get(v_toApplicative_6169_, 1);
lean_inc(v_toPure_6175_);
lean_dec_ref(v_toApplicative_6169_);
v___x_6176_ = lean_apply_2(v_toPure_6175_, lean_box(0), v___y_6173_);
return v___x_6176_;
}
else
{
lean_object* v_toPure_6177_; lean_object* v___x_6178_; lean_object* v___f_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; 
v_toPure_6177_ = lean_ctor_get(v_toApplicative_6169_, 1);
lean_inc(v_toPure_6177_);
lean_dec_ref(v_toApplicative_6169_);
v___x_6178_ = lean_box(v_isExporting_6174_);
v___f_6179_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6179_, 0, v_env_6171_);
lean_closure_set(v___f_6179_, 1, v___x_6178_);
v___x_6180_ = lean_box(0);
v___x_6181_ = l_List_filterTR_loop___redArg(v___f_6179_, v___y_6173_, v___x_6180_);
v___x_6182_ = lean_apply_2(v_toPure_6177_, lean_box(0), v___x_6181_);
return v___x_6182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_6192_, lean_object* v_toApplicative_6193_, lean_object* v_className_6194_, lean_object* v_env_6195_){
_start:
{
lean_object* v_res_6196_; 
v_res_6196_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_6192_, v_toApplicative_6193_, v_className_6194_, v_env_6195_);
lean_dec(v_className_6194_);
return v_res_6196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_6197_, lean_object* v_inst_6198_, lean_object* v_className_6199_){
_start:
{
lean_object* v_toApplicative_6200_; lean_object* v_toBind_6201_; lean_object* v_getEnv_6202_; lean_object* v___x_6203_; lean_object* v___f_6204_; lean_object* v___x_6205_; 
v_toApplicative_6200_ = lean_ctor_get(v_inst_6197_, 0);
lean_inc_ref(v_toApplicative_6200_);
v_toBind_6201_ = lean_ctor_get(v_inst_6197_, 1);
lean_inc(v_toBind_6201_);
lean_dec_ref(v_inst_6197_);
v_getEnv_6202_ = lean_ctor_get(v_inst_6198_, 0);
lean_inc(v_getEnv_6202_);
lean_dec_ref(v_inst_6198_);
v___x_6203_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6204_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_6204_, 0, v___x_6203_);
lean_closure_set(v___f_6204_, 1, v_toApplicative_6200_);
lean_closure_set(v___f_6204_, 2, v_className_6199_);
v___x_6205_ = lean_apply_4(v_toBind_6201_, lean_box(0), lean_box(0), v_getEnv_6202_, v___f_6204_);
return v___x_6205_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6206_, lean_object* v_inst_6207_, lean_object* v_inst_6208_, lean_object* v_className_6209_){
_start:
{
lean_object* v___x_6210_; 
v___x_6210_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6207_, v_inst_6208_, v_className_6209_);
return v___x_6210_;
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
