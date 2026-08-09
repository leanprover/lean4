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
lean_object* lean_st_ref_set(lean_object*, lean_object*);
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
size_t v_x_1620__boxed_1701_; size_t v_x_1621__boxed_1702_; lean_object* v_res_1703_; 
v_x_1620__boxed_1701_ = lean_unbox_usize(v_x_1697_);
lean_dec(v_x_1697_);
v_x_1621__boxed_1702_ = lean_unbox_usize(v_x_1698_);
lean_dec(v_x_1698_);
v_res_1703_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1696_, v_x_1620__boxed_1701_, v_x_1621__boxed_1702_, v_x_1699_, v_x_1700_);
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
lean_object* v___x_1715_; lean_object* v_mctx_1716_; lean_object* v_cache_1717_; lean_object* v_zetaDeltaFVarIds_1718_; lean_object* v_postponed_1719_; lean_object* v_diag_1720_; lean_object* v___x_1722_; uint8_t v_isShared_1723_; uint8_t v_isSharedCheck_1748_; 
v___x_1715_ = lean_st_ref_take(v___y_1713_);
v_mctx_1716_ = lean_ctor_get(v___x_1715_, 0);
v_cache_1717_ = lean_ctor_get(v___x_1715_, 1);
v_zetaDeltaFVarIds_1718_ = lean_ctor_get(v___x_1715_, 2);
v_postponed_1719_ = lean_ctor_get(v___x_1715_, 3);
v_diag_1720_ = lean_ctor_get(v___x_1715_, 4);
v_isSharedCheck_1748_ = !lean_is_exclusive(v___x_1715_);
if (v_isSharedCheck_1748_ == 0)
{
v___x_1722_ = v___x_1715_;
v_isShared_1723_ = v_isSharedCheck_1748_;
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
v_isShared_1723_ = v_isSharedCheck_1748_;
goto v_resetjp_1721_;
}
v_resetjp_1721_:
{
lean_object* v_depth_1724_; lean_object* v_levelAssignDepth_1725_; lean_object* v_lmvarCounter_1726_; lean_object* v_mvarCounter_1727_; lean_object* v_lDecls_1728_; lean_object* v_decls_1729_; lean_object* v_userNames_1730_; lean_object* v_lAssignment_1731_; lean_object* v_eAssignment_1732_; lean_object* v_dAssignment_1733_; lean_object* v___x_1735_; uint8_t v_isShared_1736_; uint8_t v_isSharedCheck_1747_; 
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
v_isSharedCheck_1747_ = !lean_is_exclusive(v_mctx_1716_);
if (v_isSharedCheck_1747_ == 0)
{
v___x_1735_ = v_mctx_1716_;
v_isShared_1736_ = v_isSharedCheck_1747_;
goto v_resetjp_1734_;
}
else
{
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
v___x_1735_ = lean_box(0);
v_isShared_1736_ = v_isSharedCheck_1747_;
goto v_resetjp_1734_;
}
v_resetjp_1734_:
{
lean_object* v___x_1737_; lean_object* v___x_1739_; 
v___x_1737_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_eAssignment_1732_, v_mvarId_1711_, v_val_1712_);
if (v_isShared_1736_ == 0)
{
lean_ctor_set(v___x_1735_, 8, v___x_1737_);
v___x_1739_ = v___x_1735_;
goto v_reusejp_1738_;
}
else
{
lean_object* v_reuseFailAlloc_1746_; 
v_reuseFailAlloc_1746_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1746_, 0, v_depth_1724_);
lean_ctor_set(v_reuseFailAlloc_1746_, 1, v_levelAssignDepth_1725_);
lean_ctor_set(v_reuseFailAlloc_1746_, 2, v_lmvarCounter_1726_);
lean_ctor_set(v_reuseFailAlloc_1746_, 3, v_mvarCounter_1727_);
lean_ctor_set(v_reuseFailAlloc_1746_, 4, v_lDecls_1728_);
lean_ctor_set(v_reuseFailAlloc_1746_, 5, v_decls_1729_);
lean_ctor_set(v_reuseFailAlloc_1746_, 6, v_userNames_1730_);
lean_ctor_set(v_reuseFailAlloc_1746_, 7, v_lAssignment_1731_);
lean_ctor_set(v_reuseFailAlloc_1746_, 8, v___x_1737_);
lean_ctor_set(v_reuseFailAlloc_1746_, 9, v_dAssignment_1733_);
v___x_1739_ = v_reuseFailAlloc_1746_;
goto v_reusejp_1738_;
}
v_reusejp_1738_:
{
lean_object* v___x_1741_; 
if (v_isShared_1723_ == 0)
{
lean_ctor_set(v___x_1722_, 0, v___x_1739_);
v___x_1741_ = v___x_1722_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1745_; 
v_reuseFailAlloc_1745_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1745_, 0, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1745_, 1, v_cache_1717_);
lean_ctor_set(v_reuseFailAlloc_1745_, 2, v_zetaDeltaFVarIds_1718_);
lean_ctor_set(v_reuseFailAlloc_1745_, 3, v_postponed_1719_);
lean_ctor_set(v_reuseFailAlloc_1745_, 4, v_diag_1720_);
v___x_1741_ = v_reuseFailAlloc_1745_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1742_; lean_object* v___x_1743_; lean_object* v___x_1744_; 
v___x_1742_ = lean_st_ref_set(v___y_1713_, v___x_1741_);
v___x_1743_ = lean_box(0);
v___x_1744_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1744_, 0, v___x_1743_);
return v___x_1744_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg___boxed(lean_object* v_mvarId_1749_, lean_object* v_val_1750_, lean_object* v___y_1751_, lean_object* v___y_1752_){
_start:
{
lean_object* v_res_1753_; 
v_res_1753_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1749_, v_val_1750_, v___y_1751_);
lean_dec(v___y_1751_);
return v_res_1753_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(lean_object* v_argMVars_1754_, lean_object* v_argVars_1755_, lean_object* v_as_1756_, size_t v_sz_1757_, size_t v_i_1758_, lean_object* v_b_1759_, lean_object* v___y_1760_, lean_object* v___y_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_){
_start:
{
uint8_t v___x_1765_; 
v___x_1765_ = lean_usize_dec_lt(v_i_1758_, v_sz_1757_);
if (v___x_1765_ == 0)
{
lean_object* v___x_1766_; 
v___x_1766_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1766_, 0, v_b_1759_);
return v___x_1766_;
}
else
{
lean_object* v___x_1767_; lean_object* v_a_1768_; lean_object* v___y_1770_; lean_object* v___y_1771_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___x_1789_; lean_object* v___x_1790_; 
v___x_1767_ = lean_box(0);
v_a_1768_ = lean_array_uget_borrowed(v_as_1756_, v_i_1758_);
v___x_1789_ = lean_unsigned_to_nat(0u);
v___x_1790_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1768_, v_argMVars_1754_, v___x_1789_);
if (lean_obj_tag(v___x_1790_) == 1)
{
lean_object* v_val_1791_; lean_object* v___x_1792_; lean_object* v___x_1793_; lean_object* v___x_1794_; 
v_val_1791_ = lean_ctor_get(v___x_1790_, 0);
lean_inc(v_val_1791_);
lean_dec_ref_known(v___x_1790_, 1);
v___x_1792_ = l_Lean_instInhabitedExpr;
v___x_1793_ = lean_array_get_borrowed(v___x_1792_, v_argVars_1755_, v_val_1791_);
lean_dec(v_val_1791_);
lean_inc(v___x_1793_);
lean_inc(v_a_1768_);
v___x_1794_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_a_1768_, v___x_1793_, v___y_1761_);
if (lean_obj_tag(v___x_1794_) == 0)
{
lean_dec_ref_known(v___x_1794_, 1);
v___y_1770_ = v___y_1760_;
v___y_1771_ = v___y_1761_;
v___y_1772_ = v___y_1762_;
v___y_1773_ = v___y_1763_;
goto v___jp_1769_;
}
else
{
return v___x_1794_;
}
}
else
{
lean_dec(v___x_1790_);
v___y_1770_ = v___y_1760_;
v___y_1771_ = v___y_1761_;
v___y_1772_ = v___y_1762_;
v___y_1773_ = v___y_1763_;
goto v___jp_1769_;
}
v___jp_1769_:
{
lean_object* v___x_1774_; lean_object* v___x_1775_; 
lean_inc(v_a_1768_);
v___x_1774_ = l_Lean_Expr_mvar___override(v_a_1768_);
lean_inc(v___y_1773_);
lean_inc_ref(v___y_1772_);
lean_inc(v___y_1771_);
lean_inc_ref(v___y_1770_);
v___x_1775_ = lean_infer_type(v___x_1774_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
if (lean_obj_tag(v___x_1775_) == 0)
{
lean_object* v_a_1776_; lean_object* v___x_1777_; 
v_a_1776_ = lean_ctor_get(v___x_1775_, 0);
lean_inc(v_a_1776_);
lean_dec_ref_known(v___x_1775_, 1);
v___x_1777_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1754_, v_argVars_1755_, v_a_1776_, v___y_1770_, v___y_1771_, v___y_1772_, v___y_1773_);
if (lean_obj_tag(v___x_1777_) == 0)
{
size_t v___x_1778_; size_t v___x_1779_; 
lean_dec_ref_known(v___x_1777_, 1);
v___x_1778_ = ((size_t)1ULL);
v___x_1779_ = lean_usize_add(v_i_1758_, v___x_1778_);
v_i_1758_ = v___x_1779_;
v_b_1759_ = v___x_1767_;
goto _start;
}
else
{
return v___x_1777_;
}
}
else
{
lean_object* v_a_1781_; lean_object* v___x_1783_; uint8_t v_isShared_1784_; uint8_t v_isSharedCheck_1788_; 
v_a_1781_ = lean_ctor_get(v___x_1775_, 0);
v_isSharedCheck_1788_ = !lean_is_exclusive(v___x_1775_);
if (v_isSharedCheck_1788_ == 0)
{
v___x_1783_ = v___x_1775_;
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
else
{
lean_inc(v_a_1781_);
lean_dec(v___x_1775_);
v___x_1783_ = lean_box(0);
v_isShared_1784_ = v_isSharedCheck_1788_;
goto v_resetjp_1782_;
}
v_resetjp_1782_:
{
lean_object* v___x_1786_; 
if (v_isShared_1784_ == 0)
{
v___x_1786_ = v___x_1783_;
goto v_reusejp_1785_;
}
else
{
lean_object* v_reuseFailAlloc_1787_; 
v_reuseFailAlloc_1787_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1787_, 0, v_a_1781_);
v___x_1786_ = v_reuseFailAlloc_1787_;
goto v_reusejp_1785_;
}
v_reusejp_1785_:
{
return v___x_1786_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1795_, lean_object* v_argVars_1796_, lean_object* v_e_1797_, lean_object* v_a_1798_, lean_object* v_a_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_Lean_Meta_getMVars(v_e_1797_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
if (lean_obj_tag(v___x_1803_) == 0)
{
lean_object* v_a_1804_; lean_object* v___x_1805_; size_t v_sz_1806_; size_t v___x_1807_; lean_object* v___x_1808_; 
v_a_1804_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_a_1804_);
lean_dec_ref_known(v___x_1803_, 1);
v___x_1805_ = lean_box(0);
v_sz_1806_ = lean_array_size(v_a_1804_);
v___x_1807_ = ((size_t)0ULL);
v___x_1808_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1795_, v_argVars_1796_, v_a_1804_, v_sz_1806_, v___x_1807_, v___x_1805_, v_a_1798_, v_a_1799_, v_a_1800_, v_a_1801_);
lean_dec(v_a_1804_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v___x_1810_; uint8_t v_isShared_1811_; uint8_t v_isSharedCheck_1815_; 
v_isSharedCheck_1815_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1815_ == 0)
{
lean_object* v_unused_1816_; 
v_unused_1816_ = lean_ctor_get(v___x_1808_, 0);
lean_dec(v_unused_1816_);
v___x_1810_ = v___x_1808_;
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
else
{
lean_dec(v___x_1808_);
v___x_1810_ = lean_box(0);
v_isShared_1811_ = v_isSharedCheck_1815_;
goto v_resetjp_1809_;
}
v_resetjp_1809_:
{
lean_object* v___x_1813_; 
if (v_isShared_1811_ == 0)
{
lean_ctor_set(v___x_1810_, 0, v___x_1805_);
v___x_1813_ = v___x_1810_;
goto v_reusejp_1812_;
}
else
{
lean_object* v_reuseFailAlloc_1814_; 
v_reuseFailAlloc_1814_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1814_, 0, v___x_1805_);
v___x_1813_ = v_reuseFailAlloc_1814_;
goto v_reusejp_1812_;
}
v_reusejp_1812_:
{
return v___x_1813_;
}
}
}
else
{
return v___x_1808_;
}
}
else
{
lean_object* v_a_1817_; lean_object* v___x_1819_; uint8_t v_isShared_1820_; uint8_t v_isSharedCheck_1824_; 
v_a_1817_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1824_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1824_ == 0)
{
v___x_1819_ = v___x_1803_;
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
else
{
lean_inc(v_a_1817_);
lean_dec(v___x_1803_);
v___x_1819_ = lean_box(0);
v_isShared_1820_ = v_isSharedCheck_1824_;
goto v_resetjp_1818_;
}
v_resetjp_1818_:
{
lean_object* v___x_1822_; 
if (v_isShared_1820_ == 0)
{
v___x_1822_ = v___x_1819_;
goto v_reusejp_1821_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_a_1817_);
v___x_1822_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1821_;
}
v_reusejp_1821_:
{
return v___x_1822_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1825_, lean_object* v_argVars_1826_, lean_object* v_e_1827_, lean_object* v_a_1828_, lean_object* v_a_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1825_, v_argVars_1826_, v_e_1827_, v_a_1828_, v_a_1829_, v_a_1830_, v_a_1831_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec(v_a_1829_);
lean_dec_ref(v_a_1828_);
lean_dec_ref(v_argVars_1826_);
lean_dec_ref(v_argMVars_1825_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2___boxed(lean_object* v_argMVars_1834_, lean_object* v_argVars_1835_, lean_object* v_as_1836_, lean_object* v_sz_1837_, lean_object* v_i_1838_, lean_object* v_b_1839_, lean_object* v___y_1840_, lean_object* v___y_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_){
_start:
{
size_t v_sz_boxed_1845_; size_t v_i_boxed_1846_; lean_object* v_res_1847_; 
v_sz_boxed_1845_ = lean_unbox_usize(v_sz_1837_);
lean_dec(v_sz_1837_);
v_i_boxed_1846_ = lean_unbox_usize(v_i_1838_);
lean_dec(v_i_1838_);
v_res_1847_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1834_, v_argVars_1835_, v_as_1836_, v_sz_boxed_1845_, v_i_boxed_1846_, v_b_1839_, v___y_1840_, v___y_1841_, v___y_1842_, v___y_1843_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec(v___y_1841_);
lean_dec_ref(v___y_1840_);
lean_dec_ref(v_as_1836_);
lean_dec_ref(v_argVars_1835_);
lean_dec_ref(v_argMVars_1834_);
return v_res_1847_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_mvarId_1848_, lean_object* v_val_1849_, lean_object* v___y_1850_, lean_object* v___y_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_){
_start:
{
lean_object* v___x_1855_; 
v___x_1855_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1848_, v_val_1849_, v___y_1851_);
return v___x_1855_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_mvarId_1856_, lean_object* v_val_1857_, lean_object* v___y_1858_, lean_object* v___y_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_mvarId_1856_, v_val_1857_, v___y_1858_, v___y_1859_, v___y_1860_, v___y_1861_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
lean_dec(v___y_1859_);
lean_dec_ref(v___y_1858_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1(lean_object* v_00_u03b2_1864_, lean_object* v_x_1865_, lean_object* v_x_1866_, lean_object* v_x_1867_){
_start:
{
lean_object* v___x_1868_; 
v___x_1868_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_x_1865_, v_x_1866_, v_x_1867_);
return v___x_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1869_, lean_object* v_x_1870_, size_t v_x_1871_, size_t v_x_1872_, lean_object* v_x_1873_, lean_object* v_x_1874_){
_start:
{
lean_object* v___x_1875_; 
v___x_1875_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1870_, v_x_1871_, v_x_1872_, v_x_1873_, v_x_1874_);
return v___x_1875_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1876_, lean_object* v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_){
_start:
{
size_t v_x_1982__boxed_1882_; size_t v_x_1983__boxed_1883_; lean_object* v_res_1884_; 
v_x_1982__boxed_1882_ = lean_unbox_usize(v_x_1878_);
lean_dec(v_x_1878_);
v_x_1983__boxed_1883_ = lean_unbox_usize(v_x_1879_);
lean_dec(v_x_1879_);
v_res_1884_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(v_00_u03b2_1876_, v_x_1877_, v_x_1982__boxed_1882_, v_x_1983__boxed_1883_, v_x_1880_, v_x_1881_);
return v_res_1884_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1885_, lean_object* v_n_1886_, lean_object* v_k_1887_, lean_object* v_v_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v_n_1886_, v_k_1887_, v_v_1888_);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1890_, size_t v_depth_1891_, lean_object* v_keys_1892_, lean_object* v_vals_1893_, lean_object* v_heq_1894_, lean_object* v_i_1895_, lean_object* v_entries_1896_){
_start:
{
lean_object* v___x_1897_; 
v___x_1897_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_1891_, v_keys_1892_, v_vals_1893_, v_i_1895_, v_entries_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1898_, lean_object* v_depth_1899_, lean_object* v_keys_1900_, lean_object* v_vals_1901_, lean_object* v_heq_1902_, lean_object* v_i_1903_, lean_object* v_entries_1904_){
_start:
{
size_t v_depth_boxed_1905_; lean_object* v_res_1906_; 
v_depth_boxed_1905_ = lean_unbox_usize(v_depth_1899_);
lean_dec(v_depth_1899_);
v_res_1906_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_1898_, v_depth_boxed_1905_, v_keys_1900_, v_vals_1901_, v_heq_1902_, v_i_1903_, v_entries_1904_);
lean_dec_ref(v_vals_1901_);
lean_dec_ref(v_keys_1900_);
return v_res_1906_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1907_, lean_object* v_x_1908_, lean_object* v_x_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_){
_start:
{
lean_object* v___x_1912_; 
v___x_1912_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1908_, v_x_1909_, v_x_1910_, v_x_1911_);
return v___x_1912_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_1913_, lean_object* v___y_1914_){
_start:
{
uint8_t v___x_1916_; 
v___x_1916_ = l_Lean_Expr_hasMVar(v_e_1913_);
if (v___x_1916_ == 0)
{
lean_object* v___x_1917_; 
v___x_1917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1917_, 0, v_e_1913_);
return v___x_1917_;
}
else
{
lean_object* v___x_1918_; lean_object* v_mctx_1919_; lean_object* v___x_1920_; lean_object* v_fst_1921_; lean_object* v_snd_1922_; lean_object* v___x_1923_; lean_object* v_cache_1924_; lean_object* v_zetaDeltaFVarIds_1925_; lean_object* v_postponed_1926_; lean_object* v_diag_1927_; lean_object* v___x_1929_; uint8_t v_isShared_1930_; uint8_t v_isSharedCheck_1936_; 
v___x_1918_ = lean_st_ref_get(v___y_1914_);
v_mctx_1919_ = lean_ctor_get(v___x_1918_, 0);
lean_inc_ref(v_mctx_1919_);
lean_dec(v___x_1918_);
v___x_1920_ = l_Lean_instantiateMVarsCore(v_mctx_1919_, v_e_1913_);
v_fst_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc(v_fst_1921_);
v_snd_1922_ = lean_ctor_get(v___x_1920_, 1);
lean_inc(v_snd_1922_);
lean_dec_ref(v___x_1920_);
v___x_1923_ = lean_st_ref_take(v___y_1914_);
v_cache_1924_ = lean_ctor_get(v___x_1923_, 1);
v_zetaDeltaFVarIds_1925_ = lean_ctor_get(v___x_1923_, 2);
v_postponed_1926_ = lean_ctor_get(v___x_1923_, 3);
v_diag_1927_ = lean_ctor_get(v___x_1923_, 4);
v_isSharedCheck_1936_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1936_ == 0)
{
lean_object* v_unused_1937_; 
v_unused_1937_ = lean_ctor_get(v___x_1923_, 0);
lean_dec(v_unused_1937_);
v___x_1929_ = v___x_1923_;
v_isShared_1930_ = v_isSharedCheck_1936_;
goto v_resetjp_1928_;
}
else
{
lean_inc(v_diag_1927_);
lean_inc(v_postponed_1926_);
lean_inc(v_zetaDeltaFVarIds_1925_);
lean_inc(v_cache_1924_);
lean_dec(v___x_1923_);
v___x_1929_ = lean_box(0);
v_isShared_1930_ = v_isSharedCheck_1936_;
goto v_resetjp_1928_;
}
v_resetjp_1928_:
{
lean_object* v___x_1932_; 
if (v_isShared_1930_ == 0)
{
lean_ctor_set(v___x_1929_, 0, v_snd_1922_);
v___x_1932_ = v___x_1929_;
goto v_reusejp_1931_;
}
else
{
lean_object* v_reuseFailAlloc_1935_; 
v_reuseFailAlloc_1935_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1935_, 0, v_snd_1922_);
lean_ctor_set(v_reuseFailAlloc_1935_, 1, v_cache_1924_);
lean_ctor_set(v_reuseFailAlloc_1935_, 2, v_zetaDeltaFVarIds_1925_);
lean_ctor_set(v_reuseFailAlloc_1935_, 3, v_postponed_1926_);
lean_ctor_set(v_reuseFailAlloc_1935_, 4, v_diag_1927_);
v___x_1932_ = v_reuseFailAlloc_1935_;
goto v_reusejp_1931_;
}
v_reusejp_1931_:
{
lean_object* v___x_1933_; lean_object* v___x_1934_; 
v___x_1933_ = lean_st_ref_set(v___y_1914_, v___x_1932_);
v___x_1934_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1934_, 0, v_fst_1921_);
return v___x_1934_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_1938_, lean_object* v___y_1939_, lean_object* v___y_1940_){
_start:
{
lean_object* v_res_1941_; 
v_res_1941_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1938_, v___y_1939_);
lean_dec(v___y_1939_);
return v_res_1941_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_1942_, lean_object* v___y_1943_, lean_object* v___y_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1942_, v___y_1944_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_1949_, v___y_1950_, v___y_1951_, v___y_1952_, v___y_1953_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
lean_dec(v___y_1951_);
lean_dec_ref(v___y_1950_);
return v_res_1955_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_1956_, lean_object* v_opt_1957_){
_start:
{
lean_object* v_name_1958_; lean_object* v_defValue_1959_; lean_object* v_map_1960_; lean_object* v___x_1961_; 
v_name_1958_ = lean_ctor_get(v_opt_1957_, 0);
v_defValue_1959_ = lean_ctor_get(v_opt_1957_, 1);
v_map_1960_ = lean_ctor_get(v_opts_1956_, 0);
v___x_1961_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1960_, v_name_1958_);
if (lean_obj_tag(v___x_1961_) == 0)
{
uint8_t v___x_1962_; 
v___x_1962_ = lean_unbox(v_defValue_1959_);
return v___x_1962_;
}
else
{
lean_object* v_val_1963_; 
v_val_1963_ = lean_ctor_get(v___x_1961_, 0);
lean_inc(v_val_1963_);
lean_dec_ref_known(v___x_1961_, 1);
if (lean_obj_tag(v_val_1963_) == 1)
{
uint8_t v_v_1964_; 
v_v_1964_ = lean_ctor_get_uint8(v_val_1963_, 0);
lean_dec_ref_known(v_val_1963_, 0);
return v_v_1964_;
}
else
{
uint8_t v___x_1965_; 
lean_dec(v_val_1963_);
v___x_1965_ = lean_unbox(v_defValue_1959_);
return v___x_1965_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_1966_, lean_object* v_opt_1967_){
_start:
{
uint8_t v_res_1968_; lean_object* v_r_1969_; 
v_res_1968_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_1966_, v_opt_1967_);
lean_dec_ref(v_opt_1967_);
lean_dec_ref(v_opts_1966_);
v_r_1969_ = lean_box(v_res_1968_);
return v_r_1969_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_1970_, lean_object* v_as_1971_, size_t v_i_1972_, size_t v_stop_1973_){
_start:
{
uint8_t v___x_1974_; 
v___x_1974_ = lean_usize_dec_eq(v_i_1972_, v_stop_1973_);
if (v___x_1974_ == 0)
{
lean_object* v___x_1975_; uint8_t v___x_1976_; 
v___x_1975_ = lean_array_uget_borrowed(v_as_1971_, v_i_1972_);
v___x_1976_ = lean_nat_dec_eq(v_a_1970_, v___x_1975_);
if (v___x_1976_ == 0)
{
size_t v___x_1977_; size_t v___x_1978_; 
v___x_1977_ = ((size_t)1ULL);
v___x_1978_ = lean_usize_add(v_i_1972_, v___x_1977_);
v_i_1972_ = v___x_1978_;
goto _start;
}
else
{
return v___x_1976_;
}
}
else
{
uint8_t v___x_1980_; 
v___x_1980_ = 0;
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_1981_, lean_object* v_as_1982_, lean_object* v_i_1983_, lean_object* v_stop_1984_){
_start:
{
size_t v_i_boxed_1985_; size_t v_stop_boxed_1986_; uint8_t v_res_1987_; lean_object* v_r_1988_; 
v_i_boxed_1985_ = lean_unbox_usize(v_i_1983_);
lean_dec(v_i_1983_);
v_stop_boxed_1986_ = lean_unbox_usize(v_stop_1984_);
lean_dec(v_stop_1984_);
v_res_1987_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1981_, v_as_1982_, v_i_boxed_1985_, v_stop_boxed_1986_);
lean_dec_ref(v_as_1982_);
lean_dec(v_a_1981_);
v_r_1988_ = lean_box(v_res_1987_);
return v_r_1988_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_1989_, lean_object* v_a_1990_){
_start:
{
lean_object* v___x_1991_; lean_object* v___x_1992_; uint8_t v___x_1993_; 
v___x_1991_ = lean_unsigned_to_nat(0u);
v___x_1992_ = lean_array_get_size(v_as_1989_);
v___x_1993_ = lean_nat_dec_lt(v___x_1991_, v___x_1992_);
if (v___x_1993_ == 0)
{
return v___x_1993_;
}
else
{
if (v___x_1993_ == 0)
{
return v___x_1993_;
}
else
{
size_t v___x_1994_; size_t v___x_1995_; uint8_t v___x_1996_; 
v___x_1994_ = ((size_t)0ULL);
v___x_1995_ = lean_usize_of_nat(v___x_1992_);
v___x_1996_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1990_, v_as_1989_, v___x_1994_, v___x_1995_);
return v___x_1996_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_1997_, lean_object* v_a_1998_){
_start:
{
uint8_t v_res_1999_; lean_object* v_r_2000_; 
v_res_1999_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_1997_, v_a_1998_);
lean_dec(v_a_1998_);
lean_dec_ref(v_as_1997_);
v_r_2000_ = lean_box(v_res_1999_);
return v_r_2000_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_2001_, lean_object* v_fst_2002_, lean_object* v_argVars_2003_, lean_object* v_as_2004_, size_t v_sz_2005_, size_t v_i_2006_, lean_object* v_b_2007_, lean_object* v___y_2008_, lean_object* v___y_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_){
_start:
{
lean_object* v_a_2014_; uint8_t v___x_2018_; 
v___x_2018_ = lean_usize_dec_lt(v_i_2006_, v_sz_2005_);
if (v___x_2018_ == 0)
{
lean_object* v___x_2019_; 
v___x_2019_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2019_, 0, v_b_2007_);
return v___x_2019_;
}
else
{
lean_object* v_next_2020_; 
v_next_2020_ = lean_ctor_get(v_b_2007_, 0);
lean_inc(v_next_2020_);
if (lean_obj_tag(v_next_2020_) == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_b_2007_);
return v___x_2021_;
}
else
{
lean_object* v_upperBound_2022_; lean_object* v_val_2023_; lean_object* v___x_2025_; uint8_t v_isShared_2026_; uint8_t v_isSharedCheck_2054_; 
v_upperBound_2022_ = lean_ctor_get(v_b_2007_, 1);
v_val_2023_ = lean_ctor_get(v_next_2020_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v_next_2020_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2025_ = v_next_2020_;
v_isShared_2026_ = v_isSharedCheck_2054_;
goto v_resetjp_2024_;
}
else
{
lean_inc(v_val_2023_);
lean_dec(v_next_2020_);
v___x_2025_ = lean_box(0);
v_isShared_2026_ = v_isSharedCheck_2054_;
goto v_resetjp_2024_;
}
v_resetjp_2024_:
{
uint8_t v___x_2027_; 
v___x_2027_ = lean_nat_dec_lt(v_val_2023_, v_upperBound_2022_);
if (v___x_2027_ == 0)
{
lean_object* v___x_2028_; 
lean_del_object(v___x_2025_);
lean_dec(v_val_2023_);
v___x_2028_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2028_, 0, v_b_2007_);
return v___x_2028_;
}
else
{
lean_object* v___x_2030_; uint8_t v_isShared_2031_; uint8_t v_isSharedCheck_2051_; 
lean_inc(v_upperBound_2022_);
v_isSharedCheck_2051_ = !lean_is_exclusive(v_b_2007_);
if (v_isSharedCheck_2051_ == 0)
{
lean_object* v_unused_2052_; lean_object* v_unused_2053_; 
v_unused_2052_ = lean_ctor_get(v_b_2007_, 1);
lean_dec(v_unused_2052_);
v_unused_2053_ = lean_ctor_get(v_b_2007_, 0);
lean_dec(v_unused_2053_);
v___x_2030_ = v_b_2007_;
v_isShared_2031_ = v_isSharedCheck_2051_;
goto v_resetjp_2029_;
}
else
{
lean_dec(v_b_2007_);
v___x_2030_ = lean_box(0);
v_isShared_2031_ = v_isSharedCheck_2051_;
goto v_resetjp_2029_;
}
v_resetjp_2029_:
{
lean_object* v___x_2032_; lean_object* v___x_2033_; lean_object* v___x_2035_; 
v___x_2032_ = lean_unsigned_to_nat(1u);
v___x_2033_ = lean_nat_add(v_val_2023_, v___x_2032_);
if (v_isShared_2026_ == 0)
{
lean_ctor_set(v___x_2025_, 0, v___x_2033_);
v___x_2035_ = v___x_2025_;
goto v_reusejp_2034_;
}
else
{
lean_object* v_reuseFailAlloc_2050_; 
v_reuseFailAlloc_2050_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2050_, 0, v___x_2033_);
v___x_2035_ = v_reuseFailAlloc_2050_;
goto v_reusejp_2034_;
}
v_reusejp_2034_:
{
lean_object* v___x_2037_; 
if (v_isShared_2031_ == 0)
{
lean_ctor_set(v___x_2030_, 0, v___x_2035_);
v___x_2037_ = v___x_2030_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v___x_2035_);
lean_ctor_set(v_reuseFailAlloc_2049_, 1, v_upperBound_2022_);
v___x_2037_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
uint8_t v___x_2038_; 
v___x_2038_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2001_, v_val_2023_);
lean_dec(v_val_2023_);
if (v___x_2038_ == 0)
{
lean_object* v_a_2039_; lean_object* v___x_2040_; 
v_a_2039_ = lean_array_uget_borrowed(v_as_2004_, v_i_2006_);
lean_inc(v_a_2039_);
v___x_2040_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2002_, v_argVars_2003_, v_a_2039_, v___y_2008_, v___y_2009_, v___y_2010_, v___y_2011_);
if (lean_obj_tag(v___x_2040_) == 0)
{
lean_dec_ref_known(v___x_2040_, 1);
v_a_2014_ = v___x_2037_;
goto v___jp_2013_;
}
else
{
lean_object* v_a_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2048_; 
lean_dec_ref(v___x_2037_);
v_a_2041_ = lean_ctor_get(v___x_2040_, 0);
v_isSharedCheck_2048_ = !lean_is_exclusive(v___x_2040_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_2043_ = v___x_2040_;
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_a_2041_);
lean_dec(v___x_2040_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2048_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2046_; 
if (v_isShared_2044_ == 0)
{
v___x_2046_ = v___x_2043_;
goto v_reusejp_2045_;
}
else
{
lean_object* v_reuseFailAlloc_2047_; 
v_reuseFailAlloc_2047_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2047_, 0, v_a_2041_);
v___x_2046_ = v_reuseFailAlloc_2047_;
goto v_reusejp_2045_;
}
v_reusejp_2045_:
{
return v___x_2046_;
}
}
}
}
else
{
v_a_2014_ = v___x_2037_;
goto v___jp_2013_;
}
}
}
}
}
}
}
}
v___jp_2013_:
{
size_t v___x_2015_; size_t v___x_2016_; 
v___x_2015_ = ((size_t)1ULL);
v___x_2016_ = lean_usize_add(v_i_2006_, v___x_2015_);
v_i_2006_ = v___x_2016_;
v_b_2007_ = v_a_2014_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2055_, lean_object* v_fst_2056_, lean_object* v_argVars_2057_, lean_object* v_as_2058_, lean_object* v_sz_2059_, lean_object* v_i_2060_, lean_object* v_b_2061_, lean_object* v___y_2062_, lean_object* v___y_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_){
_start:
{
size_t v_sz_boxed_2067_; size_t v_i_boxed_2068_; lean_object* v_res_2069_; 
v_sz_boxed_2067_ = lean_unbox_usize(v_sz_2059_);
lean_dec(v_sz_2059_);
v_i_boxed_2068_ = lean_unbox_usize(v_i_2060_);
lean_dec(v_i_2060_);
v_res_2069_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2055_, v_fst_2056_, v_argVars_2057_, v_as_2058_, v_sz_boxed_2067_, v_i_boxed_2068_, v_b_2061_, v___y_2062_, v___y_2063_, v___y_2064_, v___y_2065_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec(v___y_2063_);
lean_dec_ref(v___y_2062_);
lean_dec_ref(v_as_2058_);
lean_dec_ref(v_argVars_2057_);
lean_dec_ref(v_fst_2056_);
lean_dec_ref(v_a_2055_);
return v_res_2069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2070_, lean_object* v_as_2071_, size_t v_i_2072_, size_t v_stop_2073_, lean_object* v_b_2074_){
_start:
{
lean_object* v___y_2076_; uint8_t v___x_2080_; 
v___x_2080_ = lean_usize_dec_eq(v_i_2072_, v_stop_2073_);
if (v___x_2080_ == 0)
{
lean_object* v___x_2081_; uint8_t v___x_2082_; 
v___x_2081_ = lean_array_uget_borrowed(v_as_2071_, v_i_2072_);
v___x_2082_ = lean_nat_dec_eq(v___x_2081_, v_next_2070_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; 
lean_inc(v___x_2081_);
v___x_2083_ = lean_array_push(v_b_2074_, v___x_2081_);
v___y_2076_ = v___x_2083_;
goto v___jp_2075_;
}
else
{
v___y_2076_ = v_b_2074_;
goto v___jp_2075_;
}
}
else
{
return v_b_2074_;
}
v___jp_2075_:
{
size_t v___x_2077_; size_t v___x_2078_; 
v___x_2077_ = ((size_t)1ULL);
v___x_2078_ = lean_usize_add(v_i_2072_, v___x_2077_);
v_i_2072_ = v___x_2078_;
v_b_2074_ = v___y_2076_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2084_, lean_object* v_as_2085_, lean_object* v_i_2086_, lean_object* v_stop_2087_, lean_object* v_b_2088_){
_start:
{
size_t v_i_boxed_2089_; size_t v_stop_boxed_2090_; lean_object* v_res_2091_; 
v_i_boxed_2089_ = lean_unbox_usize(v_i_2086_);
lean_dec(v_i_2086_);
v_stop_boxed_2090_ = lean_unbox_usize(v_stop_2087_);
lean_dec(v_stop_2087_);
v_res_2091_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2084_, v_as_2085_, v_i_boxed_2089_, v_stop_boxed_2090_, v_b_2088_);
lean_dec_ref(v_as_2085_);
lean_dec(v_next_2084_);
return v_res_2091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object* v_fst_2092_, lean_object* v_fst_2093_, lean_object* v_argVars_2094_, lean_object* v_snd_2095_, lean_object* v_next_2096_, lean_object* v___y_2097_, lean_object* v___y_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_){
_start:
{
lean_object* v___x_2102_; lean_object* v___y_2104_; lean_object* v___x_2145_; lean_object* v___x_2146_; lean_object* v___x_2147_; uint8_t v___x_2148_; 
lean_inc(v_next_2096_);
v___x_2102_ = lean_array_push(v_fst_2092_, v_next_2096_);
v___x_2145_ = lean_unsigned_to_nat(0u);
v___x_2146_ = lean_array_get_size(v_snd_2095_);
v___x_2147_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2148_ = lean_nat_dec_lt(v___x_2145_, v___x_2146_);
if (v___x_2148_ == 0)
{
v___y_2104_ = v___x_2147_;
goto v___jp_2103_;
}
else
{
uint8_t v___x_2149_; 
v___x_2149_ = lean_nat_dec_le(v___x_2146_, v___x_2146_);
if (v___x_2149_ == 0)
{
if (v___x_2148_ == 0)
{
v___y_2104_ = v___x_2147_;
goto v___jp_2103_;
}
else
{
size_t v___x_2150_; size_t v___x_2151_; lean_object* v___x_2152_; 
v___x_2150_ = ((size_t)0ULL);
v___x_2151_ = lean_usize_of_nat(v___x_2146_);
v___x_2152_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2096_, v_snd_2095_, v___x_2150_, v___x_2151_, v___x_2147_);
v___y_2104_ = v___x_2152_;
goto v___jp_2103_;
}
}
else
{
size_t v___x_2153_; size_t v___x_2154_; lean_object* v___x_2155_; 
v___x_2153_ = ((size_t)0ULL);
v___x_2154_ = lean_usize_of_nat(v___x_2146_);
v___x_2155_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2096_, v_snd_2095_, v___x_2153_, v___x_2154_, v___x_2147_);
v___y_2104_ = v___x_2155_;
goto v___jp_2103_;
}
}
v___jp_2103_:
{
lean_object* v___x_2105_; lean_object* v___x_2106_; lean_object* v___x_2107_; 
v___x_2105_ = l_Lean_instInhabitedExpr;
v___x_2106_ = lean_array_get_borrowed(v___x_2105_, v_fst_2093_, v_next_2096_);
lean_dec(v_next_2096_);
lean_inc(v___y_2100_);
lean_inc_ref(v___y_2099_);
lean_inc(v___y_2098_);
lean_inc_ref(v___y_2097_);
lean_inc(v___x_2106_);
v___x_2107_ = lean_infer_type(v___x_2106_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2107_) == 0)
{
lean_object* v_a_2108_; lean_object* v___x_2109_; 
v_a_2108_ = lean_ctor_get(v___x_2107_, 0);
lean_inc(v_a_2108_);
lean_dec_ref_known(v___x_2107_, 1);
v___x_2109_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2093_, v_argVars_2094_, v_a_2108_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v___x_2110_; 
lean_dec_ref_known(v___x_2109_, 1);
lean_inc(v___x_2106_);
v___x_2110_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2093_, v_argVars_2094_, v___x_2106_, v___y_2097_, v___y_2098_, v___y_2099_, v___y_2100_);
if (lean_obj_tag(v___x_2110_) == 0)
{
lean_object* v___x_2112_; uint8_t v_isShared_2113_; uint8_t v_isSharedCheck_2119_; 
v_isSharedCheck_2119_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2119_ == 0)
{
lean_object* v_unused_2120_; 
v_unused_2120_ = lean_ctor_get(v___x_2110_, 0);
lean_dec(v_unused_2120_);
v___x_2112_ = v___x_2110_;
v_isShared_2113_ = v_isSharedCheck_2119_;
goto v_resetjp_2111_;
}
else
{
lean_dec(v___x_2110_);
v___x_2112_ = lean_box(0);
v_isShared_2113_ = v_isSharedCheck_2119_;
goto v_resetjp_2111_;
}
v_resetjp_2111_:
{
lean_object* v___x_2114_; lean_object* v___x_2115_; lean_object* v___x_2117_; 
v___x_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2114_, 0, v___x_2102_);
lean_ctor_set(v___x_2114_, 1, v___y_2104_);
v___x_2115_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2115_, 0, v___x_2114_);
if (v_isShared_2113_ == 0)
{
lean_ctor_set(v___x_2112_, 0, v___x_2115_);
v___x_2117_ = v___x_2112_;
goto v_reusejp_2116_;
}
else
{
lean_object* v_reuseFailAlloc_2118_; 
v_reuseFailAlloc_2118_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2118_, 0, v___x_2115_);
v___x_2117_ = v_reuseFailAlloc_2118_;
goto v_reusejp_2116_;
}
v_reusejp_2116_:
{
return v___x_2117_;
}
}
}
else
{
lean_object* v_a_2121_; lean_object* v___x_2123_; uint8_t v_isShared_2124_; uint8_t v_isSharedCheck_2128_; 
lean_dec_ref(v___y_2104_);
lean_dec_ref(v___x_2102_);
v_a_2121_ = lean_ctor_get(v___x_2110_, 0);
v_isSharedCheck_2128_ = !lean_is_exclusive(v___x_2110_);
if (v_isSharedCheck_2128_ == 0)
{
v___x_2123_ = v___x_2110_;
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
else
{
lean_inc(v_a_2121_);
lean_dec(v___x_2110_);
v___x_2123_ = lean_box(0);
v_isShared_2124_ = v_isSharedCheck_2128_;
goto v_resetjp_2122_;
}
v_resetjp_2122_:
{
lean_object* v___x_2126_; 
if (v_isShared_2124_ == 0)
{
v___x_2126_ = v___x_2123_;
goto v_reusejp_2125_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v_a_2121_);
v___x_2126_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2125_;
}
v_reusejp_2125_:
{
return v___x_2126_;
}
}
}
}
else
{
lean_object* v_a_2129_; lean_object* v___x_2131_; uint8_t v_isShared_2132_; uint8_t v_isSharedCheck_2136_; 
lean_dec_ref(v___y_2104_);
lean_dec_ref(v___x_2102_);
v_a_2129_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2136_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2136_ == 0)
{
v___x_2131_ = v___x_2109_;
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
else
{
lean_inc(v_a_2129_);
lean_dec(v___x_2109_);
v___x_2131_ = lean_box(0);
v_isShared_2132_ = v_isSharedCheck_2136_;
goto v_resetjp_2130_;
}
v_resetjp_2130_:
{
lean_object* v___x_2134_; 
if (v_isShared_2132_ == 0)
{
v___x_2134_ = v___x_2131_;
goto v_reusejp_2133_;
}
else
{
lean_object* v_reuseFailAlloc_2135_; 
v_reuseFailAlloc_2135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2135_, 0, v_a_2129_);
v___x_2134_ = v_reuseFailAlloc_2135_;
goto v_reusejp_2133_;
}
v_reusejp_2133_:
{
return v___x_2134_;
}
}
}
}
else
{
lean_object* v_a_2137_; lean_object* v___x_2139_; uint8_t v_isShared_2140_; uint8_t v_isSharedCheck_2144_; 
lean_dec_ref(v___y_2104_);
lean_dec_ref(v___x_2102_);
v_a_2137_ = lean_ctor_get(v___x_2107_, 0);
v_isSharedCheck_2144_ = !lean_is_exclusive(v___x_2107_);
if (v_isSharedCheck_2144_ == 0)
{
v___x_2139_ = v___x_2107_;
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
else
{
lean_inc(v_a_2137_);
lean_dec(v___x_2107_);
v___x_2139_ = lean_box(0);
v_isShared_2140_ = v_isSharedCheck_2144_;
goto v_resetjp_2138_;
}
v_resetjp_2138_:
{
lean_object* v___x_2142_; 
if (v_isShared_2140_ == 0)
{
v___x_2142_ = v___x_2139_;
goto v_reusejp_2141_;
}
else
{
lean_object* v_reuseFailAlloc_2143_; 
v_reuseFailAlloc_2143_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2143_, 0, v_a_2137_);
v___x_2142_ = v_reuseFailAlloc_2143_;
goto v_reusejp_2141_;
}
v_reusejp_2141_:
{
return v___x_2142_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object* v_fst_2156_, lean_object* v_fst_2157_, lean_object* v_argVars_2158_, lean_object* v_snd_2159_, lean_object* v_next_2160_, lean_object* v___y_2161_, lean_object* v___y_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_){
_start:
{
lean_object* v_res_2166_; 
v_res_2166_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2156_, v_fst_2157_, v_argVars_2158_, v_snd_2159_, v_next_2160_, v___y_2161_, v___y_2162_, v___y_2163_, v___y_2164_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v___y_2162_);
lean_dec_ref(v___y_2161_);
lean_dec(v_snd_2159_);
lean_dec_ref(v_argVars_2158_);
lean_dec_ref(v_fst_2157_);
return v_res_2166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2167_, lean_object* v___x_2168_, lean_object* v_a_2169_, lean_object* v_a_2170_, lean_object* v_b_2171_){
_start:
{
uint8_t v___x_2173_; 
v___x_2173_ = lean_nat_dec_lt(v_a_2170_, v_upperBound_2167_);
if (v___x_2173_ == 0)
{
lean_object* v___x_2174_; 
lean_dec(v_a_2170_);
v___x_2174_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2174_, 0, v_b_2171_);
return v___x_2174_;
}
else
{
lean_object* v_snd_2175_; lean_object* v___x_2177_; uint8_t v_isShared_2178_; uint8_t v_isSharedCheck_2216_; 
v_snd_2175_ = lean_ctor_get(v_b_2171_, 1);
v_isSharedCheck_2216_ = !lean_is_exclusive(v_b_2171_);
if (v_isSharedCheck_2216_ == 0)
{
lean_object* v_unused_2217_; 
v_unused_2217_ = lean_ctor_get(v_b_2171_, 0);
lean_dec(v_unused_2217_);
v___x_2177_ = v_b_2171_;
v_isShared_2178_ = v_isSharedCheck_2216_;
goto v_resetjp_2176_;
}
else
{
lean_inc(v_snd_2175_);
lean_dec(v_b_2171_);
v___x_2177_ = lean_box(0);
v_isShared_2178_ = v_isSharedCheck_2216_;
goto v_resetjp_2176_;
}
v_resetjp_2176_:
{
lean_object* v_array_2179_; lean_object* v_start_2180_; lean_object* v_stop_2181_; lean_object* v___x_2182_; uint8_t v___x_2183_; 
v_array_2179_ = lean_ctor_get(v_snd_2175_, 0);
v_start_2180_ = lean_ctor_get(v_snd_2175_, 1);
v_stop_2181_ = lean_ctor_get(v_snd_2175_, 2);
v___x_2182_ = lean_box(0);
v___x_2183_ = lean_nat_dec_lt(v_start_2180_, v_stop_2181_);
if (v___x_2183_ == 0)
{
lean_object* v___x_2185_; 
lean_dec(v_a_2170_);
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 0, v___x_2182_);
v___x_2185_ = v___x_2177_;
goto v_reusejp_2184_;
}
else
{
lean_object* v_reuseFailAlloc_2187_; 
v_reuseFailAlloc_2187_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2187_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2187_, 1, v_snd_2175_);
v___x_2185_ = v_reuseFailAlloc_2187_;
goto v_reusejp_2184_;
}
v_reusejp_2184_:
{
lean_object* v___x_2186_; 
v___x_2186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2186_, 0, v___x_2185_);
return v___x_2186_;
}
}
else
{
lean_object* v___x_2189_; uint8_t v_isShared_2190_; uint8_t v_isSharedCheck_2212_; 
lean_inc(v_stop_2181_);
lean_inc(v_start_2180_);
lean_inc_ref(v_array_2179_);
v_isSharedCheck_2212_ = !lean_is_exclusive(v_snd_2175_);
if (v_isSharedCheck_2212_ == 0)
{
lean_object* v_unused_2213_; lean_object* v_unused_2214_; lean_object* v_unused_2215_; 
v_unused_2213_ = lean_ctor_get(v_snd_2175_, 2);
lean_dec(v_unused_2213_);
v_unused_2214_ = lean_ctor_get(v_snd_2175_, 1);
lean_dec(v_unused_2214_);
v_unused_2215_ = lean_ctor_get(v_snd_2175_, 0);
lean_dec(v_unused_2215_);
v___x_2189_ = v_snd_2175_;
v_isShared_2190_ = v_isSharedCheck_2212_;
goto v_resetjp_2188_;
}
else
{
lean_dec(v_snd_2175_);
v___x_2189_ = lean_box(0);
v_isShared_2190_ = v_isSharedCheck_2212_;
goto v_resetjp_2188_;
}
v_resetjp_2188_:
{
lean_object* v___x_2191_; uint8_t v___x_2192_; lean_object* v___x_2193_; lean_object* v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2197_; 
v___x_2191_ = lean_unsigned_to_nat(0u);
v___x_2192_ = lean_nat_dec_eq(v___x_2168_, v___x_2191_);
v___x_2193_ = lean_array_fget(v_array_2179_, v_start_2180_);
v___x_2194_ = lean_unsigned_to_nat(1u);
v___x_2195_ = lean_nat_add(v_start_2180_, v___x_2194_);
lean_dec(v_start_2180_);
if (v_isShared_2190_ == 0)
{
lean_ctor_set(v___x_2189_, 1, v___x_2195_);
v___x_2197_ = v___x_2189_;
goto v_reusejp_2196_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v_array_2179_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v___x_2195_);
lean_ctor_set(v_reuseFailAlloc_2211_, 2, v_stop_2181_);
v___x_2197_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2196_;
}
v_reusejp_2196_:
{
uint8_t v___x_2210_; 
v___x_2210_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2169_, v_a_2170_);
if (v___x_2210_ == 0)
{
goto v___jp_2204_;
}
else
{
if (v___x_2192_ == 0)
{
lean_dec(v___x_2193_);
goto v___jp_2198_;
}
else
{
goto v___jp_2204_;
}
}
v___jp_2198_:
{
lean_object* v___x_2200_; 
if (v_isShared_2178_ == 0)
{
lean_ctor_set(v___x_2177_, 1, v___x_2197_);
lean_ctor_set(v___x_2177_, 0, v___x_2182_);
v___x_2200_ = v___x_2177_;
goto v_reusejp_2199_;
}
else
{
lean_object* v_reuseFailAlloc_2203_; 
v_reuseFailAlloc_2203_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2203_, 0, v___x_2182_);
lean_ctor_set(v_reuseFailAlloc_2203_, 1, v___x_2197_);
v___x_2200_ = v_reuseFailAlloc_2203_;
goto v_reusejp_2199_;
}
v_reusejp_2199_:
{
lean_object* v___x_2201_; 
v___x_2201_ = lean_nat_add(v_a_2170_, v___x_2194_);
lean_dec(v_a_2170_);
v_a_2170_ = v___x_2201_;
v_b_2171_ = v___x_2200_;
goto _start;
}
}
v___jp_2204_:
{
uint8_t v___x_2205_; 
v___x_2205_ = l_Lean_Expr_hasExprMVar(v___x_2193_);
lean_dec(v___x_2193_);
if (v___x_2205_ == 0)
{
goto v___jp_2198_;
}
else
{
lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_del_object(v___x_2177_);
lean_dec(v_a_2170_);
v___x_2206_ = lean_box(v___x_2192_);
v___x_2207_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2207_, 0, v___x_2206_);
v___x_2208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2208_, 0, v___x_2207_);
lean_ctor_set(v___x_2208_, 1, v___x_2197_);
v___x_2209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
return v___x_2209_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2218_, lean_object* v___x_2219_, lean_object* v_a_2220_, lean_object* v_a_2221_, lean_object* v_b_2222_, lean_object* v___y_2223_){
_start:
{
lean_object* v_res_2224_; 
v_res_2224_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2218_, v___x_2219_, v_a_2220_, v_a_2221_, v_b_2222_);
lean_dec_ref(v_a_2220_);
lean_dec(v___x_2219_);
lean_dec(v_upperBound_2218_);
return v_res_2224_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2225_; lean_object* v_dummy_2226_; 
v___x_2225_ = lean_box(0);
v_dummy_2226_ = l_Lean_Expr_sort___override(v___x_2225_);
return v_dummy_2226_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2227_, lean_object* v___x_2228_, uint8_t v___x_2229_, lean_object* v_x_2230_, lean_object* v_argTy_2231_, lean_object* v___y_2232_, lean_object* v___y_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_){
_start:
{
lean_object* v___x_2237_; 
lean_inc(v___y_2235_);
lean_inc_ref(v___y_2234_);
lean_inc(v___y_2233_);
lean_inc_ref(v___y_2232_);
v___x_2237_ = lean_whnf(v_argTy_2231_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2237_) == 0)
{
lean_object* v_a_2238_; lean_object* v___x_2239_; 
v_a_2238_ = lean_ctor_get(v___x_2237_, 0);
lean_inc(v_a_2238_);
lean_dec_ref_known(v___x_2237_, 1);
v___x_2239_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2238_, v___y_2232_, v___y_2233_, v___y_2234_, v___y_2235_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v_dummy_2241_; lean_object* v_nargs_2242_; lean_object* v___x_2243_; lean_object* v___x_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v_dummy_2241_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2242_ = l_Lean_Expr_getAppNumArgs(v_a_2238_);
lean_inc(v_nargs_2242_);
v___x_2243_ = lean_mk_array(v_nargs_2242_, v_dummy_2241_);
v___x_2244_ = lean_unsigned_to_nat(1u);
v___x_2245_ = lean_nat_sub(v_nargs_2242_, v___x_2244_);
lean_dec(v_nargs_2242_);
v___x_2246_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2238_, v___x_2243_, v___x_2245_);
v___x_2247_ = lean_array_get_size(v___x_2246_);
lean_inc(v___x_2227_);
v___x_2248_ = l_Array_toSubarray___redArg(v___x_2246_, v___x_2227_, v___x_2247_);
v___x_2249_ = lean_box(0);
v___x_2250_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2250_, 0, v___x_2249_);
lean_ctor_set(v___x_2250_, 1, v___x_2248_);
v___x_2251_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2247_, v___x_2228_, v_a_2240_, v___x_2227_, v___x_2250_);
lean_dec(v_a_2240_);
if (lean_obj_tag(v___x_2251_) == 0)
{
lean_object* v_a_2252_; lean_object* v___x_2254_; uint8_t v_isShared_2255_; uint8_t v_isSharedCheck_2265_; 
v_a_2252_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2265_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2265_ == 0)
{
v___x_2254_ = v___x_2251_;
v_isShared_2255_ = v_isSharedCheck_2265_;
goto v_resetjp_2253_;
}
else
{
lean_inc(v_a_2252_);
lean_dec(v___x_2251_);
v___x_2254_ = lean_box(0);
v_isShared_2255_ = v_isSharedCheck_2265_;
goto v_resetjp_2253_;
}
v_resetjp_2253_:
{
lean_object* v_fst_2256_; 
v_fst_2256_ = lean_ctor_get(v_a_2252_, 0);
lean_inc(v_fst_2256_);
lean_dec(v_a_2252_);
if (lean_obj_tag(v_fst_2256_) == 0)
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2257_ = lean_box(v___x_2229_);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v___x_2257_);
v___x_2259_ = v___x_2254_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
return v___x_2259_;
}
}
else
{
lean_object* v_val_2261_; lean_object* v___x_2263_; 
v_val_2261_ = lean_ctor_get(v_fst_2256_, 0);
lean_inc(v_val_2261_);
lean_dec_ref_known(v_fst_2256_, 1);
if (v_isShared_2255_ == 0)
{
lean_ctor_set(v___x_2254_, 0, v_val_2261_);
v___x_2263_ = v___x_2254_;
goto v_reusejp_2262_;
}
else
{
lean_object* v_reuseFailAlloc_2264_; 
v_reuseFailAlloc_2264_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2264_, 0, v_val_2261_);
v___x_2263_ = v_reuseFailAlloc_2264_;
goto v_reusejp_2262_;
}
v_reusejp_2262_:
{
return v___x_2263_;
}
}
}
}
else
{
lean_object* v_a_2266_; lean_object* v___x_2268_; uint8_t v_isShared_2269_; uint8_t v_isSharedCheck_2273_; 
v_a_2266_ = lean_ctor_get(v___x_2251_, 0);
v_isSharedCheck_2273_ = !lean_is_exclusive(v___x_2251_);
if (v_isSharedCheck_2273_ == 0)
{
v___x_2268_ = v___x_2251_;
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
else
{
lean_inc(v_a_2266_);
lean_dec(v___x_2251_);
v___x_2268_ = lean_box(0);
v_isShared_2269_ = v_isSharedCheck_2273_;
goto v_resetjp_2267_;
}
v_resetjp_2267_:
{
lean_object* v___x_2271_; 
if (v_isShared_2269_ == 0)
{
v___x_2271_ = v___x_2268_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2272_; 
v_reuseFailAlloc_2272_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2272_, 0, v_a_2266_);
v___x_2271_ = v_reuseFailAlloc_2272_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
return v___x_2271_;
}
}
}
}
else
{
lean_object* v_a_2274_; lean_object* v___x_2276_; uint8_t v_isShared_2277_; uint8_t v_isSharedCheck_2281_; 
lean_dec(v_a_2238_);
lean_dec(v___x_2227_);
v_a_2274_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2281_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2281_ == 0)
{
v___x_2276_ = v___x_2239_;
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
else
{
lean_inc(v_a_2274_);
lean_dec(v___x_2239_);
v___x_2276_ = lean_box(0);
v_isShared_2277_ = v_isSharedCheck_2281_;
goto v_resetjp_2275_;
}
v_resetjp_2275_:
{
lean_object* v___x_2279_; 
if (v_isShared_2277_ == 0)
{
v___x_2279_ = v___x_2276_;
goto v_reusejp_2278_;
}
else
{
lean_object* v_reuseFailAlloc_2280_; 
v_reuseFailAlloc_2280_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2280_, 0, v_a_2274_);
v___x_2279_ = v_reuseFailAlloc_2280_;
goto v_reusejp_2278_;
}
v_reusejp_2278_:
{
return v___x_2279_;
}
}
}
}
else
{
lean_object* v_a_2282_; lean_object* v___x_2284_; uint8_t v_isShared_2285_; uint8_t v_isSharedCheck_2289_; 
lean_dec(v___x_2227_);
v_a_2282_ = lean_ctor_get(v___x_2237_, 0);
v_isSharedCheck_2289_ = !lean_is_exclusive(v___x_2237_);
if (v_isSharedCheck_2289_ == 0)
{
v___x_2284_ = v___x_2237_;
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
else
{
lean_inc(v_a_2282_);
lean_dec(v___x_2237_);
v___x_2284_ = lean_box(0);
v_isShared_2285_ = v_isSharedCheck_2289_;
goto v_resetjp_2283_;
}
v_resetjp_2283_:
{
lean_object* v___x_2287_; 
if (v_isShared_2285_ == 0)
{
v___x_2287_ = v___x_2284_;
goto v_reusejp_2286_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v_a_2282_);
v___x_2287_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2286_;
}
v_reusejp_2286_:
{
return v___x_2287_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2290_, lean_object* v___x_2291_, lean_object* v___x_2292_, lean_object* v_x_2293_, lean_object* v_argTy_2294_, lean_object* v___y_2295_, lean_object* v___y_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_){
_start:
{
uint8_t v___x_26128__boxed_2300_; lean_object* v_res_2301_; 
v___x_26128__boxed_2300_ = lean_unbox(v___x_2292_);
v_res_2301_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2290_, v___x_2291_, v___x_26128__boxed_2300_, v_x_2293_, v_argTy_2294_, v___y_2295_, v___y_2296_, v___y_2297_, v___y_2298_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec(v___y_2296_);
lean_dec_ref(v___y_2295_);
lean_dec_ref(v_x_2293_);
lean_dec(v___x_2291_);
return v_res_2301_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2305_, lean_object* v_projInfo_x3f_2306_, lean_object* v___x_2307_, lean_object* v_argVars_2308_, lean_object* v_as_2309_, size_t v_sz_2310_, size_t v_i_2311_, lean_object* v_b_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_){
_start:
{
uint8_t v___x_2318_; 
v___x_2318_ = lean_usize_dec_lt(v_i_2311_, v_sz_2310_);
if (v___x_2318_ == 0)
{
lean_object* v___x_2319_; 
lean_dec(v___x_2307_);
v___x_2319_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2319_, 0, v_b_2312_);
return v___x_2319_;
}
else
{
lean_object* v_a_2320_; lean_object* v___x_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; 
lean_dec_ref(v_b_2312_);
v_a_2320_ = lean_array_uget_borrowed(v_as_2309_, v_i_2311_);
v___x_2321_ = l_Lean_instInhabitedExpr;
v___x_2322_ = lean_array_get_borrowed(v___x_2321_, v_fst_2305_, v_a_2320_);
lean_inc(v___y_2316_);
lean_inc_ref(v___y_2315_);
lean_inc(v___y_2314_);
lean_inc_ref(v___y_2313_);
lean_inc(v___x_2322_);
v___x_2323_ = lean_infer_type(v___x_2322_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2323_) == 0)
{
lean_object* v_a_2324_; lean_object* v___x_2325_; 
v_a_2324_ = lean_ctor_get(v___x_2323_, 0);
lean_inc(v_a_2324_);
lean_dec_ref_known(v___x_2323_, 1);
v___x_2325_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2324_, v___y_2314_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2328_; uint8_t v_isShared_2329_; uint8_t v_isSharedCheck_2372_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2328_ = v___x_2325_;
v_isShared_2329_ = v_isSharedCheck_2372_;
goto v_resetjp_2327_;
}
else
{
lean_inc(v_a_2326_);
lean_dec(v___x_2325_);
v___x_2328_ = lean_box(0);
v_isShared_2329_ = v_isSharedCheck_2372_;
goto v_resetjp_2327_;
}
v_resetjp_2327_:
{
lean_object* v___x_2330_; lean_object* v___x_2338_; lean_object* v___y_2340_; lean_object* v___x_2354_; lean_object* v___x_2355_; lean_object* v___f_2356_; uint8_t v___x_2357_; 
v___x_2330_ = lean_box(0);
v___x_2338_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2354_ = lean_unsigned_to_nat(0u);
v___x_2355_ = lean_box(v___x_2318_);
lean_inc(v___x_2307_);
v___f_2356_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2356_, 0, v___x_2354_);
lean_closure_set(v___f_2356_, 1, v___x_2307_);
lean_closure_set(v___f_2356_, 2, v___x_2355_);
v___x_2357_ = lean_nat_dec_eq(v___x_2307_, v___x_2354_);
if (lean_obj_tag(v_projInfo_x3f_2306_) == 1)
{
lean_object* v_val_2358_; lean_object* v_numParams_2359_; uint8_t v___x_2360_; 
v_val_2358_ = lean_ctor_get(v_projInfo_x3f_2306_, 0);
v_numParams_2359_ = lean_ctor_get(v_val_2358_, 1);
v___x_2360_ = lean_nat_dec_eq(v_numParams_2359_, v_a_2320_);
if (v___x_2360_ == 0)
{
lean_object* v___x_2361_; 
v___x_2361_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2326_, v___f_2356_, v___x_2357_, v___x_2357_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
v___y_2340_ = v___x_2361_;
goto v___jp_2339_;
}
else
{
lean_object* v___x_2362_; 
lean_dec_ref(v___f_2356_);
lean_dec(v___x_2307_);
v___x_2362_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2305_, v_argVars_2308_, v_a_2326_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
if (lean_obj_tag(v___x_2362_) == 0)
{
lean_dec_ref_known(v___x_2362_, 1);
goto v___jp_2331_;
}
else
{
lean_object* v_a_2363_; lean_object* v___x_2365_; uint8_t v_isShared_2366_; uint8_t v_isSharedCheck_2370_; 
lean_del_object(v___x_2328_);
v_a_2363_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2370_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2365_ = v___x_2362_;
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
else
{
lean_inc(v_a_2363_);
lean_dec(v___x_2362_);
v___x_2365_ = lean_box(0);
v_isShared_2366_ = v_isSharedCheck_2370_;
goto v_resetjp_2364_;
}
v_resetjp_2364_:
{
lean_object* v___x_2368_; 
if (v_isShared_2366_ == 0)
{
v___x_2368_ = v___x_2365_;
goto v_reusejp_2367_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_a_2363_);
v___x_2368_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2367_;
}
v_reusejp_2367_:
{
return v___x_2368_;
}
}
}
}
}
else
{
lean_object* v___x_2371_; 
v___x_2371_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2326_, v___f_2356_, v___x_2357_, v___x_2357_, v___y_2313_, v___y_2314_, v___y_2315_, v___y_2316_);
v___y_2340_ = v___x_2371_;
goto v___jp_2339_;
}
v___jp_2331_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; lean_object* v___x_2336_; 
lean_inc(v_a_2320_);
v___x_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2332_, 0, v_a_2320_);
v___x_2333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2333_, 0, v___x_2332_);
v___x_2334_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2334_, 0, v___x_2333_);
lean_ctor_set(v___x_2334_, 1, v___x_2330_);
if (v_isShared_2329_ == 0)
{
lean_ctor_set(v___x_2328_, 0, v___x_2334_);
v___x_2336_ = v___x_2328_;
goto v_reusejp_2335_;
}
else
{
lean_object* v_reuseFailAlloc_2337_; 
v_reuseFailAlloc_2337_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2337_, 0, v___x_2334_);
v___x_2336_ = v_reuseFailAlloc_2337_;
goto v_reusejp_2335_;
}
v_reusejp_2335_:
{
return v___x_2336_;
}
}
v___jp_2339_:
{
if (lean_obj_tag(v___y_2340_) == 0)
{
lean_object* v_a_2341_; uint8_t v___x_2342_; 
v_a_2341_ = lean_ctor_get(v___y_2340_, 0);
lean_inc(v_a_2341_);
lean_dec_ref_known(v___y_2340_, 1);
v___x_2342_ = lean_unbox(v_a_2341_);
lean_dec(v_a_2341_);
if (v___x_2342_ == 0)
{
size_t v___x_2343_; size_t v___x_2344_; 
lean_del_object(v___x_2328_);
v___x_2343_ = ((size_t)1ULL);
v___x_2344_ = lean_usize_add(v_i_2311_, v___x_2343_);
v_i_2311_ = v___x_2344_;
v_b_2312_ = v___x_2338_;
goto _start;
}
else
{
lean_dec(v___x_2307_);
goto v___jp_2331_;
}
}
else
{
lean_object* v_a_2346_; lean_object* v___x_2348_; uint8_t v_isShared_2349_; uint8_t v_isSharedCheck_2353_; 
lean_del_object(v___x_2328_);
lean_dec(v___x_2307_);
v_a_2346_ = lean_ctor_get(v___y_2340_, 0);
v_isSharedCheck_2353_ = !lean_is_exclusive(v___y_2340_);
if (v_isSharedCheck_2353_ == 0)
{
v___x_2348_ = v___y_2340_;
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
else
{
lean_inc(v_a_2346_);
lean_dec(v___y_2340_);
v___x_2348_ = lean_box(0);
v_isShared_2349_ = v_isSharedCheck_2353_;
goto v_resetjp_2347_;
}
v_resetjp_2347_:
{
lean_object* v___x_2351_; 
if (v_isShared_2349_ == 0)
{
v___x_2351_ = v___x_2348_;
goto v_reusejp_2350_;
}
else
{
lean_object* v_reuseFailAlloc_2352_; 
v_reuseFailAlloc_2352_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2352_, 0, v_a_2346_);
v___x_2351_ = v_reuseFailAlloc_2352_;
goto v_reusejp_2350_;
}
v_reusejp_2350_:
{
return v___x_2351_;
}
}
}
}
}
}
else
{
lean_object* v_a_2373_; lean_object* v___x_2375_; uint8_t v_isShared_2376_; uint8_t v_isSharedCheck_2380_; 
lean_dec(v___x_2307_);
v_a_2373_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2375_ = v___x_2325_;
v_isShared_2376_ = v_isSharedCheck_2380_;
goto v_resetjp_2374_;
}
else
{
lean_inc(v_a_2373_);
lean_dec(v___x_2325_);
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
else
{
lean_object* v_a_2381_; lean_object* v___x_2383_; uint8_t v_isShared_2384_; uint8_t v_isSharedCheck_2388_; 
lean_dec(v___x_2307_);
v_a_2381_ = lean_ctor_get(v___x_2323_, 0);
v_isSharedCheck_2388_ = !lean_is_exclusive(v___x_2323_);
if (v_isSharedCheck_2388_ == 0)
{
v___x_2383_ = v___x_2323_;
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
else
{
lean_inc(v_a_2381_);
lean_dec(v___x_2323_);
v___x_2383_ = lean_box(0);
v_isShared_2384_ = v_isSharedCheck_2388_;
goto v_resetjp_2382_;
}
v_resetjp_2382_:
{
lean_object* v___x_2386_; 
if (v_isShared_2384_ == 0)
{
v___x_2386_ = v___x_2383_;
goto v_reusejp_2385_;
}
else
{
lean_object* v_reuseFailAlloc_2387_; 
v_reuseFailAlloc_2387_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2387_, 0, v_a_2381_);
v___x_2386_ = v_reuseFailAlloc_2387_;
goto v_reusejp_2385_;
}
v_reusejp_2385_:
{
return v___x_2386_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2389_, lean_object* v_projInfo_x3f_2390_, lean_object* v___x_2391_, lean_object* v_argVars_2392_, lean_object* v_as_2393_, lean_object* v_sz_2394_, lean_object* v_i_2395_, lean_object* v_b_2396_, lean_object* v___y_2397_, lean_object* v___y_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_){
_start:
{
size_t v_sz_boxed_2402_; size_t v_i_boxed_2403_; lean_object* v_res_2404_; 
v_sz_boxed_2402_ = lean_unbox_usize(v_sz_2394_);
lean_dec(v_sz_2394_);
v_i_boxed_2403_ = lean_unbox_usize(v_i_2395_);
lean_dec(v_i_2395_);
v_res_2404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2389_, v_projInfo_x3f_2390_, v___x_2391_, v_argVars_2392_, v_as_2393_, v_sz_boxed_2402_, v_i_boxed_2403_, v_b_2396_, v___y_2397_, v___y_2398_, v___y_2399_, v___y_2400_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec(v___y_2398_);
lean_dec_ref(v___y_2397_);
lean_dec_ref(v_as_2393_);
lean_dec_ref(v_argVars_2392_);
lean_dec(v_projInfo_x3f_2390_);
lean_dec_ref(v_fst_2389_);
return v_res_2404_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2405_, lean_object* v___y_2406_, lean_object* v___y_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_){
_start:
{
lean_object* v___x_2411_; lean_object* v_env_2412_; lean_object* v___x_2413_; lean_object* v_mctx_2414_; lean_object* v_lctx_2415_; lean_object* v_options_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; lean_object* v___x_2419_; 
v___x_2411_ = lean_st_ref_get(v___y_2409_);
v_env_2412_ = lean_ctor_get(v___x_2411_, 0);
lean_inc_ref(v_env_2412_);
lean_dec(v___x_2411_);
v___x_2413_ = lean_st_ref_get(v___y_2407_);
v_mctx_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc_ref(v_mctx_2414_);
lean_dec(v___x_2413_);
v_lctx_2415_ = lean_ctor_get(v___y_2406_, 2);
v_options_2416_ = lean_ctor_get(v___y_2408_, 2);
lean_inc_ref(v_options_2416_);
lean_inc_ref(v_lctx_2415_);
v___x_2417_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2417_, 0, v_env_2412_);
lean_ctor_set(v___x_2417_, 1, v_mctx_2414_);
lean_ctor_set(v___x_2417_, 2, v_lctx_2415_);
lean_ctor_set(v___x_2417_, 3, v_options_2416_);
v___x_2418_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2418_, 0, v___x_2417_);
lean_ctor_set(v___x_2418_, 1, v_msgData_2405_);
v___x_2419_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2419_, 0, v___x_2418_);
return v___x_2419_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2420_, lean_object* v___y_2421_, lean_object* v___y_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_){
_start:
{
lean_object* v_res_2426_; 
v_res_2426_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2420_, v___y_2421_, v___y_2422_, v___y_2423_, v___y_2424_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec(v___y_2422_);
lean_dec_ref(v___y_2421_);
return v_res_2426_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2427_, lean_object* v___y_2428_, lean_object* v___y_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_){
_start:
{
lean_object* v_ref_2433_; lean_object* v___x_2434_; lean_object* v_a_2435_; lean_object* v___x_2437_; uint8_t v_isShared_2438_; uint8_t v_isSharedCheck_2443_; 
v_ref_2433_ = lean_ctor_get(v___y_2430_, 5);
v___x_2434_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2427_, v___y_2428_, v___y_2429_, v___y_2430_, v___y_2431_);
v_a_2435_ = lean_ctor_get(v___x_2434_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2434_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2437_ = v___x_2434_;
v_isShared_2438_ = v_isSharedCheck_2443_;
goto v_resetjp_2436_;
}
else
{
lean_inc(v_a_2435_);
lean_dec(v___x_2434_);
v___x_2437_ = lean_box(0);
v_isShared_2438_ = v_isSharedCheck_2443_;
goto v_resetjp_2436_;
}
v_resetjp_2436_:
{
lean_object* v___x_2439_; lean_object* v___x_2441_; 
lean_inc(v_ref_2433_);
v___x_2439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2439_, 0, v_ref_2433_);
lean_ctor_set(v___x_2439_, 1, v_a_2435_);
if (v_isShared_2438_ == 0)
{
lean_ctor_set_tag(v___x_2437_, 1);
lean_ctor_set(v___x_2437_, 0, v___x_2439_);
v___x_2441_ = v___x_2437_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v___x_2439_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2444_, lean_object* v___y_2445_, lean_object* v___y_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_){
_start:
{
lean_object* v_res_2450_; 
v_res_2450_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2444_, v___y_2445_, v___y_2446_, v___y_2447_, v___y_2448_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
lean_dec(v___y_2446_);
lean_dec_ref(v___y_2445_);
return v_res_2450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2451_, size_t v_sz_2452_, size_t v_i_2453_, lean_object* v_bs_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_){
_start:
{
uint8_t v___x_2460_; 
v___x_2460_ = lean_usize_dec_lt(v_i_2453_, v_sz_2452_);
if (v___x_2460_ == 0)
{
lean_object* v___x_2461_; 
v___x_2461_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2461_, 0, v_bs_2454_);
return v___x_2461_;
}
else
{
lean_object* v_v_2462_; lean_object* v___x_2463_; lean_object* v___x_2464_; lean_object* v___x_2465_; 
v_v_2462_ = lean_array_uget_borrowed(v_bs_2454_, v_i_2453_);
v___x_2463_ = l_Lean_instInhabitedExpr;
v___x_2464_ = lean_array_get_borrowed(v___x_2463_, v_fst_2451_, v_v_2462_);
lean_inc(v___y_2458_);
lean_inc_ref(v___y_2457_);
lean_inc(v___y_2456_);
lean_inc_ref(v___y_2455_);
lean_inc(v___x_2464_);
v___x_2465_ = lean_infer_type(v___x_2464_, v___y_2455_, v___y_2456_, v___y_2457_, v___y_2458_);
if (lean_obj_tag(v___x_2465_) == 0)
{
lean_object* v_a_2466_; lean_object* v___x_2467_; 
v_a_2466_ = lean_ctor_get(v___x_2465_, 0);
lean_inc(v_a_2466_);
lean_dec_ref_known(v___x_2465_, 1);
v___x_2467_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2466_, v___y_2456_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2469_; lean_object* v_bs_x27_2470_; lean_object* v___x_2471_; lean_object* v___x_2472_; size_t v___x_2473_; size_t v___x_2474_; lean_object* v___x_2475_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___x_2467_, 1);
v___x_2469_ = lean_unsigned_to_nat(0u);
v_bs_x27_2470_ = lean_array_uset(v_bs_2454_, v_i_2453_, v___x_2469_);
v___x_2471_ = l_Lean_Expr_setPPExplicit(v_a_2468_, v___x_2460_);
v___x_2472_ = l_Lean_indentExpr(v___x_2471_);
v___x_2473_ = ((size_t)1ULL);
v___x_2474_ = lean_usize_add(v_i_2453_, v___x_2473_);
v___x_2475_ = lean_array_uset(v_bs_x27_2470_, v_i_2453_, v___x_2472_);
v_i_2453_ = v___x_2474_;
v_bs_2454_ = v___x_2475_;
goto _start;
}
else
{
lean_object* v_a_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
lean_dec_ref(v_bs_2454_);
v_a_2477_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2467_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_a_2477_);
lean_dec(v___x_2467_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_a_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
else
{
lean_object* v_a_2485_; lean_object* v___x_2487_; uint8_t v_isShared_2488_; uint8_t v_isSharedCheck_2492_; 
lean_dec_ref(v_bs_2454_);
v_a_2485_ = lean_ctor_get(v___x_2465_, 0);
v_isSharedCheck_2492_ = !lean_is_exclusive(v___x_2465_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2487_ = v___x_2465_;
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
else
{
lean_inc(v_a_2485_);
lean_dec(v___x_2465_);
v___x_2487_ = lean_box(0);
v_isShared_2488_ = v_isSharedCheck_2492_;
goto v_resetjp_2486_;
}
v_resetjp_2486_:
{
lean_object* v___x_2490_; 
if (v_isShared_2488_ == 0)
{
v___x_2490_ = v___x_2487_;
goto v_reusejp_2489_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_a_2485_);
v___x_2490_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2489_;
}
v_reusejp_2489_:
{
return v___x_2490_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2493_, lean_object* v_sz_2494_, lean_object* v_i_2495_, lean_object* v_bs_2496_, lean_object* v___y_2497_, lean_object* v___y_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_){
_start:
{
size_t v_sz_boxed_2502_; size_t v_i_boxed_2503_; lean_object* v_res_2504_; 
v_sz_boxed_2502_ = lean_unbox_usize(v_sz_2494_);
lean_dec(v_sz_2494_);
v_i_boxed_2503_ = lean_unbox_usize(v_i_2495_);
lean_dec(v_i_2495_);
v_res_2504_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2493_, v_sz_boxed_2502_, v_i_boxed_2503_, v_bs_2496_, v___y_2497_, v___y_2498_, v___y_2499_, v___y_2500_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec(v___y_2498_);
lean_dec_ref(v___y_2497_);
lean_dec_ref(v_fst_2493_);
return v_res_2504_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object* v_snd_2505_, lean_object* v___f_2506_, lean_object* v_____r_2507_, lean_object* v___y_2508_, lean_object* v___y_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_){
_start:
{
lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v___x_2513_ = lean_unsigned_to_nat(0u);
v___x_2514_ = lean_array_get_borrowed(v___x_2513_, v_snd_2505_, v___x_2513_);
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
lean_inc(v___y_2509_);
lean_inc_ref(v___y_2508_);
lean_inc(v___x_2514_);
v___x_2515_ = lean_apply_6(v___f_2506_, v___x_2514_, v___y_2508_, v___y_2509_, v___y_2510_, v___y_2511_, lean_box(0));
return v___x_2515_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object* v_snd_2516_, lean_object* v___f_2517_, lean_object* v_____r_2518_, lean_object* v___y_2519_, lean_object* v___y_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_){
_start:
{
lean_object* v_res_2524_; 
v_res_2524_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2516_, v___f_2517_, v_____r_2518_, v___y_2519_, v___y_2520_, v___y_2521_, v___y_2522_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v___y_2520_);
lean_dec_ref(v___y_2519_);
lean_dec(v_snd_2516_);
return v_res_2524_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2528_; lean_object* v___x_2529_; 
v___x_2528_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1));
v___x_2529_ = l_Lean_MessageData_ofFormat(v___x_2528_);
return v___x_2529_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2531_; lean_object* v___x_2532_; 
v___x_2531_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3));
v___x_2532_ = l_Lean_stringToMessageData(v___x_2531_);
return v___x_2532_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2534_; lean_object* v___x_2535_; 
v___x_2534_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5));
v___x_2535_ = l_Lean_stringToMessageData(v___x_2534_);
return v___x_2535_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2537_; lean_object* v___x_2538_; 
v___x_2537_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7));
v___x_2538_ = l_Lean_stringToMessageData(v___x_2537_);
return v___x_2538_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(lean_object* v_fst_2539_, lean_object* v_argVars_2540_, lean_object* v_inst_2541_, lean_object* v_a_2542_, lean_object* v_projInfo_x3f_2543_, lean_object* v_a_2544_, lean_object* v___y_2545_, lean_object* v___y_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_){
_start:
{
lean_object* v___y_2551_; lean_object* v_fst_2571_; lean_object* v_snd_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2648_; 
v_fst_2571_ = lean_ctor_get(v_a_2544_, 0);
v_snd_2572_ = lean_ctor_get(v_a_2544_, 1);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_a_2544_);
if (v_isSharedCheck_2648_ == 0)
{
v___x_2574_ = v_a_2544_;
v_isShared_2575_ = v_isSharedCheck_2648_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_snd_2572_);
lean_inc(v_fst_2571_);
lean_dec(v_a_2544_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2648_;
goto v_resetjp_2573_;
}
v___jp_2550_:
{
if (lean_obj_tag(v___y_2551_) == 0)
{
lean_object* v_a_2552_; lean_object* v___x_2554_; uint8_t v_isShared_2555_; uint8_t v_isSharedCheck_2562_; 
v_a_2552_ = lean_ctor_get(v___y_2551_, 0);
v_isSharedCheck_2562_ = !lean_is_exclusive(v___y_2551_);
if (v_isSharedCheck_2562_ == 0)
{
v___x_2554_ = v___y_2551_;
v_isShared_2555_ = v_isSharedCheck_2562_;
goto v_resetjp_2553_;
}
else
{
lean_inc(v_a_2552_);
lean_dec(v___y_2551_);
v___x_2554_ = lean_box(0);
v_isShared_2555_ = v_isSharedCheck_2562_;
goto v_resetjp_2553_;
}
v_resetjp_2553_:
{
if (lean_obj_tag(v_a_2552_) == 0)
{
lean_object* v_a_2556_; lean_object* v___x_2558_; 
lean_dec_ref(v_a_2542_);
lean_dec_ref(v_inst_2541_);
lean_dec_ref(v_argVars_2540_);
lean_dec_ref(v_fst_2539_);
v_a_2556_ = lean_ctor_get(v_a_2552_, 0);
lean_inc(v_a_2556_);
lean_dec_ref_known(v_a_2552_, 1);
if (v_isShared_2555_ == 0)
{
lean_ctor_set(v___x_2554_, 0, v_a_2556_);
v___x_2558_ = v___x_2554_;
goto v_reusejp_2557_;
}
else
{
lean_object* v_reuseFailAlloc_2559_; 
v_reuseFailAlloc_2559_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2559_, 0, v_a_2556_);
v___x_2558_ = v_reuseFailAlloc_2559_;
goto v_reusejp_2557_;
}
v_reusejp_2557_:
{
return v___x_2558_;
}
}
else
{
lean_object* v_a_2560_; 
lean_del_object(v___x_2554_);
v_a_2560_ = lean_ctor_get(v_a_2552_, 0);
lean_inc(v_a_2560_);
lean_dec_ref_known(v_a_2552_, 1);
v_a_2544_ = v_a_2560_;
goto _start;
}
}
}
else
{
lean_object* v_a_2563_; lean_object* v___x_2565_; uint8_t v_isShared_2566_; uint8_t v_isSharedCheck_2570_; 
lean_dec_ref(v_a_2542_);
lean_dec_ref(v_inst_2541_);
lean_dec_ref(v_argVars_2540_);
lean_dec_ref(v_fst_2539_);
v_a_2563_ = lean_ctor_get(v___y_2551_, 0);
v_isSharedCheck_2570_ = !lean_is_exclusive(v___y_2551_);
if (v_isSharedCheck_2570_ == 0)
{
v___x_2565_ = v___y_2551_;
v_isShared_2566_ = v_isSharedCheck_2570_;
goto v_resetjp_2564_;
}
else
{
lean_inc(v_a_2563_);
lean_dec(v___y_2551_);
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
}
v_resetjp_2573_:
{
lean_object* v___x_2576_; lean_object* v___x_2577_; uint8_t v___x_2578_; 
v___x_2576_ = lean_array_get_size(v_snd_2572_);
v___x_2577_ = lean_unsigned_to_nat(0u);
v___x_2578_ = lean_nat_dec_eq(v___x_2576_, v___x_2577_);
if (v___x_2578_ == 0)
{
lean_object* v___x_2579_; lean_object* v___x_2580_; size_t v_sz_2581_; size_t v___x_2582_; lean_object* v___x_2583_; 
lean_del_object(v___x_2574_);
v___x_2579_ = lean_box(0);
v___x_2580_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2581_ = lean_array_size(v_snd_2572_);
v___x_2582_ = ((size_t)0ULL);
v___x_2583_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2539_, v_projInfo_x3f_2543_, v___x_2576_, v_argVars_2540_, v_snd_2572_, v_sz_2581_, v___x_2582_, v___x_2580_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2583_) == 0)
{
lean_object* v_a_2584_; lean_object* v_fst_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2634_; 
v_a_2584_ = lean_ctor_get(v___x_2583_, 0);
lean_inc(v_a_2584_);
lean_dec_ref_known(v___x_2583_, 1);
v_fst_2585_ = lean_ctor_get(v_a_2584_, 0);
v_isSharedCheck_2634_ = !lean_is_exclusive(v_a_2584_);
if (v_isSharedCheck_2634_ == 0)
{
lean_object* v_unused_2635_; 
v_unused_2635_ = lean_ctor_get(v_a_2584_, 1);
lean_dec(v_unused_2635_);
v___x_2587_ = v_a_2584_;
v_isShared_2588_ = v_isSharedCheck_2634_;
goto v_resetjp_2586_;
}
else
{
lean_inc(v_fst_2585_);
lean_dec(v_a_2584_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2634_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___f_2589_; 
lean_inc(v_snd_2572_);
lean_inc_ref(v_argVars_2540_);
lean_inc_ref(v_fst_2539_);
lean_inc(v_fst_2571_);
v___f_2589_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2589_, 0, v_fst_2571_);
lean_closure_set(v___f_2589_, 1, v_fst_2539_);
lean_closure_set(v___f_2589_, 2, v_argVars_2540_);
lean_closure_set(v___f_2589_, 3, v_snd_2572_);
if (lean_obj_tag(v_fst_2585_) == 0)
{
lean_dec(v_fst_2571_);
goto v___jp_2590_;
}
else
{
lean_object* v_val_2631_; 
v_val_2631_ = lean_ctor_get(v_fst_2585_, 0);
lean_inc(v_val_2631_);
lean_dec_ref_known(v_fst_2585_, 1);
if (lean_obj_tag(v_val_2631_) == 0)
{
lean_dec(v_fst_2571_);
goto v___jp_2590_;
}
else
{
lean_object* v_val_2632_; lean_object* v___x_2633_; 
lean_dec_ref(v___f_2589_);
lean_del_object(v___x_2587_);
v_val_2632_ = lean_ctor_get(v_val_2631_, 0);
lean_inc(v_val_2632_);
lean_dec_ref_known(v_val_2631_, 1);
v___x_2633_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2571_, v_fst_2539_, v_argVars_2540_, v_snd_2572_, v_val_2632_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v_snd_2572_);
v___y_2551_ = v___x_2633_;
goto v___jp_2550_;
}
}
v___jp_2590_:
{
lean_object* v_options_2591_; lean_object* v___x_2592_; uint8_t v___x_2593_; 
v_options_2591_ = lean_ctor_get(v___y_2547_, 2);
v___x_2592_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2593_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2591_, v___x_2592_);
if (v___x_2593_ == 0)
{
lean_object* v___x_2594_; 
lean_del_object(v___x_2587_);
v___x_2594_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2572_, v___f_2589_, v___x_2579_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v_snd_2572_);
v___y_2551_ = v___x_2594_;
goto v___jp_2550_;
}
else
{
lean_object* v___x_2595_; 
lean_inc(v_snd_2572_);
v___x_2595_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2539_, v_sz_2581_, v___x_2582_, v_snd_2572_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2595_) == 0)
{
lean_object* v_a_2596_; lean_object* v___x_2597_; lean_object* v___x_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2603_; 
v_a_2596_ = lean_ctor_get(v___x_2595_, 0);
lean_inc(v_a_2596_);
lean_dec_ref_known(v___x_2595_, 1);
v___x_2597_ = lean_array_to_list(v_a_2596_);
v___x_2598_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2599_ = l_Lean_MessageData_joinSep(v___x_2597_, v___x_2598_);
v___x_2600_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4);
lean_inc_ref(v_inst_2541_);
v___x_2601_ = l_Lean_MessageData_ofExpr(v_inst_2541_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set_tag(v___x_2587_, 7);
lean_ctor_set(v___x_2587_, 1, v___x_2601_);
lean_ctor_set(v___x_2587_, 0, v___x_2600_);
v___x_2603_ = v___x_2587_;
goto v_reusejp_2602_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v___x_2600_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v___x_2601_);
v___x_2603_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2602_;
}
v_reusejp_2602_:
{
lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; 
v___x_2604_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6);
v___x_2605_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2605_, 0, v___x_2603_);
lean_ctor_set(v___x_2605_, 1, v___x_2604_);
lean_inc_ref(v_a_2542_);
v___x_2606_ = l_Lean_indentExpr(v_a_2542_);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
v___x_2608_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8);
v___x_2609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2607_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2610_, 0, v___x_2609_);
lean_ctor_set(v___x_2610_, 1, v___x_2599_);
v___x_2611_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2610_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
if (lean_obj_tag(v___x_2611_) == 0)
{
lean_object* v_a_2612_; lean_object* v___x_2613_; 
v_a_2612_ = lean_ctor_get(v___x_2611_, 0);
lean_inc(v_a_2612_);
lean_dec_ref_known(v___x_2611_, 1);
v___x_2613_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2572_, v___f_2589_, v_a_2612_, v___y_2545_, v___y_2546_, v___y_2547_, v___y_2548_);
lean_dec(v_snd_2572_);
v___y_2551_ = v___x_2613_;
goto v___jp_2550_;
}
else
{
lean_object* v_a_2614_; lean_object* v___x_2616_; uint8_t v_isShared_2617_; uint8_t v_isSharedCheck_2621_; 
lean_dec_ref(v___f_2589_);
lean_dec(v_snd_2572_);
lean_dec_ref(v_a_2542_);
lean_dec_ref(v_inst_2541_);
lean_dec_ref(v_argVars_2540_);
lean_dec_ref(v_fst_2539_);
v_a_2614_ = lean_ctor_get(v___x_2611_, 0);
v_isSharedCheck_2621_ = !lean_is_exclusive(v___x_2611_);
if (v_isSharedCheck_2621_ == 0)
{
v___x_2616_ = v___x_2611_;
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
else
{
lean_inc(v_a_2614_);
lean_dec(v___x_2611_);
v___x_2616_ = lean_box(0);
v_isShared_2617_ = v_isSharedCheck_2621_;
goto v_resetjp_2615_;
}
v_resetjp_2615_:
{
lean_object* v___x_2619_; 
if (v_isShared_2617_ == 0)
{
v___x_2619_ = v___x_2616_;
goto v_reusejp_2618_;
}
else
{
lean_object* v_reuseFailAlloc_2620_; 
v_reuseFailAlloc_2620_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2620_, 0, v_a_2614_);
v___x_2619_ = v_reuseFailAlloc_2620_;
goto v_reusejp_2618_;
}
v_reusejp_2618_:
{
return v___x_2619_;
}
}
}
}
}
else
{
lean_object* v_a_2623_; lean_object* v___x_2625_; uint8_t v_isShared_2626_; uint8_t v_isSharedCheck_2630_; 
lean_dec_ref(v___f_2589_);
lean_del_object(v___x_2587_);
lean_dec(v_snd_2572_);
lean_dec_ref(v_a_2542_);
lean_dec_ref(v_inst_2541_);
lean_dec_ref(v_argVars_2540_);
lean_dec_ref(v_fst_2539_);
v_a_2623_ = lean_ctor_get(v___x_2595_, 0);
v_isSharedCheck_2630_ = !lean_is_exclusive(v___x_2595_);
if (v_isSharedCheck_2630_ == 0)
{
v___x_2625_ = v___x_2595_;
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
else
{
lean_inc(v_a_2623_);
lean_dec(v___x_2595_);
v___x_2625_ = lean_box(0);
v_isShared_2626_ = v_isSharedCheck_2630_;
goto v_resetjp_2624_;
}
v_resetjp_2624_:
{
lean_object* v___x_2628_; 
if (v_isShared_2626_ == 0)
{
v___x_2628_ = v___x_2625_;
goto v_reusejp_2627_;
}
else
{
lean_object* v_reuseFailAlloc_2629_; 
v_reuseFailAlloc_2629_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2629_, 0, v_a_2623_);
v___x_2628_ = v_reuseFailAlloc_2629_;
goto v_reusejp_2627_;
}
v_reusejp_2627_:
{
return v___x_2628_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2636_; lean_object* v___x_2638_; uint8_t v_isShared_2639_; uint8_t v_isSharedCheck_2643_; 
lean_dec(v_snd_2572_);
lean_dec(v_fst_2571_);
lean_dec_ref(v_a_2542_);
lean_dec_ref(v_inst_2541_);
lean_dec_ref(v_argVars_2540_);
lean_dec_ref(v_fst_2539_);
v_a_2636_ = lean_ctor_get(v___x_2583_, 0);
v_isSharedCheck_2643_ = !lean_is_exclusive(v___x_2583_);
if (v_isSharedCheck_2643_ == 0)
{
v___x_2638_ = v___x_2583_;
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
else
{
lean_inc(v_a_2636_);
lean_dec(v___x_2583_);
v___x_2638_ = lean_box(0);
v_isShared_2639_ = v_isSharedCheck_2643_;
goto v_resetjp_2637_;
}
v_resetjp_2637_:
{
lean_object* v___x_2641_; 
if (v_isShared_2639_ == 0)
{
v___x_2641_ = v___x_2638_;
goto v_reusejp_2640_;
}
else
{
lean_object* v_reuseFailAlloc_2642_; 
v_reuseFailAlloc_2642_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2642_, 0, v_a_2636_);
v___x_2641_ = v_reuseFailAlloc_2642_;
goto v_reusejp_2640_;
}
v_reusejp_2640_:
{
return v___x_2641_;
}
}
}
}
else
{
lean_object* v___x_2645_; 
lean_dec_ref(v_a_2542_);
lean_dec_ref(v_inst_2541_);
lean_dec_ref(v_argVars_2540_);
lean_dec_ref(v_fst_2539_);
if (v_isShared_2575_ == 0)
{
v___x_2645_ = v___x_2574_;
goto v_reusejp_2644_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_fst_2571_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_snd_2572_);
v___x_2645_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2644_;
}
v_reusejp_2644_:
{
lean_object* v___x_2646_; 
v___x_2646_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2646_, 0, v___x_2645_);
return v___x_2646_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___boxed(lean_object* v_fst_2649_, lean_object* v_argVars_2650_, lean_object* v_inst_2651_, lean_object* v_a_2652_, lean_object* v_projInfo_x3f_2653_, lean_object* v_a_2654_, lean_object* v___y_2655_, lean_object* v___y_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_){
_start:
{
lean_object* v_res_2660_; 
v_res_2660_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2649_, v_argVars_2650_, v_inst_2651_, v_a_2652_, v_projInfo_x3f_2653_, v_a_2654_, v___y_2655_, v___y_2656_, v___y_2657_, v___y_2658_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v___y_2656_);
lean_dec_ref(v___y_2655_);
lean_dec(v_projInfo_x3f_2653_);
return v_res_2660_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2661_, lean_object* v_a_2662_, lean_object* v_a_2663_){
_start:
{
if (lean_obj_tag(v_a_2662_) == 0)
{
lean_object* v___x_2664_; 
v___x_2664_ = l_List_reverse___redArg(v_a_2663_);
return v___x_2664_;
}
else
{
lean_object* v_head_2665_; lean_object* v_tail_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2681_; 
v_head_2665_ = lean_ctor_get(v_a_2662_, 0);
v_tail_2666_ = lean_ctor_get(v_a_2662_, 1);
v_isSharedCheck_2681_ = !lean_is_exclusive(v_a_2662_);
if (v_isSharedCheck_2681_ == 0)
{
v___x_2668_ = v_a_2662_;
v_isShared_2669_ = v_isSharedCheck_2681_;
goto v_resetjp_2667_;
}
else
{
lean_inc(v_tail_2666_);
lean_inc(v_head_2665_);
lean_dec(v_a_2662_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2681_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
uint8_t v___x_2670_; lean_object* v___x_2671_; lean_object* v___x_2672_; uint8_t v___x_2673_; uint8_t v___x_2674_; uint8_t v___x_2675_; 
v___x_2670_ = 0;
v___x_2671_ = lean_box(v___x_2670_);
v___x_2672_ = lean_array_get(v___x_2671_, v_fst_2661_, v_head_2665_);
lean_dec(v___x_2671_);
v___x_2673_ = 3;
v___x_2674_ = lean_unbox(v___x_2672_);
lean_dec(v___x_2672_);
v___x_2675_ = l_Lean_instBEqBinderInfo_beq(v___x_2674_, v___x_2673_);
if (v___x_2675_ == 0)
{
lean_del_object(v___x_2668_);
lean_dec(v_head_2665_);
v_a_2662_ = v_tail_2666_;
goto _start;
}
else
{
lean_object* v___x_2678_; 
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v_a_2663_);
v___x_2678_ = v___x_2668_;
goto v_reusejp_2677_;
}
else
{
lean_object* v_reuseFailAlloc_2680_; 
v_reuseFailAlloc_2680_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2680_, 0, v_head_2665_);
lean_ctor_set(v_reuseFailAlloc_2680_, 1, v_a_2663_);
v___x_2678_ = v_reuseFailAlloc_2680_;
goto v_reusejp_2677_;
}
v_reusejp_2677_:
{
v_a_2662_ = v_tail_2666_;
v_a_2663_ = v___x_2678_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2682_, lean_object* v_a_2683_, lean_object* v_a_2684_){
_start:
{
lean_object* v_res_2685_; 
v_res_2685_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2682_, v_a_2683_, v_a_2684_);
lean_dec_ref(v_fst_2682_);
return v_res_2685_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2686_, size_t v_sz_2687_, size_t v_i_2688_, lean_object* v_bs_2689_, lean_object* v___y_2690_, lean_object* v___y_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_){
_start:
{
uint8_t v___x_2695_; 
v___x_2695_ = lean_usize_dec_lt(v_i_2688_, v_sz_2687_);
if (v___x_2695_ == 0)
{
lean_object* v___x_2696_; 
v___x_2696_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2696_, 0, v_bs_2689_);
return v___x_2696_;
}
else
{
lean_object* v_v_2697_; lean_object* v___x_2698_; lean_object* v___x_2699_; lean_object* v___x_2700_; 
v_v_2697_ = lean_array_uget_borrowed(v_bs_2689_, v_i_2688_);
v___x_2698_ = l_Lean_instInhabitedExpr;
v___x_2699_ = lean_array_get_borrowed(v___x_2698_, v_argVars_2686_, v_v_2697_);
lean_inc(v___y_2693_);
lean_inc_ref(v___y_2692_);
lean_inc(v___y_2691_);
lean_inc_ref(v___y_2690_);
lean_inc(v___x_2699_);
v___x_2700_ = lean_infer_type(v___x_2699_, v___y_2690_, v___y_2691_, v___y_2692_, v___y_2693_);
if (lean_obj_tag(v___x_2700_) == 0)
{
lean_object* v_a_2701_; lean_object* v___x_2702_; lean_object* v_bs_x27_2703_; lean_object* v___x_2704_; size_t v___x_2705_; size_t v___x_2706_; lean_object* v___x_2707_; 
v_a_2701_ = lean_ctor_get(v___x_2700_, 0);
lean_inc(v_a_2701_);
lean_dec_ref_known(v___x_2700_, 1);
v___x_2702_ = lean_unsigned_to_nat(0u);
v_bs_x27_2703_ = lean_array_uset(v_bs_2689_, v_i_2688_, v___x_2702_);
v___x_2704_ = l_Lean_indentExpr(v_a_2701_);
v___x_2705_ = ((size_t)1ULL);
v___x_2706_ = lean_usize_add(v_i_2688_, v___x_2705_);
v___x_2707_ = lean_array_uset(v_bs_x27_2703_, v_i_2688_, v___x_2704_);
v_i_2688_ = v___x_2706_;
v_bs_2689_ = v___x_2707_;
goto _start;
}
else
{
lean_object* v_a_2709_; lean_object* v___x_2711_; uint8_t v_isShared_2712_; uint8_t v_isSharedCheck_2716_; 
lean_dec_ref(v_bs_2689_);
v_a_2709_ = lean_ctor_get(v___x_2700_, 0);
v_isSharedCheck_2716_ = !lean_is_exclusive(v___x_2700_);
if (v_isSharedCheck_2716_ == 0)
{
v___x_2711_ = v___x_2700_;
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
else
{
lean_inc(v_a_2709_);
lean_dec(v___x_2700_);
v___x_2711_ = lean_box(0);
v_isShared_2712_ = v_isSharedCheck_2716_;
goto v_resetjp_2710_;
}
v_resetjp_2710_:
{
lean_object* v___x_2714_; 
if (v_isShared_2712_ == 0)
{
v___x_2714_ = v___x_2711_;
goto v_reusejp_2713_;
}
else
{
lean_object* v_reuseFailAlloc_2715_; 
v_reuseFailAlloc_2715_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2715_, 0, v_a_2709_);
v___x_2714_ = v_reuseFailAlloc_2715_;
goto v_reusejp_2713_;
}
v_reusejp_2713_:
{
return v___x_2714_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2717_, lean_object* v_sz_2718_, lean_object* v_i_2719_, lean_object* v_bs_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_){
_start:
{
size_t v_sz_boxed_2726_; size_t v_i_boxed_2727_; lean_object* v_res_2728_; 
v_sz_boxed_2726_ = lean_unbox_usize(v_sz_2718_);
lean_dec(v_sz_2718_);
v_i_boxed_2727_ = lean_unbox_usize(v_i_2719_);
lean_dec(v_i_2719_);
v_res_2728_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2717_, v_sz_boxed_2726_, v_i_boxed_2727_, v_bs_2720_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec(v___y_2722_);
lean_dec_ref(v___y_2721_);
lean_dec_ref(v_argVars_2717_);
return v_res_2728_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2729_, lean_object* v_a_2730_){
_start:
{
if (lean_obj_tag(v_a_2729_) == 0)
{
lean_object* v___x_2731_; 
v___x_2731_ = l_List_reverse___redArg(v_a_2730_);
return v___x_2731_;
}
else
{
lean_object* v_head_2732_; lean_object* v_tail_2733_; lean_object* v___x_2735_; uint8_t v_isShared_2736_; uint8_t v_isSharedCheck_2744_; 
v_head_2732_ = lean_ctor_get(v_a_2729_, 0);
v_tail_2733_ = lean_ctor_get(v_a_2729_, 1);
v_isSharedCheck_2744_ = !lean_is_exclusive(v_a_2729_);
if (v_isSharedCheck_2744_ == 0)
{
v___x_2735_ = v_a_2729_;
v_isShared_2736_ = v_isSharedCheck_2744_;
goto v_resetjp_2734_;
}
else
{
lean_inc(v_tail_2733_);
lean_inc(v_head_2732_);
lean_dec(v_a_2729_);
v___x_2735_ = lean_box(0);
v_isShared_2736_ = v_isSharedCheck_2744_;
goto v_resetjp_2734_;
}
v_resetjp_2734_:
{
lean_object* v___x_2737_; lean_object* v___x_2738_; lean_object* v___x_2739_; lean_object* v___x_2741_; 
v___x_2737_ = l_Nat_reprFast(v_head_2732_);
v___x_2738_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2738_, 0, v___x_2737_);
v___x_2739_ = l_Lean_MessageData_ofFormat(v___x_2738_);
if (v_isShared_2736_ == 0)
{
lean_ctor_set(v___x_2735_, 1, v_a_2730_);
lean_ctor_set(v___x_2735_, 0, v___x_2739_);
v___x_2741_ = v___x_2735_;
goto v_reusejp_2740_;
}
else
{
lean_object* v_reuseFailAlloc_2743_; 
v_reuseFailAlloc_2743_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2743_, 0, v___x_2739_);
lean_ctor_set(v_reuseFailAlloc_2743_, 1, v_a_2730_);
v___x_2741_ = v_reuseFailAlloc_2743_;
goto v_reusejp_2740_;
}
v_reusejp_2740_:
{
v_a_2729_ = v_tail_2733_;
v_a_2730_ = v___x_2741_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2745_; double v___x_2746_; 
v___x_2745_ = lean_unsigned_to_nat(0u);
v___x_2746_ = lean_float_of_nat(v___x_2745_);
return v___x_2746_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2749_, lean_object* v_msg_2750_, lean_object* v___y_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_){
_start:
{
lean_object* v_ref_2756_; lean_object* v___x_2757_; lean_object* v_a_2758_; lean_object* v___x_2760_; uint8_t v_isShared_2761_; uint8_t v_isSharedCheck_2802_; 
v_ref_2756_ = lean_ctor_get(v___y_2753_, 5);
v___x_2757_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2750_, v___y_2751_, v___y_2752_, v___y_2753_, v___y_2754_);
v_a_2758_ = lean_ctor_get(v___x_2757_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v___x_2757_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2760_ = v___x_2757_;
v_isShared_2761_ = v_isSharedCheck_2802_;
goto v_resetjp_2759_;
}
else
{
lean_inc(v_a_2758_);
lean_dec(v___x_2757_);
v___x_2760_ = lean_box(0);
v_isShared_2761_ = v_isSharedCheck_2802_;
goto v_resetjp_2759_;
}
v_resetjp_2759_:
{
lean_object* v___x_2762_; lean_object* v_traceState_2763_; lean_object* v_env_2764_; lean_object* v_nextMacroScope_2765_; lean_object* v_ngen_2766_; lean_object* v_auxDeclNGen_2767_; lean_object* v_cache_2768_; lean_object* v_messages_2769_; lean_object* v_infoState_2770_; lean_object* v_snapshotTasks_2771_; lean_object* v___x_2773_; uint8_t v_isShared_2774_; uint8_t v_isSharedCheck_2801_; 
v___x_2762_ = lean_st_ref_take(v___y_2754_);
v_traceState_2763_ = lean_ctor_get(v___x_2762_, 4);
v_env_2764_ = lean_ctor_get(v___x_2762_, 0);
v_nextMacroScope_2765_ = lean_ctor_get(v___x_2762_, 1);
v_ngen_2766_ = lean_ctor_get(v___x_2762_, 2);
v_auxDeclNGen_2767_ = lean_ctor_get(v___x_2762_, 3);
v_cache_2768_ = lean_ctor_get(v___x_2762_, 5);
v_messages_2769_ = lean_ctor_get(v___x_2762_, 6);
v_infoState_2770_ = lean_ctor_get(v___x_2762_, 7);
v_snapshotTasks_2771_ = lean_ctor_get(v___x_2762_, 8);
v_isSharedCheck_2801_ = !lean_is_exclusive(v___x_2762_);
if (v_isSharedCheck_2801_ == 0)
{
v___x_2773_ = v___x_2762_;
v_isShared_2774_ = v_isSharedCheck_2801_;
goto v_resetjp_2772_;
}
else
{
lean_inc(v_snapshotTasks_2771_);
lean_inc(v_infoState_2770_);
lean_inc(v_messages_2769_);
lean_inc(v_cache_2768_);
lean_inc(v_traceState_2763_);
lean_inc(v_auxDeclNGen_2767_);
lean_inc(v_ngen_2766_);
lean_inc(v_nextMacroScope_2765_);
lean_inc(v_env_2764_);
lean_dec(v___x_2762_);
v___x_2773_ = lean_box(0);
v_isShared_2774_ = v_isSharedCheck_2801_;
goto v_resetjp_2772_;
}
v_resetjp_2772_:
{
uint64_t v_tid_2775_; lean_object* v_traces_2776_; lean_object* v___x_2778_; uint8_t v_isShared_2779_; uint8_t v_isSharedCheck_2800_; 
v_tid_2775_ = lean_ctor_get_uint64(v_traceState_2763_, sizeof(void*)*1);
v_traces_2776_ = lean_ctor_get(v_traceState_2763_, 0);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_traceState_2763_);
if (v_isSharedCheck_2800_ == 0)
{
v___x_2778_ = v_traceState_2763_;
v_isShared_2779_ = v_isSharedCheck_2800_;
goto v_resetjp_2777_;
}
else
{
lean_inc(v_traces_2776_);
lean_dec(v_traceState_2763_);
v___x_2778_ = lean_box(0);
v_isShared_2779_ = v_isSharedCheck_2800_;
goto v_resetjp_2777_;
}
v_resetjp_2777_:
{
lean_object* v___x_2780_; double v___x_2781_; uint8_t v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2790_; 
v___x_2780_ = lean_box(0);
v___x_2781_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2782_ = 0;
v___x_2783_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___x_2784_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2784_, 0, v_cls_2749_);
lean_ctor_set(v___x_2784_, 1, v___x_2780_);
lean_ctor_set(v___x_2784_, 2, v___x_2783_);
lean_ctor_set_float(v___x_2784_, sizeof(void*)*3, v___x_2781_);
lean_ctor_set_float(v___x_2784_, sizeof(void*)*3 + 8, v___x_2781_);
lean_ctor_set_uint8(v___x_2784_, sizeof(void*)*3 + 16, v___x_2782_);
v___x_2785_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2786_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2786_, 0, v___x_2784_);
lean_ctor_set(v___x_2786_, 1, v_a_2758_);
lean_ctor_set(v___x_2786_, 2, v___x_2785_);
lean_inc(v_ref_2756_);
v___x_2787_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2787_, 0, v_ref_2756_);
lean_ctor_set(v___x_2787_, 1, v___x_2786_);
v___x_2788_ = l_Lean_PersistentArray_push___redArg(v_traces_2776_, v___x_2787_);
if (v_isShared_2779_ == 0)
{
lean_ctor_set(v___x_2778_, 0, v___x_2788_);
v___x_2790_ = v___x_2778_;
goto v_reusejp_2789_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2788_);
lean_ctor_set_uint64(v_reuseFailAlloc_2799_, sizeof(void*)*1, v_tid_2775_);
v___x_2790_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2789_;
}
v_reusejp_2789_:
{
lean_object* v___x_2792_; 
if (v_isShared_2774_ == 0)
{
lean_ctor_set(v___x_2773_, 4, v___x_2790_);
v___x_2792_ = v___x_2773_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2798_; 
v_reuseFailAlloc_2798_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2798_, 0, v_env_2764_);
lean_ctor_set(v_reuseFailAlloc_2798_, 1, v_nextMacroScope_2765_);
lean_ctor_set(v_reuseFailAlloc_2798_, 2, v_ngen_2766_);
lean_ctor_set(v_reuseFailAlloc_2798_, 3, v_auxDeclNGen_2767_);
lean_ctor_set(v_reuseFailAlloc_2798_, 4, v___x_2790_);
lean_ctor_set(v_reuseFailAlloc_2798_, 5, v_cache_2768_);
lean_ctor_set(v_reuseFailAlloc_2798_, 6, v_messages_2769_);
lean_ctor_set(v_reuseFailAlloc_2798_, 7, v_infoState_2770_);
lean_ctor_set(v_reuseFailAlloc_2798_, 8, v_snapshotTasks_2771_);
v___x_2792_ = v_reuseFailAlloc_2798_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2796_; 
v___x_2793_ = lean_st_ref_set(v___y_2754_, v___x_2792_);
v___x_2794_ = lean_box(0);
if (v_isShared_2761_ == 0)
{
lean_ctor_set(v___x_2760_, 0, v___x_2794_);
v___x_2796_ = v___x_2760_;
goto v_reusejp_2795_;
}
else
{
lean_object* v_reuseFailAlloc_2797_; 
v_reuseFailAlloc_2797_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2797_, 0, v___x_2794_);
v___x_2796_ = v_reuseFailAlloc_2797_;
goto v_reusejp_2795_;
}
v_reusejp_2795_:
{
return v___x_2796_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2803_, lean_object* v_msg_2804_, lean_object* v___y_2805_, lean_object* v___y_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_){
_start:
{
lean_object* v_res_2810_; 
v_res_2810_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2803_, v_msg_2804_, v___y_2805_, v___y_2806_, v___y_2807_, v___y_2808_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
lean_dec(v___y_2806_);
lean_dec_ref(v___y_2805_);
return v_res_2810_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2820_; 
v___x_2818_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2819_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2820_ = l_Lean_Name_append(v___x_2819_, v___x_2818_);
return v___x_2820_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2822_; lean_object* v___x_2823_; 
v___x_2822_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2823_ = l_Lean_stringToMessageData(v___x_2822_);
return v___x_2823_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2825_; lean_object* v___x_2826_; 
v___x_2825_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2826_ = l_Lean_stringToMessageData(v___x_2825_);
return v___x_2826_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2828_; lean_object* v___x_2829_; 
v___x_2828_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2829_ = l_Lean_stringToMessageData(v___x_2828_);
return v___x_2829_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2831_; lean_object* v___x_2832_; 
v___x_2831_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2832_ = l_Lean_stringToMessageData(v___x_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2833_, lean_object* v_fst_2834_, lean_object* v_fst_2835_, lean_object* v_inst_2836_, lean_object* v_a_2837_, lean_object* v_projInfo_x3f_2838_, lean_object* v_argVars_2839_, lean_object* v_x_2840_, lean_object* v___y_2841_, lean_object* v___y_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_){
_start:
{
lean_object* v___x_2846_; 
v___x_2846_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2833_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2846_) == 0)
{
lean_object* v_a_2847_; lean_object* v_dummy_2848_; lean_object* v_nargs_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; size_t v_sz_2857_; size_t v___x_2858_; lean_object* v___x_2859_; 
v_a_2847_ = lean_ctor_get(v___x_2846_, 0);
lean_inc(v_a_2847_);
lean_dec_ref_known(v___x_2846_, 1);
v_dummy_2848_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2849_ = l_Lean_Expr_getAppNumArgs(v_a_2833_);
lean_inc(v_nargs_2849_);
v___x_2850_ = lean_mk_array(v_nargs_2849_, v_dummy_2848_);
v___x_2851_ = lean_unsigned_to_nat(1u);
v___x_2852_ = lean_nat_sub(v_nargs_2849_, v___x_2851_);
lean_dec(v_nargs_2849_);
lean_inc_ref(v_a_2833_);
v___x_2853_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2833_, v___x_2850_, v___x_2852_);
v___x_2854_ = lean_array_get_size(v___x_2853_);
v___x_2855_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2856_, 0, v___x_2855_);
lean_ctor_set(v___x_2856_, 1, v___x_2854_);
v_sz_2857_ = lean_array_size(v___x_2853_);
v___x_2858_ = ((size_t)0ULL);
v___x_2859_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2847_, v_fst_2834_, v_argVars_2839_, v___x_2853_, v_sz_2857_, v___x_2858_, v___x_2856_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
lean_dec_ref(v___x_2853_);
lean_dec(v_a_2847_);
if (lean_obj_tag(v___x_2859_) == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; 
lean_dec_ref_known(v___x_2859_, 1);
v___x_2860_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2861_ = lean_array_get_size(v_fst_2834_);
v___x_2862_ = l_List_range(v___x_2861_);
v___x_2863_ = lean_box(0);
v___x_2864_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2835_, v___x_2862_, v___x_2863_);
v___x_2865_ = lean_array_mk(v___x_2864_);
v___x_2866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2866_, 0, v___x_2860_);
lean_ctor_set(v___x_2866_, 1, v___x_2865_);
lean_inc_ref(v_inst_2836_);
lean_inc_ref(v_argVars_2839_);
v___x_2867_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2834_, v_argVars_2839_, v_inst_2836_, v_a_2837_, v_projInfo_x3f_2838_, v___x_2866_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
if (lean_obj_tag(v___x_2867_) == 0)
{
lean_object* v_a_2868_; lean_object* v___x_2870_; uint8_t v_isShared_2871_; uint8_t v_isSharedCheck_2960_; 
v_a_2868_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2960_ == 0)
{
v___x_2870_ = v___x_2867_;
v_isShared_2871_ = v_isSharedCheck_2960_;
goto v_resetjp_2869_;
}
else
{
lean_inc(v_a_2868_);
lean_dec(v___x_2867_);
v___x_2870_ = lean_box(0);
v_isShared_2871_ = v_isSharedCheck_2960_;
goto v_resetjp_2869_;
}
v_resetjp_2869_:
{
lean_object* v_fst_2872_; lean_object* v___x_2874_; uint8_t v_isShared_2875_; uint8_t v_isSharedCheck_2958_; 
v_fst_2872_ = lean_ctor_get(v_a_2868_, 0);
v_isSharedCheck_2958_ = !lean_is_exclusive(v_a_2868_);
if (v_isSharedCheck_2958_ == 0)
{
lean_object* v_unused_2959_; 
v_unused_2959_ = lean_ctor_get(v_a_2868_, 1);
lean_dec(v_unused_2959_);
v___x_2874_ = v_a_2868_;
v_isShared_2875_ = v_isSharedCheck_2958_;
goto v_resetjp_2873_;
}
else
{
lean_inc(v_fst_2872_);
lean_dec(v_a_2868_);
v___x_2874_ = lean_box(0);
v_isShared_2875_ = v_isSharedCheck_2958_;
goto v_resetjp_2873_;
}
v_resetjp_2873_:
{
lean_object* v___y_2877_; lean_object* v___y_2878_; lean_object* v___y_2879_; lean_object* v_options_2880_; lean_object* v_inheritedTraceOptions_2881_; lean_object* v___y_2882_; lean_object* v_options_2938_; lean_object* v_inheritedTraceOptions_2939_; lean_object* v___x_2940_; uint8_t v___x_2941_; 
v_options_2938_ = lean_ctor_get(v___y_2843_, 2);
v_inheritedTraceOptions_2939_ = lean_ctor_get(v___y_2843_, 13);
v___x_2940_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2941_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2938_, v___x_2940_);
if (v___x_2941_ == 0)
{
lean_dec_ref(v_a_2833_);
v___y_2877_ = v___y_2841_;
v___y_2878_ = v___y_2842_;
v___y_2879_ = v___y_2843_;
v_options_2880_ = v_options_2938_;
v_inheritedTraceOptions_2881_ = v_inheritedTraceOptions_2939_;
v___y_2882_ = v___y_2844_;
goto v___jp_2876_;
}
else
{
lean_object* v___x_2942_; lean_object* v_a_2943_; uint8_t v___x_2944_; 
v___x_2942_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2833_, v___y_2842_);
v_a_2943_ = lean_ctor_get(v___x_2942_, 0);
lean_inc(v_a_2943_);
lean_dec_ref(v___x_2942_);
v___x_2944_ = l_Lean_Expr_hasExprMVar(v_a_2943_);
if (v___x_2944_ == 0)
{
lean_dec(v_a_2943_);
v___y_2877_ = v___y_2841_;
v___y_2878_ = v___y_2842_;
v___y_2879_ = v___y_2843_;
v_options_2880_ = v_options_2938_;
v_inheritedTraceOptions_2881_ = v_inheritedTraceOptions_2939_;
v___y_2882_ = v___y_2844_;
goto v___jp_2876_;
}
else
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v_a_2950_; lean_object* v___x_2952_; uint8_t v_isShared_2953_; uint8_t v_isSharedCheck_2957_; 
lean_del_object(v___x_2874_);
lean_dec(v_fst_2872_);
lean_del_object(v___x_2870_);
lean_dec_ref(v_argVars_2839_);
lean_dec_ref(v_inst_2836_);
v___x_2945_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_2946_ = l_Lean_Expr_setPPExplicit(v_a_2943_, v___x_2944_);
v___x_2947_ = l_Lean_indentExpr(v___x_2946_);
v___x_2948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2948_, 0, v___x_2945_);
lean_ctor_set(v___x_2948_, 1, v___x_2947_);
v___x_2949_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2948_, v___y_2841_, v___y_2842_, v___y_2843_, v___y_2844_);
v_a_2950_ = lean_ctor_get(v___x_2949_, 0);
v_isSharedCheck_2957_ = !lean_is_exclusive(v___x_2949_);
if (v_isSharedCheck_2957_ == 0)
{
v___x_2952_ = v___x_2949_;
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
else
{
lean_inc(v_a_2950_);
lean_dec(v___x_2949_);
v___x_2952_ = lean_box(0);
v_isShared_2953_ = v_isSharedCheck_2957_;
goto v_resetjp_2951_;
}
v_resetjp_2951_:
{
lean_object* v___x_2955_; 
if (v_isShared_2953_ == 0)
{
v___x_2955_ = v___x_2952_;
goto v_reusejp_2954_;
}
else
{
lean_object* v_reuseFailAlloc_2956_; 
v_reuseFailAlloc_2956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2956_, 0, v_a_2950_);
v___x_2955_ = v_reuseFailAlloc_2956_;
goto v_reusejp_2954_;
}
v_reusejp_2954_:
{
return v___x_2955_;
}
}
}
}
v___jp_2876_:
{
uint8_t v_hasTrace_2883_; 
v_hasTrace_2883_ = lean_ctor_get_uint8(v_options_2880_, sizeof(void*)*1);
if (v_hasTrace_2883_ == 0)
{
lean_object* v___x_2885_; 
lean_del_object(v___x_2874_);
lean_dec_ref(v_argVars_2839_);
lean_dec_ref(v_inst_2836_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v_fst_2872_);
v___x_2885_ = v___x_2870_;
goto v_reusejp_2884_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v_fst_2872_);
v___x_2885_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2884_;
}
v_reusejp_2884_:
{
return v___x_2885_;
}
}
else
{
lean_object* v___x_2887_; lean_object* v___x_2888_; uint8_t v___x_2889_; 
v___x_2887_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2888_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2889_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2881_, v_options_2880_, v___x_2888_);
if (v___x_2889_ == 0)
{
lean_object* v___x_2891_; 
lean_del_object(v___x_2874_);
lean_dec_ref(v_argVars_2839_);
lean_dec_ref(v_inst_2836_);
if (v_isShared_2871_ == 0)
{
lean_ctor_set(v___x_2870_, 0, v_fst_2872_);
v___x_2891_ = v___x_2870_;
goto v_reusejp_2890_;
}
else
{
lean_object* v_reuseFailAlloc_2892_; 
v_reuseFailAlloc_2892_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2892_, 0, v_fst_2872_);
v___x_2891_ = v_reuseFailAlloc_2892_;
goto v_reusejp_2890_;
}
v_reusejp_2890_:
{
return v___x_2891_;
}
}
else
{
size_t v_sz_2893_; lean_object* v___x_2894_; 
lean_del_object(v___x_2870_);
v_sz_2893_ = lean_array_size(v_fst_2872_);
lean_inc(v_fst_2872_);
v___x_2894_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2839_, v_sz_2893_, v___x_2858_, v_fst_2872_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2882_);
lean_dec_ref(v_argVars_2839_);
if (lean_obj_tag(v___x_2894_) == 0)
{
lean_object* v_a_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2899_; 
v_a_2895_ = lean_ctor_get(v___x_2894_, 0);
lean_inc(v_a_2895_);
lean_dec_ref_known(v___x_2894_, 1);
v___x_2896_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_2897_ = l_Lean_MessageData_ofExpr(v_inst_2836_);
if (v_isShared_2875_ == 0)
{
lean_ctor_set_tag(v___x_2874_, 7);
lean_ctor_set(v___x_2874_, 1, v___x_2897_);
lean_ctor_set(v___x_2874_, 0, v___x_2896_);
v___x_2899_ = v___x_2874_;
goto v_reusejp_2898_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v___x_2896_);
lean_ctor_set(v_reuseFailAlloc_2929_, 1, v___x_2897_);
v___x_2899_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2898_;
}
v_reusejp_2898_:
{
lean_object* v___x_2900_; lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; 
v___x_2900_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_2901_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2901_, 0, v___x_2899_);
lean_ctor_set(v___x_2901_, 1, v___x_2900_);
lean_inc(v_fst_2872_);
v___x_2902_ = lean_array_to_list(v_fst_2872_);
v___x_2903_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_2902_, v___x_2863_);
v___x_2904_ = l_Lean_MessageData_ofList(v___x_2903_);
v___x_2905_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2905_, 0, v___x_2901_);
lean_ctor_set(v___x_2905_, 1, v___x_2904_);
v___x_2906_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2905_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = lean_array_to_list(v_a_2895_);
v___x_2909_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2910_ = l_Lean_MessageData_joinSep(v___x_2908_, v___x_2909_);
v___x_2911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2911_, 0, v___x_2907_);
lean_ctor_set(v___x_2911_, 1, v___x_2910_);
v___x_2912_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2887_, v___x_2911_, v___y_2877_, v___y_2878_, v___y_2879_, v___y_2882_);
if (lean_obj_tag(v___x_2912_) == 0)
{
lean_object* v___x_2914_; uint8_t v_isShared_2915_; uint8_t v_isSharedCheck_2919_; 
v_isSharedCheck_2919_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2919_ == 0)
{
lean_object* v_unused_2920_; 
v_unused_2920_ = lean_ctor_get(v___x_2912_, 0);
lean_dec(v_unused_2920_);
v___x_2914_ = v___x_2912_;
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
else
{
lean_dec(v___x_2912_);
v___x_2914_ = lean_box(0);
v_isShared_2915_ = v_isSharedCheck_2919_;
goto v_resetjp_2913_;
}
v_resetjp_2913_:
{
lean_object* v___x_2917_; 
if (v_isShared_2915_ == 0)
{
lean_ctor_set(v___x_2914_, 0, v_fst_2872_);
v___x_2917_ = v___x_2914_;
goto v_reusejp_2916_;
}
else
{
lean_object* v_reuseFailAlloc_2918_; 
v_reuseFailAlloc_2918_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2918_, 0, v_fst_2872_);
v___x_2917_ = v_reuseFailAlloc_2918_;
goto v_reusejp_2916_;
}
v_reusejp_2916_:
{
return v___x_2917_;
}
}
}
else
{
lean_object* v_a_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2928_; 
lean_dec(v_fst_2872_);
v_a_2921_ = lean_ctor_get(v___x_2912_, 0);
v_isSharedCheck_2928_ = !lean_is_exclusive(v___x_2912_);
if (v_isSharedCheck_2928_ == 0)
{
v___x_2923_ = v___x_2912_;
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
else
{
lean_inc(v_a_2921_);
lean_dec(v___x_2912_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2928_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2926_; 
if (v_isShared_2924_ == 0)
{
v___x_2926_ = v___x_2923_;
goto v_reusejp_2925_;
}
else
{
lean_object* v_reuseFailAlloc_2927_; 
v_reuseFailAlloc_2927_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2927_, 0, v_a_2921_);
v___x_2926_ = v_reuseFailAlloc_2927_;
goto v_reusejp_2925_;
}
v_reusejp_2925_:
{
return v___x_2926_;
}
}
}
}
}
else
{
lean_object* v_a_2930_; lean_object* v___x_2932_; uint8_t v_isShared_2933_; uint8_t v_isSharedCheck_2937_; 
lean_del_object(v___x_2874_);
lean_dec(v_fst_2872_);
lean_dec_ref(v_inst_2836_);
v_a_2930_ = lean_ctor_get(v___x_2894_, 0);
v_isSharedCheck_2937_ = !lean_is_exclusive(v___x_2894_);
if (v_isSharedCheck_2937_ == 0)
{
v___x_2932_ = v___x_2894_;
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
else
{
lean_inc(v_a_2930_);
lean_dec(v___x_2894_);
v___x_2932_ = lean_box(0);
v_isShared_2933_ = v_isSharedCheck_2937_;
goto v_resetjp_2931_;
}
v_resetjp_2931_:
{
lean_object* v___x_2935_; 
if (v_isShared_2933_ == 0)
{
v___x_2935_ = v___x_2932_;
goto v_reusejp_2934_;
}
else
{
lean_object* v_reuseFailAlloc_2936_; 
v_reuseFailAlloc_2936_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2936_, 0, v_a_2930_);
v___x_2935_ = v_reuseFailAlloc_2936_;
goto v_reusejp_2934_;
}
v_reusejp_2934_:
{
return v___x_2935_;
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
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_dec_ref(v_argVars_2839_);
lean_dec_ref(v_inst_2836_);
lean_dec_ref(v_a_2833_);
v_a_2961_ = lean_ctor_get(v___x_2867_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2867_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2867_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2867_);
v___x_2963_ = lean_box(0);
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
v_resetjp_2962_:
{
lean_object* v___x_2966_; 
if (v_isShared_2964_ == 0)
{
v___x_2966_ = v___x_2963_;
goto v_reusejp_2965_;
}
else
{
lean_object* v_reuseFailAlloc_2967_; 
v_reuseFailAlloc_2967_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2967_, 0, v_a_2961_);
v___x_2966_ = v_reuseFailAlloc_2967_;
goto v_reusejp_2965_;
}
v_reusejp_2965_:
{
return v___x_2966_;
}
}
}
}
else
{
lean_object* v_a_2969_; lean_object* v___x_2971_; uint8_t v_isShared_2972_; uint8_t v_isSharedCheck_2976_; 
lean_dec_ref(v_argVars_2839_);
lean_dec_ref(v_a_2837_);
lean_dec_ref(v_inst_2836_);
lean_dec_ref(v_fst_2834_);
lean_dec_ref(v_a_2833_);
v_a_2969_ = lean_ctor_get(v___x_2859_, 0);
v_isSharedCheck_2976_ = !lean_is_exclusive(v___x_2859_);
if (v_isSharedCheck_2976_ == 0)
{
v___x_2971_ = v___x_2859_;
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
else
{
lean_inc(v_a_2969_);
lean_dec(v___x_2859_);
v___x_2971_ = lean_box(0);
v_isShared_2972_ = v_isSharedCheck_2976_;
goto v_resetjp_2970_;
}
v_resetjp_2970_:
{
lean_object* v___x_2974_; 
if (v_isShared_2972_ == 0)
{
v___x_2974_ = v___x_2971_;
goto v_reusejp_2973_;
}
else
{
lean_object* v_reuseFailAlloc_2975_; 
v_reuseFailAlloc_2975_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2975_, 0, v_a_2969_);
v___x_2974_ = v_reuseFailAlloc_2975_;
goto v_reusejp_2973_;
}
v_reusejp_2973_:
{
return v___x_2974_;
}
}
}
}
else
{
lean_dec_ref(v_argVars_2839_);
lean_dec_ref(v_a_2837_);
lean_dec_ref(v_inst_2836_);
lean_dec_ref(v_fst_2834_);
lean_dec_ref(v_a_2833_);
return v___x_2846_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_2977_, lean_object* v_fst_2978_, lean_object* v_fst_2979_, lean_object* v_inst_2980_, lean_object* v_a_2981_, lean_object* v_projInfo_x3f_2982_, lean_object* v_argVars_2983_, lean_object* v_x_2984_, lean_object* v___y_2985_, lean_object* v___y_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_){
_start:
{
lean_object* v_res_2990_; 
v_res_2990_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_2977_, v_fst_2978_, v_fst_2979_, v_inst_2980_, v_a_2981_, v_projInfo_x3f_2982_, v_argVars_2983_, v_x_2984_, v___y_2985_, v___y_2986_, v___y_2987_, v___y_2988_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec(v___y_2986_);
lean_dec_ref(v___y_2985_);
lean_dec_ref(v_x_2984_);
lean_dec(v_projInfo_x3f_2982_);
lean_dec_ref(v_fst_2979_);
return v_res_2990_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_2991_, lean_object* v_projInfo_x3f_2992_, lean_object* v_a_2993_, lean_object* v_a_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_){
_start:
{
lean_object* v_keyedConfig_2998_; uint8_t v_trackZetaDelta_2999_; lean_object* v_zetaDeltaSet_3000_; lean_object* v_lctx_3001_; lean_object* v_localInstances_3002_; lean_object* v_defEqCtx_x3f_3003_; lean_object* v_synthPendingDepth_3004_; lean_object* v_customCanUnfoldPredicate_x3f_3005_; uint8_t v_univApprox_3006_; uint8_t v_inTypeClassResolution_3007_; uint8_t v_cacheInferType_3008_; uint8_t v___x_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; lean_object* v___x_3012_; 
v_keyedConfig_2998_ = lean_ctor_get(v_a_2993_, 0);
v_trackZetaDelta_2999_ = lean_ctor_get_uint8(v_a_2993_, sizeof(void*)*7);
v_zetaDeltaSet_3000_ = lean_ctor_get(v_a_2993_, 1);
v_lctx_3001_ = lean_ctor_get(v_a_2993_, 2);
v_localInstances_3002_ = lean_ctor_get(v_a_2993_, 3);
v_defEqCtx_x3f_3003_ = lean_ctor_get(v_a_2993_, 4);
v_synthPendingDepth_3004_ = lean_ctor_get(v_a_2993_, 5);
v_customCanUnfoldPredicate_x3f_3005_ = lean_ctor_get(v_a_2993_, 6);
v_univApprox_3006_ = lean_ctor_get_uint8(v_a_2993_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3007_ = lean_ctor_get_uint8(v_a_2993_, sizeof(void*)*7 + 2);
v_cacheInferType_3008_ = lean_ctor_get_uint8(v_a_2993_, sizeof(void*)*7 + 3);
v___x_3009_ = 2;
lean_inc_ref(v_keyedConfig_2998_);
v___x_3010_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3009_, v_keyedConfig_2998_);
lean_inc(v_customCanUnfoldPredicate_x3f_3005_);
lean_inc(v_synthPendingDepth_3004_);
lean_inc(v_defEqCtx_x3f_3003_);
lean_inc_ref(v_localInstances_3002_);
lean_inc_ref(v_lctx_3001_);
lean_inc(v_zetaDeltaSet_3000_);
v___x_3011_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3011_, 0, v___x_3010_);
lean_ctor_set(v___x_3011_, 1, v_zetaDeltaSet_3000_);
lean_ctor_set(v___x_3011_, 2, v_lctx_3001_);
lean_ctor_set(v___x_3011_, 3, v_localInstances_3002_);
lean_ctor_set(v___x_3011_, 4, v_defEqCtx_x3f_3003_);
lean_ctor_set(v___x_3011_, 5, v_synthPendingDepth_3004_);
lean_ctor_set(v___x_3011_, 6, v_customCanUnfoldPredicate_x3f_3005_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*7, v_trackZetaDelta_2999_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*7 + 1, v_univApprox_3006_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3007_);
lean_ctor_set_uint8(v___x_3011_, sizeof(void*)*7 + 3, v_cacheInferType_3008_);
lean_inc(v_a_2996_);
lean_inc_ref(v_a_2995_);
lean_inc(v_a_2994_);
lean_inc_ref(v___x_3011_);
lean_inc_ref(v_inst_2991_);
v___x_3012_ = lean_infer_type(v_inst_2991_, v___x_3011_, v_a_2994_, v_a_2995_, v_a_2996_);
if (lean_obj_tag(v___x_3012_) == 0)
{
lean_object* v_a_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; lean_object* v___x_3016_; 
v_a_3013_ = lean_ctor_get(v___x_3012_, 0);
lean_inc_n(v_a_3013_, 2);
lean_dec_ref_known(v___x_3012_, 1);
v___x_3014_ = lean_box(0);
v___x_3015_ = 0;
v___x_3016_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3013_, v___x_3014_, v___x_3015_, v___x_3011_, v_a_2994_, v_a_2995_, v_a_2996_);
if (lean_obj_tag(v___x_3016_) == 0)
{
lean_object* v_a_3017_; lean_object* v_snd_3018_; lean_object* v_fst_3019_; lean_object* v_fst_3020_; lean_object* v_snd_3021_; lean_object* v___x_3022_; 
v_a_3017_ = lean_ctor_get(v___x_3016_, 0);
lean_inc(v_a_3017_);
lean_dec_ref_known(v___x_3016_, 1);
v_snd_3018_ = lean_ctor_get(v_a_3017_, 1);
lean_inc(v_snd_3018_);
v_fst_3019_ = lean_ctor_get(v_a_3017_, 0);
lean_inc(v_fst_3019_);
lean_dec(v_a_3017_);
v_fst_3020_ = lean_ctor_get(v_snd_3018_, 0);
lean_inc(v_fst_3020_);
v_snd_3021_ = lean_ctor_get(v_snd_3018_, 1);
lean_inc(v_snd_3021_);
lean_dec(v_snd_3018_);
lean_inc(v_a_2996_);
lean_inc_ref(v_a_2995_);
lean_inc(v_a_2994_);
lean_inc_ref(v___x_3011_);
v___x_3022_ = lean_whnf(v_snd_3021_, v___x_3011_, v_a_2994_, v_a_2995_, v_a_2996_);
if (lean_obj_tag(v___x_3022_) == 0)
{
lean_object* v_a_3023_; lean_object* v___f_3024_; uint8_t v___x_3025_; lean_object* v___x_3026_; 
v_a_3023_ = lean_ctor_get(v___x_3022_, 0);
lean_inc(v_a_3023_);
lean_dec_ref_known(v___x_3022_, 1);
lean_inc(v_a_3013_);
v___f_3024_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3024_, 0, v_a_3023_);
lean_closure_set(v___f_3024_, 1, v_fst_3019_);
lean_closure_set(v___f_3024_, 2, v_fst_3020_);
lean_closure_set(v___f_3024_, 3, v_inst_2991_);
lean_closure_set(v___f_3024_, 4, v_a_3013_);
lean_closure_set(v___f_3024_, 5, v_projInfo_x3f_2992_);
v___x_3025_ = 0;
v___x_3026_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3013_, v___f_3024_, v___x_3025_, v___x_3025_, v___x_3011_, v_a_2994_, v_a_2995_, v_a_2996_);
lean_dec_ref_known(v___x_3011_, 7);
return v___x_3026_;
}
else
{
lean_object* v_a_3027_; lean_object* v___x_3029_; uint8_t v_isShared_3030_; uint8_t v_isSharedCheck_3034_; 
lean_dec(v_fst_3020_);
lean_dec(v_fst_3019_);
lean_dec(v_a_3013_);
lean_dec_ref_known(v___x_3011_, 7);
lean_dec(v_projInfo_x3f_2992_);
lean_dec_ref(v_inst_2991_);
v_a_3027_ = lean_ctor_get(v___x_3022_, 0);
v_isSharedCheck_3034_ = !lean_is_exclusive(v___x_3022_);
if (v_isSharedCheck_3034_ == 0)
{
v___x_3029_ = v___x_3022_;
v_isShared_3030_ = v_isSharedCheck_3034_;
goto v_resetjp_3028_;
}
else
{
lean_inc(v_a_3027_);
lean_dec(v___x_3022_);
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
else
{
lean_object* v_a_3035_; lean_object* v___x_3037_; uint8_t v_isShared_3038_; uint8_t v_isSharedCheck_3042_; 
lean_dec(v_a_3013_);
lean_dec_ref_known(v___x_3011_, 7);
lean_dec(v_projInfo_x3f_2992_);
lean_dec_ref(v_inst_2991_);
v_a_3035_ = lean_ctor_get(v___x_3016_, 0);
v_isSharedCheck_3042_ = !lean_is_exclusive(v___x_3016_);
if (v_isSharedCheck_3042_ == 0)
{
v___x_3037_ = v___x_3016_;
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
else
{
lean_inc(v_a_3035_);
lean_dec(v___x_3016_);
v___x_3037_ = lean_box(0);
v_isShared_3038_ = v_isSharedCheck_3042_;
goto v_resetjp_3036_;
}
v_resetjp_3036_:
{
lean_object* v___x_3040_; 
if (v_isShared_3038_ == 0)
{
v___x_3040_ = v___x_3037_;
goto v_reusejp_3039_;
}
else
{
lean_object* v_reuseFailAlloc_3041_; 
v_reuseFailAlloc_3041_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3041_, 0, v_a_3035_);
v___x_3040_ = v_reuseFailAlloc_3041_;
goto v_reusejp_3039_;
}
v_reusejp_3039_:
{
return v___x_3040_;
}
}
}
}
else
{
lean_object* v_a_3043_; lean_object* v___x_3045_; uint8_t v_isShared_3046_; uint8_t v_isSharedCheck_3050_; 
lean_dec_ref_known(v___x_3011_, 7);
lean_dec(v_projInfo_x3f_2992_);
lean_dec_ref(v_inst_2991_);
v_a_3043_ = lean_ctor_get(v___x_3012_, 0);
v_isSharedCheck_3050_ = !lean_is_exclusive(v___x_3012_);
if (v_isSharedCheck_3050_ == 0)
{
v___x_3045_ = v___x_3012_;
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
else
{
lean_inc(v_a_3043_);
lean_dec(v___x_3012_);
v___x_3045_ = lean_box(0);
v_isShared_3046_ = v_isSharedCheck_3050_;
goto v_resetjp_3044_;
}
v_resetjp_3044_:
{
lean_object* v___x_3048_; 
if (v_isShared_3046_ == 0)
{
v___x_3048_ = v___x_3045_;
goto v_reusejp_3047_;
}
else
{
lean_object* v_reuseFailAlloc_3049_; 
v_reuseFailAlloc_3049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3049_, 0, v_a_3043_);
v___x_3048_ = v_reuseFailAlloc_3049_;
goto v_reusejp_3047_;
}
v_reusejp_3047_:
{
return v___x_3048_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_3051_, lean_object* v_projInfo_x3f_3052_, lean_object* v_a_3053_, lean_object* v_a_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_){
_start:
{
lean_object* v_res_3058_; 
v_res_3058_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_3051_, v_projInfo_x3f_3052_, v_a_3053_, v_a_3054_, v_a_3055_, v_a_3056_);
lean_dec(v_a_3056_);
lean_dec_ref(v_a_3055_);
lean_dec(v_a_3054_);
lean_dec_ref(v_a_3053_);
return v_res_3058_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_3059_, lean_object* v___x_3060_, lean_object* v_a_3061_, lean_object* v_inst_3062_, lean_object* v_R_3063_, lean_object* v_a_3064_, lean_object* v_b_3065_, lean_object* v_c_3066_, lean_object* v___y_3067_, lean_object* v___y_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_){
_start:
{
lean_object* v___x_3072_; 
v___x_3072_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_3059_, v___x_3060_, v_a_3061_, v_a_3064_, v_b_3065_);
return v___x_3072_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_3073_, lean_object* v___x_3074_, lean_object* v_a_3075_, lean_object* v_inst_3076_, lean_object* v_R_3077_, lean_object* v_a_3078_, lean_object* v_b_3079_, lean_object* v_c_3080_, lean_object* v___y_3081_, lean_object* v___y_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_){
_start:
{
lean_object* v_res_3086_; 
v_res_3086_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_3073_, v___x_3074_, v_a_3075_, v_inst_3076_, v_R_3077_, v_a_3078_, v_b_3079_, v_c_3080_, v___y_3081_, v___y_3082_, v___y_3083_, v___y_3084_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec(v___y_3082_);
lean_dec_ref(v___y_3081_);
lean_dec_ref(v_a_3075_);
lean_dec(v___x_3074_);
lean_dec(v_upperBound_3073_);
return v_res_3086_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3087_, lean_object* v_msg_3088_, lean_object* v___y_3089_, lean_object* v___y_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_){
_start:
{
lean_object* v___x_3094_; 
v___x_3094_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3088_, v___y_3089_, v___y_3090_, v___y_3091_, v___y_3092_);
return v___x_3094_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3095_, lean_object* v_msg_3096_, lean_object* v___y_3097_, lean_object* v___y_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_){
_start:
{
lean_object* v_res_3102_; 
v_res_3102_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3095_, v_msg_3096_, v___y_3097_, v___y_3098_, v___y_3099_, v___y_3100_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
lean_dec(v___y_3098_);
lean_dec_ref(v___y_3097_);
return v_res_3102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_3103_, lean_object* v_argVars_3104_, lean_object* v_inst_3105_, lean_object* v_a_3106_, lean_object* v_projInfo_x3f_3107_, lean_object* v_inst_3108_, lean_object* v_a_3109_, lean_object* v___y_3110_, lean_object* v___y_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_3103_, v_argVars_3104_, v_inst_3105_, v_a_3106_, v_projInfo_x3f_3107_, v_a_3109_, v___y_3110_, v___y_3111_, v___y_3112_, v___y_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_3116_, lean_object* v_argVars_3117_, lean_object* v_inst_3118_, lean_object* v_a_3119_, lean_object* v_projInfo_x3f_3120_, lean_object* v_inst_3121_, lean_object* v_a_3122_, lean_object* v___y_3123_, lean_object* v___y_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_3116_, v_argVars_3117_, v_inst_3118_, v_a_3119_, v_projInfo_x3f_3120_, v_inst_3121_, v_a_3122_, v___y_3123_, v___y_3124_, v___y_3125_, v___y_3126_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v___y_3124_);
lean_dec_ref(v___y_3123_);
lean_dec(v_projInfo_x3f_3120_);
return v_res_3128_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(lean_object* v_type_3129_, lean_object* v_k_3130_, uint8_t v_cleanupAnnotations_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_){
_start:
{
lean_object* v___f_3137_; uint8_t v___x_3138_; lean_object* v___x_3139_; lean_object* v___x_3140_; 
v___f_3137_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3137_, 0, v_k_3130_);
v___x_3138_ = 0;
v___x_3139_ = lean_box(0);
v___x_3140_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3138_, v___x_3139_, v_type_3129_, v___f_3137_, v_cleanupAnnotations_3131_, v___x_3138_, v___y_3132_, v___y_3133_, v___y_3134_, v___y_3135_);
if (lean_obj_tag(v___x_3140_) == 0)
{
lean_object* v_a_3141_; lean_object* v___x_3143_; uint8_t v_isShared_3144_; uint8_t v_isSharedCheck_3148_; 
v_a_3141_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3148_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3148_ == 0)
{
v___x_3143_ = v___x_3140_;
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
else
{
lean_inc(v_a_3141_);
lean_dec(v___x_3140_);
v___x_3143_ = lean_box(0);
v_isShared_3144_ = v_isSharedCheck_3148_;
goto v_resetjp_3142_;
}
v_resetjp_3142_:
{
lean_object* v___x_3146_; 
if (v_isShared_3144_ == 0)
{
v___x_3146_ = v___x_3143_;
goto v_reusejp_3145_;
}
else
{
lean_object* v_reuseFailAlloc_3147_; 
v_reuseFailAlloc_3147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3147_, 0, v_a_3141_);
v___x_3146_ = v_reuseFailAlloc_3147_;
goto v_reusejp_3145_;
}
v_reusejp_3145_:
{
return v___x_3146_;
}
}
}
else
{
lean_object* v_a_3149_; lean_object* v___x_3151_; uint8_t v_isShared_3152_; uint8_t v_isSharedCheck_3156_; 
v_a_3149_ = lean_ctor_get(v___x_3140_, 0);
v_isSharedCheck_3156_ = !lean_is_exclusive(v___x_3140_);
if (v_isSharedCheck_3156_ == 0)
{
v___x_3151_ = v___x_3140_;
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
else
{
lean_inc(v_a_3149_);
lean_dec(v___x_3140_);
v___x_3151_ = lean_box(0);
v_isShared_3152_ = v_isSharedCheck_3156_;
goto v_resetjp_3150_;
}
v_resetjp_3150_:
{
lean_object* v___x_3154_; 
if (v_isShared_3152_ == 0)
{
v___x_3154_ = v___x_3151_;
goto v_reusejp_3153_;
}
else
{
lean_object* v_reuseFailAlloc_3155_; 
v_reuseFailAlloc_3155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3155_, 0, v_a_3149_);
v___x_3154_ = v_reuseFailAlloc_3155_;
goto v_reusejp_3153_;
}
v_reusejp_3153_:
{
return v___x_3154_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg___boxed(lean_object* v_type_3157_, lean_object* v_k_3158_, lean_object* v_cleanupAnnotations_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3165_; lean_object* v_res_3166_; 
v_cleanupAnnotations_boxed_3165_ = lean_unbox(v_cleanupAnnotations_3159_);
v_res_3166_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3157_, v_k_3158_, v_cleanupAnnotations_boxed_3165_, v___y_3160_, v___y_3161_, v___y_3162_, v___y_3163_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
lean_dec(v___y_3161_);
lean_dec_ref(v___y_3160_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(lean_object* v_00_u03b1_3167_, lean_object* v_type_3168_, lean_object* v_k_3169_, uint8_t v_cleanupAnnotations_3170_, lean_object* v___y_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_){
_start:
{
lean_object* v___x_3176_; 
v___x_3176_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3168_, v_k_3169_, v_cleanupAnnotations_3170_, v___y_3171_, v___y_3172_, v___y_3173_, v___y_3174_);
return v___x_3176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___boxed(lean_object* v_00_u03b1_3177_, lean_object* v_type_3178_, lean_object* v_k_3179_, lean_object* v_cleanupAnnotations_3180_, lean_object* v___y_3181_, lean_object* v___y_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3186_; lean_object* v_res_3187_; 
v_cleanupAnnotations_boxed_3186_ = lean_unbox(v_cleanupAnnotations_3180_);
v_res_3187_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(v_00_u03b1_3177_, v_type_3178_, v_k_3179_, v_cleanupAnnotations_boxed_3186_, v___y_3181_, v___y_3182_, v___y_3183_, v___y_3184_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
lean_dec(v___y_3182_);
lean_dec_ref(v___y_3181_);
return v_res_3187_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(lean_object* v_as_3188_, size_t v_sz_3189_, size_t v_i_3190_, lean_object* v_b_3191_, lean_object* v___y_3192_, lean_object* v___y_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_){
_start:
{
lean_object* v_a_3198_; uint8_t v___x_3202_; 
v___x_3202_ = lean_usize_dec_lt(v_i_3190_, v_sz_3189_);
if (v___x_3202_ == 0)
{
lean_object* v___x_3203_; 
v___x_3203_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3203_, 0, v_b_3191_);
return v___x_3203_;
}
else
{
lean_object* v_a_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
v_a_3204_ = lean_array_uget_borrowed(v_as_3188_, v_i_3190_);
v___x_3205_ = l_Lean_Expr_fvarId_x21(v_a_3204_);
lean_inc(v___x_3205_);
v___x_3206_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_3205_, v___y_3193_, v___y_3194_, v___y_3195_);
if (lean_obj_tag(v___x_3206_) == 0)
{
lean_object* v_a_3207_; lean_object* v___x_3208_; uint8_t v___x_3209_; uint8_t v___x_3210_; 
v_a_3207_ = lean_ctor_get(v___x_3206_, 0);
lean_inc(v_a_3207_);
lean_dec_ref_known(v___x_3206_, 1);
v___x_3208_ = lean_box(0);
v___x_3209_ = lean_unbox(v_a_3207_);
lean_dec(v_a_3207_);
v___x_3210_ = l_Lean_BinderInfo_isInstImplicit(v___x_3209_);
if (v___x_3210_ == 0)
{
lean_dec(v___x_3205_);
v_a_3198_ = v___x_3208_;
goto v___jp_3197_;
}
else
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; 
v___x_3211_ = lean_st_ref_take(v___y_3192_);
v___x_3212_ = l_Lean_CollectFVars_State_add(v___x_3211_, v___x_3205_);
v___x_3213_ = lean_st_ref_set(v___y_3192_, v___x_3212_);
v_a_3198_ = v___x_3208_;
goto v___jp_3197_;
}
}
else
{
lean_object* v_a_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3221_; 
lean_dec(v___x_3205_);
v_a_3214_ = lean_ctor_get(v___x_3206_, 0);
v_isSharedCheck_3221_ = !lean_is_exclusive(v___x_3206_);
if (v_isSharedCheck_3221_ == 0)
{
v___x_3216_ = v___x_3206_;
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_a_3214_);
lean_dec(v___x_3206_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3221_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3219_; 
if (v_isShared_3217_ == 0)
{
v___x_3219_ = v___x_3216_;
goto v_reusejp_3218_;
}
else
{
lean_object* v_reuseFailAlloc_3220_; 
v_reuseFailAlloc_3220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3220_, 0, v_a_3214_);
v___x_3219_ = v_reuseFailAlloc_3220_;
goto v_reusejp_3218_;
}
v_reusejp_3218_:
{
return v___x_3219_;
}
}
}
}
v___jp_3197_:
{
size_t v___x_3199_; size_t v___x_3200_; 
v___x_3199_ = ((size_t)1ULL);
v___x_3200_ = lean_usize_add(v_i_3190_, v___x_3199_);
v_i_3190_ = v___x_3200_;
v_b_3191_ = v_a_3198_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg___boxed(lean_object* v_as_3222_, lean_object* v_sz_3223_, lean_object* v_i_3224_, lean_object* v_b_3225_, lean_object* v___y_3226_, lean_object* v___y_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_){
_start:
{
size_t v_sz_boxed_3231_; size_t v_i_boxed_3232_; lean_object* v_res_3233_; 
v_sz_boxed_3231_ = lean_unbox_usize(v_sz_3223_);
lean_dec(v_sz_3223_);
v_i_boxed_3232_ = lean_unbox_usize(v_i_3224_);
lean_dec(v_i_3224_);
v_res_3233_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_as_3222_, v_sz_boxed_3231_, v_i_boxed_3232_, v_b_3225_, v___y_3226_, v___y_3227_, v___y_3228_, v___y_3229_);
lean_dec(v___y_3229_);
lean_dec_ref(v___y_3228_);
lean_dec_ref(v___y_3227_);
lean_dec(v___y_3226_);
lean_dec_ref(v_as_3222_);
return v_res_3233_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object* v_k_3234_, lean_object* v_t_3235_){
_start:
{
if (lean_obj_tag(v_t_3235_) == 0)
{
lean_object* v_k_3236_; lean_object* v_l_3237_; lean_object* v_r_3238_; uint8_t v___x_3239_; 
v_k_3236_ = lean_ctor_get(v_t_3235_, 1);
v_l_3237_ = lean_ctor_get(v_t_3235_, 3);
v_r_3238_ = lean_ctor_get(v_t_3235_, 4);
v___x_3239_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3234_, v_k_3236_);
switch(v___x_3239_)
{
case 0:
{
v_t_3235_ = v_l_3237_;
goto _start;
}
case 1:
{
uint8_t v___x_3241_; 
v___x_3241_ = 1;
return v___x_3241_;
}
default: 
{
v_t_3235_ = v_r_3238_;
goto _start;
}
}
}
else
{
uint8_t v___x_3243_; 
v___x_3243_ = 0;
return v___x_3243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object* v_k_3244_, lean_object* v_t_3245_){
_start:
{
uint8_t v_res_3246_; lean_object* v_r_3247_; 
v_res_3246_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3244_, v_t_3245_);
lean_dec(v_t_3245_);
lean_dec(v_k_3244_);
v_r_3247_ = lean_box(v_res_3246_);
return v_r_3247_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3249_; lean_object* v___x_3250_; 
v___x_3249_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__0));
v___x_3250_ = l_Lean_stringToMessageData(v___x_3249_);
return v___x_3250_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3252_; lean_object* v___x_3253_; 
v___x_3252_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__2));
v___x_3253_ = l_Lean_stringToMessageData(v___x_3252_);
return v___x_3253_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(lean_object* v_a_3254_, lean_object* v_as_3255_, size_t v_sz_3256_, size_t v_i_3257_, lean_object* v_b_3258_, lean_object* v___y_3259_, lean_object* v___y_3260_, lean_object* v___y_3261_){
_start:
{
lean_object* v_a_3264_; uint8_t v___x_3268_; 
v___x_3268_ = lean_usize_dec_lt(v_i_3257_, v_sz_3256_);
if (v___x_3268_ == 0)
{
lean_object* v___x_3269_; 
v___x_3269_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3269_, 0, v_b_3258_);
return v___x_3269_;
}
else
{
lean_object* v_snd_3270_; 
v_snd_3270_ = lean_ctor_get(v_b_3258_, 1);
lean_inc(v_snd_3270_);
if (lean_obj_tag(v_snd_3270_) == 0)
{
lean_object* v_fst_3271_; lean_object* v___x_3273_; uint8_t v_isShared_3274_; uint8_t v_isSharedCheck_3279_; 
v_fst_3271_ = lean_ctor_get(v_b_3258_, 0);
v_isSharedCheck_3279_ = !lean_is_exclusive(v_b_3258_);
if (v_isSharedCheck_3279_ == 0)
{
lean_object* v_unused_3280_; 
v_unused_3280_ = lean_ctor_get(v_b_3258_, 1);
lean_dec(v_unused_3280_);
v___x_3273_ = v_b_3258_;
v_isShared_3274_ = v_isSharedCheck_3279_;
goto v_resetjp_3272_;
}
else
{
lean_inc(v_fst_3271_);
lean_dec(v_b_3258_);
v___x_3273_ = lean_box(0);
v_isShared_3274_ = v_isSharedCheck_3279_;
goto v_resetjp_3272_;
}
v_resetjp_3272_:
{
lean_object* v___x_3276_; 
if (v_isShared_3274_ == 0)
{
v___x_3276_ = v___x_3273_;
goto v_reusejp_3275_;
}
else
{
lean_object* v_reuseFailAlloc_3278_; 
v_reuseFailAlloc_3278_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3278_, 0, v_fst_3271_);
lean_ctor_set(v_reuseFailAlloc_3278_, 1, v_snd_3270_);
v___x_3276_ = v_reuseFailAlloc_3278_;
goto v_reusejp_3275_;
}
v_reusejp_3275_:
{
lean_object* v___x_3277_; 
v___x_3277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3277_, 0, v___x_3276_);
return v___x_3277_;
}
}
}
else
{
lean_object* v_fst_3281_; lean_object* v___x_3283_; uint8_t v_isShared_3284_; uint8_t v_isSharedCheck_3338_; 
v_fst_3281_ = lean_ctor_get(v_b_3258_, 0);
v_isSharedCheck_3338_ = !lean_is_exclusive(v_b_3258_);
if (v_isSharedCheck_3338_ == 0)
{
lean_object* v_unused_3339_; 
v_unused_3339_ = lean_ctor_get(v_b_3258_, 1);
lean_dec(v_unused_3339_);
v___x_3283_ = v_b_3258_;
v_isShared_3284_ = v_isSharedCheck_3338_;
goto v_resetjp_3282_;
}
else
{
lean_inc(v_fst_3281_);
lean_dec(v_b_3258_);
v___x_3283_ = lean_box(0);
v_isShared_3284_ = v_isSharedCheck_3338_;
goto v_resetjp_3282_;
}
v_resetjp_3282_:
{
lean_object* v_val_3285_; lean_object* v___x_3287_; uint8_t v_isShared_3288_; uint8_t v_isSharedCheck_3337_; 
v_val_3285_ = lean_ctor_get(v_snd_3270_, 0);
v_isSharedCheck_3337_ = !lean_is_exclusive(v_snd_3270_);
if (v_isSharedCheck_3337_ == 0)
{
v___x_3287_ = v_snd_3270_;
v_isShared_3288_ = v_isSharedCheck_3337_;
goto v_resetjp_3286_;
}
else
{
lean_inc(v_val_3285_);
lean_dec(v_snd_3270_);
v___x_3287_ = lean_box(0);
v_isShared_3288_ = v_isSharedCheck_3337_;
goto v_resetjp_3286_;
}
v_resetjp_3286_:
{
lean_object* v_fvarSet_3289_; lean_object* v_a_3290_; lean_object* v___x_3291_; lean_object* v___x_3292_; lean_object* v___x_3294_; 
v_fvarSet_3289_ = lean_ctor_get(v_a_3254_, 1);
v_a_3290_ = lean_array_uget_borrowed(v_as_3255_, v_i_3257_);
v___x_3291_ = lean_unsigned_to_nat(1u);
v___x_3292_ = lean_nat_add(v_val_3285_, v___x_3291_);
if (v_isShared_3288_ == 0)
{
lean_ctor_set(v___x_3287_, 0, v___x_3292_);
v___x_3294_ = v___x_3287_;
goto v_reusejp_3293_;
}
else
{
lean_object* v_reuseFailAlloc_3336_; 
v_reuseFailAlloc_3336_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3336_, 0, v___x_3292_);
v___x_3294_ = v_reuseFailAlloc_3336_;
goto v_reusejp_3293_;
}
v_reusejp_3293_:
{
lean_object* v___x_3295_; uint8_t v___x_3296_; 
v___x_3295_ = l_Lean_Expr_fvarId_x21(v_a_3290_);
v___x_3296_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v___x_3295_, v_fvarSet_3289_);
if (v___x_3296_ == 0)
{
lean_object* v___x_3297_; 
v___x_3297_ = l_Lean_FVarId_getDecl___redArg(v___x_3295_, v___y_3259_, v___y_3260_, v___y_3261_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v_a_3298_; lean_object* v___x_3299_; 
v_a_3298_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_a_3298_);
lean_dec_ref_known(v___x_3297_, 1);
v___x_3299_ = l_Lean_LocalDecl_ppAsBinder(v_a_3298_);
if (lean_obj_tag(v___x_3299_) == 1)
{
lean_object* v_val_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3321_; 
v_val_3300_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3321_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3321_ == 0)
{
v___x_3302_ = v___x_3299_;
v_isShared_3303_ = v_isSharedCheck_3321_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_val_3300_);
lean_dec(v___x_3299_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3321_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3307_; 
v___x_3304_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1);
v___x_3305_ = l_Nat_reprFast(v_val_3285_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set_tag(v___x_3302_, 3);
lean_ctor_set(v___x_3302_, 0, v___x_3305_);
v___x_3307_ = v___x_3302_;
goto v_reusejp_3306_;
}
else
{
lean_object* v_reuseFailAlloc_3320_; 
v_reuseFailAlloc_3320_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3320_, 0, v___x_3305_);
v___x_3307_ = v_reuseFailAlloc_3320_;
goto v_reusejp_3306_;
}
v_reusejp_3306_:
{
lean_object* v___x_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3318_; 
v___x_3308_ = l_Lean_MessageData_ofFormat(v___x_3307_);
v___x_3309_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3309_, 0, v___x_3304_);
lean_ctor_set(v___x_3309_, 1, v___x_3308_);
v___x_3310_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3309_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3312_, 0, v___x_3311_);
lean_ctor_set(v___x_3312_, 1, v_val_3300_);
v___x_3313_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3312_);
lean_ctor_set(v___x_3314_, 1, v___x_3313_);
v___x_3315_ = l_Lean_indentD(v___x_3314_);
v___x_3316_ = lean_array_push(v_fst_3281_, v___x_3315_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 1, v___x_3294_);
lean_ctor_set(v___x_3283_, 0, v___x_3316_);
v___x_3318_ = v___x_3283_;
goto v_reusejp_3317_;
}
else
{
lean_object* v_reuseFailAlloc_3319_; 
v_reuseFailAlloc_3319_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3319_, 0, v___x_3316_);
lean_ctor_set(v_reuseFailAlloc_3319_, 1, v___x_3294_);
v___x_3318_ = v_reuseFailAlloc_3319_;
goto v_reusejp_3317_;
}
v_reusejp_3317_:
{
v_a_3264_ = v___x_3318_;
goto v___jp_3263_;
}
}
}
}
else
{
lean_object* v___x_3323_; 
lean_dec(v___x_3299_);
lean_dec(v_val_3285_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 1, v___x_3294_);
v___x_3323_ = v___x_3283_;
goto v_reusejp_3322_;
}
else
{
lean_object* v_reuseFailAlloc_3324_; 
v_reuseFailAlloc_3324_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3324_, 0, v_fst_3281_);
lean_ctor_set(v_reuseFailAlloc_3324_, 1, v___x_3294_);
v___x_3323_ = v_reuseFailAlloc_3324_;
goto v_reusejp_3322_;
}
v_reusejp_3322_:
{
v_a_3264_ = v___x_3323_;
goto v___jp_3263_;
}
}
}
else
{
lean_object* v_a_3325_; lean_object* v___x_3327_; uint8_t v_isShared_3328_; uint8_t v_isSharedCheck_3332_; 
lean_dec_ref(v___x_3294_);
lean_dec(v_val_3285_);
lean_del_object(v___x_3283_);
lean_dec(v_fst_3281_);
v_a_3325_ = lean_ctor_get(v___x_3297_, 0);
v_isSharedCheck_3332_ = !lean_is_exclusive(v___x_3297_);
if (v_isSharedCheck_3332_ == 0)
{
v___x_3327_ = v___x_3297_;
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
else
{
lean_inc(v_a_3325_);
lean_dec(v___x_3297_);
v___x_3327_ = lean_box(0);
v_isShared_3328_ = v_isSharedCheck_3332_;
goto v_resetjp_3326_;
}
v_resetjp_3326_:
{
lean_object* v___x_3330_; 
if (v_isShared_3328_ == 0)
{
v___x_3330_ = v___x_3327_;
goto v_reusejp_3329_;
}
else
{
lean_object* v_reuseFailAlloc_3331_; 
v_reuseFailAlloc_3331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3331_, 0, v_a_3325_);
v___x_3330_ = v_reuseFailAlloc_3331_;
goto v_reusejp_3329_;
}
v_reusejp_3329_:
{
return v___x_3330_;
}
}
}
}
else
{
lean_object* v___x_3334_; 
lean_dec(v___x_3295_);
lean_dec(v_val_3285_);
if (v_isShared_3284_ == 0)
{
lean_ctor_set(v___x_3283_, 1, v___x_3294_);
v___x_3334_ = v___x_3283_;
goto v_reusejp_3333_;
}
else
{
lean_object* v_reuseFailAlloc_3335_; 
v_reuseFailAlloc_3335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3335_, 0, v_fst_3281_);
lean_ctor_set(v_reuseFailAlloc_3335_, 1, v___x_3294_);
v___x_3334_ = v_reuseFailAlloc_3335_;
goto v_reusejp_3333_;
}
v_reusejp_3333_:
{
v_a_3264_ = v___x_3334_;
goto v___jp_3263_;
}
}
}
}
}
}
}
v___jp_3263_:
{
size_t v___x_3265_; size_t v___x_3266_; 
v___x_3265_ = ((size_t)1ULL);
v___x_3266_ = lean_usize_add(v_i_3257_, v___x_3265_);
v_i_3257_ = v___x_3266_;
v_b_3258_ = v_a_3264_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___boxed(lean_object* v_a_3340_, lean_object* v_as_3341_, lean_object* v_sz_3342_, lean_object* v_i_3343_, lean_object* v_b_3344_, lean_object* v___y_3345_, lean_object* v___y_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_){
_start:
{
size_t v_sz_boxed_3349_; size_t v_i_boxed_3350_; lean_object* v_res_3351_; 
v_sz_boxed_3349_ = lean_unbox_usize(v_sz_3342_);
lean_dec(v_sz_3342_);
v_i_boxed_3350_ = lean_unbox_usize(v_i_3343_);
lean_dec(v_i_3343_);
v_res_3351_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3340_, v_as_3341_, v_sz_boxed_3349_, v_i_boxed_3350_, v_b_3344_, v___y_3345_, v___y_3346_, v___y_3347_);
lean_dec(v___y_3347_);
lean_dec_ref(v___y_3346_);
lean_dec_ref(v___y_3345_);
lean_dec_ref(v_as_3341_);
lean_dec_ref(v_a_3340_);
return v_res_3351_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(uint8_t v___y_3359_, uint8_t v_suppressElabErrors_3360_, lean_object* v_x_3361_){
_start:
{
if (lean_obj_tag(v_x_3361_) == 1)
{
lean_object* v_pre_3362_; 
v_pre_3362_ = lean_ctor_get(v_x_3361_, 0);
switch(lean_obj_tag(v_pre_3362_))
{
case 1:
{
lean_object* v_pre_3363_; 
v_pre_3363_ = lean_ctor_get(v_pre_3362_, 0);
switch(lean_obj_tag(v_pre_3363_))
{
case 0:
{
lean_object* v_str_3364_; lean_object* v_str_3365_; lean_object* v___x_3366_; uint8_t v___x_3367_; 
v_str_3364_ = lean_ctor_get(v_x_3361_, 1);
v_str_3365_ = lean_ctor_get(v_pre_3362_, 1);
v___x_3366_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__0));
v___x_3367_ = lean_string_dec_eq(v_str_3365_, v___x_3366_);
if (v___x_3367_ == 0)
{
lean_object* v___x_3368_; uint8_t v___x_3369_; 
v___x_3368_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__1));
v___x_3369_ = lean_string_dec_eq(v_str_3365_, v___x_3368_);
if (v___x_3369_ == 0)
{
return v___y_3359_;
}
else
{
lean_object* v___x_3370_; uint8_t v___x_3371_; 
v___x_3370_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__2));
v___x_3371_ = lean_string_dec_eq(v_str_3364_, v___x_3370_);
if (v___x_3371_ == 0)
{
return v___y_3359_;
}
else
{
return v_suppressElabErrors_3360_;
}
}
}
else
{
lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3372_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__3));
v___x_3373_ = lean_string_dec_eq(v_str_3364_, v___x_3372_);
if (v___x_3373_ == 0)
{
return v___y_3359_;
}
else
{
return v_suppressElabErrors_3360_;
}
}
}
case 1:
{
lean_object* v_pre_3374_; 
v_pre_3374_ = lean_ctor_get(v_pre_3363_, 0);
if (lean_obj_tag(v_pre_3374_) == 0)
{
lean_object* v_str_3375_; lean_object* v_str_3376_; lean_object* v_str_3377_; lean_object* v___x_3378_; uint8_t v___x_3379_; 
v_str_3375_ = lean_ctor_get(v_x_3361_, 1);
v_str_3376_ = lean_ctor_get(v_pre_3362_, 1);
v_str_3377_ = lean_ctor_get(v_pre_3363_, 1);
v___x_3378_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__4));
v___x_3379_ = lean_string_dec_eq(v_str_3377_, v___x_3378_);
if (v___x_3379_ == 0)
{
return v___y_3359_;
}
else
{
lean_object* v___x_3380_; uint8_t v___x_3381_; 
v___x_3380_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__5));
v___x_3381_ = lean_string_dec_eq(v_str_3376_, v___x_3380_);
if (v___x_3381_ == 0)
{
return v___y_3359_;
}
else
{
lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3382_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__6));
v___x_3383_ = lean_string_dec_eq(v_str_3375_, v___x_3382_);
if (v___x_3383_ == 0)
{
return v___y_3359_;
}
else
{
return v_suppressElabErrors_3360_;
}
}
}
}
else
{
return v___y_3359_;
}
}
default: 
{
return v___y_3359_;
}
}
}
case 0:
{
lean_object* v_str_3384_; lean_object* v___x_3385_; uint8_t v___x_3386_; 
v_str_3384_ = lean_ctor_get(v_x_3361_, 1);
v___x_3385_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3386_ = lean_string_dec_eq(v_str_3384_, v___x_3385_);
if (v___x_3386_ == 0)
{
return v___y_3359_;
}
else
{
return v_suppressElabErrors_3360_;
}
}
default: 
{
return v___y_3359_;
}
}
}
else
{
return v___y_3359_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed(lean_object* v___y_3387_, lean_object* v_suppressElabErrors_3388_, lean_object* v_x_3389_){
_start:
{
uint8_t v___y_11912__boxed_3390_; uint8_t v_suppressElabErrors_boxed_3391_; uint8_t v_res_3392_; lean_object* v_r_3393_; 
v___y_11912__boxed_3390_ = lean_unbox(v___y_3387_);
v_suppressElabErrors_boxed_3391_ = lean_unbox(v_suppressElabErrors_3388_);
v_res_3392_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(v___y_11912__boxed_3390_, v_suppressElabErrors_boxed_3391_, v_x_3389_);
lean_dec(v_x_3389_);
v_r_3393_ = lean_box(v_res_3392_);
return v_r_3393_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(lean_object* v_ref_3394_, lean_object* v_msgData_3395_, uint8_t v_severity_3396_, uint8_t v_isSilent_3397_, lean_object* v___y_3398_, lean_object* v___y_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_){
_start:
{
lean_object* v___y_3404_; lean_object* v___y_3405_; uint8_t v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; uint8_t v___y_3409_; lean_object* v___y_3410_; lean_object* v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3440_; lean_object* v___y_3441_; uint8_t v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; uint8_t v___y_3445_; uint8_t v___y_3446_; lean_object* v___y_3447_; lean_object* v___y_3465_; lean_object* v___y_3466_; lean_object* v___y_3467_; uint8_t v___y_3468_; lean_object* v___y_3469_; uint8_t v___y_3470_; uint8_t v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3476_; lean_object* v___y_3477_; lean_object* v___y_3478_; lean_object* v___y_3479_; uint8_t v___y_3480_; uint8_t v___y_3481_; uint8_t v___y_3482_; uint8_t v___x_3487_; lean_object* v___y_3489_; lean_object* v___y_3490_; lean_object* v___y_3491_; lean_object* v___y_3492_; uint8_t v___y_3493_; uint8_t v___y_3494_; uint8_t v___y_3495_; uint8_t v___y_3497_; uint8_t v___x_3512_; 
v___x_3487_ = 2;
v___x_3512_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3396_, v___x_3487_);
if (v___x_3512_ == 0)
{
v___y_3497_ = v___x_3512_;
goto v___jp_3496_;
}
else
{
uint8_t v___x_3513_; 
lean_inc_ref(v_msgData_3395_);
v___x_3513_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3395_);
v___y_3497_ = v___x_3513_;
goto v___jp_3496_;
}
v___jp_3403_:
{
lean_object* v___x_3413_; lean_object* v_currNamespace_3414_; lean_object* v_openDecls_3415_; lean_object* v_env_3416_; lean_object* v_nextMacroScope_3417_; lean_object* v_ngen_3418_; lean_object* v_auxDeclNGen_3419_; lean_object* v_traceState_3420_; lean_object* v_cache_3421_; lean_object* v_messages_3422_; lean_object* v_infoState_3423_; lean_object* v_snapshotTasks_3424_; lean_object* v___x_3426_; uint8_t v_isShared_3427_; uint8_t v_isSharedCheck_3438_; 
v___x_3413_ = lean_st_ref_take(v___y_3412_);
v_currNamespace_3414_ = lean_ctor_get(v___y_3411_, 6);
v_openDecls_3415_ = lean_ctor_get(v___y_3411_, 7);
v_env_3416_ = lean_ctor_get(v___x_3413_, 0);
v_nextMacroScope_3417_ = lean_ctor_get(v___x_3413_, 1);
v_ngen_3418_ = lean_ctor_get(v___x_3413_, 2);
v_auxDeclNGen_3419_ = lean_ctor_get(v___x_3413_, 3);
v_traceState_3420_ = lean_ctor_get(v___x_3413_, 4);
v_cache_3421_ = lean_ctor_get(v___x_3413_, 5);
v_messages_3422_ = lean_ctor_get(v___x_3413_, 6);
v_infoState_3423_ = lean_ctor_get(v___x_3413_, 7);
v_snapshotTasks_3424_ = lean_ctor_get(v___x_3413_, 8);
v_isSharedCheck_3438_ = !lean_is_exclusive(v___x_3413_);
if (v_isSharedCheck_3438_ == 0)
{
v___x_3426_ = v___x_3413_;
v_isShared_3427_ = v_isSharedCheck_3438_;
goto v_resetjp_3425_;
}
else
{
lean_inc(v_snapshotTasks_3424_);
lean_inc(v_infoState_3423_);
lean_inc(v_messages_3422_);
lean_inc(v_cache_3421_);
lean_inc(v_traceState_3420_);
lean_inc(v_auxDeclNGen_3419_);
lean_inc(v_ngen_3418_);
lean_inc(v_nextMacroScope_3417_);
lean_inc(v_env_3416_);
lean_dec(v___x_3413_);
v___x_3426_ = lean_box(0);
v_isShared_3427_ = v_isSharedCheck_3438_;
goto v_resetjp_3425_;
}
v_resetjp_3425_:
{
lean_object* v___x_3428_; lean_object* v___x_3429_; lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3433_; 
lean_inc(v_openDecls_3415_);
lean_inc(v_currNamespace_3414_);
v___x_3428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3428_, 0, v_currNamespace_3414_);
lean_ctor_set(v___x_3428_, 1, v_openDecls_3415_);
v___x_3429_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3429_, 0, v___x_3428_);
lean_ctor_set(v___x_3429_, 1, v___y_3407_);
lean_inc_ref(v___y_3410_);
lean_inc_ref(v___y_3408_);
v___x_3430_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3430_, 0, v___y_3408_);
lean_ctor_set(v___x_3430_, 1, v___y_3404_);
lean_ctor_set(v___x_3430_, 2, v___y_3405_);
lean_ctor_set(v___x_3430_, 3, v___y_3410_);
lean_ctor_set(v___x_3430_, 4, v___x_3429_);
lean_ctor_set_uint8(v___x_3430_, sizeof(void*)*5, v___y_3409_);
lean_ctor_set_uint8(v___x_3430_, sizeof(void*)*5 + 1, v___y_3406_);
lean_ctor_set_uint8(v___x_3430_, sizeof(void*)*5 + 2, v_isSilent_3397_);
v___x_3431_ = l_Lean_MessageLog_add(v___x_3430_, v_messages_3422_);
if (v_isShared_3427_ == 0)
{
lean_ctor_set(v___x_3426_, 6, v___x_3431_);
v___x_3433_ = v___x_3426_;
goto v_reusejp_3432_;
}
else
{
lean_object* v_reuseFailAlloc_3437_; 
v_reuseFailAlloc_3437_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3437_, 0, v_env_3416_);
lean_ctor_set(v_reuseFailAlloc_3437_, 1, v_nextMacroScope_3417_);
lean_ctor_set(v_reuseFailAlloc_3437_, 2, v_ngen_3418_);
lean_ctor_set(v_reuseFailAlloc_3437_, 3, v_auxDeclNGen_3419_);
lean_ctor_set(v_reuseFailAlloc_3437_, 4, v_traceState_3420_);
lean_ctor_set(v_reuseFailAlloc_3437_, 5, v_cache_3421_);
lean_ctor_set(v_reuseFailAlloc_3437_, 6, v___x_3431_);
lean_ctor_set(v_reuseFailAlloc_3437_, 7, v_infoState_3423_);
lean_ctor_set(v_reuseFailAlloc_3437_, 8, v_snapshotTasks_3424_);
v___x_3433_ = v_reuseFailAlloc_3437_;
goto v_reusejp_3432_;
}
v_reusejp_3432_:
{
lean_object* v___x_3434_; lean_object* v___x_3435_; lean_object* v___x_3436_; 
v___x_3434_ = lean_st_ref_set(v___y_3412_, v___x_3433_);
v___x_3435_ = lean_box(0);
v___x_3436_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3436_, 0, v___x_3435_);
return v___x_3436_;
}
}
}
v___jp_3439_:
{
lean_object* v___x_3448_; lean_object* v___x_3449_; lean_object* v_a_3450_; lean_object* v___x_3452_; uint8_t v_isShared_3453_; uint8_t v_isSharedCheck_3463_; 
v___x_3448_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3395_);
v___x_3449_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3448_, v___y_3398_, v___y_3399_, v___y_3400_, v___y_3401_);
v_a_3450_ = lean_ctor_get(v___x_3449_, 0);
v_isSharedCheck_3463_ = !lean_is_exclusive(v___x_3449_);
if (v_isSharedCheck_3463_ == 0)
{
v___x_3452_ = v___x_3449_;
v_isShared_3453_ = v_isSharedCheck_3463_;
goto v_resetjp_3451_;
}
else
{
lean_inc(v_a_3450_);
lean_dec(v___x_3449_);
v___x_3452_ = lean_box(0);
v_isShared_3453_ = v_isSharedCheck_3463_;
goto v_resetjp_3451_;
}
v_resetjp_3451_:
{
lean_object* v___x_3454_; lean_object* v___x_3455_; lean_object* v___x_3456_; lean_object* v___x_3457_; 
lean_inc_ref_n(v___y_3441_, 2);
v___x_3454_ = l_Lean_FileMap_toPosition(v___y_3441_, v___y_3444_);
lean_dec(v___y_3444_);
v___x_3455_ = l_Lean_FileMap_toPosition(v___y_3441_, v___y_3447_);
lean_dec(v___y_3447_);
v___x_3456_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3456_, 0, v___x_3455_);
v___x_3457_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3446_ == 0)
{
lean_del_object(v___x_3452_);
lean_dec_ref(v___y_3440_);
v___y_3404_ = v___x_3454_;
v___y_3405_ = v___x_3456_;
v___y_3406_ = v___y_3442_;
v___y_3407_ = v_a_3450_;
v___y_3408_ = v___y_3443_;
v___y_3409_ = v___y_3445_;
v___y_3410_ = v___x_3457_;
v___y_3411_ = v___y_3400_;
v___y_3412_ = v___y_3401_;
goto v___jp_3403_;
}
else
{
uint8_t v___x_3458_; 
lean_inc(v_a_3450_);
v___x_3458_ = l_Lean_MessageData_hasTag(v___y_3440_, v_a_3450_);
if (v___x_3458_ == 0)
{
lean_object* v___x_3459_; lean_object* v___x_3461_; 
lean_dec_ref_known(v___x_3456_, 1);
lean_dec_ref(v___x_3454_);
lean_dec(v_a_3450_);
v___x_3459_ = lean_box(0);
if (v_isShared_3453_ == 0)
{
lean_ctor_set(v___x_3452_, 0, v___x_3459_);
v___x_3461_ = v___x_3452_;
goto v_reusejp_3460_;
}
else
{
lean_object* v_reuseFailAlloc_3462_; 
v_reuseFailAlloc_3462_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3462_, 0, v___x_3459_);
v___x_3461_ = v_reuseFailAlloc_3462_;
goto v_reusejp_3460_;
}
v_reusejp_3460_:
{
return v___x_3461_;
}
}
else
{
lean_del_object(v___x_3452_);
v___y_3404_ = v___x_3454_;
v___y_3405_ = v___x_3456_;
v___y_3406_ = v___y_3442_;
v___y_3407_ = v_a_3450_;
v___y_3408_ = v___y_3443_;
v___y_3409_ = v___y_3445_;
v___y_3410_ = v___x_3457_;
v___y_3411_ = v___y_3400_;
v___y_3412_ = v___y_3401_;
goto v___jp_3403_;
}
}
}
}
v___jp_3464_:
{
lean_object* v___x_3473_; 
v___x_3473_ = l_Lean_Syntax_getTailPos_x3f(v___y_3466_, v___y_3470_);
lean_dec(v___y_3466_);
if (lean_obj_tag(v___x_3473_) == 0)
{
lean_inc(v___y_3472_);
v___y_3440_ = v___y_3465_;
v___y_3441_ = v___y_3467_;
v___y_3442_ = v___y_3468_;
v___y_3443_ = v___y_3469_;
v___y_3444_ = v___y_3472_;
v___y_3445_ = v___y_3470_;
v___y_3446_ = v___y_3471_;
v___y_3447_ = v___y_3472_;
goto v___jp_3439_;
}
else
{
lean_object* v_val_3474_; 
v_val_3474_ = lean_ctor_get(v___x_3473_, 0);
lean_inc(v_val_3474_);
lean_dec_ref_known(v___x_3473_, 1);
v___y_3440_ = v___y_3465_;
v___y_3441_ = v___y_3467_;
v___y_3442_ = v___y_3468_;
v___y_3443_ = v___y_3469_;
v___y_3444_ = v___y_3472_;
v___y_3445_ = v___y_3470_;
v___y_3446_ = v___y_3471_;
v___y_3447_ = v_val_3474_;
goto v___jp_3439_;
}
}
v___jp_3475_:
{
lean_object* v_ref_3483_; lean_object* v___x_3484_; 
v_ref_3483_ = l_Lean_replaceRef(v_ref_3394_, v___y_3477_);
v___x_3484_ = l_Lean_Syntax_getPos_x3f(v_ref_3483_, v___y_3480_);
if (lean_obj_tag(v___x_3484_) == 0)
{
lean_object* v___x_3485_; 
v___x_3485_ = lean_unsigned_to_nat(0u);
v___y_3465_ = v___y_3476_;
v___y_3466_ = v_ref_3483_;
v___y_3467_ = v___y_3478_;
v___y_3468_ = v___y_3482_;
v___y_3469_ = v___y_3479_;
v___y_3470_ = v___y_3480_;
v___y_3471_ = v___y_3481_;
v___y_3472_ = v___x_3485_;
goto v___jp_3464_;
}
else
{
lean_object* v_val_3486_; 
v_val_3486_ = lean_ctor_get(v___x_3484_, 0);
lean_inc(v_val_3486_);
lean_dec_ref_known(v___x_3484_, 1);
v___y_3465_ = v___y_3476_;
v___y_3466_ = v_ref_3483_;
v___y_3467_ = v___y_3478_;
v___y_3468_ = v___y_3482_;
v___y_3469_ = v___y_3479_;
v___y_3470_ = v___y_3480_;
v___y_3471_ = v___y_3481_;
v___y_3472_ = v_val_3486_;
goto v___jp_3464_;
}
}
v___jp_3488_:
{
if (v___y_3495_ == 0)
{
v___y_3476_ = v___y_3491_;
v___y_3477_ = v___y_3489_;
v___y_3478_ = v___y_3490_;
v___y_3479_ = v___y_3492_;
v___y_3480_ = v___y_3494_;
v___y_3481_ = v___y_3493_;
v___y_3482_ = v_severity_3396_;
goto v___jp_3475_;
}
else
{
v___y_3476_ = v___y_3491_;
v___y_3477_ = v___y_3489_;
v___y_3478_ = v___y_3490_;
v___y_3479_ = v___y_3492_;
v___y_3480_ = v___y_3494_;
v___y_3481_ = v___y_3493_;
v___y_3482_ = v___x_3487_;
goto v___jp_3475_;
}
}
v___jp_3496_:
{
if (v___y_3497_ == 0)
{
lean_object* v_fileName_3498_; lean_object* v_fileMap_3499_; lean_object* v_options_3500_; lean_object* v_ref_3501_; uint8_t v_suppressElabErrors_3502_; lean_object* v___x_3503_; lean_object* v___x_3504_; lean_object* v___f_3505_; uint8_t v___x_3506_; uint8_t v___x_3507_; 
v_fileName_3498_ = lean_ctor_get(v___y_3400_, 0);
v_fileMap_3499_ = lean_ctor_get(v___y_3400_, 1);
v_options_3500_ = lean_ctor_get(v___y_3400_, 2);
v_ref_3501_ = lean_ctor_get(v___y_3400_, 5);
v_suppressElabErrors_3502_ = lean_ctor_get_uint8(v___y_3400_, sizeof(void*)*14 + 1);
v___x_3503_ = lean_box(v___y_3497_);
v___x_3504_ = lean_box(v_suppressElabErrors_3502_);
v___f_3505_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3505_, 0, v___x_3503_);
lean_closure_set(v___f_3505_, 1, v___x_3504_);
v___x_3506_ = 1;
v___x_3507_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3396_, v___x_3506_);
if (v___x_3507_ == 0)
{
v___y_3489_ = v_ref_3501_;
v___y_3490_ = v_fileMap_3499_;
v___y_3491_ = v___f_3505_;
v___y_3492_ = v_fileName_3498_;
v___y_3493_ = v_suppressElabErrors_3502_;
v___y_3494_ = v___y_3497_;
v___y_3495_ = v___x_3507_;
goto v___jp_3488_;
}
else
{
lean_object* v___x_3508_; uint8_t v___x_3509_; 
v___x_3508_ = l_Lean_warningAsError;
v___x_3509_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3500_, v___x_3508_);
v___y_3489_ = v_ref_3501_;
v___y_3490_ = v_fileMap_3499_;
v___y_3491_ = v___f_3505_;
v___y_3492_ = v_fileName_3498_;
v___y_3493_ = v_suppressElabErrors_3502_;
v___y_3494_ = v___y_3497_;
v___y_3495_ = v___x_3509_;
goto v___jp_3488_;
}
}
else
{
lean_object* v___x_3510_; lean_object* v___x_3511_; 
lean_dec_ref(v_msgData_3395_);
v___x_3510_ = lean_box(0);
v___x_3511_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3511_, 0, v___x_3510_);
return v___x_3511_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___boxed(lean_object* v_ref_3514_, lean_object* v_msgData_3515_, lean_object* v_severity_3516_, lean_object* v_isSilent_3517_, lean_object* v___y_3518_, lean_object* v___y_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_){
_start:
{
uint8_t v_severity_boxed_3523_; uint8_t v_isSilent_boxed_3524_; lean_object* v_res_3525_; 
v_severity_boxed_3523_ = lean_unbox(v_severity_3516_);
v_isSilent_boxed_3524_ = lean_unbox(v_isSilent_3517_);
v_res_3525_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3514_, v_msgData_3515_, v_severity_boxed_3523_, v_isSilent_boxed_3524_, v___y_3518_, v___y_3519_, v___y_3520_, v___y_3521_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v___y_3519_);
lean_dec_ref(v___y_3518_);
lean_dec(v_ref_3514_);
return v_res_3525_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(lean_object* v_msgData_3526_, uint8_t v_severity_3527_, uint8_t v_isSilent_3528_, lean_object* v___y_3529_, lean_object* v___y_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_){
_start:
{
lean_object* v_ref_3534_; lean_object* v___x_3535_; 
v_ref_3534_ = lean_ctor_get(v___y_3531_, 5);
v___x_3535_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3534_, v_msgData_3526_, v_severity_3527_, v_isSilent_3528_, v___y_3529_, v___y_3530_, v___y_3531_, v___y_3532_);
return v___x_3535_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3___boxed(lean_object* v_msgData_3536_, lean_object* v_severity_3537_, lean_object* v_isSilent_3538_, lean_object* v___y_3539_, lean_object* v___y_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_){
_start:
{
uint8_t v_severity_boxed_3544_; uint8_t v_isSilent_boxed_3545_; lean_object* v_res_3546_; 
v_severity_boxed_3544_ = lean_unbox(v_severity_3537_);
v_isSilent_boxed_3545_ = lean_unbox(v_isSilent_3538_);
v_res_3546_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3536_, v_severity_boxed_3544_, v_isSilent_boxed_3545_, v___y_3539_, v___y_3540_, v___y_3541_, v___y_3542_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
lean_dec(v___y_3540_);
lean_dec_ref(v___y_3539_);
return v_res_3546_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object* v_msgData_3547_, lean_object* v___y_3548_, lean_object* v___y_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_){
_start:
{
uint8_t v___x_3553_; uint8_t v___x_3554_; lean_object* v___x_3555_; 
v___x_3553_ = 1;
v___x_3554_ = 0;
v___x_3555_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3547_, v___x_3553_, v___x_3554_, v___y_3548_, v___y_3549_, v___y_3550_, v___y_3551_);
return v___x_3555_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object* v_msgData_3556_, lean_object* v___y_3557_, lean_object* v___y_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_){
_start:
{
lean_object* v_res_3562_; 
v_res_3562_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v_msgData_3556_, v___y_3557_, v___y_3558_, v___y_3559_, v___y_3560_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
lean_dec(v___y_3558_);
lean_dec_ref(v___y_3557_);
return v_res_3562_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3564_; lean_object* v___x_3565_; 
v___x_3564_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0));
v___x_3565_ = l_Lean_stringToMessageData(v___x_3564_);
return v___x_3565_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3567_; lean_object* v___x_3568_; 
v___x_3567_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2));
v___x_3568_ = l_Lean_stringToMessageData(v___x_3567_);
return v___x_3568_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; lean_object* v___x_3571_; 
v___x_3569_ = lean_box(0);
v___x_3570_ = lean_unsigned_to_nat(16u);
v___x_3571_ = lean_mk_array(v___x_3570_, v___x_3569_);
return v___x_3571_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3572_; lean_object* v___x_3573_; lean_object* v___x_3574_; 
v___x_3572_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4);
v___x_3573_ = lean_unsigned_to_nat(0u);
v___x_3574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3574_, 0, v___x_3573_);
lean_ctor_set(v___x_3574_, 1, v___x_3572_);
return v___x_3574_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3577_; lean_object* v___x_3578_; lean_object* v___x_3579_; lean_object* v___x_3580_; 
v___x_3577_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6));
v___x_3578_ = lean_box(1);
v___x_3579_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5);
v___x_3580_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3580_, 0, v___x_3579_);
lean_ctor_set(v___x_3580_, 1, v___x_3578_);
lean_ctor_set(v___x_3580_, 2, v___x_3577_);
return v___x_3580_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3587_; lean_object* v___x_3588_; 
v___x_3587_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10));
v___x_3588_ = l_Lean_stringToMessageData(v___x_3587_);
return v___x_3588_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13(void){
_start:
{
lean_object* v___x_3590_; lean_object* v___x_3591_; 
v___x_3590_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12));
v___x_3591_ = l_Lean_stringToMessageData(v___x_3590_);
return v___x_3591_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v___x_3593_, lean_object* v_args_3594_, lean_object* v_ty_3595_, lean_object* v___y_3596_, lean_object* v___y_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_){
_start:
{
lean_object* v___y_3602_; lean_object* v___y_3603_; lean_object* v___y_3604_; lean_object* v___x_3618_; lean_object* v___x_3619_; lean_object* v___x_3620_; lean_object* v___y_3676_; lean_object* v___x_3677_; 
v___x_3618_ = lean_unsigned_to_nat(0u);
v___x_3619_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7);
v___x_3620_ = lean_st_mk_ref(v___x_3619_);
v___x_3677_ = l_Lean_Expr_collectFVars(v_ty_3595_, v___x_3620_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
if (lean_obj_tag(v___x_3677_) == 0)
{
lean_object* v___x_3678_; size_t v_sz_3679_; size_t v___x_3680_; lean_object* v___x_3681_; 
lean_dec_ref_known(v___x_3677_, 1);
v___x_3678_ = lean_box(0);
v_sz_3679_ = lean_array_size(v_args_3594_);
v___x_3680_ = ((size_t)0ULL);
v___x_3681_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_args_3594_, v_sz_3679_, v___x_3680_, v___x_3678_, v___x_3620_, v___y_3596_, v___y_3598_, v___y_3599_);
if (lean_obj_tag(v___x_3681_) == 0)
{
lean_dec_ref_known(v___x_3681_, 1);
goto v___jp_3621_;
}
else
{
v___y_3676_ = v___x_3681_;
goto v___jp_3675_;
}
}
else
{
v___y_3676_ = v___x_3677_;
goto v___jp_3675_;
}
v___jp_3601_:
{
lean_object* v___x_3605_; lean_object* v___x_3606_; lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; uint8_t v___x_3615_; 
lean_inc_ref(v___y_3604_);
v___x_3605_ = l_Lean_stringToMessageData(v___y_3604_);
v___x_3606_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3606_, 0, v___y_3602_);
lean_ctor_set(v___x_3606_, 1, v___x_3605_);
v___x_3607_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1);
v___x_3608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___x_3606_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = lean_array_to_list(v___y_3603_);
v___x_3610_ = l_Lean_MessageData_nil;
v___x_3611_ = l_Lean_MessageData_joinSep(v___x_3609_, v___x_3610_);
v___x_3612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3612_, 0, v___x_3608_);
lean_ctor_set(v___x_3612_, 1, v___x_3611_);
v___x_3613_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3);
v___x_3614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3612_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = l_Lean_Expr_hasSorry(v___x_3593_);
if (v___x_3615_ == 0)
{
lean_object* v___x_3616_; 
v___x_3616_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3614_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
return v___x_3616_;
}
else
{
lean_object* v___x_3617_; 
v___x_3617_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_3614_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
return v___x_3617_;
}
}
v___jp_3621_:
{
lean_object* v___x_3622_; lean_object* v___x_3623_; 
v___x_3622_ = lean_st_ref_get(v___x_3620_);
lean_dec(v___x_3620_);
v___x_3623_ = l_Lean_CollectFVars_State_addDependencies(v___x_3622_, v___y_3596_, v___y_3597_, v___y_3598_, v___y_3599_);
if (lean_obj_tag(v___x_3623_) == 0)
{
lean_object* v_a_3624_; lean_object* v___x_3625_; lean_object* v___x_3626_; size_t v_sz_3627_; size_t v___x_3628_; lean_object* v___x_3629_; 
v_a_3624_ = lean_ctor_get(v___x_3623_, 0);
lean_inc(v_a_3624_);
lean_dec_ref_known(v___x_3623_, 1);
v___x_3625_ = lean_unsigned_to_nat(1u);
v___x_3626_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9));
v_sz_3627_ = lean_array_size(v_args_3594_);
v___x_3628_ = ((size_t)0ULL);
v___x_3629_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3624_, v_args_3594_, v_sz_3627_, v___x_3628_, v___x_3626_, v___y_3596_, v___y_3598_, v___y_3599_);
lean_dec(v_a_3624_);
if (lean_obj_tag(v___x_3629_) == 0)
{
lean_object* v_a_3630_; lean_object* v___x_3632_; uint8_t v_isShared_3633_; uint8_t v_isSharedCheck_3658_; 
v_a_3630_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3658_ == 0)
{
v___x_3632_ = v___x_3629_;
v_isShared_3633_ = v_isSharedCheck_3658_;
goto v_resetjp_3631_;
}
else
{
lean_inc(v_a_3630_);
lean_dec(v___x_3629_);
v___x_3632_ = lean_box(0);
v_isShared_3633_ = v_isSharedCheck_3658_;
goto v_resetjp_3631_;
}
v_resetjp_3631_:
{
lean_object* v_fst_3634_; lean_object* v___x_3636_; uint8_t v_isShared_3637_; uint8_t v_isSharedCheck_3656_; 
v_fst_3634_ = lean_ctor_get(v_a_3630_, 0);
v_isSharedCheck_3656_ = !lean_is_exclusive(v_a_3630_);
if (v_isSharedCheck_3656_ == 0)
{
lean_object* v_unused_3657_; 
v_unused_3657_ = lean_ctor_get(v_a_3630_, 1);
lean_dec(v_unused_3657_);
v___x_3636_ = v_a_3630_;
v_isShared_3637_ = v_isSharedCheck_3656_;
goto v_resetjp_3635_;
}
else
{
lean_inc(v_fst_3634_);
lean_dec(v_a_3630_);
v___x_3636_ = lean_box(0);
v_isShared_3637_ = v_isSharedCheck_3656_;
goto v_resetjp_3635_;
}
v_resetjp_3635_:
{
lean_object* v___x_3638_; uint8_t v___x_3639_; 
v___x_3638_ = lean_array_get_size(v_fst_3634_);
v___x_3639_ = lean_nat_dec_eq(v___x_3638_, v___x_3618_);
if (v___x_3639_ == 0)
{
lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3645_; 
lean_del_object(v___x_3632_);
v___x_3640_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11);
v___x_3641_ = l_Nat_reprFast(v___x_3638_);
v___x_3642_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
v___x_3643_ = l_Lean_MessageData_ofFormat(v___x_3642_);
if (v_isShared_3637_ == 0)
{
lean_ctor_set_tag(v___x_3636_, 7);
lean_ctor_set(v___x_3636_, 1, v___x_3643_);
lean_ctor_set(v___x_3636_, 0, v___x_3640_);
v___x_3645_ = v___x_3636_;
goto v_reusejp_3644_;
}
else
{
lean_object* v_reuseFailAlloc_3651_; 
v_reuseFailAlloc_3651_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3651_, 0, v___x_3640_);
lean_ctor_set(v_reuseFailAlloc_3651_, 1, v___x_3643_);
v___x_3645_ = v_reuseFailAlloc_3651_;
goto v_reusejp_3644_;
}
v_reusejp_3644_:
{
lean_object* v___x_3646_; lean_object* v___x_3647_; uint8_t v___x_3648_; 
v___x_3646_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13);
v___x_3647_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3647_, 0, v___x_3645_);
lean_ctor_set(v___x_3647_, 1, v___x_3646_);
v___x_3648_ = lean_nat_dec_eq(v___x_3638_, v___x_3625_);
if (v___x_3648_ == 0)
{
lean_object* v___x_3649_; 
v___x_3649_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14));
v___y_3602_ = v___x_3647_;
v___y_3603_ = v_fst_3634_;
v___y_3604_ = v___x_3649_;
goto v___jp_3601_;
}
else
{
lean_object* v___x_3650_; 
v___x_3650_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___y_3602_ = v___x_3647_;
v___y_3603_ = v_fst_3634_;
v___y_3604_ = v___x_3650_;
goto v___jp_3601_;
}
}
}
else
{
lean_object* v___x_3652_; lean_object* v___x_3654_; 
lean_del_object(v___x_3636_);
lean_dec(v_fst_3634_);
v___x_3652_ = lean_box(0);
if (v_isShared_3633_ == 0)
{
lean_ctor_set(v___x_3632_, 0, v___x_3652_);
v___x_3654_ = v___x_3632_;
goto v_reusejp_3653_;
}
else
{
lean_object* v_reuseFailAlloc_3655_; 
v_reuseFailAlloc_3655_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3655_, 0, v___x_3652_);
v___x_3654_ = v_reuseFailAlloc_3655_;
goto v_reusejp_3653_;
}
v_reusejp_3653_:
{
return v___x_3654_;
}
}
}
}
}
else
{
lean_object* v_a_3659_; lean_object* v___x_3661_; uint8_t v_isShared_3662_; uint8_t v_isSharedCheck_3666_; 
v_a_3659_ = lean_ctor_get(v___x_3629_, 0);
v_isSharedCheck_3666_ = !lean_is_exclusive(v___x_3629_);
if (v_isSharedCheck_3666_ == 0)
{
v___x_3661_ = v___x_3629_;
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
else
{
lean_inc(v_a_3659_);
lean_dec(v___x_3629_);
v___x_3661_ = lean_box(0);
v_isShared_3662_ = v_isSharedCheck_3666_;
goto v_resetjp_3660_;
}
v_resetjp_3660_:
{
lean_object* v___x_3664_; 
if (v_isShared_3662_ == 0)
{
v___x_3664_ = v___x_3661_;
goto v_reusejp_3663_;
}
else
{
lean_object* v_reuseFailAlloc_3665_; 
v_reuseFailAlloc_3665_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3665_, 0, v_a_3659_);
v___x_3664_ = v_reuseFailAlloc_3665_;
goto v_reusejp_3663_;
}
v_reusejp_3663_:
{
return v___x_3664_;
}
}
}
}
else
{
lean_object* v_a_3667_; lean_object* v___x_3669_; uint8_t v_isShared_3670_; uint8_t v_isSharedCheck_3674_; 
v_a_3667_ = lean_ctor_get(v___x_3623_, 0);
v_isSharedCheck_3674_ = !lean_is_exclusive(v___x_3623_);
if (v_isSharedCheck_3674_ == 0)
{
v___x_3669_ = v___x_3623_;
v_isShared_3670_ = v_isSharedCheck_3674_;
goto v_resetjp_3668_;
}
else
{
lean_inc(v_a_3667_);
lean_dec(v___x_3623_);
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
v___jp_3675_:
{
if (lean_obj_tag(v___y_3676_) == 0)
{
lean_dec_ref_known(v___y_3676_, 1);
goto v___jp_3621_;
}
else
{
lean_dec(v___x_3620_);
return v___y_3676_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v___x_3682_, lean_object* v_args_3683_, lean_object* v_ty_3684_, lean_object* v___y_3685_, lean_object* v___y_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_){
_start:
{
lean_object* v_res_3690_; 
v_res_3690_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v___x_3682_, v_args_3683_, v_ty_3684_, v___y_3685_, v___y_3686_, v___y_3687_, v___y_3688_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec(v___y_3686_);
lean_dec_ref(v___y_3685_);
lean_dec_ref(v_args_3683_);
lean_dec_ref(v___x_3682_);
return v_res_3690_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object* v_e_3691_){
_start:
{
lean_object* v___x_3692_; 
v___x_3692_ = l_Lean_Expr_cleanupAnnotations(v_e_3691_);
switch(lean_obj_tag(v___x_3692_))
{
case 7:
{
lean_object* v_body_3693_; uint8_t v_binderInfo_3694_; uint8_t v___x_3695_; 
v_body_3693_ = lean_ctor_get(v___x_3692_, 2);
lean_inc_ref(v_body_3693_);
v_binderInfo_3694_ = lean_ctor_get_uint8(v___x_3692_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3692_, 3);
v___x_3695_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3694_);
if (v___x_3695_ == 0)
{
lean_object* v___x_3696_; uint8_t v___x_3697_; 
v___x_3696_ = lean_unsigned_to_nat(0u);
v___x_3697_ = lean_expr_has_loose_bvar(v_body_3693_, v___x_3696_);
if (v___x_3697_ == 0)
{
uint8_t v___x_3698_; 
lean_dec_ref(v_body_3693_);
v___x_3698_ = 1;
return v___x_3698_;
}
else
{
v_e_3691_ = v_body_3693_;
goto _start;
}
}
else
{
v_e_3691_ = v_body_3693_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3701_; 
v_body_3701_ = lean_ctor_get(v___x_3692_, 3);
lean_inc_ref(v_body_3701_);
lean_dec_ref_known(v___x_3692_, 4);
v_e_3691_ = v_body_3701_;
goto _start;
}
default: 
{
uint8_t v___x_3703_; 
lean_dec_ref(v___x_3692_);
v___x_3703_ = 0;
return v___x_3703_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_e_3704_){
_start:
{
uint8_t v_res_3705_; lean_object* v_r_3706_; 
v_res_3705_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_e_3704_);
v_r_3706_ = lean_box(v_res_3705_);
return v_r_3706_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_cinfo_3707_, lean_object* v_a_3708_, lean_object* v_a_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_){
_start:
{
lean_object* v___x_3713_; uint8_t v___x_3714_; 
v___x_3713_ = l_Lean_ConstantInfo_type(v_cinfo_3707_);
lean_inc_ref(v___x_3713_);
v___x_3714_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(v___x_3713_);
if (v___x_3714_ == 0)
{
lean_object* v___x_3715_; lean_object* v___x_3716_; 
lean_dec_ref(v___x_3713_);
v___x_3715_ = lean_box(0);
v___x_3716_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3716_, 0, v___x_3715_);
return v___x_3716_;
}
else
{
lean_object* v___f_3717_; uint8_t v___x_3718_; lean_object* v___x_3719_; 
lean_inc_ref(v___x_3713_);
v___f_3717_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3717_, 0, v___x_3713_);
v___x_3718_ = 0;
v___x_3719_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v___x_3713_, v___f_3717_, v___x_3718_, v_a_3708_, v_a_3709_, v_a_3710_, v_a_3711_);
return v___x_3719_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_cinfo_3720_, lean_object* v_a_3721_, lean_object* v_a_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_){
_start:
{
lean_object* v_res_3726_; 
v_res_3726_ = l_Lean_Meta_checkImpossibleInstance(v_cinfo_3720_, v_a_3721_, v_a_3722_, v_a_3723_, v_a_3724_);
lean_dec(v_a_3724_);
lean_dec_ref(v_a_3723_);
lean_dec(v_a_3722_);
lean_dec_ref(v_a_3721_);
lean_dec_ref(v_cinfo_3720_);
return v_res_3726_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v_00_u03b2_3727_, lean_object* v_k_3728_, lean_object* v_t_3729_){
_start:
{
uint8_t v___x_3730_; 
v___x_3730_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3728_, v_t_3729_);
return v___x_3730_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v_00_u03b2_3731_, lean_object* v_k_3732_, lean_object* v_t_3733_){
_start:
{
uint8_t v_res_3734_; lean_object* v_r_3735_; 
v_res_3734_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(v_00_u03b2_3731_, v_k_3732_, v_t_3733_);
lean_dec(v_t_3733_);
lean_dec(v_k_3732_);
v_r_3735_ = lean_box(v_res_3734_);
return v_r_3735_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_a_3736_, lean_object* v_as_3737_, size_t v_sz_3738_, size_t v_i_3739_, lean_object* v_b_3740_, lean_object* v___y_3741_, lean_object* v___y_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_){
_start:
{
lean_object* v___x_3746_; 
v___x_3746_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3736_, v_as_3737_, v_sz_3738_, v_i_3739_, v_b_3740_, v___y_3741_, v___y_3743_, v___y_3744_);
return v___x_3746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_a_3747_, lean_object* v_as_3748_, lean_object* v_sz_3749_, lean_object* v_i_3750_, lean_object* v_b_3751_, lean_object* v___y_3752_, lean_object* v___y_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_){
_start:
{
size_t v_sz_boxed_3757_; size_t v_i_boxed_3758_; lean_object* v_res_3759_; 
v_sz_boxed_3757_ = lean_unbox_usize(v_sz_3749_);
lean_dec(v_sz_3749_);
v_i_boxed_3758_ = lean_unbox_usize(v_i_3750_);
lean_dec(v_i_3750_);
v_res_3759_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_a_3747_, v_as_3748_, v_sz_boxed_3757_, v_i_boxed_3758_, v_b_3751_, v___y_3752_, v___y_3753_, v___y_3754_, v___y_3755_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec(v___y_3753_);
lean_dec_ref(v___y_3752_);
lean_dec_ref(v_as_3748_);
lean_dec_ref(v_a_3747_);
return v_res_3759_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object* v_as_3760_, size_t v_sz_3761_, size_t v_i_3762_, lean_object* v_b_3763_, lean_object* v___y_3764_, lean_object* v___y_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_){
_start:
{
lean_object* v___x_3770_; 
v___x_3770_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_as_3760_, v_sz_3761_, v_i_3762_, v_b_3763_, v___y_3764_, v___y_3765_, v___y_3767_, v___y_3768_);
return v___x_3770_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object* v_as_3771_, lean_object* v_sz_3772_, lean_object* v_i_3773_, lean_object* v_b_3774_, lean_object* v___y_3775_, lean_object* v___y_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_){
_start:
{
size_t v_sz_boxed_3781_; size_t v_i_boxed_3782_; lean_object* v_res_3783_; 
v_sz_boxed_3781_ = lean_unbox_usize(v_sz_3772_);
lean_dec(v_sz_3772_);
v_i_boxed_3782_ = lean_unbox_usize(v_i_3773_);
lean_dec(v_i_3773_);
v_res_3783_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(v_as_3771_, v_sz_boxed_3781_, v_i_boxed_3782_, v_b_3774_, v___y_3775_, v___y_3776_, v___y_3777_, v___y_3778_, v___y_3779_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v___y_3776_);
lean_dec(v___y_3775_);
lean_dec_ref(v_as_3771_);
return v_res_3783_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3785_; lean_object* v___x_3786_; 
v___x_3785_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3786_ = l_Lean_stringToMessageData(v___x_3785_);
return v___x_3786_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3788_; lean_object* v___x_3789_; 
v___x_3788_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3789_ = l_Lean_stringToMessageData(v___x_3788_);
return v___x_3789_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3791_; lean_object* v___x_3792_; 
v___x_3791_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3792_ = l_Lean_stringToMessageData(v___x_3791_);
return v___x_3792_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_c_3793_, lean_object* v_x_3794_, lean_object* v_target_3795_, lean_object* v___y_3796_, lean_object* v___y_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_){
_start:
{
lean_object* v___x_3801_; 
lean_inc_ref(v_target_3795_);
v___x_3801_ = l_Lean_Meta_isClass_x3f(v_target_3795_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
if (lean_obj_tag(v___x_3801_) == 0)
{
lean_object* v_a_3802_; lean_object* v___x_3804_; uint8_t v_isShared_3805_; uint8_t v_isSharedCheck_3820_; 
v_a_3802_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3820_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3820_ == 0)
{
v___x_3804_ = v___x_3801_;
v_isShared_3805_ = v_isSharedCheck_3820_;
goto v_resetjp_3803_;
}
else
{
lean_inc(v_a_3802_);
lean_dec(v___x_3801_);
v___x_3804_ = lean_box(0);
v_isShared_3805_ = v_isSharedCheck_3820_;
goto v_resetjp_3803_;
}
v_resetjp_3803_:
{
if (lean_obj_tag(v_a_3802_) == 0)
{
lean_object* v___x_3806_; lean_object* v___x_3807_; lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; 
lean_del_object(v___x_3804_);
v___x_3806_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3807_ = l_Lean_MessageData_ofExpr(v_c_3793_);
v___x_3808_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3808_, 0, v___x_3806_);
lean_ctor_set(v___x_3808_, 1, v___x_3807_);
v___x_3809_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3808_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = l_Lean_MessageData_ofExpr(v_target_3795_);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3814_, v___y_3796_, v___y_3797_, v___y_3798_, v___y_3799_);
return v___x_3815_;
}
else
{
lean_object* v___x_3816_; lean_object* v___x_3818_; 
lean_dec_ref_known(v_a_3802_, 1);
lean_dec_ref(v_target_3795_);
lean_dec_ref(v_c_3793_);
v___x_3816_ = lean_box(0);
if (v_isShared_3805_ == 0)
{
lean_ctor_set(v___x_3804_, 0, v___x_3816_);
v___x_3818_ = v___x_3804_;
goto v_reusejp_3817_;
}
else
{
lean_object* v_reuseFailAlloc_3819_; 
v_reuseFailAlloc_3819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3819_, 0, v___x_3816_);
v___x_3818_ = v_reuseFailAlloc_3819_;
goto v_reusejp_3817_;
}
v_reusejp_3817_:
{
return v___x_3818_;
}
}
}
}
else
{
lean_object* v_a_3821_; lean_object* v___x_3823_; uint8_t v_isShared_3824_; uint8_t v_isSharedCheck_3828_; 
lean_dec_ref(v_target_3795_);
lean_dec_ref(v_c_3793_);
v_a_3821_ = lean_ctor_get(v___x_3801_, 0);
v_isSharedCheck_3828_ = !lean_is_exclusive(v___x_3801_);
if (v_isSharedCheck_3828_ == 0)
{
v___x_3823_ = v___x_3801_;
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
else
{
lean_inc(v_a_3821_);
lean_dec(v___x_3801_);
v___x_3823_ = lean_box(0);
v_isShared_3824_ = v_isSharedCheck_3828_;
goto v_resetjp_3822_;
}
v_resetjp_3822_:
{
lean_object* v___x_3826_; 
if (v_isShared_3824_ == 0)
{
v___x_3826_ = v___x_3823_;
goto v_reusejp_3825_;
}
else
{
lean_object* v_reuseFailAlloc_3827_; 
v_reuseFailAlloc_3827_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3827_, 0, v_a_3821_);
v___x_3826_ = v_reuseFailAlloc_3827_;
goto v_reusejp_3825_;
}
v_reusejp_3825_:
{
return v___x_3826_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_c_3829_, lean_object* v_x_3830_, lean_object* v_target_3831_, lean_object* v___y_3832_, lean_object* v___y_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_){
_start:
{
lean_object* v_res_3837_; 
v_res_3837_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_c_3829_, v_x_3830_, v_target_3831_, v___y_3832_, v___y_3833_, v___y_3834_, v___y_3835_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec(v___y_3833_);
lean_dec_ref(v___y_3832_);
lean_dec_ref(v_x_3830_);
return v_res_3837_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_c_3838_, lean_object* v_a_3839_, lean_object* v_a_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_){
_start:
{
lean_object* v___x_3844_; 
lean_inc(v_a_3842_);
lean_inc_ref(v_a_3841_);
lean_inc(v_a_3840_);
lean_inc_ref(v_a_3839_);
lean_inc_ref(v_c_3838_);
v___x_3844_ = lean_infer_type(v_c_3838_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
if (lean_obj_tag(v___x_3844_) == 0)
{
lean_object* v_a_3845_; lean_object* v___f_3846_; uint8_t v___x_3847_; lean_object* v___x_3848_; 
v_a_3845_ = lean_ctor_get(v___x_3844_, 0);
lean_inc(v_a_3845_);
lean_dec_ref_known(v___x_3844_, 1);
v___f_3846_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3846_, 0, v_c_3838_);
v___x_3847_ = 0;
v___x_3848_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3845_, v___f_3846_, v___x_3847_, v___x_3847_, v_a_3839_, v_a_3840_, v_a_3841_, v_a_3842_);
return v___x_3848_;
}
else
{
lean_object* v_a_3849_; lean_object* v___x_3851_; uint8_t v_isShared_3852_; uint8_t v_isSharedCheck_3856_; 
lean_dec_ref(v_c_3838_);
v_a_3849_ = lean_ctor_get(v___x_3844_, 0);
v_isSharedCheck_3856_ = !lean_is_exclusive(v___x_3844_);
if (v_isSharedCheck_3856_ == 0)
{
v___x_3851_ = v___x_3844_;
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
else
{
lean_inc(v_a_3849_);
lean_dec(v___x_3844_);
v___x_3851_ = lean_box(0);
v_isShared_3852_ = v_isSharedCheck_3856_;
goto v_resetjp_3850_;
}
v_resetjp_3850_:
{
lean_object* v___x_3854_; 
if (v_isShared_3852_ == 0)
{
v___x_3854_ = v___x_3851_;
goto v_reusejp_3853_;
}
else
{
lean_object* v_reuseFailAlloc_3855_; 
v_reuseFailAlloc_3855_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3855_, 0, v_a_3849_);
v___x_3854_ = v_reuseFailAlloc_3855_;
goto v_reusejp_3853_;
}
v_reusejp_3853_:
{
return v___x_3854_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_c_3857_, lean_object* v_a_3858_, lean_object* v_a_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_){
_start:
{
lean_object* v_res_3863_; 
v_res_3863_ = l_Lean_Meta_checkNonClassInstance(v_c_3857_, v_a_3858_, v_a_3859_, v_a_3860_, v_a_3861_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
lean_dec(v_a_3859_);
lean_dec_ref(v_a_3858_);
return v_res_3863_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3874_, lean_object* v___y_3875_){
_start:
{
lean_object* v___x_3877_; lean_object* v_env_3878_; lean_object* v___x_3879_; lean_object* v___x_3880_; 
v___x_3877_ = lean_st_ref_get(v___y_3875_);
v_env_3878_ = lean_ctor_get(v___x_3877_, 0);
lean_inc_ref(v_env_3878_);
lean_dec(v___x_3877_);
v___x_3879_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3878_, v_declName_3874_);
v___x_3880_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3880_, 0, v___x_3879_);
return v___x_3880_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3881_, lean_object* v___y_3882_, lean_object* v___y_3883_){
_start:
{
lean_object* v_res_3884_; 
v_res_3884_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3881_, v___y_3882_);
lean_dec(v___y_3882_);
return v_res_3884_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3885_, lean_object* v___y_3886_, lean_object* v___y_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_){
_start:
{
lean_object* v___x_3891_; 
v___x_3891_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3885_, v___y_3889_);
return v___x_3891_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3892_, lean_object* v___y_3893_, lean_object* v___y_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_){
_start:
{
lean_object* v_res_3898_; 
v_res_3898_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3892_, v___y_3893_, v___y_3894_, v___y_3895_, v___y_3896_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec(v___y_3894_);
lean_dec_ref(v___y_3893_);
return v_res_3898_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3899_; 
v___x_3899_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3899_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3900_; lean_object* v___x_3901_; 
v___x_3900_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3901_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3901_, 0, v___x_3900_);
return v___x_3901_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3903_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
lean_ctor_set(v___x_3903_, 1, v___x_3902_);
return v___x_3903_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3905_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
lean_ctor_set(v___x_3905_, 1, v___x_3904_);
lean_ctor_set(v___x_3905_, 2, v___x_3904_);
lean_ctor_set(v___x_3905_, 3, v___x_3904_);
lean_ctor_set(v___x_3905_, 4, v___x_3904_);
lean_ctor_set(v___x_3905_, 5, v___x_3904_);
return v___x_3905_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3906_, lean_object* v_b_3907_, uint8_t v_kind_3908_, lean_object* v___y_3909_, lean_object* v___y_3910_, lean_object* v___y_3911_){
_start:
{
lean_object* v_currNamespace_3913_; lean_object* v___x_3914_; lean_object* v_env_3915_; lean_object* v_nextMacroScope_3916_; lean_object* v_ngen_3917_; lean_object* v_auxDeclNGen_3918_; lean_object* v_traceState_3919_; lean_object* v_messages_3920_; lean_object* v_infoState_3921_; lean_object* v_snapshotTasks_3922_; lean_object* v___x_3924_; uint8_t v_isShared_3925_; uint8_t v_isSharedCheck_3949_; 
v_currNamespace_3913_ = lean_ctor_get(v___y_3910_, 6);
v___x_3914_ = lean_st_ref_take(v___y_3911_);
v_env_3915_ = lean_ctor_get(v___x_3914_, 0);
v_nextMacroScope_3916_ = lean_ctor_get(v___x_3914_, 1);
v_ngen_3917_ = lean_ctor_get(v___x_3914_, 2);
v_auxDeclNGen_3918_ = lean_ctor_get(v___x_3914_, 3);
v_traceState_3919_ = lean_ctor_get(v___x_3914_, 4);
v_messages_3920_ = lean_ctor_get(v___x_3914_, 6);
v_infoState_3921_ = lean_ctor_get(v___x_3914_, 7);
v_snapshotTasks_3922_ = lean_ctor_get(v___x_3914_, 8);
v_isSharedCheck_3949_ = !lean_is_exclusive(v___x_3914_);
if (v_isSharedCheck_3949_ == 0)
{
lean_object* v_unused_3950_; 
v_unused_3950_ = lean_ctor_get(v___x_3914_, 5);
lean_dec(v_unused_3950_);
v___x_3924_ = v___x_3914_;
v_isShared_3925_ = v_isSharedCheck_3949_;
goto v_resetjp_3923_;
}
else
{
lean_inc(v_snapshotTasks_3922_);
lean_inc(v_infoState_3921_);
lean_inc(v_messages_3920_);
lean_inc(v_traceState_3919_);
lean_inc(v_auxDeclNGen_3918_);
lean_inc(v_ngen_3917_);
lean_inc(v_nextMacroScope_3916_);
lean_inc(v_env_3915_);
lean_dec(v___x_3914_);
v___x_3924_ = lean_box(0);
v_isShared_3925_ = v_isSharedCheck_3949_;
goto v_resetjp_3923_;
}
v_resetjp_3923_:
{
lean_object* v___x_3926_; lean_object* v___x_3927_; lean_object* v___x_3929_; 
lean_inc(v_currNamespace_3913_);
v___x_3926_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3915_, v_ext_3906_, v_b_3907_, v_kind_3908_, v_currNamespace_3913_);
v___x_3927_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3925_ == 0)
{
lean_ctor_set(v___x_3924_, 5, v___x_3927_);
lean_ctor_set(v___x_3924_, 0, v___x_3926_);
v___x_3929_ = v___x_3924_;
goto v_reusejp_3928_;
}
else
{
lean_object* v_reuseFailAlloc_3948_; 
v_reuseFailAlloc_3948_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3948_, 0, v___x_3926_);
lean_ctor_set(v_reuseFailAlloc_3948_, 1, v_nextMacroScope_3916_);
lean_ctor_set(v_reuseFailAlloc_3948_, 2, v_ngen_3917_);
lean_ctor_set(v_reuseFailAlloc_3948_, 3, v_auxDeclNGen_3918_);
lean_ctor_set(v_reuseFailAlloc_3948_, 4, v_traceState_3919_);
lean_ctor_set(v_reuseFailAlloc_3948_, 5, v___x_3927_);
lean_ctor_set(v_reuseFailAlloc_3948_, 6, v_messages_3920_);
lean_ctor_set(v_reuseFailAlloc_3948_, 7, v_infoState_3921_);
lean_ctor_set(v_reuseFailAlloc_3948_, 8, v_snapshotTasks_3922_);
v___x_3929_ = v_reuseFailAlloc_3948_;
goto v_reusejp_3928_;
}
v_reusejp_3928_:
{
lean_object* v___x_3930_; lean_object* v___x_3931_; lean_object* v_mctx_3932_; lean_object* v_zetaDeltaFVarIds_3933_; lean_object* v_postponed_3934_; lean_object* v_diag_3935_; lean_object* v___x_3937_; uint8_t v_isShared_3938_; uint8_t v_isSharedCheck_3946_; 
v___x_3930_ = lean_st_ref_set(v___y_3911_, v___x_3929_);
v___x_3931_ = lean_st_ref_take(v___y_3909_);
v_mctx_3932_ = lean_ctor_get(v___x_3931_, 0);
v_zetaDeltaFVarIds_3933_ = lean_ctor_get(v___x_3931_, 2);
v_postponed_3934_ = lean_ctor_get(v___x_3931_, 3);
v_diag_3935_ = lean_ctor_get(v___x_3931_, 4);
v_isSharedCheck_3946_ = !lean_is_exclusive(v___x_3931_);
if (v_isSharedCheck_3946_ == 0)
{
lean_object* v_unused_3947_; 
v_unused_3947_ = lean_ctor_get(v___x_3931_, 1);
lean_dec(v_unused_3947_);
v___x_3937_ = v___x_3931_;
v_isShared_3938_ = v_isSharedCheck_3946_;
goto v_resetjp_3936_;
}
else
{
lean_inc(v_diag_3935_);
lean_inc(v_postponed_3934_);
lean_inc(v_zetaDeltaFVarIds_3933_);
lean_inc(v_mctx_3932_);
lean_dec(v___x_3931_);
v___x_3937_ = lean_box(0);
v_isShared_3938_ = v_isSharedCheck_3946_;
goto v_resetjp_3936_;
}
v_resetjp_3936_:
{
lean_object* v___x_3939_; lean_object* v___x_3941_; 
v___x_3939_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3938_ == 0)
{
lean_ctor_set(v___x_3937_, 1, v___x_3939_);
v___x_3941_ = v___x_3937_;
goto v_reusejp_3940_;
}
else
{
lean_object* v_reuseFailAlloc_3945_; 
v_reuseFailAlloc_3945_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3945_, 0, v_mctx_3932_);
lean_ctor_set(v_reuseFailAlloc_3945_, 1, v___x_3939_);
lean_ctor_set(v_reuseFailAlloc_3945_, 2, v_zetaDeltaFVarIds_3933_);
lean_ctor_set(v_reuseFailAlloc_3945_, 3, v_postponed_3934_);
lean_ctor_set(v_reuseFailAlloc_3945_, 4, v_diag_3935_);
v___x_3941_ = v_reuseFailAlloc_3945_;
goto v_reusejp_3940_;
}
v_reusejp_3940_:
{
lean_object* v___x_3942_; lean_object* v___x_3943_; lean_object* v___x_3944_; 
v___x_3942_ = lean_st_ref_set(v___y_3909_, v___x_3941_);
v___x_3943_ = lean_box(0);
v___x_3944_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3944_, 0, v___x_3943_);
return v___x_3944_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3951_, lean_object* v_b_3952_, lean_object* v_kind_3953_, lean_object* v___y_3954_, lean_object* v___y_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_){
_start:
{
uint8_t v_kind_boxed_3958_; lean_object* v_res_3959_; 
v_kind_boxed_3958_ = lean_unbox(v_kind_3953_);
v_res_3959_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3951_, v_b_3952_, v_kind_boxed_3958_, v___y_3954_, v___y_3955_, v___y_3956_);
lean_dec(v___y_3956_);
lean_dec_ref(v___y_3955_);
lean_dec(v___y_3954_);
return v_res_3959_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3960_, lean_object* v_00_u03b2_3961_, lean_object* v_00_u03c3_3962_, lean_object* v_ext_3963_, lean_object* v_b_3964_, uint8_t v_kind_3965_, lean_object* v___y_3966_, lean_object* v___y_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_){
_start:
{
lean_object* v___x_3971_; 
v___x_3971_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3963_, v_b_3964_, v_kind_3965_, v___y_3967_, v___y_3968_, v___y_3969_);
return v___x_3971_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_3972_, lean_object* v_00_u03b2_3973_, lean_object* v_00_u03c3_3974_, lean_object* v_ext_3975_, lean_object* v_b_3976_, lean_object* v_kind_3977_, lean_object* v___y_3978_, lean_object* v___y_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_){
_start:
{
uint8_t v_kind_boxed_3983_; lean_object* v_res_3984_; 
v_kind_boxed_3983_ = lean_unbox(v_kind_3977_);
v_res_3984_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_3972_, v_00_u03b2_3973_, v_00_u03c3_3974_, v_ext_3975_, v_b_3976_, v_kind_boxed_3983_, v___y_3978_, v___y_3979_, v___y_3980_, v___y_3981_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
lean_dec(v___y_3979_);
lean_dec_ref(v___y_3978_);
return v_res_3984_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_3985_, lean_object* v___y_3986_){
_start:
{
lean_object* v___x_3988_; lean_object* v_env_3989_; uint8_t v___x_3990_; lean_object* v___x_3991_; lean_object* v___x_3992_; 
v___x_3988_ = lean_st_ref_get(v___y_3986_);
v_env_3989_ = lean_ctor_get(v___x_3988_, 0);
lean_inc_ref(v_env_3989_);
lean_dec(v___x_3988_);
v___x_3990_ = l_Lean_getReducibilityStatusCore(v_env_3989_, v_declName_3985_);
v___x_3991_ = lean_box(v___x_3990_);
v___x_3992_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3992_, 0, v___x_3991_);
return v___x_3992_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_3993_, lean_object* v___y_3994_, lean_object* v___y_3995_){
_start:
{
lean_object* v_res_3996_; 
v_res_3996_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3993_, v___y_3994_);
lean_dec(v___y_3994_);
return v_res_3996_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_3997_, lean_object* v___y_3998_, lean_object* v___y_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_){
_start:
{
lean_object* v___x_4003_; 
v___x_4003_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3997_, v___y_4001_);
return v___x_4003_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_4004_, lean_object* v___y_4005_, lean_object* v___y_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_){
_start:
{
lean_object* v_res_4010_; 
v_res_4010_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_4004_, v___y_4005_, v___y_4006_, v___y_4007_, v___y_4008_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
lean_dec(v___y_4006_);
lean_dec_ref(v___y_4005_);
return v_res_4010_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_4011_, lean_object* v_msg_4012_, lean_object* v___y_4013_, lean_object* v___y_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_){
_start:
{
lean_object* v_fileName_4018_; lean_object* v_fileMap_4019_; lean_object* v_options_4020_; lean_object* v_currRecDepth_4021_; lean_object* v_maxRecDepth_4022_; lean_object* v_ref_4023_; lean_object* v_currNamespace_4024_; lean_object* v_openDecls_4025_; lean_object* v_initHeartbeats_4026_; lean_object* v_maxHeartbeats_4027_; lean_object* v_quotContext_4028_; lean_object* v_currMacroScope_4029_; uint8_t v_diag_4030_; lean_object* v_cancelTk_x3f_4031_; uint8_t v_suppressElabErrors_4032_; lean_object* v_inheritedTraceOptions_4033_; lean_object* v_ref_4034_; lean_object* v___x_4035_; lean_object* v___x_4036_; 
v_fileName_4018_ = lean_ctor_get(v___y_4015_, 0);
v_fileMap_4019_ = lean_ctor_get(v___y_4015_, 1);
v_options_4020_ = lean_ctor_get(v___y_4015_, 2);
v_currRecDepth_4021_ = lean_ctor_get(v___y_4015_, 3);
v_maxRecDepth_4022_ = lean_ctor_get(v___y_4015_, 4);
v_ref_4023_ = lean_ctor_get(v___y_4015_, 5);
v_currNamespace_4024_ = lean_ctor_get(v___y_4015_, 6);
v_openDecls_4025_ = lean_ctor_get(v___y_4015_, 7);
v_initHeartbeats_4026_ = lean_ctor_get(v___y_4015_, 8);
v_maxHeartbeats_4027_ = lean_ctor_get(v___y_4015_, 9);
v_quotContext_4028_ = lean_ctor_get(v___y_4015_, 10);
v_currMacroScope_4029_ = lean_ctor_get(v___y_4015_, 11);
v_diag_4030_ = lean_ctor_get_uint8(v___y_4015_, sizeof(void*)*14);
v_cancelTk_x3f_4031_ = lean_ctor_get(v___y_4015_, 12);
v_suppressElabErrors_4032_ = lean_ctor_get_uint8(v___y_4015_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4033_ = lean_ctor_get(v___y_4015_, 13);
v_ref_4034_ = l_Lean_replaceRef(v_ref_4011_, v_ref_4023_);
lean_inc_ref(v_inheritedTraceOptions_4033_);
lean_inc(v_cancelTk_x3f_4031_);
lean_inc(v_currMacroScope_4029_);
lean_inc(v_quotContext_4028_);
lean_inc(v_maxHeartbeats_4027_);
lean_inc(v_initHeartbeats_4026_);
lean_inc(v_openDecls_4025_);
lean_inc(v_currNamespace_4024_);
lean_inc(v_maxRecDepth_4022_);
lean_inc(v_currRecDepth_4021_);
lean_inc_ref(v_options_4020_);
lean_inc_ref(v_fileMap_4019_);
lean_inc_ref(v_fileName_4018_);
v___x_4035_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4035_, 0, v_fileName_4018_);
lean_ctor_set(v___x_4035_, 1, v_fileMap_4019_);
lean_ctor_set(v___x_4035_, 2, v_options_4020_);
lean_ctor_set(v___x_4035_, 3, v_currRecDepth_4021_);
lean_ctor_set(v___x_4035_, 4, v_maxRecDepth_4022_);
lean_ctor_set(v___x_4035_, 5, v_ref_4034_);
lean_ctor_set(v___x_4035_, 6, v_currNamespace_4024_);
lean_ctor_set(v___x_4035_, 7, v_openDecls_4025_);
lean_ctor_set(v___x_4035_, 8, v_initHeartbeats_4026_);
lean_ctor_set(v___x_4035_, 9, v_maxHeartbeats_4027_);
lean_ctor_set(v___x_4035_, 10, v_quotContext_4028_);
lean_ctor_set(v___x_4035_, 11, v_currMacroScope_4029_);
lean_ctor_set(v___x_4035_, 12, v_cancelTk_x3f_4031_);
lean_ctor_set(v___x_4035_, 13, v_inheritedTraceOptions_4033_);
lean_ctor_set_uint8(v___x_4035_, sizeof(void*)*14, v_diag_4030_);
lean_ctor_set_uint8(v___x_4035_, sizeof(void*)*14 + 1, v_suppressElabErrors_4032_);
v___x_4036_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_4012_, v___y_4013_, v___y_4014_, v___x_4035_, v___y_4016_);
lean_dec_ref_known(v___x_4035_, 14);
return v___x_4036_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_4037_, lean_object* v_msg_4038_, lean_object* v___y_4039_, lean_object* v___y_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_){
_start:
{
lean_object* v_res_4044_; 
v_res_4044_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4037_, v_msg_4038_, v___y_4039_, v___y_4040_, v___y_4041_, v___y_4042_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v___y_4040_);
lean_dec_ref(v___y_4039_);
lean_dec(v_ref_4037_);
return v_res_4044_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_4045_; 
v___x_4045_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4045_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_4046_; lean_object* v___x_4047_; 
v___x_4046_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4047_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4047_, 0, v___x_4046_);
return v___x_4047_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; lean_object* v___x_4050_; 
v___x_4048_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4049_ = lean_unsigned_to_nat(0u);
v___x_4050_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4050_, 0, v___x_4049_);
lean_ctor_set(v___x_4050_, 1, v___x_4049_);
lean_ctor_set(v___x_4050_, 2, v___x_4049_);
lean_ctor_set(v___x_4050_, 3, v___x_4049_);
lean_ctor_set(v___x_4050_, 4, v___x_4048_);
lean_ctor_set(v___x_4050_, 5, v___x_4048_);
lean_ctor_set(v___x_4050_, 6, v___x_4048_);
lean_ctor_set(v___x_4050_, 7, v___x_4048_);
lean_ctor_set(v___x_4050_, 8, v___x_4048_);
lean_ctor_set(v___x_4050_, 9, v___x_4048_);
return v___x_4050_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_4051_; lean_object* v___x_4052_; lean_object* v___x_4053_; 
v___x_4051_ = lean_unsigned_to_nat(32u);
v___x_4052_ = lean_mk_empty_array_with_capacity(v___x_4051_);
v___x_4053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4053_, 0, v___x_4052_);
return v___x_4053_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_4054_; lean_object* v___x_4055_; lean_object* v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; 
v___x_4054_ = ((size_t)5ULL);
v___x_4055_ = lean_unsigned_to_nat(0u);
v___x_4056_ = lean_unsigned_to_nat(32u);
v___x_4057_ = lean_mk_empty_array_with_capacity(v___x_4056_);
v___x_4058_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4059_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4059_, 0, v___x_4058_);
lean_ctor_set(v___x_4059_, 1, v___x_4057_);
lean_ctor_set(v___x_4059_, 2, v___x_4055_);
lean_ctor_set(v___x_4059_, 3, v___x_4055_);
lean_ctor_set_usize(v___x_4059_, 4, v___x_4054_);
return v___x_4059_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_4060_; lean_object* v___x_4061_; lean_object* v___x_4062_; lean_object* v___x_4063_; 
v___x_4060_ = lean_box(1);
v___x_4061_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_4062_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4063_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4063_, 0, v___x_4062_);
lean_ctor_set(v___x_4063_, 1, v___x_4061_);
lean_ctor_set(v___x_4063_, 2, v___x_4060_);
return v___x_4063_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_4065_; lean_object* v___x_4066_; 
v___x_4065_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_4066_ = l_Lean_stringToMessageData(v___x_4065_);
return v___x_4066_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_4068_; lean_object* v___x_4069_; 
v___x_4068_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_4069_ = l_Lean_stringToMessageData(v___x_4068_);
return v___x_4069_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_4071_; lean_object* v___x_4072_; 
v___x_4071_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_4072_ = l_Lean_stringToMessageData(v___x_4071_);
return v___x_4072_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_4074_; lean_object* v___x_4075_; 
v___x_4074_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_4075_ = l_Lean_stringToMessageData(v___x_4074_);
return v___x_4075_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_4077_; lean_object* v___x_4078_; 
v___x_4077_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_4078_ = l_Lean_stringToMessageData(v___x_4077_);
return v___x_4078_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_4080_; lean_object* v___x_4081_; 
v___x_4080_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_4081_ = l_Lean_stringToMessageData(v___x_4080_);
return v___x_4081_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_4083_; lean_object* v___x_4084_; 
v___x_4083_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_4084_ = l_Lean_stringToMessageData(v___x_4083_);
return v___x_4084_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_4085_, lean_object* v_declHint_4086_, lean_object* v___y_4087_){
_start:
{
lean_object* v___x_4089_; lean_object* v_env_4090_; uint8_t v___x_4091_; 
v___x_4089_ = lean_st_ref_get(v___y_4087_);
v_env_4090_ = lean_ctor_get(v___x_4089_, 0);
lean_inc_ref(v_env_4090_);
lean_dec(v___x_4089_);
v___x_4091_ = l_Lean_Name_isAnonymous(v_declHint_4086_);
if (v___x_4091_ == 0)
{
uint8_t v_isExporting_4092_; 
v_isExporting_4092_ = lean_ctor_get_uint8(v_env_4090_, sizeof(void*)*8);
if (v_isExporting_4092_ == 0)
{
lean_object* v___x_4093_; 
lean_dec_ref(v_env_4090_);
lean_dec(v_declHint_4086_);
v___x_4093_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4093_, 0, v_msg_4085_);
return v___x_4093_;
}
else
{
lean_object* v___x_4094_; uint8_t v___x_4095_; 
lean_inc_ref(v_env_4090_);
v___x_4094_ = l_Lean_Environment_setExporting(v_env_4090_, v___x_4091_);
lean_inc(v_declHint_4086_);
lean_inc_ref(v___x_4094_);
v___x_4095_ = l_Lean_Environment_contains(v___x_4094_, v_declHint_4086_, v_isExporting_4092_);
if (v___x_4095_ == 0)
{
lean_object* v___x_4096_; 
lean_dec_ref(v___x_4094_);
lean_dec_ref(v_env_4090_);
lean_dec(v_declHint_4086_);
v___x_4096_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4096_, 0, v_msg_4085_);
return v___x_4096_;
}
else
{
lean_object* v___x_4097_; lean_object* v___x_4098_; lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v_c_4102_; lean_object* v___x_4103_; 
v___x_4097_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4098_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_4099_ = l_Lean_Options_empty;
v___x_4100_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4094_);
lean_ctor_set(v___x_4100_, 1, v___x_4097_);
lean_ctor_set(v___x_4100_, 2, v___x_4098_);
lean_ctor_set(v___x_4100_, 3, v___x_4099_);
lean_inc(v_declHint_4086_);
v___x_4101_ = l_Lean_MessageData_ofConstName(v_declHint_4086_, v___x_4091_);
v_c_4102_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4102_, 0, v___x_4100_);
lean_ctor_set(v_c_4102_, 1, v___x_4101_);
v___x_4103_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4090_, v_declHint_4086_);
if (lean_obj_tag(v___x_4103_) == 0)
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; 
lean_dec_ref(v_env_4090_);
lean_dec(v_declHint_4086_);
v___x_4104_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4105_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4105_, 0, v___x_4104_);
lean_ctor_set(v___x_4105_, 1, v_c_4102_);
v___x_4106_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_4107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4105_);
lean_ctor_set(v___x_4107_, 1, v___x_4106_);
v___x_4108_ = l_Lean_MessageData_note(v___x_4107_);
v___x_4109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4109_, 0, v_msg_4085_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
v___x_4110_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4110_, 0, v___x_4109_);
return v___x_4110_;
}
else
{
lean_object* v_val_4111_; lean_object* v___x_4113_; uint8_t v_isShared_4114_; uint8_t v_isSharedCheck_4146_; 
v_val_4111_ = lean_ctor_get(v___x_4103_, 0);
v_isSharedCheck_4146_ = !lean_is_exclusive(v___x_4103_);
if (v_isSharedCheck_4146_ == 0)
{
v___x_4113_ = v___x_4103_;
v_isShared_4114_ = v_isSharedCheck_4146_;
goto v_resetjp_4112_;
}
else
{
lean_inc(v_val_4111_);
lean_dec(v___x_4103_);
v___x_4113_ = lean_box(0);
v_isShared_4114_ = v_isSharedCheck_4146_;
goto v_resetjp_4112_;
}
v_resetjp_4112_:
{
lean_object* v___x_4115_; lean_object* v___x_4116_; lean_object* v___x_4117_; lean_object* v_mod_4118_; uint8_t v___x_4119_; 
v___x_4115_ = lean_box(0);
v___x_4116_ = l_Lean_Environment_header(v_env_4090_);
lean_dec_ref(v_env_4090_);
v___x_4117_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4116_);
v_mod_4118_ = lean_array_get(v___x_4115_, v___x_4117_, v_val_4111_);
lean_dec(v_val_4111_);
lean_dec_ref(v___x_4117_);
v___x_4119_ = l_Lean_isPrivateName(v_declHint_4086_);
lean_dec(v_declHint_4086_);
if (v___x_4119_ == 0)
{
lean_object* v___x_4120_; lean_object* v___x_4121_; lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4131_; 
v___x_4120_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_4121_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4121_, 0, v___x_4120_);
lean_ctor_set(v___x_4121_, 1, v_c_4102_);
v___x_4122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_4123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4121_);
lean_ctor_set(v___x_4123_, 1, v___x_4122_);
v___x_4124_ = l_Lean_MessageData_ofName(v_mod_4118_);
v___x_4125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4123_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_4127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4125_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = l_Lean_MessageData_note(v___x_4127_);
v___x_4129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4129_, 0, v_msg_4085_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
if (v_isShared_4114_ == 0)
{
lean_ctor_set_tag(v___x_4113_, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4129_);
v___x_4131_ = v___x_4113_;
goto v_reusejp_4130_;
}
else
{
lean_object* v_reuseFailAlloc_4132_; 
v_reuseFailAlloc_4132_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4132_, 0, v___x_4129_);
v___x_4131_ = v_reuseFailAlloc_4132_;
goto v_reusejp_4130_;
}
v_reusejp_4130_:
{
return v___x_4131_;
}
}
else
{
lean_object* v___x_4133_; lean_object* v___x_4134_; lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4144_; 
v___x_4133_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4134_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4134_, 0, v___x_4133_);
lean_ctor_set(v___x_4134_, 1, v_c_4102_);
v___x_4135_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_4136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4134_);
lean_ctor_set(v___x_4136_, 1, v___x_4135_);
v___x_4137_ = l_Lean_MessageData_ofName(v_mod_4118_);
v___x_4138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4136_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
v___x_4139_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4138_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = l_Lean_MessageData_note(v___x_4140_);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v_msg_4085_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
if (v_isShared_4114_ == 0)
{
lean_ctor_set_tag(v___x_4113_, 0);
lean_ctor_set(v___x_4113_, 0, v___x_4142_);
v___x_4144_ = v___x_4113_;
goto v_reusejp_4143_;
}
else
{
lean_object* v_reuseFailAlloc_4145_; 
v_reuseFailAlloc_4145_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4145_, 0, v___x_4142_);
v___x_4144_ = v_reuseFailAlloc_4145_;
goto v_reusejp_4143_;
}
v_reusejp_4143_:
{
return v___x_4144_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4147_; 
lean_dec_ref(v_env_4090_);
lean_dec(v_declHint_4086_);
v___x_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4147_, 0, v_msg_4085_);
return v___x_4147_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_4148_, lean_object* v_declHint_4149_, lean_object* v___y_4150_, lean_object* v___y_4151_){
_start:
{
lean_object* v_res_4152_; 
v_res_4152_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4148_, v_declHint_4149_, v___y_4150_);
lean_dec(v___y_4150_);
return v_res_4152_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(lean_object* v_msg_4153_, lean_object* v_declHint_4154_, lean_object* v___y_4155_, lean_object* v___y_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_){
_start:
{
lean_object* v___x_4160_; lean_object* v_a_4161_; lean_object* v___x_4163_; uint8_t v_isShared_4164_; uint8_t v_isSharedCheck_4170_; 
v___x_4160_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4153_, v_declHint_4154_, v___y_4158_);
v_a_4161_ = lean_ctor_get(v___x_4160_, 0);
v_isSharedCheck_4170_ = !lean_is_exclusive(v___x_4160_);
if (v_isSharedCheck_4170_ == 0)
{
v___x_4163_ = v___x_4160_;
v_isShared_4164_ = v_isSharedCheck_4170_;
goto v_resetjp_4162_;
}
else
{
lean_inc(v_a_4161_);
lean_dec(v___x_4160_);
v___x_4163_ = lean_box(0);
v_isShared_4164_ = v_isSharedCheck_4170_;
goto v_resetjp_4162_;
}
v_resetjp_4162_:
{
lean_object* v___x_4165_; lean_object* v___x_4166_; lean_object* v___x_4168_; 
v___x_4165_ = l_Lean_unknownIdentifierMessageTag;
v___x_4166_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4166_, 0, v___x_4165_);
lean_ctor_set(v___x_4166_, 1, v_a_4161_);
if (v_isShared_4164_ == 0)
{
lean_ctor_set(v___x_4163_, 0, v___x_4166_);
v___x_4168_ = v___x_4163_;
goto v_reusejp_4167_;
}
else
{
lean_object* v_reuseFailAlloc_4169_; 
v_reuseFailAlloc_4169_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4169_, 0, v___x_4166_);
v___x_4168_ = v_reuseFailAlloc_4169_;
goto v_reusejp_4167_;
}
v_reusejp_4167_:
{
return v___x_4168_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_4171_, lean_object* v_declHint_4172_, lean_object* v___y_4173_, lean_object* v___y_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_){
_start:
{
lean_object* v_res_4178_; 
v_res_4178_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4171_, v_declHint_4172_, v___y_4173_, v___y_4174_, v___y_4175_, v___y_4176_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
lean_dec(v___y_4174_);
lean_dec_ref(v___y_4173_);
return v_res_4178_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_ref_4179_, lean_object* v_msg_4180_, lean_object* v_declHint_4181_, lean_object* v___y_4182_, lean_object* v___y_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_){
_start:
{
lean_object* v___x_4187_; lean_object* v_a_4188_; lean_object* v___x_4189_; 
v___x_4187_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4180_, v_declHint_4181_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
v_a_4188_ = lean_ctor_get(v___x_4187_, 0);
lean_inc(v_a_4188_);
lean_dec_ref(v___x_4187_);
v___x_4189_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4179_, v_a_4188_, v___y_4182_, v___y_4183_, v___y_4184_, v___y_4185_);
return v___x_4189_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_ref_4190_, lean_object* v_msg_4191_, lean_object* v_declHint_4192_, lean_object* v___y_4193_, lean_object* v___y_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_){
_start:
{
lean_object* v_res_4198_; 
v_res_4198_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4190_, v_msg_4191_, v_declHint_4192_, v___y_4193_, v___y_4194_, v___y_4195_, v___y_4196_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v___y_4194_);
lean_dec_ref(v___y_4193_);
lean_dec(v_ref_4190_);
return v_res_4198_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_4200_; lean_object* v___x_4201_; 
v___x_4200_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_4201_ = l_Lean_stringToMessageData(v___x_4200_);
return v___x_4201_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_4202_, lean_object* v_constName_4203_, lean_object* v___y_4204_, lean_object* v___y_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v___x_4209_; uint8_t v___x_4210_; lean_object* v___x_4211_; lean_object* v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; 
v___x_4209_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_4210_ = 0;
lean_inc(v_constName_4203_);
v___x_4211_ = l_Lean_MessageData_ofConstName(v_constName_4203_, v___x_4210_);
v___x_4212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4212_, 0, v___x_4209_);
lean_ctor_set(v___x_4212_, 1, v___x_4211_);
v___x_4213_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4212_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
v___x_4215_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4202_, v___x_4214_, v_constName_4203_, v___y_4204_, v___y_4205_, v___y_4206_, v___y_4207_);
return v___x_4215_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_4216_, lean_object* v_constName_4217_, lean_object* v___y_4218_, lean_object* v___y_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_){
_start:
{
lean_object* v_res_4223_; 
v_res_4223_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4216_, v_constName_4217_, v___y_4218_, v___y_4219_, v___y_4220_, v___y_4221_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v___y_4219_);
lean_dec_ref(v___y_4218_);
lean_dec(v_ref_4216_);
return v_res_4223_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_4224_, lean_object* v___y_4225_, lean_object* v___y_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_){
_start:
{
lean_object* v_ref_4230_; lean_object* v___x_4231_; 
v_ref_4230_ = lean_ctor_get(v___y_4227_, 5);
v___x_4231_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4230_, v_constName_4224_, v___y_4225_, v___y_4226_, v___y_4227_, v___y_4228_);
return v___x_4231_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_4232_, lean_object* v___y_4233_, lean_object* v___y_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_){
_start:
{
lean_object* v_res_4238_; 
v_res_4238_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4232_, v___y_4233_, v___y_4234_, v___y_4235_, v___y_4236_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
lean_dec(v___y_4234_);
lean_dec_ref(v___y_4233_);
return v_res_4238_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_){
_start:
{
lean_object* v___x_4245_; lean_object* v_env_4246_; uint8_t v___x_4247_; lean_object* v___x_4248_; 
v___x_4245_ = lean_st_ref_get(v___y_4243_);
v_env_4246_ = lean_ctor_get(v___x_4245_, 0);
lean_inc_ref(v_env_4246_);
lean_dec(v___x_4245_);
v___x_4247_ = 0;
lean_inc(v_constName_4239_);
v___x_4248_ = l_Lean_Environment_find_x3f(v_env_4246_, v_constName_4239_, v___x_4247_);
if (lean_obj_tag(v___x_4248_) == 0)
{
lean_object* v___x_4249_; 
v___x_4249_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4239_, v___y_4240_, v___y_4241_, v___y_4242_, v___y_4243_);
return v___x_4249_;
}
else
{
lean_object* v_val_4250_; lean_object* v___x_4252_; uint8_t v_isShared_4253_; uint8_t v_isSharedCheck_4257_; 
lean_dec(v_constName_4239_);
v_val_4250_ = lean_ctor_get(v___x_4248_, 0);
v_isSharedCheck_4257_ = !lean_is_exclusive(v___x_4248_);
if (v_isSharedCheck_4257_ == 0)
{
v___x_4252_ = v___x_4248_;
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
else
{
lean_inc(v_val_4250_);
lean_dec(v___x_4248_);
v___x_4252_ = lean_box(0);
v_isShared_4253_ = v_isSharedCheck_4257_;
goto v_resetjp_4251_;
}
v_resetjp_4251_:
{
lean_object* v___x_4255_; 
if (v_isShared_4253_ == 0)
{
lean_ctor_set_tag(v___x_4252_, 0);
v___x_4255_ = v___x_4252_;
goto v_reusejp_4254_;
}
else
{
lean_object* v_reuseFailAlloc_4256_; 
v_reuseFailAlloc_4256_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4256_, 0, v_val_4250_);
v___x_4255_ = v_reuseFailAlloc_4256_;
goto v_reusejp_4254_;
}
v_reusejp_4254_:
{
return v___x_4255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_4258_, lean_object* v___y_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v_res_4264_; 
v_res_4264_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_4258_, v___y_4259_, v___y_4260_, v___y_4261_, v___y_4262_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
lean_dec(v___y_4260_);
lean_dec_ref(v___y_4259_);
return v_res_4264_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4265_, lean_object* v___y_4266_, lean_object* v___y_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_){
_start:
{
lean_object* v___x_4271_; lean_object* v_env_4272_; uint8_t v___x_4273_; lean_object* v___x_4274_; 
v___x_4271_ = lean_st_ref_get(v___y_4269_);
v_env_4272_ = lean_ctor_get(v___x_4271_, 0);
lean_inc_ref(v_env_4272_);
lean_dec(v___x_4271_);
v___x_4273_ = 0;
lean_inc(v_constName_4265_);
v___x_4274_ = l_Lean_Environment_findConstVal_x3f(v_env_4272_, v_constName_4265_, v___x_4273_);
if (lean_obj_tag(v___x_4274_) == 0)
{
lean_object* v___x_4275_; 
v___x_4275_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4265_, v___y_4266_, v___y_4267_, v___y_4268_, v___y_4269_);
return v___x_4275_;
}
else
{
lean_object* v_val_4276_; lean_object* v___x_4278_; uint8_t v_isShared_4279_; uint8_t v_isSharedCheck_4283_; 
lean_dec(v_constName_4265_);
v_val_4276_ = lean_ctor_get(v___x_4274_, 0);
v_isSharedCheck_4283_ = !lean_is_exclusive(v___x_4274_);
if (v_isSharedCheck_4283_ == 0)
{
v___x_4278_ = v___x_4274_;
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
else
{
lean_inc(v_val_4276_);
lean_dec(v___x_4274_);
v___x_4278_ = lean_box(0);
v_isShared_4279_ = v_isSharedCheck_4283_;
goto v_resetjp_4277_;
}
v_resetjp_4277_:
{
lean_object* v___x_4281_; 
if (v_isShared_4279_ == 0)
{
lean_ctor_set_tag(v___x_4278_, 0);
v___x_4281_ = v___x_4278_;
goto v_reusejp_4280_;
}
else
{
lean_object* v_reuseFailAlloc_4282_; 
v_reuseFailAlloc_4282_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4282_, 0, v_val_4276_);
v___x_4281_ = v_reuseFailAlloc_4282_;
goto v_reusejp_4280_;
}
v_reusejp_4280_:
{
return v___x_4281_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4284_, lean_object* v___y_4285_, lean_object* v___y_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_){
_start:
{
lean_object* v_res_4290_; 
v_res_4290_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4284_, v___y_4285_, v___y_4286_, v___y_4287_, v___y_4288_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
lean_dec(v___y_4286_);
lean_dec_ref(v___y_4285_);
return v_res_4290_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4291_, lean_object* v_a_4292_){
_start:
{
if (lean_obj_tag(v_a_4291_) == 0)
{
lean_object* v___x_4293_; 
v___x_4293_ = l_List_reverse___redArg(v_a_4292_);
return v___x_4293_;
}
else
{
lean_object* v_head_4294_; lean_object* v_tail_4295_; lean_object* v___x_4297_; uint8_t v_isShared_4298_; uint8_t v_isSharedCheck_4304_; 
v_head_4294_ = lean_ctor_get(v_a_4291_, 0);
v_tail_4295_ = lean_ctor_get(v_a_4291_, 1);
v_isSharedCheck_4304_ = !lean_is_exclusive(v_a_4291_);
if (v_isSharedCheck_4304_ == 0)
{
v___x_4297_ = v_a_4291_;
v_isShared_4298_ = v_isSharedCheck_4304_;
goto v_resetjp_4296_;
}
else
{
lean_inc(v_tail_4295_);
lean_inc(v_head_4294_);
lean_dec(v_a_4291_);
v___x_4297_ = lean_box(0);
v_isShared_4298_ = v_isSharedCheck_4304_;
goto v_resetjp_4296_;
}
v_resetjp_4296_:
{
lean_object* v___x_4299_; lean_object* v___x_4301_; 
v___x_4299_ = l_Lean_mkLevelParam(v_head_4294_);
if (v_isShared_4298_ == 0)
{
lean_ctor_set(v___x_4297_, 1, v_a_4292_);
lean_ctor_set(v___x_4297_, 0, v___x_4299_);
v___x_4301_ = v___x_4297_;
goto v_reusejp_4300_;
}
else
{
lean_object* v_reuseFailAlloc_4303_; 
v_reuseFailAlloc_4303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4303_, 0, v___x_4299_);
lean_ctor_set(v_reuseFailAlloc_4303_, 1, v_a_4292_);
v___x_4301_ = v_reuseFailAlloc_4303_;
goto v_reusejp_4300_;
}
v_reusejp_4300_:
{
v_a_4291_ = v_tail_4295_;
v_a_4292_ = v___x_4301_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4305_, lean_object* v___y_4306_, lean_object* v___y_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_){
_start:
{
lean_object* v___x_4311_; 
lean_inc(v_constName_4305_);
v___x_4311_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4305_, v___y_4306_, v___y_4307_, v___y_4308_, v___y_4309_);
if (lean_obj_tag(v___x_4311_) == 0)
{
lean_object* v_a_4312_; lean_object* v___x_4314_; uint8_t v_isShared_4315_; uint8_t v_isSharedCheck_4323_; 
v_a_4312_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4323_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4323_ == 0)
{
v___x_4314_ = v___x_4311_;
v_isShared_4315_ = v_isSharedCheck_4323_;
goto v_resetjp_4313_;
}
else
{
lean_inc(v_a_4312_);
lean_dec(v___x_4311_);
v___x_4314_ = lean_box(0);
v_isShared_4315_ = v_isSharedCheck_4323_;
goto v_resetjp_4313_;
}
v_resetjp_4313_:
{
lean_object* v_levelParams_4316_; lean_object* v___x_4317_; lean_object* v___x_4318_; lean_object* v___x_4319_; lean_object* v___x_4321_; 
v_levelParams_4316_ = lean_ctor_get(v_a_4312_, 1);
lean_inc(v_levelParams_4316_);
lean_dec(v_a_4312_);
v___x_4317_ = lean_box(0);
v___x_4318_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4316_, v___x_4317_);
v___x_4319_ = l_Lean_mkConst(v_constName_4305_, v___x_4318_);
if (v_isShared_4315_ == 0)
{
lean_ctor_set(v___x_4314_, 0, v___x_4319_);
v___x_4321_ = v___x_4314_;
goto v_reusejp_4320_;
}
else
{
lean_object* v_reuseFailAlloc_4322_; 
v_reuseFailAlloc_4322_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4322_, 0, v___x_4319_);
v___x_4321_ = v_reuseFailAlloc_4322_;
goto v_reusejp_4320_;
}
v_reusejp_4320_:
{
return v___x_4321_;
}
}
}
else
{
lean_object* v_a_4324_; lean_object* v___x_4326_; uint8_t v_isShared_4327_; uint8_t v_isSharedCheck_4331_; 
lean_dec(v_constName_4305_);
v_a_4324_ = lean_ctor_get(v___x_4311_, 0);
v_isSharedCheck_4331_ = !lean_is_exclusive(v___x_4311_);
if (v_isSharedCheck_4331_ == 0)
{
v___x_4326_ = v___x_4311_;
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
else
{
lean_inc(v_a_4324_);
lean_dec(v___x_4311_);
v___x_4326_ = lean_box(0);
v_isShared_4327_ = v_isSharedCheck_4331_;
goto v_resetjp_4325_;
}
v_resetjp_4325_:
{
lean_object* v___x_4329_; 
if (v_isShared_4327_ == 0)
{
v___x_4329_ = v___x_4326_;
goto v_reusejp_4328_;
}
else
{
lean_object* v_reuseFailAlloc_4330_; 
v_reuseFailAlloc_4330_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4330_, 0, v_a_4324_);
v___x_4329_ = v_reuseFailAlloc_4330_;
goto v_reusejp_4328_;
}
v_reusejp_4328_:
{
return v___x_4329_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4332_, lean_object* v___y_4333_, lean_object* v___y_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_){
_start:
{
lean_object* v_res_4338_; 
v_res_4338_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4332_, v___y_4333_, v___y_4334_, v___y_4335_, v___y_4336_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
lean_dec(v___y_4334_);
lean_dec_ref(v___y_4333_);
return v_res_4338_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4340_; lean_object* v___x_4341_; 
v___x_4340_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4341_ = l_Lean_stringToMessageData(v___x_4340_);
return v___x_4341_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4343_; lean_object* v___x_4344_; 
v___x_4343_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4344_ = l_Lean_stringToMessageData(v___x_4343_);
return v___x_4344_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_4346_; lean_object* v___x_4347_; 
v___x_4346_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_4347_ = l_Lean_stringToMessageData(v___x_4346_);
return v___x_4347_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__7(void){
_start:
{
lean_object* v___x_4349_; lean_object* v___x_4350_; 
v___x_4349_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__6));
v___x_4350_ = l_Lean_stringToMessageData(v___x_4349_);
return v___x_4350_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4351_, uint8_t v_attrKind_4352_, lean_object* v_prio_4353_, lean_object* v_a_4354_, lean_object* v_a_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_){
_start:
{
lean_object* v___x_4359_; 
lean_inc(v_declName_4351_);
v___x_4359_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4351_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4359_) == 0)
{
lean_object* v_a_4360_; lean_object* v___y_4362_; lean_object* v___y_4363_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4390_; lean_object* v___y_4391_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___x_4438_; 
v_a_4360_ = lean_ctor_get(v___x_4359_, 0);
lean_inc(v_a_4360_);
lean_dec_ref_known(v___x_4359_, 1);
lean_inc(v_declName_4351_);
v___x_4438_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4351_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4438_) == 0)
{
lean_object* v_a_4439_; lean_object* v___x_4440_; uint8_t v___x_4441_; 
v_a_4439_ = lean_ctor_get(v___x_4438_, 0);
lean_inc(v_a_4439_);
lean_dec_ref_known(v___x_4438_, 1);
v___x_4440_ = l_Lean_ConstantInfo_type(v_a_4439_);
v___x_4441_ = l_Lean_Expr_hasSorry(v___x_4440_);
lean_dec_ref(v___x_4440_);
if (v___x_4441_ == 0)
{
lean_object* v___x_4442_; 
lean_inc(v_a_4360_);
v___x_4442_ = l_Lean_Meta_checkNonClassInstance(v_a_4360_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
if (lean_obj_tag(v___x_4442_) == 0)
{
lean_object* v___x_4443_; 
lean_dec_ref_known(v___x_4442_, 1);
v___x_4443_ = l_Lean_Meta_checkImpossibleInstance(v_a_4439_, v_a_4354_, v_a_4355_, v_a_4356_, v_a_4357_);
lean_dec(v_a_4439_);
if (lean_obj_tag(v___x_4443_) == 0)
{
lean_dec_ref_known(v___x_4443_, 1);
v___y_4390_ = v_a_4354_;
v___y_4391_ = v_a_4355_;
v___y_4392_ = v_a_4356_;
v___y_4393_ = v_a_4357_;
goto v___jp_4389_;
}
else
{
lean_dec(v_a_4360_);
lean_dec(v_prio_4353_);
lean_dec(v_declName_4351_);
return v___x_4443_;
}
}
else
{
lean_dec(v_a_4439_);
lean_dec(v_a_4360_);
lean_dec(v_prio_4353_);
lean_dec(v_declName_4351_);
return v___x_4442_;
}
}
else
{
lean_dec(v_a_4439_);
v___y_4390_ = v_a_4354_;
v___y_4391_ = v_a_4355_;
v___y_4392_ = v_a_4356_;
v___y_4393_ = v_a_4357_;
goto v___jp_4389_;
}
}
else
{
lean_object* v_a_4444_; lean_object* v___x_4446_; uint8_t v_isShared_4447_; uint8_t v_isSharedCheck_4451_; 
lean_dec(v_a_4360_);
lean_dec(v_prio_4353_);
lean_dec(v_declName_4351_);
v_a_4444_ = lean_ctor_get(v___x_4438_, 0);
v_isSharedCheck_4451_ = !lean_is_exclusive(v___x_4438_);
if (v_isSharedCheck_4451_ == 0)
{
v___x_4446_ = v___x_4438_;
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
else
{
lean_inc(v_a_4444_);
lean_dec(v___x_4438_);
v___x_4446_ = lean_box(0);
v_isShared_4447_ = v_isSharedCheck_4451_;
goto v_resetjp_4445_;
}
v_resetjp_4445_:
{
lean_object* v___x_4449_; 
if (v_isShared_4447_ == 0)
{
v___x_4449_ = v___x_4446_;
goto v_reusejp_4448_;
}
else
{
lean_object* v_reuseFailAlloc_4450_; 
v_reuseFailAlloc_4450_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4450_, 0, v_a_4444_);
v___x_4449_ = v_reuseFailAlloc_4450_;
goto v_reusejp_4448_;
}
v_reusejp_4448_:
{
return v___x_4449_;
}
}
}
v___jp_4361_:
{
lean_object* v___x_4367_; lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4388_; 
lean_inc(v_declName_4351_);
v___x_4367_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4351_, v___y_4366_);
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4388_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4388_ == 0)
{
v___x_4370_ = v___x_4367_;
v_isShared_4371_ = v_isSharedCheck_4388_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4388_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v___x_4372_; 
lean_inc(v_a_4360_);
v___x_4372_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4360_, v_a_4368_, v___y_4363_, v___y_4364_, v___y_4365_, v___y_4366_);
if (lean_obj_tag(v___x_4372_) == 0)
{
lean_object* v_a_4373_; lean_object* v___x_4374_; lean_object* v___x_4376_; 
v_a_4373_ = lean_ctor_get(v___x_4372_, 0);
lean_inc(v_a_4373_);
lean_dec_ref_known(v___x_4372_, 1);
v___x_4374_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4371_ == 0)
{
lean_ctor_set_tag(v___x_4370_, 1);
lean_ctor_set(v___x_4370_, 0, v_declName_4351_);
v___x_4376_ = v___x_4370_;
goto v_reusejp_4375_;
}
else
{
lean_object* v_reuseFailAlloc_4379_; 
v_reuseFailAlloc_4379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4379_, 0, v_declName_4351_);
v___x_4376_ = v_reuseFailAlloc_4379_;
goto v_reusejp_4375_;
}
v_reusejp_4375_:
{
lean_object* v___x_4377_; lean_object* v___x_4378_; 
v___x_4377_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4377_, 0, v___y_4362_);
lean_ctor_set(v___x_4377_, 1, v_a_4360_);
lean_ctor_set(v___x_4377_, 2, v_prio_4353_);
lean_ctor_set(v___x_4377_, 3, v___x_4376_);
lean_ctor_set(v___x_4377_, 4, v_a_4373_);
lean_ctor_set_uint8(v___x_4377_, sizeof(void*)*5, v_attrKind_4352_);
v___x_4378_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4374_, v___x_4377_, v_attrKind_4352_, v___y_4364_, v___y_4365_, v___y_4366_);
return v___x_4378_;
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_del_object(v___x_4370_);
lean_dec_ref(v___y_4362_);
lean_dec(v_a_4360_);
lean_dec(v_prio_4353_);
lean_dec(v_declName_4351_);
v_a_4380_ = lean_ctor_get(v___x_4372_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4372_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4372_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4372_);
v___x_4382_ = lean_box(0);
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
v_resetjp_4381_:
{
lean_object* v___x_4385_; 
if (v_isShared_4383_ == 0)
{
v___x_4385_ = v___x_4382_;
goto v_reusejp_4384_;
}
else
{
lean_object* v_reuseFailAlloc_4386_; 
v_reuseFailAlloc_4386_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4386_, 0, v_a_4380_);
v___x_4385_ = v_reuseFailAlloc_4386_;
goto v_reusejp_4384_;
}
v_reusejp_4384_:
{
return v___x_4385_;
}
}
}
}
}
v___jp_4389_:
{
lean_object* v___x_4394_; 
lean_inc(v_a_4360_);
v___x_4394_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4360_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4394_) == 0)
{
lean_object* v_a_4395_; lean_object* v___x_4396_; lean_object* v_a_4397_; uint8_t v___x_4398_; uint8_t v___x_4399_; uint8_t v___x_4400_; 
v_a_4395_ = lean_ctor_get(v___x_4394_, 0);
lean_inc(v_a_4395_);
lean_dec_ref_known(v___x_4394_, 1);
lean_inc(v_declName_4351_);
v___x_4396_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4351_, v___y_4393_);
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_a_4397_);
lean_dec_ref(v___x_4396_);
v___x_4398_ = 1;
v___x_4399_ = lean_unbox(v_a_4397_);
lean_dec(v_a_4397_);
v___x_4400_ = l_Lean_instBEqReducibilityStatus_beq(v___x_4399_, v___x_4398_);
if (v___x_4400_ == 0)
{
v___y_4362_ = v_a_4395_;
v___y_4363_ = v___y_4390_;
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
goto v___jp_4361_;
}
else
{
lean_object* v___x_4401_; 
lean_inc(v_declName_4351_);
v___x_4401_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4351_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4401_) == 0)
{
lean_object* v_a_4402_; uint8_t v___x_4403_; 
v_a_4402_ = lean_ctor_get(v___x_4401_, 0);
lean_inc(v_a_4402_);
lean_dec_ref_known(v___x_4401_, 1);
v___x_4403_ = l_Lean_ConstantInfo_isDefinition(v_a_4402_);
lean_dec(v_a_4402_);
if (v___x_4403_ == 0)
{
lean_object* v___x_4404_; lean_object* v_env_4405_; uint8_t v___x_4406_; 
v___x_4404_ = lean_st_ref_get(v___y_4393_);
v_env_4405_ = lean_ctor_get(v___x_4404_, 0);
lean_inc_ref(v_env_4405_);
lean_dec(v___x_4404_);
lean_inc(v_declName_4351_);
v___x_4406_ = l_Lean_wasOriginallyDefn(v_env_4405_, v_declName_4351_);
if (v___x_4406_ == 0)
{
v___y_4362_ = v_a_4395_;
v___y_4363_ = v___y_4390_;
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
goto v___jp_4361_;
}
else
{
lean_object* v___x_4407_; lean_object* v___x_4408_; lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; 
v___x_4407_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4351_);
v___x_4408_ = l_Lean_MessageData_ofName(v_declName_4351_);
v___x_4409_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4409_, 0, v___x_4407_);
lean_ctor_set(v___x_4409_, 1, v___x_4408_);
v___x_4410_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4409_);
lean_ctor_set(v___x_4411_, 1, v___x_4410_);
v___x_4412_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4411_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_dec_ref_known(v___x_4412_, 1);
v___y_4362_ = v_a_4395_;
v___y_4363_ = v___y_4390_;
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
goto v___jp_4361_;
}
else
{
lean_dec(v_a_4395_);
lean_dec(v_a_4360_);
lean_dec(v_prio_4353_);
lean_dec(v_declName_4351_);
return v___x_4412_;
}
}
}
else
{
lean_object* v_options_4413_; lean_object* v___x_4414_; uint8_t v___x_4415_; 
v_options_4413_ = lean_ctor_get(v___y_4392_, 2);
v___x_4414_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility));
v___x_4415_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_4413_, v___x_4414_);
if (v___x_4415_ == 0)
{
v___y_4362_ = v_a_4395_;
v___y_4363_ = v___y_4390_;
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
goto v___jp_4361_;
}
else
{
lean_object* v___x_4416_; lean_object* v___x_4417_; lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; 
v___x_4416_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
lean_inc(v_declName_4351_);
v___x_4417_ = l_Lean_MessageData_ofName(v_declName_4351_);
v___x_4418_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4418_, 0, v___x_4416_);
lean_ctor_set(v___x_4418_, 1, v___x_4417_);
v___x_4419_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__7, &l_Lean_Meta_addInstance___closed__7_once, _init_l_Lean_Meta_addInstance___closed__7);
v___x_4420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4418_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
v___x_4421_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4420_, v___y_4390_, v___y_4391_, v___y_4392_, v___y_4393_);
if (lean_obj_tag(v___x_4421_) == 0)
{
lean_dec_ref_known(v___x_4421_, 1);
v___y_4362_ = v_a_4395_;
v___y_4363_ = v___y_4390_;
v___y_4364_ = v___y_4391_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
goto v___jp_4361_;
}
else
{
lean_dec(v_a_4395_);
lean_dec(v_a_4360_);
lean_dec(v_prio_4353_);
lean_dec(v_declName_4351_);
return v___x_4421_;
}
}
}
}
else
{
lean_object* v_a_4422_; lean_object* v___x_4424_; uint8_t v_isShared_4425_; uint8_t v_isSharedCheck_4429_; 
lean_dec(v_a_4395_);
lean_dec(v_a_4360_);
lean_dec(v_prio_4353_);
lean_dec(v_declName_4351_);
v_a_4422_ = lean_ctor_get(v___x_4401_, 0);
v_isSharedCheck_4429_ = !lean_is_exclusive(v___x_4401_);
if (v_isSharedCheck_4429_ == 0)
{
v___x_4424_ = v___x_4401_;
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
else
{
lean_inc(v_a_4422_);
lean_dec(v___x_4401_);
v___x_4424_ = lean_box(0);
v_isShared_4425_ = v_isSharedCheck_4429_;
goto v_resetjp_4423_;
}
v_resetjp_4423_:
{
lean_object* v___x_4427_; 
if (v_isShared_4425_ == 0)
{
v___x_4427_ = v___x_4424_;
goto v_reusejp_4426_;
}
else
{
lean_object* v_reuseFailAlloc_4428_; 
v_reuseFailAlloc_4428_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4428_, 0, v_a_4422_);
v___x_4427_ = v_reuseFailAlloc_4428_;
goto v_reusejp_4426_;
}
v_reusejp_4426_:
{
return v___x_4427_;
}
}
}
}
}
else
{
lean_object* v_a_4430_; lean_object* v___x_4432_; uint8_t v_isShared_4433_; uint8_t v_isSharedCheck_4437_; 
lean_dec(v_a_4360_);
lean_dec(v_prio_4353_);
lean_dec(v_declName_4351_);
v_a_4430_ = lean_ctor_get(v___x_4394_, 0);
v_isSharedCheck_4437_ = !lean_is_exclusive(v___x_4394_);
if (v_isSharedCheck_4437_ == 0)
{
v___x_4432_ = v___x_4394_;
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
else
{
lean_inc(v_a_4430_);
lean_dec(v___x_4394_);
v___x_4432_ = lean_box(0);
v_isShared_4433_ = v_isSharedCheck_4437_;
goto v_resetjp_4431_;
}
v_resetjp_4431_:
{
lean_object* v___x_4435_; 
if (v_isShared_4433_ == 0)
{
v___x_4435_ = v___x_4432_;
goto v_reusejp_4434_;
}
else
{
lean_object* v_reuseFailAlloc_4436_; 
v_reuseFailAlloc_4436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4436_, 0, v_a_4430_);
v___x_4435_ = v_reuseFailAlloc_4436_;
goto v_reusejp_4434_;
}
v_reusejp_4434_:
{
return v___x_4435_;
}
}
}
}
}
else
{
lean_object* v_a_4452_; lean_object* v___x_4454_; uint8_t v_isShared_4455_; uint8_t v_isSharedCheck_4459_; 
lean_dec(v_prio_4353_);
lean_dec(v_declName_4351_);
v_a_4452_ = lean_ctor_get(v___x_4359_, 0);
v_isSharedCheck_4459_ = !lean_is_exclusive(v___x_4359_);
if (v_isSharedCheck_4459_ == 0)
{
v___x_4454_ = v___x_4359_;
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
else
{
lean_inc(v_a_4452_);
lean_dec(v___x_4359_);
v___x_4454_ = lean_box(0);
v_isShared_4455_ = v_isSharedCheck_4459_;
goto v_resetjp_4453_;
}
v_resetjp_4453_:
{
lean_object* v___x_4457_; 
if (v_isShared_4455_ == 0)
{
v___x_4457_ = v___x_4454_;
goto v_reusejp_4456_;
}
else
{
lean_object* v_reuseFailAlloc_4458_; 
v_reuseFailAlloc_4458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4458_, 0, v_a_4452_);
v___x_4457_ = v_reuseFailAlloc_4458_;
goto v_reusejp_4456_;
}
v_reusejp_4456_:
{
return v___x_4457_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4460_, lean_object* v_attrKind_4461_, lean_object* v_prio_4462_, lean_object* v_a_4463_, lean_object* v_a_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_){
_start:
{
uint8_t v_attrKind_boxed_4468_; lean_object* v_res_4469_; 
v_attrKind_boxed_4468_ = lean_unbox(v_attrKind_4461_);
v_res_4469_ = l_Lean_Meta_addInstance(v_declName_4460_, v_attrKind_boxed_4468_, v_prio_4462_, v_a_4463_, v_a_4464_, v_a_4465_, v_a_4466_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
lean_dec(v_a_4464_);
lean_dec_ref(v_a_4463_);
return v_res_4469_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_4470_, lean_object* v_constName_4471_, lean_object* v___y_4472_, lean_object* v___y_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_){
_start:
{
lean_object* v___x_4477_; 
v___x_4477_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4471_, v___y_4472_, v___y_4473_, v___y_4474_, v___y_4475_);
return v___x_4477_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4478_, lean_object* v_constName_4479_, lean_object* v___y_4480_, lean_object* v___y_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_){
_start:
{
lean_object* v_res_4485_; 
v_res_4485_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_4478_, v_constName_4479_, v___y_4480_, v___y_4481_, v___y_4482_, v___y_4483_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
lean_dec(v___y_4481_);
lean_dec_ref(v___y_4480_);
return v_res_4485_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_4486_, lean_object* v_ref_4487_, lean_object* v_constName_4488_, lean_object* v___y_4489_, lean_object* v___y_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_){
_start:
{
lean_object* v___x_4494_; 
v___x_4494_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4487_, v_constName_4488_, v___y_4489_, v___y_4490_, v___y_4491_, v___y_4492_);
return v___x_4494_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4495_, lean_object* v_ref_4496_, lean_object* v_constName_4497_, lean_object* v___y_4498_, lean_object* v___y_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_){
_start:
{
lean_object* v_res_4503_; 
v_res_4503_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_4495_, v_ref_4496_, v_constName_4497_, v___y_4498_, v___y_4499_, v___y_4500_, v___y_4501_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v___y_4499_);
lean_dec_ref(v___y_4498_);
lean_dec(v_ref_4496_);
return v_res_4503_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b1_4504_, lean_object* v_ref_4505_, lean_object* v_msg_4506_, lean_object* v_declHint_4507_, lean_object* v___y_4508_, lean_object* v___y_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_){
_start:
{
lean_object* v___x_4513_; 
v___x_4513_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4505_, v_msg_4506_, v_declHint_4507_, v___y_4508_, v___y_4509_, v___y_4510_, v___y_4511_);
return v___x_4513_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4514_, lean_object* v_ref_4515_, lean_object* v_msg_4516_, lean_object* v_declHint_4517_, lean_object* v___y_4518_, lean_object* v___y_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_){
_start:
{
lean_object* v_res_4523_; 
v_res_4523_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(v_00_u03b1_4514_, v_ref_4515_, v_msg_4516_, v_declHint_4517_, v___y_4518_, v___y_4519_, v___y_4520_, v___y_4521_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v___y_4519_);
lean_dec_ref(v___y_4518_);
lean_dec(v_ref_4515_);
return v_res_4523_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_4524_, lean_object* v_declHint_4525_, lean_object* v___y_4526_, lean_object* v___y_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_){
_start:
{
lean_object* v___x_4531_; 
v___x_4531_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4524_, v_declHint_4525_, v___y_4529_);
return v___x_4531_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_4532_, lean_object* v_declHint_4533_, lean_object* v___y_4534_, lean_object* v___y_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_){
_start:
{
lean_object* v_res_4539_; 
v_res_4539_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(v_msg_4532_, v_declHint_4533_, v___y_4534_, v___y_4535_, v___y_4536_, v___y_4537_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
lean_dec(v___y_4535_);
lean_dec_ref(v___y_4534_);
return v_res_4539_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_4540_, lean_object* v_ref_4541_, lean_object* v_msg_4542_, lean_object* v___y_4543_, lean_object* v___y_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_){
_start:
{
lean_object* v___x_4548_; 
v___x_4548_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4541_, v_msg_4542_, v___y_4543_, v___y_4544_, v___y_4545_, v___y_4546_);
return v___x_4548_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4549_, lean_object* v_ref_4550_, lean_object* v_msg_4551_, lean_object* v___y_4552_, lean_object* v___y_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_){
_start:
{
lean_object* v_res_4557_; 
v_res_4557_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_4549_, v_ref_4550_, v_msg_4551_, v___y_4552_, v___y_4553_, v___y_4554_, v___y_4555_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v___y_4553_);
lean_dec_ref(v___y_4552_);
lean_dec(v_ref_4550_);
return v_res_4557_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4558_, uint8_t v_s_4559_, lean_object* v___y_4560_, lean_object* v___y_4561_){
_start:
{
lean_object* v___x_4563_; lean_object* v_env_4564_; lean_object* v_nextMacroScope_4565_; lean_object* v_ngen_4566_; lean_object* v_auxDeclNGen_4567_; lean_object* v_traceState_4568_; lean_object* v_messages_4569_; lean_object* v_infoState_4570_; lean_object* v_snapshotTasks_4571_; lean_object* v___x_4573_; uint8_t v_isShared_4574_; uint8_t v_isSharedCheck_4600_; 
v___x_4563_ = lean_st_ref_take(v___y_4561_);
v_env_4564_ = lean_ctor_get(v___x_4563_, 0);
v_nextMacroScope_4565_ = lean_ctor_get(v___x_4563_, 1);
v_ngen_4566_ = lean_ctor_get(v___x_4563_, 2);
v_auxDeclNGen_4567_ = lean_ctor_get(v___x_4563_, 3);
v_traceState_4568_ = lean_ctor_get(v___x_4563_, 4);
v_messages_4569_ = lean_ctor_get(v___x_4563_, 6);
v_infoState_4570_ = lean_ctor_get(v___x_4563_, 7);
v_snapshotTasks_4571_ = lean_ctor_get(v___x_4563_, 8);
v_isSharedCheck_4600_ = !lean_is_exclusive(v___x_4563_);
if (v_isSharedCheck_4600_ == 0)
{
lean_object* v_unused_4601_; 
v_unused_4601_ = lean_ctor_get(v___x_4563_, 5);
lean_dec(v_unused_4601_);
v___x_4573_ = v___x_4563_;
v_isShared_4574_ = v_isSharedCheck_4600_;
goto v_resetjp_4572_;
}
else
{
lean_inc(v_snapshotTasks_4571_);
lean_inc(v_infoState_4570_);
lean_inc(v_messages_4569_);
lean_inc(v_traceState_4568_);
lean_inc(v_auxDeclNGen_4567_);
lean_inc(v_ngen_4566_);
lean_inc(v_nextMacroScope_4565_);
lean_inc(v_env_4564_);
lean_dec(v___x_4563_);
v___x_4573_ = lean_box(0);
v_isShared_4574_ = v_isSharedCheck_4600_;
goto v_resetjp_4572_;
}
v_resetjp_4572_:
{
uint8_t v___x_4575_; lean_object* v___x_4576_; lean_object* v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4580_; 
v___x_4575_ = 0;
v___x_4576_ = lean_box(0);
v___x_4577_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4564_, v_declName_4558_, v_s_4559_, v___x_4575_, v___x_4576_);
v___x_4578_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4574_ == 0)
{
lean_ctor_set(v___x_4573_, 5, v___x_4578_);
lean_ctor_set(v___x_4573_, 0, v___x_4577_);
v___x_4580_ = v___x_4573_;
goto v_reusejp_4579_;
}
else
{
lean_object* v_reuseFailAlloc_4599_; 
v_reuseFailAlloc_4599_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4599_, 0, v___x_4577_);
lean_ctor_set(v_reuseFailAlloc_4599_, 1, v_nextMacroScope_4565_);
lean_ctor_set(v_reuseFailAlloc_4599_, 2, v_ngen_4566_);
lean_ctor_set(v_reuseFailAlloc_4599_, 3, v_auxDeclNGen_4567_);
lean_ctor_set(v_reuseFailAlloc_4599_, 4, v_traceState_4568_);
lean_ctor_set(v_reuseFailAlloc_4599_, 5, v___x_4578_);
lean_ctor_set(v_reuseFailAlloc_4599_, 6, v_messages_4569_);
lean_ctor_set(v_reuseFailAlloc_4599_, 7, v_infoState_4570_);
lean_ctor_set(v_reuseFailAlloc_4599_, 8, v_snapshotTasks_4571_);
v___x_4580_ = v_reuseFailAlloc_4599_;
goto v_reusejp_4579_;
}
v_reusejp_4579_:
{
lean_object* v___x_4581_; lean_object* v___x_4582_; lean_object* v_mctx_4583_; lean_object* v_zetaDeltaFVarIds_4584_; lean_object* v_postponed_4585_; lean_object* v_diag_4586_; lean_object* v___x_4588_; uint8_t v_isShared_4589_; uint8_t v_isSharedCheck_4597_; 
v___x_4581_ = lean_st_ref_set(v___y_4561_, v___x_4580_);
v___x_4582_ = lean_st_ref_take(v___y_4560_);
v_mctx_4583_ = lean_ctor_get(v___x_4582_, 0);
v_zetaDeltaFVarIds_4584_ = lean_ctor_get(v___x_4582_, 2);
v_postponed_4585_ = lean_ctor_get(v___x_4582_, 3);
v_diag_4586_ = lean_ctor_get(v___x_4582_, 4);
v_isSharedCheck_4597_ = !lean_is_exclusive(v___x_4582_);
if (v_isSharedCheck_4597_ == 0)
{
lean_object* v_unused_4598_; 
v_unused_4598_ = lean_ctor_get(v___x_4582_, 1);
lean_dec(v_unused_4598_);
v___x_4588_ = v___x_4582_;
v_isShared_4589_ = v_isSharedCheck_4597_;
goto v_resetjp_4587_;
}
else
{
lean_inc(v_diag_4586_);
lean_inc(v_postponed_4585_);
lean_inc(v_zetaDeltaFVarIds_4584_);
lean_inc(v_mctx_4583_);
lean_dec(v___x_4582_);
v___x_4588_ = lean_box(0);
v_isShared_4589_ = v_isSharedCheck_4597_;
goto v_resetjp_4587_;
}
v_resetjp_4587_:
{
lean_object* v___x_4590_; lean_object* v___x_4592_; 
v___x_4590_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_4589_ == 0)
{
lean_ctor_set(v___x_4588_, 1, v___x_4590_);
v___x_4592_ = v___x_4588_;
goto v_reusejp_4591_;
}
else
{
lean_object* v_reuseFailAlloc_4596_; 
v_reuseFailAlloc_4596_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4596_, 0, v_mctx_4583_);
lean_ctor_set(v_reuseFailAlloc_4596_, 1, v___x_4590_);
lean_ctor_set(v_reuseFailAlloc_4596_, 2, v_zetaDeltaFVarIds_4584_);
lean_ctor_set(v_reuseFailAlloc_4596_, 3, v_postponed_4585_);
lean_ctor_set(v_reuseFailAlloc_4596_, 4, v_diag_4586_);
v___x_4592_ = v_reuseFailAlloc_4596_;
goto v_reusejp_4591_;
}
v_reusejp_4591_:
{
lean_object* v___x_4593_; lean_object* v___x_4594_; lean_object* v___x_4595_; 
v___x_4593_ = lean_st_ref_set(v___y_4560_, v___x_4592_);
v___x_4594_ = lean_box(0);
v___x_4595_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4595_, 0, v___x_4594_);
return v___x_4595_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4602_, lean_object* v_s_4603_, lean_object* v___y_4604_, lean_object* v___y_4605_, lean_object* v___y_4606_){
_start:
{
uint8_t v_s_boxed_4607_; lean_object* v_res_4608_; 
v_s_boxed_4607_ = lean_unbox(v_s_4603_);
v_res_4608_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4602_, v_s_boxed_4607_, v___y_4604_, v___y_4605_);
lean_dec(v___y_4605_);
lean_dec(v___y_4604_);
return v_res_4608_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4609_, uint8_t v_s_4610_, lean_object* v___y_4611_, lean_object* v___y_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_){
_start:
{
lean_object* v___x_4616_; 
v___x_4616_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4609_, v_s_4610_, v___y_4612_, v___y_4614_);
return v___x_4616_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4617_, lean_object* v_s_4618_, lean_object* v___y_4619_, lean_object* v___y_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_){
_start:
{
uint8_t v_s_boxed_4624_; lean_object* v_res_4625_; 
v_s_boxed_4624_ = lean_unbox(v_s_4618_);
v_res_4625_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4617_, v_s_boxed_4624_, v___y_4619_, v___y_4620_, v___y_4621_, v___y_4622_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
lean_dec(v___y_4620_);
lean_dec_ref(v___y_4619_);
return v_res_4625_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4626_, uint8_t v_attrKind_4627_, lean_object* v_prio_4628_, lean_object* v_a_4629_, lean_object* v_a_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_){
_start:
{
uint8_t v___x_4634_; lean_object* v___x_4635_; lean_object* v___x_4636_; 
v___x_4634_ = 4;
lean_inc(v_declName_4626_);
v___x_4635_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4626_, v___x_4634_, v_a_4630_, v_a_4632_);
lean_dec_ref(v___x_4635_);
v___x_4636_ = l_Lean_Meta_addInstance(v_declName_4626_, v_attrKind_4627_, v_prio_4628_, v_a_4629_, v_a_4630_, v_a_4631_, v_a_4632_);
return v___x_4636_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4637_, lean_object* v_attrKind_4638_, lean_object* v_prio_4639_, lean_object* v_a_4640_, lean_object* v_a_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_){
_start:
{
uint8_t v_attrKind_boxed_4645_; lean_object* v_res_4646_; 
v_attrKind_boxed_4645_ = lean_unbox(v_attrKind_4638_);
v_res_4646_ = l_Lean_Meta_registerInstance(v_declName_4637_, v_attrKind_boxed_4645_, v_prio_4639_, v_a_4640_, v_a_4641_, v_a_4642_, v_a_4643_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
lean_dec(v_a_4641_);
lean_dec_ref(v_a_4640_);
return v_res_4646_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4647_, lean_object* v_x_4648_){
_start:
{
lean_inc_ref(v_a_4647_);
return v_a_4647_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4649_, lean_object* v_x_4650_){
_start:
{
lean_object* v_res_4651_; 
v_res_4651_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4649_, v_x_4650_);
lean_dec_ref(v_x_4650_);
lean_dec_ref(v_a_4649_);
return v_res_4651_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
lean_object* v___x_4656_; lean_object* v_env_4657_; lean_object* v_options_4658_; lean_object* v___x_4659_; lean_object* v___x_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; 
v___x_4656_ = lean_st_ref_get(v___y_4654_);
v_env_4657_ = lean_ctor_get(v___x_4656_, 0);
lean_inc_ref(v_env_4657_);
lean_dec(v___x_4656_);
v_options_4658_ = lean_ctor_get(v___y_4653_, 2);
v___x_4659_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4660_ = lean_unsigned_to_nat(32u);
v___x_4661_ = lean_mk_empty_array_with_capacity(v___x_4660_);
lean_dec_ref(v___x_4661_);
v___x_4662_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_4658_);
v___x_4663_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4663_, 0, v_env_4657_);
lean_ctor_set(v___x_4663_, 1, v___x_4659_);
lean_ctor_set(v___x_4663_, 2, v___x_4662_);
lean_ctor_set(v___x_4663_, 3, v_options_4658_);
v___x_4664_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4664_, 0, v___x_4663_);
lean_ctor_set(v___x_4664_, 1, v_msgData_4652_);
v___x_4665_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4665_, 0, v___x_4664_);
return v___x_4665_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_){
_start:
{
lean_object* v_res_4670_; 
v_res_4670_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4666_, v___y_4667_, v___y_4668_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
return v_res_4670_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4671_, lean_object* v___y_4672_, lean_object* v___y_4673_){
_start:
{
lean_object* v_ref_4675_; lean_object* v___x_4676_; lean_object* v_a_4677_; lean_object* v___x_4679_; uint8_t v_isShared_4680_; uint8_t v_isSharedCheck_4685_; 
v_ref_4675_ = lean_ctor_get(v___y_4672_, 5);
v___x_4676_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4671_, v___y_4672_, v___y_4673_);
v_a_4677_ = lean_ctor_get(v___x_4676_, 0);
v_isSharedCheck_4685_ = !lean_is_exclusive(v___x_4676_);
if (v_isSharedCheck_4685_ == 0)
{
v___x_4679_ = v___x_4676_;
v_isShared_4680_ = v_isSharedCheck_4685_;
goto v_resetjp_4678_;
}
else
{
lean_inc(v_a_4677_);
lean_dec(v___x_4676_);
v___x_4679_ = lean_box(0);
v_isShared_4680_ = v_isSharedCheck_4685_;
goto v_resetjp_4678_;
}
v_resetjp_4678_:
{
lean_object* v___x_4681_; lean_object* v___x_4683_; 
lean_inc(v_ref_4675_);
v___x_4681_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4681_, 0, v_ref_4675_);
lean_ctor_set(v___x_4681_, 1, v_a_4677_);
if (v_isShared_4680_ == 0)
{
lean_ctor_set_tag(v___x_4679_, 1);
lean_ctor_set(v___x_4679_, 0, v___x_4681_);
v___x_4683_ = v___x_4679_;
goto v_reusejp_4682_;
}
else
{
lean_object* v_reuseFailAlloc_4684_; 
v_reuseFailAlloc_4684_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4684_, 0, v___x_4681_);
v___x_4683_ = v_reuseFailAlloc_4684_;
goto v_reusejp_4682_;
}
v_reusejp_4682_:
{
return v___x_4683_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4686_, lean_object* v___y_4687_, lean_object* v___y_4688_, lean_object* v___y_4689_){
_start:
{
lean_object* v_res_4690_; 
v_res_4690_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4686_, v___y_4687_, v___y_4688_);
lean_dec(v___y_4688_);
lean_dec_ref(v___y_4687_);
return v_res_4690_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4691_, lean_object* v_i_4692_, lean_object* v_k_4693_){
_start:
{
lean_object* v___x_4694_; uint8_t v___x_4695_; 
v___x_4694_ = lean_array_get_size(v_keys_4691_);
v___x_4695_ = lean_nat_dec_lt(v_i_4692_, v___x_4694_);
if (v___x_4695_ == 0)
{
lean_dec(v_i_4692_);
return v___x_4695_;
}
else
{
lean_object* v_k_x27_4696_; uint8_t v___x_4697_; 
v_k_x27_4696_ = lean_array_fget_borrowed(v_keys_4691_, v_i_4692_);
v___x_4697_ = lean_name_eq(v_k_4693_, v_k_x27_4696_);
if (v___x_4697_ == 0)
{
lean_object* v___x_4698_; lean_object* v___x_4699_; 
v___x_4698_ = lean_unsigned_to_nat(1u);
v___x_4699_ = lean_nat_add(v_i_4692_, v___x_4698_);
lean_dec(v_i_4692_);
v_i_4692_ = v___x_4699_;
goto _start;
}
else
{
lean_dec(v_i_4692_);
return v___x_4697_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4701_, lean_object* v_i_4702_, lean_object* v_k_4703_){
_start:
{
uint8_t v_res_4704_; lean_object* v_r_4705_; 
v_res_4704_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4701_, v_i_4702_, v_k_4703_);
lean_dec(v_k_4703_);
lean_dec_ref(v_keys_4701_);
v_r_4705_ = lean_box(v_res_4704_);
return v_r_4705_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4706_, size_t v_x_4707_, lean_object* v_x_4708_){
_start:
{
if (lean_obj_tag(v_x_4706_) == 0)
{
lean_object* v_es_4709_; lean_object* v___x_4710_; size_t v___x_4711_; size_t v___x_4712_; lean_object* v_j_4713_; lean_object* v___x_4714_; 
v_es_4709_ = lean_ctor_get(v_x_4706_, 0);
v___x_4710_ = lean_box(2);
v___x_4711_ = ((size_t)31ULL);
v___x_4712_ = lean_usize_land(v_x_4707_, v___x_4711_);
v_j_4713_ = lean_usize_to_nat(v___x_4712_);
v___x_4714_ = lean_array_get_borrowed(v___x_4710_, v_es_4709_, v_j_4713_);
lean_dec(v_j_4713_);
switch(lean_obj_tag(v___x_4714_))
{
case 0:
{
lean_object* v_key_4715_; uint8_t v___x_4716_; 
v_key_4715_ = lean_ctor_get(v___x_4714_, 0);
v___x_4716_ = lean_name_eq(v_x_4708_, v_key_4715_);
return v___x_4716_;
}
case 1:
{
lean_object* v_node_4717_; size_t v___x_4718_; size_t v___x_4719_; 
v_node_4717_ = lean_ctor_get(v___x_4714_, 0);
v___x_4718_ = ((size_t)5ULL);
v___x_4719_ = lean_usize_shift_right(v_x_4707_, v___x_4718_);
v_x_4706_ = v_node_4717_;
v_x_4707_ = v___x_4719_;
goto _start;
}
default: 
{
uint8_t v___x_4721_; 
v___x_4721_ = 0;
return v___x_4721_;
}
}
}
else
{
lean_object* v_ks_4722_; lean_object* v___x_4723_; uint8_t v___x_4724_; 
v_ks_4722_ = lean_ctor_get(v_x_4706_, 0);
v___x_4723_ = lean_unsigned_to_nat(0u);
v___x_4724_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4722_, v___x_4723_, v_x_4708_);
return v___x_4724_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4725_, lean_object* v_x_4726_, lean_object* v_x_4727_){
_start:
{
size_t v_x_2345__boxed_4728_; uint8_t v_res_4729_; lean_object* v_r_4730_; 
v_x_2345__boxed_4728_ = lean_unbox_usize(v_x_4726_);
lean_dec(v_x_4726_);
v_res_4729_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4725_, v_x_2345__boxed_4728_, v_x_4727_);
lean_dec(v_x_4727_);
lean_dec_ref(v_x_4725_);
v_r_4730_ = lean_box(v_res_4729_);
return v_r_4730_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4731_, lean_object* v_x_4732_){
_start:
{
uint64_t v___y_4734_; 
if (lean_obj_tag(v_x_4732_) == 0)
{
uint64_t v___x_4737_; 
v___x_4737_ = 1723ULL;
v___y_4734_ = v___x_4737_;
goto v___jp_4733_;
}
else
{
uint64_t v_hash_4738_; 
v_hash_4738_ = lean_ctor_get_uint64(v_x_4732_, sizeof(void*)*2);
v___y_4734_ = v_hash_4738_;
goto v___jp_4733_;
}
v___jp_4733_:
{
size_t v___x_4735_; uint8_t v___x_4736_; 
v___x_4735_ = lean_uint64_to_usize(v___y_4734_);
v___x_4736_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4731_, v___x_4735_, v_x_4732_);
return v___x_4736_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4739_, lean_object* v_x_4740_){
_start:
{
uint8_t v_res_4741_; lean_object* v_r_4742_; 
v_res_4741_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4739_, v_x_4740_);
lean_dec(v_x_4740_);
lean_dec_ref(v_x_4739_);
v_r_4742_ = lean_box(v_res_4741_);
return v_r_4742_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4743_, lean_object* v_declName_4744_, lean_object* v___y_4745_, lean_object* v___y_4746_){
_start:
{
lean_object* v_instanceNames_4751_; uint8_t v___x_4752_; 
v_instanceNames_4751_ = lean_ctor_get(v_d_4743_, 1);
v___x_4752_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4751_, v_declName_4744_);
if (v___x_4752_ == 0)
{
lean_object* v___x_4753_; lean_object* v___x_4754_; lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v_a_4759_; lean_object* v___x_4761_; uint8_t v_isShared_4762_; uint8_t v_isSharedCheck_4766_; 
lean_dec_ref(v_d_4743_);
v___x_4753_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4754_ = l_Lean_MessageData_ofConstName(v_declName_4744_, v___x_4752_);
v___x_4755_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4755_, 0, v___x_4753_);
lean_ctor_set(v___x_4755_, 1, v___x_4754_);
v___x_4756_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4755_);
lean_ctor_set(v___x_4757_, 1, v___x_4756_);
v___x_4758_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4757_, v___y_4745_, v___y_4746_);
v_a_4759_ = lean_ctor_get(v___x_4758_, 0);
v_isSharedCheck_4766_ = !lean_is_exclusive(v___x_4758_);
if (v_isSharedCheck_4766_ == 0)
{
v___x_4761_ = v___x_4758_;
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
else
{
lean_inc(v_a_4759_);
lean_dec(v___x_4758_);
v___x_4761_ = lean_box(0);
v_isShared_4762_ = v_isSharedCheck_4766_;
goto v_resetjp_4760_;
}
v_resetjp_4760_:
{
lean_object* v___x_4764_; 
if (v_isShared_4762_ == 0)
{
v___x_4764_ = v___x_4761_;
goto v_reusejp_4763_;
}
else
{
lean_object* v_reuseFailAlloc_4765_; 
v_reuseFailAlloc_4765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4765_, 0, v_a_4759_);
v___x_4764_ = v_reuseFailAlloc_4765_;
goto v_reusejp_4763_;
}
v_reusejp_4763_:
{
return v___x_4764_;
}
}
}
else
{
goto v___jp_4748_;
}
v___jp_4748_:
{
lean_object* v___x_4749_; lean_object* v___x_4750_; 
v___x_4749_ = l_Lean_Meta_Instances_eraseCore(v_d_4743_, v_declName_4744_);
v___x_4750_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4750_, 0, v___x_4749_);
return v___x_4750_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4767_, lean_object* v_declName_4768_, lean_object* v___y_4769_, lean_object* v___y_4770_, lean_object* v___y_4771_){
_start:
{
lean_object* v_res_4772_; 
v_res_4772_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4767_, v_declName_4768_, v___y_4769_, v___y_4770_);
lean_dec(v___y_4770_);
lean_dec_ref(v___y_4769_);
return v_res_4772_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4773_, lean_object* v_declName_4774_, lean_object* v___y_4775_, lean_object* v___y_4776_){
_start:
{
lean_object* v___x_4778_; lean_object* v_env_4779_; lean_object* v___x_4780_; lean_object* v_ext_4781_; lean_object* v_toEnvExtension_4782_; lean_object* v_asyncMode_4783_; lean_object* v___x_4784_; lean_object* v___x_4785_; 
v___x_4778_ = lean_st_ref_get(v___y_4776_);
v_env_4779_ = lean_ctor_get(v___x_4778_, 0);
lean_inc_ref(v_env_4779_);
lean_dec(v___x_4778_);
v___x_4780_ = l_Lean_Meta_instanceExtension;
v_ext_4781_ = lean_ctor_get(v___x_4780_, 1);
v_toEnvExtension_4782_ = lean_ctor_get(v_ext_4781_, 0);
v_asyncMode_4783_ = lean_ctor_get(v_toEnvExtension_4782_, 2);
v___x_4784_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4773_, v___x_4780_, v_env_4779_, v_asyncMode_4783_);
v___x_4785_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4784_, v_declName_4774_, v___y_4775_, v___y_4776_);
if (lean_obj_tag(v___x_4785_) == 0)
{
lean_object* v_a_4786_; lean_object* v___x_4788_; uint8_t v_isShared_4789_; uint8_t v_isSharedCheck_4815_; 
v_a_4786_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4815_ == 0)
{
v___x_4788_ = v___x_4785_;
v_isShared_4789_ = v_isSharedCheck_4815_;
goto v_resetjp_4787_;
}
else
{
lean_inc(v_a_4786_);
lean_dec(v___x_4785_);
v___x_4788_ = lean_box(0);
v_isShared_4789_ = v_isSharedCheck_4815_;
goto v_resetjp_4787_;
}
v_resetjp_4787_:
{
lean_object* v___x_4790_; lean_object* v_env_4791_; lean_object* v_nextMacroScope_4792_; lean_object* v_ngen_4793_; lean_object* v_auxDeclNGen_4794_; lean_object* v_traceState_4795_; lean_object* v_messages_4796_; lean_object* v_infoState_4797_; lean_object* v_snapshotTasks_4798_; lean_object* v___x_4800_; uint8_t v_isShared_4801_; uint8_t v_isSharedCheck_4813_; 
v___x_4790_ = lean_st_ref_take(v___y_4776_);
v_env_4791_ = lean_ctor_get(v___x_4790_, 0);
v_nextMacroScope_4792_ = lean_ctor_get(v___x_4790_, 1);
v_ngen_4793_ = lean_ctor_get(v___x_4790_, 2);
v_auxDeclNGen_4794_ = lean_ctor_get(v___x_4790_, 3);
v_traceState_4795_ = lean_ctor_get(v___x_4790_, 4);
v_messages_4796_ = lean_ctor_get(v___x_4790_, 6);
v_infoState_4797_ = lean_ctor_get(v___x_4790_, 7);
v_snapshotTasks_4798_ = lean_ctor_get(v___x_4790_, 8);
v_isSharedCheck_4813_ = !lean_is_exclusive(v___x_4790_);
if (v_isSharedCheck_4813_ == 0)
{
lean_object* v_unused_4814_; 
v_unused_4814_ = lean_ctor_get(v___x_4790_, 5);
lean_dec(v_unused_4814_);
v___x_4800_ = v___x_4790_;
v_isShared_4801_ = v_isSharedCheck_4813_;
goto v_resetjp_4799_;
}
else
{
lean_inc(v_snapshotTasks_4798_);
lean_inc(v_infoState_4797_);
lean_inc(v_messages_4796_);
lean_inc(v_traceState_4795_);
lean_inc(v_auxDeclNGen_4794_);
lean_inc(v_ngen_4793_);
lean_inc(v_nextMacroScope_4792_);
lean_inc(v_env_4791_);
lean_dec(v___x_4790_);
v___x_4800_ = lean_box(0);
v_isShared_4801_ = v_isSharedCheck_4813_;
goto v_resetjp_4799_;
}
v_resetjp_4799_:
{
lean_object* v___f_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4806_; 
v___f_4802_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4802_, 0, v_a_4786_);
v___x_4803_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4780_, v_env_4791_, v___f_4802_);
v___x_4804_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4801_ == 0)
{
lean_ctor_set(v___x_4800_, 5, v___x_4804_);
lean_ctor_set(v___x_4800_, 0, v___x_4803_);
v___x_4806_ = v___x_4800_;
goto v_reusejp_4805_;
}
else
{
lean_object* v_reuseFailAlloc_4812_; 
v_reuseFailAlloc_4812_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4812_, 0, v___x_4803_);
lean_ctor_set(v_reuseFailAlloc_4812_, 1, v_nextMacroScope_4792_);
lean_ctor_set(v_reuseFailAlloc_4812_, 2, v_ngen_4793_);
lean_ctor_set(v_reuseFailAlloc_4812_, 3, v_auxDeclNGen_4794_);
lean_ctor_set(v_reuseFailAlloc_4812_, 4, v_traceState_4795_);
lean_ctor_set(v_reuseFailAlloc_4812_, 5, v___x_4804_);
lean_ctor_set(v_reuseFailAlloc_4812_, 6, v_messages_4796_);
lean_ctor_set(v_reuseFailAlloc_4812_, 7, v_infoState_4797_);
lean_ctor_set(v_reuseFailAlloc_4812_, 8, v_snapshotTasks_4798_);
v___x_4806_ = v_reuseFailAlloc_4812_;
goto v_reusejp_4805_;
}
v_reusejp_4805_:
{
lean_object* v___x_4807_; lean_object* v___x_4808_; lean_object* v___x_4810_; 
v___x_4807_ = lean_st_ref_set(v___y_4776_, v___x_4806_);
v___x_4808_ = lean_box(0);
if (v_isShared_4789_ == 0)
{
lean_ctor_set(v___x_4788_, 0, v___x_4808_);
v___x_4810_ = v___x_4788_;
goto v_reusejp_4809_;
}
else
{
lean_object* v_reuseFailAlloc_4811_; 
v_reuseFailAlloc_4811_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4811_, 0, v___x_4808_);
v___x_4810_ = v_reuseFailAlloc_4811_;
goto v_reusejp_4809_;
}
v_reusejp_4809_:
{
return v___x_4810_;
}
}
}
}
}
else
{
lean_object* v_a_4816_; lean_object* v___x_4818_; uint8_t v_isShared_4819_; uint8_t v_isSharedCheck_4823_; 
v_a_4816_ = lean_ctor_get(v___x_4785_, 0);
v_isSharedCheck_4823_ = !lean_is_exclusive(v___x_4785_);
if (v_isSharedCheck_4823_ == 0)
{
v___x_4818_ = v___x_4785_;
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
else
{
lean_inc(v_a_4816_);
lean_dec(v___x_4785_);
v___x_4818_ = lean_box(0);
v_isShared_4819_ = v_isSharedCheck_4823_;
goto v_resetjp_4817_;
}
v_resetjp_4817_:
{
lean_object* v___x_4821_; 
if (v_isShared_4819_ == 0)
{
v___x_4821_ = v___x_4818_;
goto v_reusejp_4820_;
}
else
{
lean_object* v_reuseFailAlloc_4822_; 
v_reuseFailAlloc_4822_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4822_, 0, v_a_4816_);
v___x_4821_ = v_reuseFailAlloc_4822_;
goto v_reusejp_4820_;
}
v_reusejp_4820_:
{
return v___x_4821_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4824_, lean_object* v_declName_4825_, lean_object* v___y_4826_, lean_object* v___y_4827_, lean_object* v___y_4828_){
_start:
{
lean_object* v_res_4829_; 
v_res_4829_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4824_, v_declName_4825_, v___y_4826_, v___y_4827_);
lean_dec(v___y_4827_);
lean_dec_ref(v___y_4826_);
lean_dec_ref(v___x_4824_);
return v_res_4829_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4836_; uint64_t v___x_4837_; 
v___x_4836_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4837_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4836_);
return v___x_4837_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4838_; lean_object* v___x_4839_; lean_object* v___x_4840_; 
v___x_4838_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4839_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4840_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4840_, 0, v___x_4839_);
lean_ctor_set_uint64(v___x_4840_, sizeof(void*)*1, v___x_4838_);
return v___x_4840_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4841_; 
v___x_4841_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4841_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4842_; lean_object* v___x_4843_; 
v___x_4842_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4843_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4843_, 0, v___x_4842_);
return v___x_4843_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4844_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4845_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4844_);
lean_ctor_set(v___x_4845_, 1, v___x_4844_);
lean_ctor_set(v___x_4845_, 2, v___x_4844_);
lean_ctor_set(v___x_4845_, 3, v___x_4844_);
lean_ctor_set(v___x_4845_, 4, v___x_4844_);
lean_ctor_set(v___x_4845_, 5, v___x_4844_);
return v___x_4845_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4846_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4847_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4846_);
lean_ctor_set(v___x_4847_, 1, v___x_4846_);
lean_ctor_set(v___x_4847_, 2, v___x_4846_);
lean_ctor_set(v___x_4847_, 3, v___x_4846_);
lean_ctor_set(v___x_4847_, 4, v___x_4846_);
return v___x_4847_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4848_, lean_object* v___x_4849_, lean_object* v_declName_4850_, lean_object* v_stx_4851_, uint8_t v_attrKind_4852_, lean_object* v___y_4853_, lean_object* v___y_4854_){
_start:
{
lean_object* v___x_4856_; lean_object* v___x_4857_; lean_object* v___x_4858_; 
v___x_4856_ = lean_unsigned_to_nat(1u);
v___x_4857_ = l_Lean_Syntax_getArg(v_stx_4851_, v___x_4856_);
v___x_4858_ = l_Lean_getAttrParamOptPrio(v___x_4857_, v___y_4853_, v___y_4854_);
if (lean_obj_tag(v___x_4858_) == 0)
{
lean_object* v_a_4859_; uint8_t v___x_4860_; uint8_t v___x_4861_; lean_object* v___x_4862_; lean_object* v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; size_t v___x_4867_; lean_object* v___x_4868_; lean_object* v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; 
v_a_4859_ = lean_ctor_get(v___x_4858_, 0);
lean_inc(v_a_4859_);
lean_dec_ref_known(v___x_4858_, 1);
v___x_4860_ = 0;
v___x_4861_ = 1;
v___x_4862_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4863_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4864_ = lean_unsigned_to_nat(32u);
v___x_4865_ = lean_mk_empty_array_with_capacity(v___x_4864_);
v___x_4866_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4867_ = ((size_t)5ULL);
lean_inc_n(v___x_4848_, 6);
v___x_4868_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4868_, 0, v___x_4866_);
lean_ctor_set(v___x_4868_, 1, v___x_4865_);
lean_ctor_set(v___x_4868_, 2, v___x_4848_);
lean_ctor_set(v___x_4868_, 3, v___x_4848_);
lean_ctor_set_usize(v___x_4868_, 4, v___x_4867_);
v___x_4869_ = lean_box(1);
lean_inc_ref(v___x_4868_);
v___x_4870_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4870_, 0, v___x_4863_);
lean_ctor_set(v___x_4870_, 1, v___x_4868_);
lean_ctor_set(v___x_4870_, 2, v___x_4869_);
v___x_4871_ = lean_mk_empty_array_with_capacity(v___x_4848_);
v___x_4872_ = lean_box(0);
lean_inc(v___x_4849_);
v___x_4873_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4873_, 0, v___x_4862_);
lean_ctor_set(v___x_4873_, 1, v___x_4849_);
lean_ctor_set(v___x_4873_, 2, v___x_4870_);
lean_ctor_set(v___x_4873_, 3, v___x_4871_);
lean_ctor_set(v___x_4873_, 4, v___x_4872_);
lean_ctor_set(v___x_4873_, 5, v___x_4848_);
lean_ctor_set(v___x_4873_, 6, v___x_4872_);
lean_ctor_set_uint8(v___x_4873_, sizeof(void*)*7, v___x_4860_);
lean_ctor_set_uint8(v___x_4873_, sizeof(void*)*7 + 1, v___x_4860_);
lean_ctor_set_uint8(v___x_4873_, sizeof(void*)*7 + 2, v___x_4860_);
lean_ctor_set_uint8(v___x_4873_, sizeof(void*)*7 + 3, v___x_4861_);
v___x_4874_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4874_, 0, v___x_4848_);
lean_ctor_set(v___x_4874_, 1, v___x_4848_);
lean_ctor_set(v___x_4874_, 2, v___x_4848_);
lean_ctor_set(v___x_4874_, 3, v___x_4848_);
lean_ctor_set(v___x_4874_, 4, v___x_4863_);
lean_ctor_set(v___x_4874_, 5, v___x_4863_);
lean_ctor_set(v___x_4874_, 6, v___x_4863_);
lean_ctor_set(v___x_4874_, 7, v___x_4863_);
lean_ctor_set(v___x_4874_, 8, v___x_4863_);
lean_ctor_set(v___x_4874_, 9, v___x_4863_);
v___x_4875_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4876_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4877_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4877_, 0, v___x_4874_);
lean_ctor_set(v___x_4877_, 1, v___x_4875_);
lean_ctor_set(v___x_4877_, 2, v___x_4849_);
lean_ctor_set(v___x_4877_, 3, v___x_4868_);
lean_ctor_set(v___x_4877_, 4, v___x_4876_);
v___x_4878_ = lean_st_mk_ref(v___x_4877_);
v___x_4879_ = l_Lean_Meta_addInstance(v_declName_4850_, v_attrKind_4852_, v_a_4859_, v___x_4873_, v___x_4878_, v___y_4853_, v___y_4854_);
lean_dec_ref_known(v___x_4873_, 7);
if (lean_obj_tag(v___x_4879_) == 0)
{
lean_object* v___x_4881_; uint8_t v_isShared_4882_; uint8_t v_isSharedCheck_4888_; 
v_isSharedCheck_4888_ = !lean_is_exclusive(v___x_4879_);
if (v_isSharedCheck_4888_ == 0)
{
lean_object* v_unused_4889_; 
v_unused_4889_ = lean_ctor_get(v___x_4879_, 0);
lean_dec(v_unused_4889_);
v___x_4881_ = v___x_4879_;
v_isShared_4882_ = v_isSharedCheck_4888_;
goto v_resetjp_4880_;
}
else
{
lean_dec(v___x_4879_);
v___x_4881_ = lean_box(0);
v_isShared_4882_ = v_isSharedCheck_4888_;
goto v_resetjp_4880_;
}
v_resetjp_4880_:
{
lean_object* v___x_4883_; lean_object* v___x_4884_; lean_object* v___x_4886_; 
v___x_4883_ = lean_st_ref_get(v___x_4878_);
lean_dec(v___x_4878_);
lean_dec(v___x_4883_);
v___x_4884_ = lean_box(0);
if (v_isShared_4882_ == 0)
{
lean_ctor_set(v___x_4881_, 0, v___x_4884_);
v___x_4886_ = v___x_4881_;
goto v_reusejp_4885_;
}
else
{
lean_object* v_reuseFailAlloc_4887_; 
v_reuseFailAlloc_4887_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4887_, 0, v___x_4884_);
v___x_4886_ = v_reuseFailAlloc_4887_;
goto v_reusejp_4885_;
}
v_reusejp_4885_:
{
return v___x_4886_;
}
}
}
else
{
lean_dec(v___x_4878_);
return v___x_4879_;
}
}
else
{
lean_object* v_a_4890_; lean_object* v___x_4892_; uint8_t v_isShared_4893_; uint8_t v_isSharedCheck_4897_; 
lean_dec(v_declName_4850_);
lean_dec(v___x_4849_);
lean_dec(v___x_4848_);
v_a_4890_ = lean_ctor_get(v___x_4858_, 0);
v_isSharedCheck_4897_ = !lean_is_exclusive(v___x_4858_);
if (v_isSharedCheck_4897_ == 0)
{
v___x_4892_ = v___x_4858_;
v_isShared_4893_ = v_isSharedCheck_4897_;
goto v_resetjp_4891_;
}
else
{
lean_inc(v_a_4890_);
lean_dec(v___x_4858_);
v___x_4892_ = lean_box(0);
v_isShared_4893_ = v_isSharedCheck_4897_;
goto v_resetjp_4891_;
}
v_resetjp_4891_:
{
lean_object* v___x_4895_; 
if (v_isShared_4893_ == 0)
{
v___x_4895_ = v___x_4892_;
goto v_reusejp_4894_;
}
else
{
lean_object* v_reuseFailAlloc_4896_; 
v_reuseFailAlloc_4896_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4896_, 0, v_a_4890_);
v___x_4895_ = v_reuseFailAlloc_4896_;
goto v_reusejp_4894_;
}
v_reusejp_4894_:
{
return v___x_4895_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4898_, lean_object* v___x_4899_, lean_object* v_declName_4900_, lean_object* v_stx_4901_, lean_object* v_attrKind_4902_, lean_object* v___y_4903_, lean_object* v___y_4904_, lean_object* v___y_4905_){
_start:
{
uint8_t v_attrKind_boxed_4906_; lean_object* v_res_4907_; 
v_attrKind_boxed_4906_ = lean_unbox(v_attrKind_4902_);
v_res_4907_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4898_, v___x_4899_, v_declName_4900_, v_stx_4901_, v_attrKind_boxed_4906_, v___y_4903_, v___y_4904_);
lean_dec(v___y_4904_);
lean_dec_ref(v___y_4903_);
lean_dec(v_stx_4901_);
return v_res_4907_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4908_; lean_object* v___f_4909_; 
v___x_4908_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4909_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4909_, 0, v___x_4908_);
return v___f_4909_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4976_; lean_object* v___f_4977_; lean_object* v___x_4978_; lean_object* v___x_4979_; 
v___f_4976_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_4977_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4978_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4979_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4979_, 0, v___x_4978_);
lean_ctor_set(v___x_4979_, 1, v___f_4977_);
lean_ctor_set(v___x_4979_, 2, v___f_4976_);
return v___x_4979_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4981_; lean_object* v___x_4982_; 
v___x_4981_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4982_ = l_Lean_registerBuiltinAttribute(v___x_4981_);
return v___x_4982_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4983_){
_start:
{
lean_object* v_res_4984_; 
v_res_4984_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4984_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4985_, lean_object* v_x_4986_, lean_object* v_x_4987_){
_start:
{
uint8_t v___x_4988_; 
v___x_4988_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4986_, v_x_4987_);
return v___x_4988_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_4989_, lean_object* v_x_4990_, lean_object* v_x_4991_){
_start:
{
uint8_t v_res_4992_; lean_object* v_r_4993_; 
v_res_4992_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_4989_, v_x_4990_, v_x_4991_);
lean_dec(v_x_4991_);
lean_dec_ref(v_x_4990_);
v_r_4993_ = lean_box(v_res_4992_);
return v_r_4993_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_4994_, lean_object* v_msg_4995_, lean_object* v___y_4996_, lean_object* v___y_4997_){
_start:
{
lean_object* v___x_4999_; 
v___x_4999_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4995_, v___y_4996_, v___y_4997_);
return v___x_4999_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_5000_, lean_object* v_msg_5001_, lean_object* v___y_5002_, lean_object* v___y_5003_, lean_object* v___y_5004_){
_start:
{
lean_object* v_res_5005_; 
v_res_5005_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_5000_, v_msg_5001_, v___y_5002_, v___y_5003_);
lean_dec(v___y_5003_);
lean_dec_ref(v___y_5002_);
return v_res_5005_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5006_, lean_object* v_x_5007_, size_t v_x_5008_, lean_object* v_x_5009_){
_start:
{
uint8_t v___x_5010_; 
v___x_5010_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5007_, v_x_5008_, v_x_5009_);
return v___x_5010_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5011_, lean_object* v_x_5012_, lean_object* v_x_5013_, lean_object* v_x_5014_){
_start:
{
size_t v_x_2994__boxed_5015_; uint8_t v_res_5016_; lean_object* v_r_5017_; 
v_x_2994__boxed_5015_ = lean_unbox_usize(v_x_5013_);
lean_dec(v_x_5013_);
v_res_5016_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_5011_, v_x_5012_, v_x_2994__boxed_5015_, v_x_5014_);
lean_dec(v_x_5014_);
lean_dec_ref(v_x_5012_);
v_r_5017_ = lean_box(v_res_5016_);
return v_r_5017_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5018_, lean_object* v_keys_5019_, lean_object* v_vals_5020_, lean_object* v_heq_5021_, lean_object* v_i_5022_, lean_object* v_k_5023_){
_start:
{
uint8_t v___x_5024_; 
v___x_5024_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_5019_, v_i_5022_, v_k_5023_);
return v___x_5024_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5025_, lean_object* v_keys_5026_, lean_object* v_vals_5027_, lean_object* v_heq_5028_, lean_object* v_i_5029_, lean_object* v_k_5030_){
_start:
{
uint8_t v_res_5031_; lean_object* v_r_5032_; 
v_res_5031_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_5025_, v_keys_5026_, v_vals_5027_, v_heq_5028_, v_i_5029_, v_k_5030_);
lean_dec(v_k_5030_);
lean_dec_ref(v_vals_5027_);
lean_dec_ref(v_keys_5026_);
v_r_5032_ = lean_box(v_res_5031_);
return v_r_5032_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5035_; lean_object* v___x_5036_; lean_object* v___x_5037_; 
v___x_5035_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5036_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5037_ = l_Lean_addBuiltinDocString(v___x_5035_, v___x_5036_);
return v___x_5037_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5038_){
_start:
{
lean_object* v_res_5039_; 
v_res_5039_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5039_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_5040_){
_start:
{
lean_object* v___x_5042_; lean_object* v_env_5043_; lean_object* v___x_5044_; lean_object* v_ext_5045_; lean_object* v_toEnvExtension_5046_; lean_object* v_asyncMode_5047_; lean_object* v___x_5048_; lean_object* v___x_5049_; lean_object* v_discrTree_5050_; lean_object* v___x_5051_; 
v___x_5042_ = lean_st_ref_get(v_a_5040_);
v_env_5043_ = lean_ctor_get(v___x_5042_, 0);
lean_inc_ref(v_env_5043_);
lean_dec(v___x_5042_);
v___x_5044_ = l_Lean_Meta_instanceExtension;
v_ext_5045_ = lean_ctor_get(v___x_5044_, 1);
v_toEnvExtension_5046_ = lean_ctor_get(v_ext_5045_, 0);
v_asyncMode_5047_ = lean_ctor_get(v_toEnvExtension_5046_, 2);
v___x_5048_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5049_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5048_, v___x_5044_, v_env_5043_, v_asyncMode_5047_);
v_discrTree_5050_ = lean_ctor_get(v___x_5049_, 0);
lean_inc_ref(v_discrTree_5050_);
lean_dec(v___x_5049_);
v___x_5051_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5051_, 0, v_discrTree_5050_);
return v___x_5051_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_5052_, lean_object* v_a_5053_){
_start:
{
lean_object* v_res_5054_; 
v_res_5054_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5052_);
lean_dec(v_a_5052_);
return v_res_5054_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_5055_, lean_object* v_a_5056_){
_start:
{
lean_object* v___x_5058_; 
v___x_5058_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5056_);
return v___x_5058_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_5059_, lean_object* v_a_5060_, lean_object* v_a_5061_){
_start:
{
lean_object* v_res_5062_; 
v_res_5062_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_5059_, v_a_5060_);
lean_dec(v_a_5060_);
lean_dec_ref(v_a_5059_);
return v_res_5062_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_5063_){
_start:
{
lean_object* v___x_5065_; lean_object* v_env_5066_; lean_object* v___x_5067_; lean_object* v_ext_5068_; lean_object* v_toEnvExtension_5069_; lean_object* v_asyncMode_5070_; lean_object* v___x_5071_; lean_object* v___x_5072_; lean_object* v_erased_5073_; lean_object* v___x_5074_; 
v___x_5065_ = lean_st_ref_get(v_a_5063_);
v_env_5066_ = lean_ctor_get(v___x_5065_, 0);
lean_inc_ref(v_env_5066_);
lean_dec(v___x_5065_);
v___x_5067_ = l_Lean_Meta_instanceExtension;
v_ext_5068_ = lean_ctor_get(v___x_5067_, 1);
v_toEnvExtension_5069_ = lean_ctor_get(v_ext_5068_, 0);
v_asyncMode_5070_ = lean_ctor_get(v_toEnvExtension_5069_, 2);
v___x_5071_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5072_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5071_, v___x_5067_, v_env_5066_, v_asyncMode_5070_);
v_erased_5073_ = lean_ctor_get(v___x_5072_, 2);
lean_inc_ref(v_erased_5073_);
lean_dec(v___x_5072_);
v___x_5074_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5074_, 0, v_erased_5073_);
return v___x_5074_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_5075_, lean_object* v_a_5076_){
_start:
{
lean_object* v_res_5077_; 
v_res_5077_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5075_);
lean_dec(v_a_5075_);
return v_res_5077_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_5078_, lean_object* v_a_5079_){
_start:
{
lean_object* v___x_5081_; 
v___x_5081_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5079_);
return v___x_5081_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_5082_, lean_object* v_a_5083_, lean_object* v_a_5084_){
_start:
{
lean_object* v_res_5085_; 
v_res_5085_ = l_Lean_Meta_getErasedInstances(v_a_5082_, v_a_5083_);
lean_dec(v_a_5083_);
lean_dec_ref(v_a_5082_);
return v_res_5085_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_5086_, lean_object* v_declName_5087_){
_start:
{
lean_object* v___x_5088_; lean_object* v_ext_5089_; lean_object* v_toEnvExtension_5090_; lean_object* v_asyncMode_5091_; lean_object* v___x_5092_; lean_object* v___x_5093_; lean_object* v_instanceNames_5094_; uint8_t v___x_5095_; 
v___x_5088_ = l_Lean_Meta_instanceExtension;
v_ext_5089_ = lean_ctor_get(v___x_5088_, 1);
v_toEnvExtension_5090_ = lean_ctor_get(v_ext_5089_, 0);
v_asyncMode_5091_ = lean_ctor_get(v_toEnvExtension_5090_, 2);
v___x_5092_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5093_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5092_, v___x_5088_, v_env_5086_, v_asyncMode_5091_);
v_instanceNames_5094_ = lean_ctor_get(v___x_5093_, 1);
lean_inc_ref(v_instanceNames_5094_);
lean_dec(v___x_5093_);
v___x_5095_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_5094_, v_declName_5087_);
lean_dec_ref(v_instanceNames_5094_);
return v___x_5095_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_5096_, lean_object* v_declName_5097_){
_start:
{
uint8_t v_res_5098_; lean_object* v_r_5099_; 
v_res_5098_ = l_Lean_Meta_isInstanceCore(v_env_5096_, v_declName_5097_);
lean_dec(v_declName_5097_);
v_r_5099_ = lean_box(v_res_5098_);
return v_r_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_5100_, lean_object* v_a_5101_){
_start:
{
lean_object* v___x_5103_; lean_object* v_env_5104_; uint8_t v___x_5105_; lean_object* v___x_5106_; lean_object* v___x_5107_; 
v___x_5103_ = lean_st_ref_get(v_a_5101_);
v_env_5104_ = lean_ctor_get(v___x_5103_, 0);
lean_inc_ref(v_env_5104_);
lean_dec(v___x_5103_);
v___x_5105_ = l_Lean_Meta_isInstanceCore(v_env_5104_, v_declName_5100_);
v___x_5106_ = lean_box(v___x_5105_);
v___x_5107_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5107_, 0, v___x_5106_);
return v___x_5107_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_5108_, lean_object* v_a_5109_, lean_object* v_a_5110_){
_start:
{
lean_object* v_res_5111_; 
v_res_5111_ = l_Lean_Meta_isInstance___redArg(v_declName_5108_, v_a_5109_);
lean_dec(v_a_5109_);
lean_dec(v_declName_5108_);
return v_res_5111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_5112_, lean_object* v_a_5113_, lean_object* v_a_5114_){
_start:
{
lean_object* v___x_5116_; 
v___x_5116_ = l_Lean_Meta_isInstance___redArg(v_declName_5112_, v_a_5114_);
return v___x_5116_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_5117_, lean_object* v_a_5118_, lean_object* v_a_5119_, lean_object* v_a_5120_){
_start:
{
lean_object* v_res_5121_; 
v_res_5121_ = l_Lean_Meta_isInstance(v_declName_5117_, v_a_5118_, v_a_5119_);
lean_dec(v_a_5119_);
lean_dec_ref(v_a_5118_);
lean_dec(v_declName_5117_);
return v_res_5121_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5122_, lean_object* v_vals_5123_, lean_object* v_i_5124_, lean_object* v_k_5125_){
_start:
{
lean_object* v___x_5126_; uint8_t v___x_5127_; 
v___x_5126_ = lean_array_get_size(v_keys_5122_);
v___x_5127_ = lean_nat_dec_lt(v_i_5124_, v___x_5126_);
if (v___x_5127_ == 0)
{
lean_object* v___x_5128_; 
lean_dec(v_i_5124_);
v___x_5128_ = lean_box(0);
return v___x_5128_;
}
else
{
lean_object* v_k_x27_5129_; uint8_t v___x_5130_; 
v_k_x27_5129_ = lean_array_fget_borrowed(v_keys_5122_, v_i_5124_);
v___x_5130_ = lean_name_eq(v_k_5125_, v_k_x27_5129_);
if (v___x_5130_ == 0)
{
lean_object* v___x_5131_; lean_object* v___x_5132_; 
v___x_5131_ = lean_unsigned_to_nat(1u);
v___x_5132_ = lean_nat_add(v_i_5124_, v___x_5131_);
lean_dec(v_i_5124_);
v_i_5124_ = v___x_5132_;
goto _start;
}
else
{
lean_object* v___x_5134_; lean_object* v___x_5135_; 
v___x_5134_ = lean_array_fget_borrowed(v_vals_5123_, v_i_5124_);
lean_dec(v_i_5124_);
lean_inc(v___x_5134_);
v___x_5135_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5135_, 0, v___x_5134_);
return v___x_5135_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5136_, lean_object* v_vals_5137_, lean_object* v_i_5138_, lean_object* v_k_5139_){
_start:
{
lean_object* v_res_5140_; 
v_res_5140_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5136_, v_vals_5137_, v_i_5138_, v_k_5139_);
lean_dec(v_k_5139_);
lean_dec_ref(v_vals_5137_);
lean_dec_ref(v_keys_5136_);
return v_res_5140_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_5141_, size_t v_x_5142_, lean_object* v_x_5143_){
_start:
{
if (lean_obj_tag(v_x_5141_) == 0)
{
lean_object* v_es_5144_; lean_object* v___x_5145_; size_t v___x_5146_; size_t v___x_5147_; lean_object* v_j_5148_; lean_object* v___x_5149_; 
v_es_5144_ = lean_ctor_get(v_x_5141_, 0);
v___x_5145_ = lean_box(2);
v___x_5146_ = ((size_t)31ULL);
v___x_5147_ = lean_usize_land(v_x_5142_, v___x_5146_);
v_j_5148_ = lean_usize_to_nat(v___x_5147_);
v___x_5149_ = lean_array_get_borrowed(v___x_5145_, v_es_5144_, v_j_5148_);
lean_dec(v_j_5148_);
switch(lean_obj_tag(v___x_5149_))
{
case 0:
{
lean_object* v_key_5150_; lean_object* v_val_5151_; uint8_t v___x_5152_; 
v_key_5150_ = lean_ctor_get(v___x_5149_, 0);
v_val_5151_ = lean_ctor_get(v___x_5149_, 1);
v___x_5152_ = lean_name_eq(v_x_5143_, v_key_5150_);
if (v___x_5152_ == 0)
{
lean_object* v___x_5153_; 
v___x_5153_ = lean_box(0);
return v___x_5153_;
}
else
{
lean_object* v___x_5154_; 
lean_inc(v_val_5151_);
v___x_5154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5154_, 0, v_val_5151_);
return v___x_5154_;
}
}
case 1:
{
lean_object* v_node_5155_; size_t v___x_5156_; size_t v___x_5157_; 
v_node_5155_ = lean_ctor_get(v___x_5149_, 0);
v___x_5156_ = ((size_t)5ULL);
v___x_5157_ = lean_usize_shift_right(v_x_5142_, v___x_5156_);
v_x_5141_ = v_node_5155_;
v_x_5142_ = v___x_5157_;
goto _start;
}
default: 
{
lean_object* v___x_5159_; 
v___x_5159_ = lean_box(0);
return v___x_5159_;
}
}
}
else
{
lean_object* v_ks_5160_; lean_object* v_vs_5161_; lean_object* v___x_5162_; lean_object* v___x_5163_; 
v_ks_5160_ = lean_ctor_get(v_x_5141_, 0);
v_vs_5161_ = lean_ctor_get(v_x_5141_, 1);
v___x_5162_ = lean_unsigned_to_nat(0u);
v___x_5163_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5160_, v_vs_5161_, v___x_5162_, v_x_5143_);
return v___x_5163_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5164_, lean_object* v_x_5165_, lean_object* v_x_5166_){
_start:
{
size_t v_x_478__boxed_5167_; lean_object* v_res_5168_; 
v_x_478__boxed_5167_ = lean_unbox_usize(v_x_5165_);
lean_dec(v_x_5165_);
v_res_5168_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5164_, v_x_478__boxed_5167_, v_x_5166_);
lean_dec(v_x_5166_);
lean_dec_ref(v_x_5164_);
return v_res_5168_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_5169_, lean_object* v_x_5170_){
_start:
{
uint64_t v___y_5172_; 
if (lean_obj_tag(v_x_5170_) == 0)
{
uint64_t v___x_5175_; 
v___x_5175_ = 1723ULL;
v___y_5172_ = v___x_5175_;
goto v___jp_5171_;
}
else
{
uint64_t v_hash_5176_; 
v_hash_5176_ = lean_ctor_get_uint64(v_x_5170_, sizeof(void*)*2);
v___y_5172_ = v_hash_5176_;
goto v___jp_5171_;
}
v___jp_5171_:
{
size_t v___x_5173_; lean_object* v___x_5174_; 
v___x_5173_ = lean_uint64_to_usize(v___y_5172_);
v___x_5174_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5169_, v___x_5173_, v_x_5170_);
return v___x_5174_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_5177_, lean_object* v_x_5178_){
_start:
{
lean_object* v_res_5179_; 
v_res_5179_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5177_, v_x_5178_);
lean_dec(v_x_5178_);
lean_dec_ref(v_x_5177_);
return v_res_5179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_5180_, lean_object* v_a_5181_){
_start:
{
lean_object* v___x_5183_; lean_object* v_env_5184_; lean_object* v___x_5185_; lean_object* v_ext_5186_; lean_object* v_toEnvExtension_5187_; lean_object* v_asyncMode_5188_; lean_object* v___x_5189_; lean_object* v___x_5190_; lean_object* v_instanceNames_5191_; lean_object* v___x_5192_; 
v___x_5183_ = lean_st_ref_get(v_a_5181_);
v_env_5184_ = lean_ctor_get(v___x_5183_, 0);
lean_inc_ref(v_env_5184_);
lean_dec(v___x_5183_);
v___x_5185_ = l_Lean_Meta_instanceExtension;
v_ext_5186_ = lean_ctor_get(v___x_5185_, 1);
v_toEnvExtension_5187_ = lean_ctor_get(v_ext_5186_, 0);
v_asyncMode_5188_ = lean_ctor_get(v_toEnvExtension_5187_, 2);
v___x_5189_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5190_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5189_, v___x_5185_, v_env_5184_, v_asyncMode_5188_);
v_instanceNames_5191_ = lean_ctor_get(v___x_5190_, 1);
lean_inc_ref(v_instanceNames_5191_);
lean_dec(v___x_5190_);
v___x_5192_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5191_, v_declName_5180_);
lean_dec_ref(v_instanceNames_5191_);
if (lean_obj_tag(v___x_5192_) == 1)
{
lean_object* v_val_5193_; lean_object* v___x_5195_; uint8_t v_isShared_5196_; uint8_t v_isSharedCheck_5202_; 
v_val_5193_ = lean_ctor_get(v___x_5192_, 0);
v_isSharedCheck_5202_ = !lean_is_exclusive(v___x_5192_);
if (v_isSharedCheck_5202_ == 0)
{
v___x_5195_ = v___x_5192_;
v_isShared_5196_ = v_isSharedCheck_5202_;
goto v_resetjp_5194_;
}
else
{
lean_inc(v_val_5193_);
lean_dec(v___x_5192_);
v___x_5195_ = lean_box(0);
v_isShared_5196_ = v_isSharedCheck_5202_;
goto v_resetjp_5194_;
}
v_resetjp_5194_:
{
lean_object* v_priority_5197_; lean_object* v___x_5199_; 
v_priority_5197_ = lean_ctor_get(v_val_5193_, 2);
lean_inc(v_priority_5197_);
lean_dec(v_val_5193_);
if (v_isShared_5196_ == 0)
{
lean_ctor_set(v___x_5195_, 0, v_priority_5197_);
v___x_5199_ = v___x_5195_;
goto v_reusejp_5198_;
}
else
{
lean_object* v_reuseFailAlloc_5201_; 
v_reuseFailAlloc_5201_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5201_, 0, v_priority_5197_);
v___x_5199_ = v_reuseFailAlloc_5201_;
goto v_reusejp_5198_;
}
v_reusejp_5198_:
{
lean_object* v___x_5200_; 
v___x_5200_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5200_, 0, v___x_5199_);
return v___x_5200_;
}
}
}
else
{
lean_object* v___x_5203_; lean_object* v___x_5204_; 
lean_dec(v___x_5192_);
v___x_5203_ = lean_box(0);
v___x_5204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5204_, 0, v___x_5203_);
return v___x_5204_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_5205_, lean_object* v_a_5206_, lean_object* v_a_5207_){
_start:
{
lean_object* v_res_5208_; 
v_res_5208_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5205_, v_a_5206_);
lean_dec(v_a_5206_);
lean_dec(v_declName_5205_);
return v_res_5208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_5209_, lean_object* v_a_5210_, lean_object* v_a_5211_){
_start:
{
lean_object* v___x_5213_; 
v___x_5213_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5209_, v_a_5211_);
return v___x_5213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_5214_, lean_object* v_a_5215_, lean_object* v_a_5216_, lean_object* v_a_5217_){
_start:
{
lean_object* v_res_5218_; 
v_res_5218_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_5214_, v_a_5215_, v_a_5216_);
lean_dec(v_a_5216_);
lean_dec_ref(v_a_5215_);
lean_dec(v_declName_5214_);
return v_res_5218_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_5219_, lean_object* v_x_5220_, lean_object* v_x_5221_){
_start:
{
lean_object* v___x_5222_; 
v___x_5222_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5220_, v_x_5221_);
return v___x_5222_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_5223_, lean_object* v_x_5224_, lean_object* v_x_5225_){
_start:
{
lean_object* v_res_5226_; 
v_res_5226_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_5223_, v_x_5224_, v_x_5225_);
lean_dec(v_x_5225_);
lean_dec_ref(v_x_5224_);
return v_res_5226_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5227_, lean_object* v_x_5228_, size_t v_x_5229_, lean_object* v_x_5230_){
_start:
{
lean_object* v___x_5231_; 
v___x_5231_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5228_, v_x_5229_, v_x_5230_);
return v___x_5231_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5232_, lean_object* v_x_5233_, lean_object* v_x_5234_, lean_object* v_x_5235_){
_start:
{
size_t v_x_589__boxed_5236_; lean_object* v_res_5237_; 
v_x_589__boxed_5236_ = lean_unbox_usize(v_x_5234_);
lean_dec(v_x_5234_);
v_res_5237_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_5232_, v_x_5233_, v_x_589__boxed_5236_, v_x_5235_);
lean_dec(v_x_5235_);
lean_dec_ref(v_x_5233_);
return v_res_5237_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5238_, lean_object* v_keys_5239_, lean_object* v_vals_5240_, lean_object* v_heq_5241_, lean_object* v_i_5242_, lean_object* v_k_5243_){
_start:
{
lean_object* v___x_5244_; 
v___x_5244_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5239_, v_vals_5240_, v_i_5242_, v_k_5243_);
return v___x_5244_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5245_, lean_object* v_keys_5246_, lean_object* v_vals_5247_, lean_object* v_heq_5248_, lean_object* v_i_5249_, lean_object* v_k_5250_){
_start:
{
lean_object* v_res_5251_; 
v_res_5251_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5245_, v_keys_5246_, v_vals_5247_, v_heq_5248_, v_i_5249_, v_k_5250_);
lean_dec(v_k_5250_);
lean_dec_ref(v_vals_5247_);
lean_dec_ref(v_keys_5246_);
return v_res_5251_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_5252_, lean_object* v_a_5253_){
_start:
{
lean_object* v___x_5255_; lean_object* v_env_5256_; lean_object* v___x_5257_; lean_object* v_ext_5258_; lean_object* v_toEnvExtension_5259_; lean_object* v_asyncMode_5260_; lean_object* v___x_5261_; lean_object* v___x_5262_; lean_object* v_instanceNames_5263_; lean_object* v___x_5264_; 
v___x_5255_ = lean_st_ref_get(v_a_5253_);
v_env_5256_ = lean_ctor_get(v___x_5255_, 0);
lean_inc_ref(v_env_5256_);
lean_dec(v___x_5255_);
v___x_5257_ = l_Lean_Meta_instanceExtension;
v_ext_5258_ = lean_ctor_get(v___x_5257_, 1);
v_toEnvExtension_5259_ = lean_ctor_get(v_ext_5258_, 0);
v_asyncMode_5260_ = lean_ctor_get(v_toEnvExtension_5259_, 2);
v___x_5261_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5262_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5261_, v___x_5257_, v_env_5256_, v_asyncMode_5260_);
v_instanceNames_5263_ = lean_ctor_get(v___x_5262_, 1);
lean_inc_ref(v_instanceNames_5263_);
lean_dec(v___x_5262_);
v___x_5264_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5263_, v_declName_5252_);
lean_dec_ref(v_instanceNames_5263_);
if (lean_obj_tag(v___x_5264_) == 1)
{
lean_object* v_val_5265_; lean_object* v___x_5267_; uint8_t v_isShared_5268_; uint8_t v_isSharedCheck_5275_; 
v_val_5265_ = lean_ctor_get(v___x_5264_, 0);
v_isSharedCheck_5275_ = !lean_is_exclusive(v___x_5264_);
if (v_isSharedCheck_5275_ == 0)
{
v___x_5267_ = v___x_5264_;
v_isShared_5268_ = v_isSharedCheck_5275_;
goto v_resetjp_5266_;
}
else
{
lean_inc(v_val_5265_);
lean_dec(v___x_5264_);
v___x_5267_ = lean_box(0);
v_isShared_5268_ = v_isSharedCheck_5275_;
goto v_resetjp_5266_;
}
v_resetjp_5266_:
{
uint8_t v_attrKind_5269_; lean_object* v___x_5270_; lean_object* v___x_5272_; 
v_attrKind_5269_ = lean_ctor_get_uint8(v_val_5265_, sizeof(void*)*5);
lean_dec(v_val_5265_);
v___x_5270_ = lean_box(v_attrKind_5269_);
if (v_isShared_5268_ == 0)
{
lean_ctor_set(v___x_5267_, 0, v___x_5270_);
v___x_5272_ = v___x_5267_;
goto v_reusejp_5271_;
}
else
{
lean_object* v_reuseFailAlloc_5274_; 
v_reuseFailAlloc_5274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5274_, 0, v___x_5270_);
v___x_5272_ = v_reuseFailAlloc_5274_;
goto v_reusejp_5271_;
}
v_reusejp_5271_:
{
lean_object* v___x_5273_; 
v___x_5273_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5273_, 0, v___x_5272_);
return v___x_5273_;
}
}
}
else
{
lean_object* v___x_5276_; lean_object* v___x_5277_; 
lean_dec(v___x_5264_);
v___x_5276_ = lean_box(0);
v___x_5277_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5277_, 0, v___x_5276_);
return v___x_5277_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_5278_, lean_object* v_a_5279_, lean_object* v_a_5280_){
_start:
{
lean_object* v_res_5281_; 
v_res_5281_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5278_, v_a_5279_);
lean_dec(v_a_5279_);
lean_dec(v_declName_5278_);
return v_res_5281_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_5282_, lean_object* v_a_5283_, lean_object* v_a_5284_){
_start:
{
lean_object* v___x_5286_; 
v___x_5286_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5282_, v_a_5284_);
return v___x_5286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_5287_, lean_object* v_a_5288_, lean_object* v_a_5289_, lean_object* v_a_5290_){
_start:
{
lean_object* v_res_5291_; 
v_res_5291_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_5287_, v_a_5288_, v_a_5289_);
lean_dec(v_a_5289_);
lean_dec_ref(v_a_5288_);
lean_dec(v_declName_5287_);
return v_res_5291_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5296_, lean_object* v_v_5297_, lean_object* v_t_5298_){
_start:
{
if (lean_obj_tag(v_t_5298_) == 0)
{
lean_object* v_size_5299_; lean_object* v_k_5300_; lean_object* v_v_5301_; lean_object* v_l_5302_; lean_object* v_r_5303_; lean_object* v___x_5305_; uint8_t v_isShared_5306_; uint8_t v_isSharedCheck_5584_; 
v_size_5299_ = lean_ctor_get(v_t_5298_, 0);
v_k_5300_ = lean_ctor_get(v_t_5298_, 1);
v_v_5301_ = lean_ctor_get(v_t_5298_, 2);
v_l_5302_ = lean_ctor_get(v_t_5298_, 3);
v_r_5303_ = lean_ctor_get(v_t_5298_, 4);
v_isSharedCheck_5584_ = !lean_is_exclusive(v_t_5298_);
if (v_isSharedCheck_5584_ == 0)
{
v___x_5305_ = v_t_5298_;
v_isShared_5306_ = v_isSharedCheck_5584_;
goto v_resetjp_5304_;
}
else
{
lean_inc(v_r_5303_);
lean_inc(v_l_5302_);
lean_inc(v_v_5301_);
lean_inc(v_k_5300_);
lean_inc(v_size_5299_);
lean_dec(v_t_5298_);
v___x_5305_ = lean_box(0);
v_isShared_5306_ = v_isSharedCheck_5584_;
goto v_resetjp_5304_;
}
v_resetjp_5304_:
{
uint8_t v___x_5307_; 
v___x_5307_ = lean_nat_dec_lt(v_k_5300_, v_k_5296_);
if (v___x_5307_ == 0)
{
uint8_t v___x_5308_; 
v___x_5308_ = lean_nat_dec_eq(v_k_5300_, v_k_5296_);
if (v___x_5308_ == 0)
{
lean_object* v_impl_5309_; lean_object* v___x_5310_; 
lean_dec(v_size_5299_);
v_impl_5309_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5296_, v_v_5297_, v_r_5303_);
v___x_5310_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5302_) == 0)
{
lean_object* v_size_5311_; lean_object* v_size_5312_; lean_object* v_k_5313_; lean_object* v_v_5314_; lean_object* v_l_5315_; lean_object* v_r_5316_; lean_object* v___x_5317_; lean_object* v___x_5318_; uint8_t v___x_5319_; 
v_size_5311_ = lean_ctor_get(v_l_5302_, 0);
v_size_5312_ = lean_ctor_get(v_impl_5309_, 0);
lean_inc(v_size_5312_);
v_k_5313_ = lean_ctor_get(v_impl_5309_, 1);
lean_inc(v_k_5313_);
v_v_5314_ = lean_ctor_get(v_impl_5309_, 2);
lean_inc(v_v_5314_);
v_l_5315_ = lean_ctor_get(v_impl_5309_, 3);
lean_inc(v_l_5315_);
v_r_5316_ = lean_ctor_get(v_impl_5309_, 4);
lean_inc(v_r_5316_);
v___x_5317_ = lean_unsigned_to_nat(3u);
v___x_5318_ = lean_nat_mul(v___x_5317_, v_size_5311_);
v___x_5319_ = lean_nat_dec_lt(v___x_5318_, v_size_5312_);
lean_dec(v___x_5318_);
if (v___x_5319_ == 0)
{
lean_object* v___x_5320_; lean_object* v___x_5321_; lean_object* v___x_5323_; 
lean_dec(v_r_5316_);
lean_dec(v_l_5315_);
lean_dec(v_v_5314_);
lean_dec(v_k_5313_);
v___x_5320_ = lean_nat_add(v___x_5310_, v_size_5311_);
v___x_5321_ = lean_nat_add(v___x_5320_, v_size_5312_);
lean_dec(v_size_5312_);
lean_dec(v___x_5320_);
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 4, v_impl_5309_);
lean_ctor_set(v___x_5305_, 0, v___x_5321_);
v___x_5323_ = v___x_5305_;
goto v_reusejp_5322_;
}
else
{
lean_object* v_reuseFailAlloc_5324_; 
v_reuseFailAlloc_5324_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5324_, 0, v___x_5321_);
lean_ctor_set(v_reuseFailAlloc_5324_, 1, v_k_5300_);
lean_ctor_set(v_reuseFailAlloc_5324_, 2, v_v_5301_);
lean_ctor_set(v_reuseFailAlloc_5324_, 3, v_l_5302_);
lean_ctor_set(v_reuseFailAlloc_5324_, 4, v_impl_5309_);
v___x_5323_ = v_reuseFailAlloc_5324_;
goto v_reusejp_5322_;
}
v_reusejp_5322_:
{
return v___x_5323_;
}
}
else
{
lean_object* v___x_5326_; uint8_t v_isShared_5327_; uint8_t v_isSharedCheck_5388_; 
v_isSharedCheck_5388_ = !lean_is_exclusive(v_impl_5309_);
if (v_isSharedCheck_5388_ == 0)
{
lean_object* v_unused_5389_; lean_object* v_unused_5390_; lean_object* v_unused_5391_; lean_object* v_unused_5392_; lean_object* v_unused_5393_; 
v_unused_5389_ = lean_ctor_get(v_impl_5309_, 4);
lean_dec(v_unused_5389_);
v_unused_5390_ = lean_ctor_get(v_impl_5309_, 3);
lean_dec(v_unused_5390_);
v_unused_5391_ = lean_ctor_get(v_impl_5309_, 2);
lean_dec(v_unused_5391_);
v_unused_5392_ = lean_ctor_get(v_impl_5309_, 1);
lean_dec(v_unused_5392_);
v_unused_5393_ = lean_ctor_get(v_impl_5309_, 0);
lean_dec(v_unused_5393_);
v___x_5326_ = v_impl_5309_;
v_isShared_5327_ = v_isSharedCheck_5388_;
goto v_resetjp_5325_;
}
else
{
lean_dec(v_impl_5309_);
v___x_5326_ = lean_box(0);
v_isShared_5327_ = v_isSharedCheck_5388_;
goto v_resetjp_5325_;
}
v_resetjp_5325_:
{
lean_object* v_size_5328_; lean_object* v_k_5329_; lean_object* v_v_5330_; lean_object* v_l_5331_; lean_object* v_r_5332_; lean_object* v_size_5333_; lean_object* v___x_5334_; lean_object* v___x_5335_; uint8_t v___x_5336_; 
v_size_5328_ = lean_ctor_get(v_l_5315_, 0);
v_k_5329_ = lean_ctor_get(v_l_5315_, 1);
v_v_5330_ = lean_ctor_get(v_l_5315_, 2);
v_l_5331_ = lean_ctor_get(v_l_5315_, 3);
v_r_5332_ = lean_ctor_get(v_l_5315_, 4);
v_size_5333_ = lean_ctor_get(v_r_5316_, 0);
v___x_5334_ = lean_unsigned_to_nat(2u);
v___x_5335_ = lean_nat_mul(v___x_5334_, v_size_5333_);
v___x_5336_ = lean_nat_dec_lt(v_size_5328_, v___x_5335_);
lean_dec(v___x_5335_);
if (v___x_5336_ == 0)
{
lean_object* v___x_5338_; uint8_t v_isShared_5339_; uint8_t v_isSharedCheck_5364_; 
lean_inc(v_r_5332_);
lean_inc(v_l_5331_);
lean_inc(v_v_5330_);
lean_inc(v_k_5329_);
v_isSharedCheck_5364_ = !lean_is_exclusive(v_l_5315_);
if (v_isSharedCheck_5364_ == 0)
{
lean_object* v_unused_5365_; lean_object* v_unused_5366_; lean_object* v_unused_5367_; lean_object* v_unused_5368_; lean_object* v_unused_5369_; 
v_unused_5365_ = lean_ctor_get(v_l_5315_, 4);
lean_dec(v_unused_5365_);
v_unused_5366_ = lean_ctor_get(v_l_5315_, 3);
lean_dec(v_unused_5366_);
v_unused_5367_ = lean_ctor_get(v_l_5315_, 2);
lean_dec(v_unused_5367_);
v_unused_5368_ = lean_ctor_get(v_l_5315_, 1);
lean_dec(v_unused_5368_);
v_unused_5369_ = lean_ctor_get(v_l_5315_, 0);
lean_dec(v_unused_5369_);
v___x_5338_ = v_l_5315_;
v_isShared_5339_ = v_isSharedCheck_5364_;
goto v_resetjp_5337_;
}
else
{
lean_dec(v_l_5315_);
v___x_5338_ = lean_box(0);
v_isShared_5339_ = v_isSharedCheck_5364_;
goto v_resetjp_5337_;
}
v_resetjp_5337_:
{
lean_object* v___x_5340_; lean_object* v___x_5341_; lean_object* v___y_5343_; lean_object* v___y_5344_; lean_object* v___y_5345_; lean_object* v___y_5354_; 
v___x_5340_ = lean_nat_add(v___x_5310_, v_size_5311_);
v___x_5341_ = lean_nat_add(v___x_5340_, v_size_5312_);
lean_dec(v_size_5312_);
if (lean_obj_tag(v_l_5331_) == 0)
{
lean_object* v_size_5362_; 
v_size_5362_ = lean_ctor_get(v_l_5331_, 0);
lean_inc(v_size_5362_);
v___y_5354_ = v_size_5362_;
goto v___jp_5353_;
}
else
{
lean_object* v___x_5363_; 
v___x_5363_ = lean_unsigned_to_nat(0u);
v___y_5354_ = v___x_5363_;
goto v___jp_5353_;
}
v___jp_5342_:
{
lean_object* v___x_5346_; lean_object* v___x_5348_; 
v___x_5346_ = lean_nat_add(v___y_5343_, v___y_5345_);
lean_dec(v___y_5345_);
lean_dec(v___y_5343_);
if (v_isShared_5339_ == 0)
{
lean_ctor_set(v___x_5338_, 4, v_r_5316_);
lean_ctor_set(v___x_5338_, 3, v_r_5332_);
lean_ctor_set(v___x_5338_, 2, v_v_5314_);
lean_ctor_set(v___x_5338_, 1, v_k_5313_);
lean_ctor_set(v___x_5338_, 0, v___x_5346_);
v___x_5348_ = v___x_5338_;
goto v_reusejp_5347_;
}
else
{
lean_object* v_reuseFailAlloc_5352_; 
v_reuseFailAlloc_5352_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5352_, 0, v___x_5346_);
lean_ctor_set(v_reuseFailAlloc_5352_, 1, v_k_5313_);
lean_ctor_set(v_reuseFailAlloc_5352_, 2, v_v_5314_);
lean_ctor_set(v_reuseFailAlloc_5352_, 3, v_r_5332_);
lean_ctor_set(v_reuseFailAlloc_5352_, 4, v_r_5316_);
v___x_5348_ = v_reuseFailAlloc_5352_;
goto v_reusejp_5347_;
}
v_reusejp_5347_:
{
lean_object* v___x_5350_; 
if (v_isShared_5327_ == 0)
{
lean_ctor_set(v___x_5326_, 4, v___x_5348_);
lean_ctor_set(v___x_5326_, 3, v___y_5344_);
lean_ctor_set(v___x_5326_, 2, v_v_5330_);
lean_ctor_set(v___x_5326_, 1, v_k_5329_);
lean_ctor_set(v___x_5326_, 0, v___x_5341_);
v___x_5350_ = v___x_5326_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5351_; 
v_reuseFailAlloc_5351_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5351_, 0, v___x_5341_);
lean_ctor_set(v_reuseFailAlloc_5351_, 1, v_k_5329_);
lean_ctor_set(v_reuseFailAlloc_5351_, 2, v_v_5330_);
lean_ctor_set(v_reuseFailAlloc_5351_, 3, v___y_5344_);
lean_ctor_set(v_reuseFailAlloc_5351_, 4, v___x_5348_);
v___x_5350_ = v_reuseFailAlloc_5351_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
return v___x_5350_;
}
}
}
v___jp_5353_:
{
lean_object* v___x_5355_; lean_object* v___x_5357_; 
v___x_5355_ = lean_nat_add(v___x_5340_, v___y_5354_);
lean_dec(v___y_5354_);
lean_dec(v___x_5340_);
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 4, v_l_5331_);
lean_ctor_set(v___x_5305_, 0, v___x_5355_);
v___x_5357_ = v___x_5305_;
goto v_reusejp_5356_;
}
else
{
lean_object* v_reuseFailAlloc_5361_; 
v_reuseFailAlloc_5361_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5361_, 0, v___x_5355_);
lean_ctor_set(v_reuseFailAlloc_5361_, 1, v_k_5300_);
lean_ctor_set(v_reuseFailAlloc_5361_, 2, v_v_5301_);
lean_ctor_set(v_reuseFailAlloc_5361_, 3, v_l_5302_);
lean_ctor_set(v_reuseFailAlloc_5361_, 4, v_l_5331_);
v___x_5357_ = v_reuseFailAlloc_5361_;
goto v_reusejp_5356_;
}
v_reusejp_5356_:
{
lean_object* v___x_5358_; 
v___x_5358_ = lean_nat_add(v___x_5310_, v_size_5333_);
if (lean_obj_tag(v_r_5332_) == 0)
{
lean_object* v_size_5359_; 
v_size_5359_ = lean_ctor_get(v_r_5332_, 0);
lean_inc(v_size_5359_);
v___y_5343_ = v___x_5358_;
v___y_5344_ = v___x_5357_;
v___y_5345_ = v_size_5359_;
goto v___jp_5342_;
}
else
{
lean_object* v___x_5360_; 
v___x_5360_ = lean_unsigned_to_nat(0u);
v___y_5343_ = v___x_5358_;
v___y_5344_ = v___x_5357_;
v___y_5345_ = v___x_5360_;
goto v___jp_5342_;
}
}
}
}
}
else
{
lean_object* v___x_5370_; lean_object* v___x_5371_; lean_object* v___x_5372_; lean_object* v___x_5374_; 
lean_del_object(v___x_5305_);
v___x_5370_ = lean_nat_add(v___x_5310_, v_size_5311_);
v___x_5371_ = lean_nat_add(v___x_5370_, v_size_5312_);
lean_dec(v_size_5312_);
v___x_5372_ = lean_nat_add(v___x_5370_, v_size_5328_);
lean_dec(v___x_5370_);
lean_inc_ref(v_l_5302_);
if (v_isShared_5327_ == 0)
{
lean_ctor_set(v___x_5326_, 4, v_l_5315_);
lean_ctor_set(v___x_5326_, 3, v_l_5302_);
lean_ctor_set(v___x_5326_, 2, v_v_5301_);
lean_ctor_set(v___x_5326_, 1, v_k_5300_);
lean_ctor_set(v___x_5326_, 0, v___x_5372_);
v___x_5374_ = v___x_5326_;
goto v_reusejp_5373_;
}
else
{
lean_object* v_reuseFailAlloc_5387_; 
v_reuseFailAlloc_5387_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5387_, 0, v___x_5372_);
lean_ctor_set(v_reuseFailAlloc_5387_, 1, v_k_5300_);
lean_ctor_set(v_reuseFailAlloc_5387_, 2, v_v_5301_);
lean_ctor_set(v_reuseFailAlloc_5387_, 3, v_l_5302_);
lean_ctor_set(v_reuseFailAlloc_5387_, 4, v_l_5315_);
v___x_5374_ = v_reuseFailAlloc_5387_;
goto v_reusejp_5373_;
}
v_reusejp_5373_:
{
lean_object* v___x_5376_; uint8_t v_isShared_5377_; uint8_t v_isSharedCheck_5381_; 
v_isSharedCheck_5381_ = !lean_is_exclusive(v_l_5302_);
if (v_isSharedCheck_5381_ == 0)
{
lean_object* v_unused_5382_; lean_object* v_unused_5383_; lean_object* v_unused_5384_; lean_object* v_unused_5385_; lean_object* v_unused_5386_; 
v_unused_5382_ = lean_ctor_get(v_l_5302_, 4);
lean_dec(v_unused_5382_);
v_unused_5383_ = lean_ctor_get(v_l_5302_, 3);
lean_dec(v_unused_5383_);
v_unused_5384_ = lean_ctor_get(v_l_5302_, 2);
lean_dec(v_unused_5384_);
v_unused_5385_ = lean_ctor_get(v_l_5302_, 1);
lean_dec(v_unused_5385_);
v_unused_5386_ = lean_ctor_get(v_l_5302_, 0);
lean_dec(v_unused_5386_);
v___x_5376_ = v_l_5302_;
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
else
{
lean_dec(v_l_5302_);
v___x_5376_ = lean_box(0);
v_isShared_5377_ = v_isSharedCheck_5381_;
goto v_resetjp_5375_;
}
v_resetjp_5375_:
{
lean_object* v___x_5379_; 
if (v_isShared_5377_ == 0)
{
lean_ctor_set(v___x_5376_, 4, v_r_5316_);
lean_ctor_set(v___x_5376_, 3, v___x_5374_);
lean_ctor_set(v___x_5376_, 2, v_v_5314_);
lean_ctor_set(v___x_5376_, 1, v_k_5313_);
lean_ctor_set(v___x_5376_, 0, v___x_5371_);
v___x_5379_ = v___x_5376_;
goto v_reusejp_5378_;
}
else
{
lean_object* v_reuseFailAlloc_5380_; 
v_reuseFailAlloc_5380_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5380_, 0, v___x_5371_);
lean_ctor_set(v_reuseFailAlloc_5380_, 1, v_k_5313_);
lean_ctor_set(v_reuseFailAlloc_5380_, 2, v_v_5314_);
lean_ctor_set(v_reuseFailAlloc_5380_, 3, v___x_5374_);
lean_ctor_set(v_reuseFailAlloc_5380_, 4, v_r_5316_);
v___x_5379_ = v_reuseFailAlloc_5380_;
goto v_reusejp_5378_;
}
v_reusejp_5378_:
{
return v___x_5379_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5394_; 
v_l_5394_ = lean_ctor_get(v_impl_5309_, 3);
lean_inc(v_l_5394_);
if (lean_obj_tag(v_l_5394_) == 0)
{
lean_object* v_r_5395_; lean_object* v_k_5396_; lean_object* v_v_5397_; lean_object* v___x_5399_; uint8_t v_isShared_5400_; uint8_t v_isSharedCheck_5420_; 
v_r_5395_ = lean_ctor_get(v_impl_5309_, 4);
v_k_5396_ = lean_ctor_get(v_impl_5309_, 1);
v_v_5397_ = lean_ctor_get(v_impl_5309_, 2);
v_isSharedCheck_5420_ = !lean_is_exclusive(v_impl_5309_);
if (v_isSharedCheck_5420_ == 0)
{
lean_object* v_unused_5421_; lean_object* v_unused_5422_; 
v_unused_5421_ = lean_ctor_get(v_impl_5309_, 3);
lean_dec(v_unused_5421_);
v_unused_5422_ = lean_ctor_get(v_impl_5309_, 0);
lean_dec(v_unused_5422_);
v___x_5399_ = v_impl_5309_;
v_isShared_5400_ = v_isSharedCheck_5420_;
goto v_resetjp_5398_;
}
else
{
lean_inc(v_r_5395_);
lean_inc(v_v_5397_);
lean_inc(v_k_5396_);
lean_dec(v_impl_5309_);
v___x_5399_ = lean_box(0);
v_isShared_5400_ = v_isSharedCheck_5420_;
goto v_resetjp_5398_;
}
v_resetjp_5398_:
{
lean_object* v_k_5401_; lean_object* v_v_5402_; lean_object* v___x_5404_; uint8_t v_isShared_5405_; uint8_t v_isSharedCheck_5416_; 
v_k_5401_ = lean_ctor_get(v_l_5394_, 1);
v_v_5402_ = lean_ctor_get(v_l_5394_, 2);
v_isSharedCheck_5416_ = !lean_is_exclusive(v_l_5394_);
if (v_isSharedCheck_5416_ == 0)
{
lean_object* v_unused_5417_; lean_object* v_unused_5418_; lean_object* v_unused_5419_; 
v_unused_5417_ = lean_ctor_get(v_l_5394_, 4);
lean_dec(v_unused_5417_);
v_unused_5418_ = lean_ctor_get(v_l_5394_, 3);
lean_dec(v_unused_5418_);
v_unused_5419_ = lean_ctor_get(v_l_5394_, 0);
lean_dec(v_unused_5419_);
v___x_5404_ = v_l_5394_;
v_isShared_5405_ = v_isSharedCheck_5416_;
goto v_resetjp_5403_;
}
else
{
lean_inc(v_v_5402_);
lean_inc(v_k_5401_);
lean_dec(v_l_5394_);
v___x_5404_ = lean_box(0);
v_isShared_5405_ = v_isSharedCheck_5416_;
goto v_resetjp_5403_;
}
v_resetjp_5403_:
{
lean_object* v___x_5406_; lean_object* v___x_5408_; 
v___x_5406_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5395_, 2);
if (v_isShared_5405_ == 0)
{
lean_ctor_set(v___x_5404_, 4, v_r_5395_);
lean_ctor_set(v___x_5404_, 3, v_r_5395_);
lean_ctor_set(v___x_5404_, 2, v_v_5301_);
lean_ctor_set(v___x_5404_, 1, v_k_5300_);
lean_ctor_set(v___x_5404_, 0, v___x_5310_);
v___x_5408_ = v___x_5404_;
goto v_reusejp_5407_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v___x_5310_);
lean_ctor_set(v_reuseFailAlloc_5415_, 1, v_k_5300_);
lean_ctor_set(v_reuseFailAlloc_5415_, 2, v_v_5301_);
lean_ctor_set(v_reuseFailAlloc_5415_, 3, v_r_5395_);
lean_ctor_set(v_reuseFailAlloc_5415_, 4, v_r_5395_);
v___x_5408_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5407_;
}
v_reusejp_5407_:
{
lean_object* v___x_5410_; 
lean_inc(v_r_5395_);
if (v_isShared_5400_ == 0)
{
lean_ctor_set(v___x_5399_, 3, v_r_5395_);
lean_ctor_set(v___x_5399_, 0, v___x_5310_);
v___x_5410_ = v___x_5399_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5414_; 
v_reuseFailAlloc_5414_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5414_, 0, v___x_5310_);
lean_ctor_set(v_reuseFailAlloc_5414_, 1, v_k_5396_);
lean_ctor_set(v_reuseFailAlloc_5414_, 2, v_v_5397_);
lean_ctor_set(v_reuseFailAlloc_5414_, 3, v_r_5395_);
lean_ctor_set(v_reuseFailAlloc_5414_, 4, v_r_5395_);
v___x_5410_ = v_reuseFailAlloc_5414_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
lean_object* v___x_5412_; 
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 4, v___x_5410_);
lean_ctor_set(v___x_5305_, 3, v___x_5408_);
lean_ctor_set(v___x_5305_, 2, v_v_5402_);
lean_ctor_set(v___x_5305_, 1, v_k_5401_);
lean_ctor_set(v___x_5305_, 0, v___x_5406_);
v___x_5412_ = v___x_5305_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5413_; 
v_reuseFailAlloc_5413_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5413_, 0, v___x_5406_);
lean_ctor_set(v_reuseFailAlloc_5413_, 1, v_k_5401_);
lean_ctor_set(v_reuseFailAlloc_5413_, 2, v_v_5402_);
lean_ctor_set(v_reuseFailAlloc_5413_, 3, v___x_5408_);
lean_ctor_set(v_reuseFailAlloc_5413_, 4, v___x_5410_);
v___x_5412_ = v_reuseFailAlloc_5413_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
return v___x_5412_;
}
}
}
}
}
}
else
{
lean_object* v_r_5423_; 
v_r_5423_ = lean_ctor_get(v_impl_5309_, 4);
lean_inc(v_r_5423_);
if (lean_obj_tag(v_r_5423_) == 0)
{
lean_object* v_k_5424_; lean_object* v_v_5425_; lean_object* v___x_5427_; uint8_t v_isShared_5428_; uint8_t v_isSharedCheck_5436_; 
v_k_5424_ = lean_ctor_get(v_impl_5309_, 1);
v_v_5425_ = lean_ctor_get(v_impl_5309_, 2);
v_isSharedCheck_5436_ = !lean_is_exclusive(v_impl_5309_);
if (v_isSharedCheck_5436_ == 0)
{
lean_object* v_unused_5437_; lean_object* v_unused_5438_; lean_object* v_unused_5439_; 
v_unused_5437_ = lean_ctor_get(v_impl_5309_, 4);
lean_dec(v_unused_5437_);
v_unused_5438_ = lean_ctor_get(v_impl_5309_, 3);
lean_dec(v_unused_5438_);
v_unused_5439_ = lean_ctor_get(v_impl_5309_, 0);
lean_dec(v_unused_5439_);
v___x_5427_ = v_impl_5309_;
v_isShared_5428_ = v_isSharedCheck_5436_;
goto v_resetjp_5426_;
}
else
{
lean_inc(v_v_5425_);
lean_inc(v_k_5424_);
lean_dec(v_impl_5309_);
v___x_5427_ = lean_box(0);
v_isShared_5428_ = v_isSharedCheck_5436_;
goto v_resetjp_5426_;
}
v_resetjp_5426_:
{
lean_object* v___x_5429_; lean_object* v___x_5431_; 
v___x_5429_ = lean_unsigned_to_nat(3u);
if (v_isShared_5428_ == 0)
{
lean_ctor_set(v___x_5427_, 4, v_l_5394_);
lean_ctor_set(v___x_5427_, 2, v_v_5301_);
lean_ctor_set(v___x_5427_, 1, v_k_5300_);
lean_ctor_set(v___x_5427_, 0, v___x_5310_);
v___x_5431_ = v___x_5427_;
goto v_reusejp_5430_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v___x_5310_);
lean_ctor_set(v_reuseFailAlloc_5435_, 1, v_k_5300_);
lean_ctor_set(v_reuseFailAlloc_5435_, 2, v_v_5301_);
lean_ctor_set(v_reuseFailAlloc_5435_, 3, v_l_5394_);
lean_ctor_set(v_reuseFailAlloc_5435_, 4, v_l_5394_);
v___x_5431_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5430_;
}
v_reusejp_5430_:
{
lean_object* v___x_5433_; 
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 4, v_r_5423_);
lean_ctor_set(v___x_5305_, 3, v___x_5431_);
lean_ctor_set(v___x_5305_, 2, v_v_5425_);
lean_ctor_set(v___x_5305_, 1, v_k_5424_);
lean_ctor_set(v___x_5305_, 0, v___x_5429_);
v___x_5433_ = v___x_5305_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5434_; 
v_reuseFailAlloc_5434_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5434_, 0, v___x_5429_);
lean_ctor_set(v_reuseFailAlloc_5434_, 1, v_k_5424_);
lean_ctor_set(v_reuseFailAlloc_5434_, 2, v_v_5425_);
lean_ctor_set(v_reuseFailAlloc_5434_, 3, v___x_5431_);
lean_ctor_set(v_reuseFailAlloc_5434_, 4, v_r_5423_);
v___x_5433_ = v_reuseFailAlloc_5434_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
return v___x_5433_;
}
}
}
}
else
{
lean_object* v___x_5440_; lean_object* v___x_5442_; 
v___x_5440_ = lean_unsigned_to_nat(2u);
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 4, v_impl_5309_);
lean_ctor_set(v___x_5305_, 3, v_r_5423_);
lean_ctor_set(v___x_5305_, 0, v___x_5440_);
v___x_5442_ = v___x_5305_;
goto v_reusejp_5441_;
}
else
{
lean_object* v_reuseFailAlloc_5443_; 
v_reuseFailAlloc_5443_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5443_, 0, v___x_5440_);
lean_ctor_set(v_reuseFailAlloc_5443_, 1, v_k_5300_);
lean_ctor_set(v_reuseFailAlloc_5443_, 2, v_v_5301_);
lean_ctor_set(v_reuseFailAlloc_5443_, 3, v_r_5423_);
lean_ctor_set(v_reuseFailAlloc_5443_, 4, v_impl_5309_);
v___x_5442_ = v_reuseFailAlloc_5443_;
goto v_reusejp_5441_;
}
v_reusejp_5441_:
{
return v___x_5442_;
}
}
}
}
}
else
{
lean_object* v___x_5445_; 
lean_dec(v_v_5301_);
lean_dec(v_k_5300_);
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 2, v_v_5297_);
lean_ctor_set(v___x_5305_, 1, v_k_5296_);
v___x_5445_ = v___x_5305_;
goto v_reusejp_5444_;
}
else
{
lean_object* v_reuseFailAlloc_5446_; 
v_reuseFailAlloc_5446_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5446_, 0, v_size_5299_);
lean_ctor_set(v_reuseFailAlloc_5446_, 1, v_k_5296_);
lean_ctor_set(v_reuseFailAlloc_5446_, 2, v_v_5297_);
lean_ctor_set(v_reuseFailAlloc_5446_, 3, v_l_5302_);
lean_ctor_set(v_reuseFailAlloc_5446_, 4, v_r_5303_);
v___x_5445_ = v_reuseFailAlloc_5446_;
goto v_reusejp_5444_;
}
v_reusejp_5444_:
{
return v___x_5445_;
}
}
}
else
{
lean_object* v_impl_5447_; lean_object* v___x_5448_; 
lean_dec(v_size_5299_);
v_impl_5447_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5296_, v_v_5297_, v_l_5302_);
v___x_5448_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5303_) == 0)
{
lean_object* v_size_5449_; lean_object* v_size_5450_; lean_object* v_k_5451_; lean_object* v_v_5452_; lean_object* v_l_5453_; lean_object* v_r_5454_; lean_object* v___x_5455_; lean_object* v___x_5456_; uint8_t v___x_5457_; 
v_size_5449_ = lean_ctor_get(v_r_5303_, 0);
v_size_5450_ = lean_ctor_get(v_impl_5447_, 0);
lean_inc(v_size_5450_);
v_k_5451_ = lean_ctor_get(v_impl_5447_, 1);
lean_inc(v_k_5451_);
v_v_5452_ = lean_ctor_get(v_impl_5447_, 2);
lean_inc(v_v_5452_);
v_l_5453_ = lean_ctor_get(v_impl_5447_, 3);
lean_inc(v_l_5453_);
v_r_5454_ = lean_ctor_get(v_impl_5447_, 4);
lean_inc(v_r_5454_);
v___x_5455_ = lean_unsigned_to_nat(3u);
v___x_5456_ = lean_nat_mul(v___x_5455_, v_size_5449_);
v___x_5457_ = lean_nat_dec_lt(v___x_5456_, v_size_5450_);
lean_dec(v___x_5456_);
if (v___x_5457_ == 0)
{
lean_object* v___x_5458_; lean_object* v___x_5459_; lean_object* v___x_5461_; 
lean_dec(v_r_5454_);
lean_dec(v_l_5453_);
lean_dec(v_v_5452_);
lean_dec(v_k_5451_);
v___x_5458_ = lean_nat_add(v___x_5448_, v_size_5450_);
lean_dec(v_size_5450_);
v___x_5459_ = lean_nat_add(v___x_5458_, v_size_5449_);
lean_dec(v___x_5458_);
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 3, v_impl_5447_);
lean_ctor_set(v___x_5305_, 0, v___x_5459_);
v___x_5461_ = v___x_5305_;
goto v_reusejp_5460_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v___x_5459_);
lean_ctor_set(v_reuseFailAlloc_5462_, 1, v_k_5300_);
lean_ctor_set(v_reuseFailAlloc_5462_, 2, v_v_5301_);
lean_ctor_set(v_reuseFailAlloc_5462_, 3, v_impl_5447_);
lean_ctor_set(v_reuseFailAlloc_5462_, 4, v_r_5303_);
v___x_5461_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5460_;
}
v_reusejp_5460_:
{
return v___x_5461_;
}
}
else
{
lean_object* v___x_5464_; uint8_t v_isShared_5465_; uint8_t v_isSharedCheck_5528_; 
v_isSharedCheck_5528_ = !lean_is_exclusive(v_impl_5447_);
if (v_isSharedCheck_5528_ == 0)
{
lean_object* v_unused_5529_; lean_object* v_unused_5530_; lean_object* v_unused_5531_; lean_object* v_unused_5532_; lean_object* v_unused_5533_; 
v_unused_5529_ = lean_ctor_get(v_impl_5447_, 4);
lean_dec(v_unused_5529_);
v_unused_5530_ = lean_ctor_get(v_impl_5447_, 3);
lean_dec(v_unused_5530_);
v_unused_5531_ = lean_ctor_get(v_impl_5447_, 2);
lean_dec(v_unused_5531_);
v_unused_5532_ = lean_ctor_get(v_impl_5447_, 1);
lean_dec(v_unused_5532_);
v_unused_5533_ = lean_ctor_get(v_impl_5447_, 0);
lean_dec(v_unused_5533_);
v___x_5464_ = v_impl_5447_;
v_isShared_5465_ = v_isSharedCheck_5528_;
goto v_resetjp_5463_;
}
else
{
lean_dec(v_impl_5447_);
v___x_5464_ = lean_box(0);
v_isShared_5465_ = v_isSharedCheck_5528_;
goto v_resetjp_5463_;
}
v_resetjp_5463_:
{
lean_object* v_size_5466_; lean_object* v_size_5467_; lean_object* v_k_5468_; lean_object* v_v_5469_; lean_object* v_l_5470_; lean_object* v_r_5471_; lean_object* v___x_5472_; lean_object* v___x_5473_; uint8_t v___x_5474_; 
v_size_5466_ = lean_ctor_get(v_l_5453_, 0);
v_size_5467_ = lean_ctor_get(v_r_5454_, 0);
v_k_5468_ = lean_ctor_get(v_r_5454_, 1);
v_v_5469_ = lean_ctor_get(v_r_5454_, 2);
v_l_5470_ = lean_ctor_get(v_r_5454_, 3);
v_r_5471_ = lean_ctor_get(v_r_5454_, 4);
v___x_5472_ = lean_unsigned_to_nat(2u);
v___x_5473_ = lean_nat_mul(v___x_5472_, v_size_5466_);
v___x_5474_ = lean_nat_dec_lt(v_size_5467_, v___x_5473_);
lean_dec(v___x_5473_);
if (v___x_5474_ == 0)
{
lean_object* v___x_5476_; uint8_t v_isShared_5477_; uint8_t v_isSharedCheck_5503_; 
lean_inc(v_r_5471_);
lean_inc(v_l_5470_);
lean_inc(v_v_5469_);
lean_inc(v_k_5468_);
v_isSharedCheck_5503_ = !lean_is_exclusive(v_r_5454_);
if (v_isSharedCheck_5503_ == 0)
{
lean_object* v_unused_5504_; lean_object* v_unused_5505_; lean_object* v_unused_5506_; lean_object* v_unused_5507_; lean_object* v_unused_5508_; 
v_unused_5504_ = lean_ctor_get(v_r_5454_, 4);
lean_dec(v_unused_5504_);
v_unused_5505_ = lean_ctor_get(v_r_5454_, 3);
lean_dec(v_unused_5505_);
v_unused_5506_ = lean_ctor_get(v_r_5454_, 2);
lean_dec(v_unused_5506_);
v_unused_5507_ = lean_ctor_get(v_r_5454_, 1);
lean_dec(v_unused_5507_);
v_unused_5508_ = lean_ctor_get(v_r_5454_, 0);
lean_dec(v_unused_5508_);
v___x_5476_ = v_r_5454_;
v_isShared_5477_ = v_isSharedCheck_5503_;
goto v_resetjp_5475_;
}
else
{
lean_dec(v_r_5454_);
v___x_5476_ = lean_box(0);
v_isShared_5477_ = v_isSharedCheck_5503_;
goto v_resetjp_5475_;
}
v_resetjp_5475_:
{
lean_object* v___x_5478_; lean_object* v___x_5479_; lean_object* v___y_5481_; lean_object* v___y_5482_; lean_object* v___y_5483_; lean_object* v___x_5491_; lean_object* v___y_5493_; 
v___x_5478_ = lean_nat_add(v___x_5448_, v_size_5450_);
lean_dec(v_size_5450_);
v___x_5479_ = lean_nat_add(v___x_5478_, v_size_5449_);
lean_dec(v___x_5478_);
v___x_5491_ = lean_nat_add(v___x_5448_, v_size_5466_);
if (lean_obj_tag(v_l_5470_) == 0)
{
lean_object* v_size_5501_; 
v_size_5501_ = lean_ctor_get(v_l_5470_, 0);
lean_inc(v_size_5501_);
v___y_5493_ = v_size_5501_;
goto v___jp_5492_;
}
else
{
lean_object* v___x_5502_; 
v___x_5502_ = lean_unsigned_to_nat(0u);
v___y_5493_ = v___x_5502_;
goto v___jp_5492_;
}
v___jp_5480_:
{
lean_object* v___x_5484_; lean_object* v___x_5486_; 
v___x_5484_ = lean_nat_add(v___y_5481_, v___y_5483_);
lean_dec(v___y_5483_);
lean_dec(v___y_5481_);
if (v_isShared_5477_ == 0)
{
lean_ctor_set(v___x_5476_, 4, v_r_5303_);
lean_ctor_set(v___x_5476_, 3, v_r_5471_);
lean_ctor_set(v___x_5476_, 2, v_v_5301_);
lean_ctor_set(v___x_5476_, 1, v_k_5300_);
lean_ctor_set(v___x_5476_, 0, v___x_5484_);
v___x_5486_ = v___x_5476_;
goto v_reusejp_5485_;
}
else
{
lean_object* v_reuseFailAlloc_5490_; 
v_reuseFailAlloc_5490_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5490_, 0, v___x_5484_);
lean_ctor_set(v_reuseFailAlloc_5490_, 1, v_k_5300_);
lean_ctor_set(v_reuseFailAlloc_5490_, 2, v_v_5301_);
lean_ctor_set(v_reuseFailAlloc_5490_, 3, v_r_5471_);
lean_ctor_set(v_reuseFailAlloc_5490_, 4, v_r_5303_);
v___x_5486_ = v_reuseFailAlloc_5490_;
goto v_reusejp_5485_;
}
v_reusejp_5485_:
{
lean_object* v___x_5488_; 
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 4, v___x_5486_);
lean_ctor_set(v___x_5464_, 3, v___y_5482_);
lean_ctor_set(v___x_5464_, 2, v_v_5469_);
lean_ctor_set(v___x_5464_, 1, v_k_5468_);
lean_ctor_set(v___x_5464_, 0, v___x_5479_);
v___x_5488_ = v___x_5464_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5489_; 
v_reuseFailAlloc_5489_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5489_, 0, v___x_5479_);
lean_ctor_set(v_reuseFailAlloc_5489_, 1, v_k_5468_);
lean_ctor_set(v_reuseFailAlloc_5489_, 2, v_v_5469_);
lean_ctor_set(v_reuseFailAlloc_5489_, 3, v___y_5482_);
lean_ctor_set(v_reuseFailAlloc_5489_, 4, v___x_5486_);
v___x_5488_ = v_reuseFailAlloc_5489_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
return v___x_5488_;
}
}
}
v___jp_5492_:
{
lean_object* v___x_5494_; lean_object* v___x_5496_; 
v___x_5494_ = lean_nat_add(v___x_5491_, v___y_5493_);
lean_dec(v___y_5493_);
lean_dec(v___x_5491_);
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 4, v_l_5470_);
lean_ctor_set(v___x_5305_, 3, v_l_5453_);
lean_ctor_set(v___x_5305_, 2, v_v_5452_);
lean_ctor_set(v___x_5305_, 1, v_k_5451_);
lean_ctor_set(v___x_5305_, 0, v___x_5494_);
v___x_5496_ = v___x_5305_;
goto v_reusejp_5495_;
}
else
{
lean_object* v_reuseFailAlloc_5500_; 
v_reuseFailAlloc_5500_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5500_, 0, v___x_5494_);
lean_ctor_set(v_reuseFailAlloc_5500_, 1, v_k_5451_);
lean_ctor_set(v_reuseFailAlloc_5500_, 2, v_v_5452_);
lean_ctor_set(v_reuseFailAlloc_5500_, 3, v_l_5453_);
lean_ctor_set(v_reuseFailAlloc_5500_, 4, v_l_5470_);
v___x_5496_ = v_reuseFailAlloc_5500_;
goto v_reusejp_5495_;
}
v_reusejp_5495_:
{
lean_object* v___x_5497_; 
v___x_5497_ = lean_nat_add(v___x_5448_, v_size_5449_);
if (lean_obj_tag(v_r_5471_) == 0)
{
lean_object* v_size_5498_; 
v_size_5498_ = lean_ctor_get(v_r_5471_, 0);
lean_inc(v_size_5498_);
v___y_5481_ = v___x_5497_;
v___y_5482_ = v___x_5496_;
v___y_5483_ = v_size_5498_;
goto v___jp_5480_;
}
else
{
lean_object* v___x_5499_; 
v___x_5499_ = lean_unsigned_to_nat(0u);
v___y_5481_ = v___x_5497_;
v___y_5482_ = v___x_5496_;
v___y_5483_ = v___x_5499_;
goto v___jp_5480_;
}
}
}
}
}
else
{
lean_object* v___x_5509_; lean_object* v___x_5510_; lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5514_; 
lean_del_object(v___x_5305_);
v___x_5509_ = lean_nat_add(v___x_5448_, v_size_5450_);
lean_dec(v_size_5450_);
v___x_5510_ = lean_nat_add(v___x_5509_, v_size_5449_);
lean_dec(v___x_5509_);
v___x_5511_ = lean_nat_add(v___x_5448_, v_size_5449_);
v___x_5512_ = lean_nat_add(v___x_5511_, v_size_5467_);
lean_dec(v___x_5511_);
lean_inc_ref(v_r_5303_);
if (v_isShared_5465_ == 0)
{
lean_ctor_set(v___x_5464_, 4, v_r_5303_);
lean_ctor_set(v___x_5464_, 3, v_r_5454_);
lean_ctor_set(v___x_5464_, 2, v_v_5301_);
lean_ctor_set(v___x_5464_, 1, v_k_5300_);
lean_ctor_set(v___x_5464_, 0, v___x_5512_);
v___x_5514_ = v___x_5464_;
goto v_reusejp_5513_;
}
else
{
lean_object* v_reuseFailAlloc_5527_; 
v_reuseFailAlloc_5527_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5527_, 0, v___x_5512_);
lean_ctor_set(v_reuseFailAlloc_5527_, 1, v_k_5300_);
lean_ctor_set(v_reuseFailAlloc_5527_, 2, v_v_5301_);
lean_ctor_set(v_reuseFailAlloc_5527_, 3, v_r_5454_);
lean_ctor_set(v_reuseFailAlloc_5527_, 4, v_r_5303_);
v___x_5514_ = v_reuseFailAlloc_5527_;
goto v_reusejp_5513_;
}
v_reusejp_5513_:
{
lean_object* v___x_5516_; uint8_t v_isShared_5517_; uint8_t v_isSharedCheck_5521_; 
v_isSharedCheck_5521_ = !lean_is_exclusive(v_r_5303_);
if (v_isSharedCheck_5521_ == 0)
{
lean_object* v_unused_5522_; lean_object* v_unused_5523_; lean_object* v_unused_5524_; lean_object* v_unused_5525_; lean_object* v_unused_5526_; 
v_unused_5522_ = lean_ctor_get(v_r_5303_, 4);
lean_dec(v_unused_5522_);
v_unused_5523_ = lean_ctor_get(v_r_5303_, 3);
lean_dec(v_unused_5523_);
v_unused_5524_ = lean_ctor_get(v_r_5303_, 2);
lean_dec(v_unused_5524_);
v_unused_5525_ = lean_ctor_get(v_r_5303_, 1);
lean_dec(v_unused_5525_);
v_unused_5526_ = lean_ctor_get(v_r_5303_, 0);
lean_dec(v_unused_5526_);
v___x_5516_ = v_r_5303_;
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
else
{
lean_dec(v_r_5303_);
v___x_5516_ = lean_box(0);
v_isShared_5517_ = v_isSharedCheck_5521_;
goto v_resetjp_5515_;
}
v_resetjp_5515_:
{
lean_object* v___x_5519_; 
if (v_isShared_5517_ == 0)
{
lean_ctor_set(v___x_5516_, 4, v___x_5514_);
lean_ctor_set(v___x_5516_, 3, v_l_5453_);
lean_ctor_set(v___x_5516_, 2, v_v_5452_);
lean_ctor_set(v___x_5516_, 1, v_k_5451_);
lean_ctor_set(v___x_5516_, 0, v___x_5510_);
v___x_5519_ = v___x_5516_;
goto v_reusejp_5518_;
}
else
{
lean_object* v_reuseFailAlloc_5520_; 
v_reuseFailAlloc_5520_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5520_, 0, v___x_5510_);
lean_ctor_set(v_reuseFailAlloc_5520_, 1, v_k_5451_);
lean_ctor_set(v_reuseFailAlloc_5520_, 2, v_v_5452_);
lean_ctor_set(v_reuseFailAlloc_5520_, 3, v_l_5453_);
lean_ctor_set(v_reuseFailAlloc_5520_, 4, v___x_5514_);
v___x_5519_ = v_reuseFailAlloc_5520_;
goto v_reusejp_5518_;
}
v_reusejp_5518_:
{
return v___x_5519_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5534_; 
v_l_5534_ = lean_ctor_get(v_impl_5447_, 3);
lean_inc(v_l_5534_);
if (lean_obj_tag(v_l_5534_) == 0)
{
lean_object* v_r_5535_; lean_object* v_k_5536_; lean_object* v_v_5537_; lean_object* v___x_5539_; uint8_t v_isShared_5540_; uint8_t v_isSharedCheck_5548_; 
v_r_5535_ = lean_ctor_get(v_impl_5447_, 4);
v_k_5536_ = lean_ctor_get(v_impl_5447_, 1);
v_v_5537_ = lean_ctor_get(v_impl_5447_, 2);
v_isSharedCheck_5548_ = !lean_is_exclusive(v_impl_5447_);
if (v_isSharedCheck_5548_ == 0)
{
lean_object* v_unused_5549_; lean_object* v_unused_5550_; 
v_unused_5549_ = lean_ctor_get(v_impl_5447_, 3);
lean_dec(v_unused_5549_);
v_unused_5550_ = lean_ctor_get(v_impl_5447_, 0);
lean_dec(v_unused_5550_);
v___x_5539_ = v_impl_5447_;
v_isShared_5540_ = v_isSharedCheck_5548_;
goto v_resetjp_5538_;
}
else
{
lean_inc(v_r_5535_);
lean_inc(v_v_5537_);
lean_inc(v_k_5536_);
lean_dec(v_impl_5447_);
v___x_5539_ = lean_box(0);
v_isShared_5540_ = v_isSharedCheck_5548_;
goto v_resetjp_5538_;
}
v_resetjp_5538_:
{
lean_object* v___x_5541_; lean_object* v___x_5543_; 
v___x_5541_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5535_);
if (v_isShared_5540_ == 0)
{
lean_ctor_set(v___x_5539_, 3, v_r_5535_);
lean_ctor_set(v___x_5539_, 2, v_v_5301_);
lean_ctor_set(v___x_5539_, 1, v_k_5300_);
lean_ctor_set(v___x_5539_, 0, v___x_5448_);
v___x_5543_ = v___x_5539_;
goto v_reusejp_5542_;
}
else
{
lean_object* v_reuseFailAlloc_5547_; 
v_reuseFailAlloc_5547_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5547_, 0, v___x_5448_);
lean_ctor_set(v_reuseFailAlloc_5547_, 1, v_k_5300_);
lean_ctor_set(v_reuseFailAlloc_5547_, 2, v_v_5301_);
lean_ctor_set(v_reuseFailAlloc_5547_, 3, v_r_5535_);
lean_ctor_set(v_reuseFailAlloc_5547_, 4, v_r_5535_);
v___x_5543_ = v_reuseFailAlloc_5547_;
goto v_reusejp_5542_;
}
v_reusejp_5542_:
{
lean_object* v___x_5545_; 
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 4, v___x_5543_);
lean_ctor_set(v___x_5305_, 3, v_l_5534_);
lean_ctor_set(v___x_5305_, 2, v_v_5537_);
lean_ctor_set(v___x_5305_, 1, v_k_5536_);
lean_ctor_set(v___x_5305_, 0, v___x_5541_);
v___x_5545_ = v___x_5305_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5546_; 
v_reuseFailAlloc_5546_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5546_, 0, v___x_5541_);
lean_ctor_set(v_reuseFailAlloc_5546_, 1, v_k_5536_);
lean_ctor_set(v_reuseFailAlloc_5546_, 2, v_v_5537_);
lean_ctor_set(v_reuseFailAlloc_5546_, 3, v_l_5534_);
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
else
{
lean_object* v_r_5551_; 
v_r_5551_ = lean_ctor_get(v_impl_5447_, 4);
lean_inc(v_r_5551_);
if (lean_obj_tag(v_r_5551_) == 0)
{
lean_object* v_k_5552_; lean_object* v_v_5553_; lean_object* v___x_5555_; uint8_t v_isShared_5556_; uint8_t v_isSharedCheck_5576_; 
v_k_5552_ = lean_ctor_get(v_impl_5447_, 1);
v_v_5553_ = lean_ctor_get(v_impl_5447_, 2);
v_isSharedCheck_5576_ = !lean_is_exclusive(v_impl_5447_);
if (v_isSharedCheck_5576_ == 0)
{
lean_object* v_unused_5577_; lean_object* v_unused_5578_; lean_object* v_unused_5579_; 
v_unused_5577_ = lean_ctor_get(v_impl_5447_, 4);
lean_dec(v_unused_5577_);
v_unused_5578_ = lean_ctor_get(v_impl_5447_, 3);
lean_dec(v_unused_5578_);
v_unused_5579_ = lean_ctor_get(v_impl_5447_, 0);
lean_dec(v_unused_5579_);
v___x_5555_ = v_impl_5447_;
v_isShared_5556_ = v_isSharedCheck_5576_;
goto v_resetjp_5554_;
}
else
{
lean_inc(v_v_5553_);
lean_inc(v_k_5552_);
lean_dec(v_impl_5447_);
v___x_5555_ = lean_box(0);
v_isShared_5556_ = v_isSharedCheck_5576_;
goto v_resetjp_5554_;
}
v_resetjp_5554_:
{
lean_object* v_k_5557_; lean_object* v_v_5558_; lean_object* v___x_5560_; uint8_t v_isShared_5561_; uint8_t v_isSharedCheck_5572_; 
v_k_5557_ = lean_ctor_get(v_r_5551_, 1);
v_v_5558_ = lean_ctor_get(v_r_5551_, 2);
v_isSharedCheck_5572_ = !lean_is_exclusive(v_r_5551_);
if (v_isSharedCheck_5572_ == 0)
{
lean_object* v_unused_5573_; lean_object* v_unused_5574_; lean_object* v_unused_5575_; 
v_unused_5573_ = lean_ctor_get(v_r_5551_, 4);
lean_dec(v_unused_5573_);
v_unused_5574_ = lean_ctor_get(v_r_5551_, 3);
lean_dec(v_unused_5574_);
v_unused_5575_ = lean_ctor_get(v_r_5551_, 0);
lean_dec(v_unused_5575_);
v___x_5560_ = v_r_5551_;
v_isShared_5561_ = v_isSharedCheck_5572_;
goto v_resetjp_5559_;
}
else
{
lean_inc(v_v_5558_);
lean_inc(v_k_5557_);
lean_dec(v_r_5551_);
v___x_5560_ = lean_box(0);
v_isShared_5561_ = v_isSharedCheck_5572_;
goto v_resetjp_5559_;
}
v_resetjp_5559_:
{
lean_object* v___x_5562_; lean_object* v___x_5564_; 
v___x_5562_ = lean_unsigned_to_nat(3u);
if (v_isShared_5561_ == 0)
{
lean_ctor_set(v___x_5560_, 4, v_l_5534_);
lean_ctor_set(v___x_5560_, 3, v_l_5534_);
lean_ctor_set(v___x_5560_, 2, v_v_5553_);
lean_ctor_set(v___x_5560_, 1, v_k_5552_);
lean_ctor_set(v___x_5560_, 0, v___x_5448_);
v___x_5564_ = v___x_5560_;
goto v_reusejp_5563_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5448_);
lean_ctor_set(v_reuseFailAlloc_5571_, 1, v_k_5552_);
lean_ctor_set(v_reuseFailAlloc_5571_, 2, v_v_5553_);
lean_ctor_set(v_reuseFailAlloc_5571_, 3, v_l_5534_);
lean_ctor_set(v_reuseFailAlloc_5571_, 4, v_l_5534_);
v___x_5564_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5563_;
}
v_reusejp_5563_:
{
lean_object* v___x_5566_; 
if (v_isShared_5556_ == 0)
{
lean_ctor_set(v___x_5555_, 4, v_l_5534_);
lean_ctor_set(v___x_5555_, 2, v_v_5301_);
lean_ctor_set(v___x_5555_, 1, v_k_5300_);
lean_ctor_set(v___x_5555_, 0, v___x_5448_);
v___x_5566_ = v___x_5555_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5570_; 
v_reuseFailAlloc_5570_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5570_, 0, v___x_5448_);
lean_ctor_set(v_reuseFailAlloc_5570_, 1, v_k_5300_);
lean_ctor_set(v_reuseFailAlloc_5570_, 2, v_v_5301_);
lean_ctor_set(v_reuseFailAlloc_5570_, 3, v_l_5534_);
lean_ctor_set(v_reuseFailAlloc_5570_, 4, v_l_5534_);
v___x_5566_ = v_reuseFailAlloc_5570_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
lean_object* v___x_5568_; 
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 4, v___x_5566_);
lean_ctor_set(v___x_5305_, 3, v___x_5564_);
lean_ctor_set(v___x_5305_, 2, v_v_5558_);
lean_ctor_set(v___x_5305_, 1, v_k_5557_);
lean_ctor_set(v___x_5305_, 0, v___x_5562_);
v___x_5568_ = v___x_5305_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5569_; 
v_reuseFailAlloc_5569_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5569_, 0, v___x_5562_);
lean_ctor_set(v_reuseFailAlloc_5569_, 1, v_k_5557_);
lean_ctor_set(v_reuseFailAlloc_5569_, 2, v_v_5558_);
lean_ctor_set(v_reuseFailAlloc_5569_, 3, v___x_5564_);
lean_ctor_set(v_reuseFailAlloc_5569_, 4, v___x_5566_);
v___x_5568_ = v_reuseFailAlloc_5569_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
return v___x_5568_;
}
}
}
}
}
}
else
{
lean_object* v___x_5580_; lean_object* v___x_5582_; 
v___x_5580_ = lean_unsigned_to_nat(2u);
if (v_isShared_5306_ == 0)
{
lean_ctor_set(v___x_5305_, 4, v_r_5551_);
lean_ctor_set(v___x_5305_, 3, v_impl_5447_);
lean_ctor_set(v___x_5305_, 0, v___x_5580_);
v___x_5582_ = v___x_5305_;
goto v_reusejp_5581_;
}
else
{
lean_object* v_reuseFailAlloc_5583_; 
v_reuseFailAlloc_5583_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5583_, 0, v___x_5580_);
lean_ctor_set(v_reuseFailAlloc_5583_, 1, v_k_5300_);
lean_ctor_set(v_reuseFailAlloc_5583_, 2, v_v_5301_);
lean_ctor_set(v_reuseFailAlloc_5583_, 3, v_impl_5447_);
lean_ctor_set(v_reuseFailAlloc_5583_, 4, v_r_5551_);
v___x_5582_ = v_reuseFailAlloc_5583_;
goto v_reusejp_5581_;
}
v_reusejp_5581_:
{
return v___x_5582_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5585_; lean_object* v___x_5586_; 
v___x_5585_ = lean_unsigned_to_nat(1u);
v___x_5586_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5586_, 0, v___x_5585_);
lean_ctor_set(v___x_5586_, 1, v_k_5296_);
lean_ctor_set(v___x_5586_, 2, v_v_5297_);
lean_ctor_set(v___x_5586_, 3, v_t_5298_);
lean_ctor_set(v___x_5586_, 4, v_t_5298_);
return v___x_5586_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5587_, lean_object* v_t_5588_){
_start:
{
if (lean_obj_tag(v_t_5588_) == 0)
{
lean_object* v_k_5589_; lean_object* v_l_5590_; lean_object* v_r_5591_; uint8_t v___x_5592_; 
v_k_5589_ = lean_ctor_get(v_t_5588_, 1);
v_l_5590_ = lean_ctor_get(v_t_5588_, 3);
v_r_5591_ = lean_ctor_get(v_t_5588_, 4);
v___x_5592_ = lean_nat_dec_lt(v_k_5589_, v_k_5587_);
if (v___x_5592_ == 0)
{
uint8_t v___x_5593_; 
v___x_5593_ = lean_nat_dec_eq(v_k_5589_, v_k_5587_);
if (v___x_5593_ == 0)
{
v_t_5588_ = v_r_5591_;
goto _start;
}
else
{
return v___x_5593_;
}
}
else
{
v_t_5588_ = v_l_5590_;
goto _start;
}
}
else
{
uint8_t v___x_5596_; 
v___x_5596_ = 0;
return v___x_5596_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5597_, lean_object* v_t_5598_){
_start:
{
uint8_t v_res_5599_; lean_object* v_r_5600_; 
v_res_5599_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5597_, v_t_5598_);
lean_dec(v_t_5598_);
lean_dec(v_k_5597_);
v_r_5600_ = lean_box(v_res_5599_);
return v_r_5600_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5601_, lean_object* v_e_5602_){
_start:
{
lean_object* v_defaultInstances_5603_; lean_object* v_priorities_5604_; lean_object* v___x_5606_; uint8_t v_isShared_5607_; uint8_t v_isSharedCheck_5631_; 
v_defaultInstances_5603_ = lean_ctor_get(v_d_5601_, 0);
v_priorities_5604_ = lean_ctor_get(v_d_5601_, 1);
v_isSharedCheck_5631_ = !lean_is_exclusive(v_d_5601_);
if (v_isSharedCheck_5631_ == 0)
{
v___x_5606_ = v_d_5601_;
v_isShared_5607_ = v_isSharedCheck_5631_;
goto v_resetjp_5605_;
}
else
{
lean_inc(v_priorities_5604_);
lean_inc(v_defaultInstances_5603_);
lean_dec(v_d_5601_);
v___x_5606_ = lean_box(0);
v_isShared_5607_ = v_isSharedCheck_5631_;
goto v_resetjp_5605_;
}
v_resetjp_5605_:
{
lean_object* v_className_5608_; lean_object* v_instanceName_5609_; lean_object* v_priority_5610_; lean_object* v___y_5612_; uint8_t v___x_5628_; 
v_className_5608_ = lean_ctor_get(v_e_5602_, 0);
lean_inc(v_className_5608_);
v_instanceName_5609_ = lean_ctor_get(v_e_5602_, 1);
lean_inc(v_instanceName_5609_);
v_priority_5610_ = lean_ctor_get(v_e_5602_, 2);
lean_inc(v_priority_5610_);
lean_dec_ref(v_e_5602_);
v___x_5628_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5610_, v_priorities_5604_);
if (v___x_5628_ == 0)
{
lean_object* v___x_5629_; lean_object* v___x_5630_; 
v___x_5629_ = lean_box(0);
lean_inc(v_priority_5610_);
v___x_5630_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5610_, v___x_5629_, v_priorities_5604_);
v___y_5612_ = v___x_5630_;
goto v___jp_5611_;
}
else
{
v___y_5612_ = v_priorities_5604_;
goto v___jp_5611_;
}
v___jp_5611_:
{
lean_object* v___x_5613_; 
v___x_5613_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5603_, v_className_5608_);
if (lean_obj_tag(v___x_5613_) == 0)
{
lean_object* v___x_5614_; lean_object* v___x_5615_; lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5619_; 
v___x_5614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5614_, 0, v_instanceName_5609_);
lean_ctor_set(v___x_5614_, 1, v_priority_5610_);
v___x_5615_ = lean_box(0);
v___x_5616_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5616_, 0, v___x_5614_);
lean_ctor_set(v___x_5616_, 1, v___x_5615_);
v___x_5617_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5608_, v___x_5616_, v_defaultInstances_5603_);
if (v_isShared_5607_ == 0)
{
lean_ctor_set(v___x_5606_, 1, v___y_5612_);
lean_ctor_set(v___x_5606_, 0, v___x_5617_);
v___x_5619_ = v___x_5606_;
goto v_reusejp_5618_;
}
else
{
lean_object* v_reuseFailAlloc_5620_; 
v_reuseFailAlloc_5620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5620_, 0, v___x_5617_);
lean_ctor_set(v_reuseFailAlloc_5620_, 1, v___y_5612_);
v___x_5619_ = v_reuseFailAlloc_5620_;
goto v_reusejp_5618_;
}
v_reusejp_5618_:
{
return v___x_5619_;
}
}
else
{
lean_object* v_val_5621_; lean_object* v___x_5622_; lean_object* v___x_5623_; lean_object* v___x_5624_; lean_object* v___x_5626_; 
v_val_5621_ = lean_ctor_get(v___x_5613_, 0);
lean_inc(v_val_5621_);
lean_dec_ref_known(v___x_5613_, 1);
v___x_5622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5622_, 0, v_instanceName_5609_);
lean_ctor_set(v___x_5622_, 1, v_priority_5610_);
v___x_5623_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5623_, 0, v___x_5622_);
lean_ctor_set(v___x_5623_, 1, v_val_5621_);
v___x_5624_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5608_, v___x_5623_, v_defaultInstances_5603_);
if (v_isShared_5607_ == 0)
{
lean_ctor_set(v___x_5606_, 1, v___y_5612_);
lean_ctor_set(v___x_5606_, 0, v___x_5624_);
v___x_5626_ = v___x_5606_;
goto v_reusejp_5625_;
}
else
{
lean_object* v_reuseFailAlloc_5627_; 
v_reuseFailAlloc_5627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5627_, 0, v___x_5624_);
lean_ctor_set(v_reuseFailAlloc_5627_, 1, v___y_5612_);
v___x_5626_ = v_reuseFailAlloc_5627_;
goto v_reusejp_5625_;
}
v_reusejp_5625_:
{
return v___x_5626_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5632_, lean_object* v_k_5633_, lean_object* v_t_5634_){
_start:
{
uint8_t v___x_5635_; 
v___x_5635_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5633_, v_t_5634_);
return v___x_5635_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5636_, lean_object* v_k_5637_, lean_object* v_t_5638_){
_start:
{
uint8_t v_res_5639_; lean_object* v_r_5640_; 
v_res_5639_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5636_, v_k_5637_, v_t_5638_);
lean_dec(v_t_5638_);
lean_dec(v_k_5637_);
v_r_5640_ = lean_box(v_res_5639_);
return v_r_5640_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5641_, lean_object* v_k_5642_, lean_object* v_v_5643_, lean_object* v_t_5644_, lean_object* v_hl_5645_){
_start:
{
lean_object* v___x_5646_; 
v___x_5646_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5642_, v_v_5643_, v_t_5644_);
return v___x_5646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object* v_env_5647_, lean_object* v_as_5648_, size_t v_i_5649_, size_t v_stop_5650_, lean_object* v_b_5651_){
_start:
{
lean_object* v___y_5653_; uint8_t v___x_5657_; 
v___x_5657_ = lean_usize_dec_eq(v_i_5649_, v_stop_5650_);
if (v___x_5657_ == 0)
{
lean_object* v___x_5658_; lean_object* v_instanceName_5659_; uint8_t v___x_5660_; lean_object* v___x_5661_; uint8_t v___x_5662_; 
v___x_5658_ = lean_array_uget_borrowed(v_as_5648_, v_i_5649_);
v_instanceName_5659_ = lean_ctor_get(v___x_5658_, 1);
v___x_5660_ = 1;
lean_inc_ref(v_env_5647_);
v___x_5661_ = l_Lean_Environment_setExporting(v_env_5647_, v___x_5660_);
lean_inc(v_instanceName_5659_);
v___x_5662_ = l_Lean_Environment_contains(v___x_5661_, v_instanceName_5659_, v___x_5657_);
if (v___x_5662_ == 0)
{
v___y_5653_ = v_b_5651_;
goto v___jp_5652_;
}
else
{
lean_object* v___x_5663_; 
lean_inc(v___x_5658_);
v___x_5663_ = lean_array_push(v_b_5651_, v___x_5658_);
v___y_5653_ = v___x_5663_;
goto v___jp_5652_;
}
}
else
{
lean_dec_ref(v_env_5647_);
return v_b_5651_;
}
v___jp_5652_:
{
size_t v___x_5654_; size_t v___x_5655_; 
v___x_5654_ = ((size_t)1ULL);
v___x_5655_ = lean_usize_add(v_i_5649_, v___x_5654_);
v_i_5649_ = v___x_5655_;
v_b_5651_ = v___y_5653_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_5664_, lean_object* v_as_5665_, lean_object* v_i_5666_, lean_object* v_stop_5667_, lean_object* v_b_5668_){
_start:
{
size_t v_i_boxed_5669_; size_t v_stop_boxed_5670_; lean_object* v_res_5671_; 
v_i_boxed_5669_ = lean_unbox_usize(v_i_5666_);
lean_dec(v_i_5666_);
v_stop_boxed_5670_ = lean_unbox_usize(v_stop_5667_);
lean_dec(v_stop_5667_);
v_res_5671_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5664_, v_as_5665_, v_i_boxed_5669_, v_stop_boxed_5670_, v_b_5668_);
lean_dec_ref(v_as_5665_);
return v_res_5671_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_env_5674_, lean_object* v_x_5675_, lean_object* v_entries_5676_){
_start:
{
lean_object* v_all_5677_; lean_object* v___x_5678_; lean_object* v___x_5679_; lean_object* v___x_5680_; uint8_t v___x_5681_; 
v_all_5677_ = lean_array_mk(v_entries_5676_);
v___x_5678_ = lean_unsigned_to_nat(0u);
v___x_5679_ = lean_array_get_size(v_all_5677_);
v___x_5680_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5681_ = lean_nat_dec_lt(v___x_5678_, v___x_5679_);
if (v___x_5681_ == 0)
{
lean_object* v___x_5682_; 
lean_dec_ref(v_env_5674_);
v___x_5682_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5682_, 0, v___x_5680_);
lean_ctor_set(v___x_5682_, 1, v___x_5680_);
lean_ctor_set(v___x_5682_, 2, v_all_5677_);
return v___x_5682_;
}
else
{
uint8_t v___x_5683_; 
v___x_5683_ = lean_nat_dec_le(v___x_5679_, v___x_5679_);
if (v___x_5683_ == 0)
{
if (v___x_5681_ == 0)
{
lean_object* v___x_5684_; 
lean_dec_ref(v_env_5674_);
v___x_5684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5680_);
lean_ctor_set(v___x_5684_, 1, v___x_5680_);
lean_ctor_set(v___x_5684_, 2, v_all_5677_);
return v___x_5684_;
}
else
{
size_t v___x_5685_; size_t v___x_5686_; lean_object* v___x_5687_; lean_object* v___x_5688_; 
v___x_5685_ = ((size_t)0ULL);
v___x_5686_ = lean_usize_of_nat(v___x_5679_);
v___x_5687_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5674_, v_all_5677_, v___x_5685_, v___x_5686_, v___x_5680_);
lean_inc_ref(v___x_5687_);
v___x_5688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5688_, 0, v___x_5687_);
lean_ctor_set(v___x_5688_, 1, v___x_5687_);
lean_ctor_set(v___x_5688_, 2, v_all_5677_);
return v___x_5688_;
}
}
else
{
size_t v___x_5689_; size_t v___x_5690_; lean_object* v___x_5691_; lean_object* v___x_5692_; 
v___x_5689_ = ((size_t)0ULL);
v___x_5690_ = lean_usize_of_nat(v___x_5679_);
v___x_5691_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5674_, v_all_5677_, v___x_5689_, v___x_5690_, v___x_5680_);
lean_inc_ref(v___x_5691_);
v___x_5692_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5692_, 0, v___x_5691_);
lean_ctor_set(v___x_5692_, 1, v___x_5691_);
lean_ctor_set(v___x_5692_, 2, v_all_5677_);
return v___x_5692_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5693_, lean_object* v_x_5694_, lean_object* v_entries_5695_){
_start:
{
lean_object* v_res_5696_; 
v_res_5696_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5693_, v_x_5694_, v_entries_5695_);
lean_dec_ref(v_x_5694_);
return v_res_5696_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5697_){
_start:
{
lean_object* v___x_5698_; 
v___x_5698_ = lean_array_mk(v_es_5697_);
return v___x_5698_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5699_, size_t v_i_5700_, size_t v_stop_5701_, lean_object* v_b_5702_){
_start:
{
uint8_t v___x_5703_; 
v___x_5703_ = lean_usize_dec_eq(v_i_5700_, v_stop_5701_);
if (v___x_5703_ == 0)
{
lean_object* v___x_5704_; lean_object* v___x_5705_; size_t v___x_5706_; size_t v___x_5707_; 
v___x_5704_ = lean_array_uget_borrowed(v_as_5699_, v_i_5700_);
lean_inc(v___x_5704_);
v___x_5705_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5702_, v___x_5704_);
v___x_5706_ = ((size_t)1ULL);
v___x_5707_ = lean_usize_add(v_i_5700_, v___x_5706_);
v_i_5700_ = v___x_5707_;
v_b_5702_ = v___x_5705_;
goto _start;
}
else
{
return v_b_5702_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5709_, lean_object* v_i_5710_, lean_object* v_stop_5711_, lean_object* v_b_5712_){
_start:
{
size_t v_i_boxed_5713_; size_t v_stop_boxed_5714_; lean_object* v_res_5715_; 
v_i_boxed_5713_ = lean_unbox_usize(v_i_5710_);
lean_dec(v_i_5710_);
v_stop_boxed_5714_ = lean_unbox_usize(v_stop_5711_);
lean_dec(v_stop_5711_);
v_res_5715_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5709_, v_i_boxed_5713_, v_stop_boxed_5714_, v_b_5712_);
lean_dec_ref(v_as_5709_);
return v_res_5715_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5716_, size_t v_i_5717_, size_t v_stop_5718_, lean_object* v_b_5719_){
_start:
{
lean_object* v___y_5721_; uint8_t v___x_5725_; 
v___x_5725_ = lean_usize_dec_eq(v_i_5717_, v_stop_5718_);
if (v___x_5725_ == 0)
{
lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; uint8_t v___x_5729_; 
v___x_5726_ = lean_array_uget_borrowed(v_as_5716_, v_i_5717_);
v___x_5727_ = lean_unsigned_to_nat(0u);
v___x_5728_ = lean_array_get_size(v___x_5726_);
v___x_5729_ = lean_nat_dec_lt(v___x_5727_, v___x_5728_);
if (v___x_5729_ == 0)
{
v___y_5721_ = v_b_5719_;
goto v___jp_5720_;
}
else
{
uint8_t v___x_5730_; 
v___x_5730_ = lean_nat_dec_le(v___x_5728_, v___x_5728_);
if (v___x_5730_ == 0)
{
if (v___x_5729_ == 0)
{
v___y_5721_ = v_b_5719_;
goto v___jp_5720_;
}
else
{
size_t v___x_5731_; size_t v___x_5732_; lean_object* v___x_5733_; 
v___x_5731_ = ((size_t)0ULL);
v___x_5732_ = lean_usize_of_nat(v___x_5728_);
v___x_5733_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5726_, v___x_5731_, v___x_5732_, v_b_5719_);
v___y_5721_ = v___x_5733_;
goto v___jp_5720_;
}
}
else
{
size_t v___x_5734_; size_t v___x_5735_; lean_object* v___x_5736_; 
v___x_5734_ = ((size_t)0ULL);
v___x_5735_ = lean_usize_of_nat(v___x_5728_);
v___x_5736_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5726_, v___x_5734_, v___x_5735_, v_b_5719_);
v___y_5721_ = v___x_5736_;
goto v___jp_5720_;
}
}
}
else
{
return v_b_5719_;
}
v___jp_5720_:
{
size_t v___x_5722_; size_t v___x_5723_; 
v___x_5722_ = ((size_t)1ULL);
v___x_5723_ = lean_usize_add(v_i_5717_, v___x_5722_);
v_i_5717_ = v___x_5723_;
v_b_5719_ = v___y_5721_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5737_, lean_object* v_i_5738_, lean_object* v_stop_5739_, lean_object* v_b_5740_){
_start:
{
size_t v_i_boxed_5741_; size_t v_stop_boxed_5742_; lean_object* v_res_5743_; 
v_i_boxed_5741_ = lean_unbox_usize(v_i_5738_);
lean_dec(v_i_5738_);
v_stop_boxed_5742_ = lean_unbox_usize(v_stop_5739_);
lean_dec(v_stop_5739_);
v_res_5743_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5737_, v_i_boxed_5741_, v_stop_boxed_5742_, v_b_5740_);
lean_dec_ref(v_as_5737_);
return v_res_5743_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_5744_, lean_object* v_as_5745_){
_start:
{
lean_object* v___x_5746_; lean_object* v___x_5747_; uint8_t v___x_5748_; 
v___x_5746_ = lean_unsigned_to_nat(0u);
v___x_5747_ = lean_array_get_size(v_as_5745_);
v___x_5748_ = lean_nat_dec_lt(v___x_5746_, v___x_5747_);
if (v___x_5748_ == 0)
{
return v_initState_5744_;
}
else
{
uint8_t v___x_5749_; 
v___x_5749_ = lean_nat_dec_le(v___x_5747_, v___x_5747_);
if (v___x_5749_ == 0)
{
if (v___x_5748_ == 0)
{
return v_initState_5744_;
}
else
{
size_t v___x_5750_; size_t v___x_5751_; lean_object* v___x_5752_; 
v___x_5750_ = ((size_t)0ULL);
v___x_5751_ = lean_usize_of_nat(v___x_5747_);
v___x_5752_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5745_, v___x_5750_, v___x_5751_, v_initState_5744_);
return v___x_5752_;
}
}
else
{
size_t v___x_5753_; size_t v___x_5754_; lean_object* v___x_5755_; 
v___x_5753_ = ((size_t)0ULL);
v___x_5754_ = lean_usize_of_nat(v___x_5747_);
v___x_5755_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5745_, v___x_5753_, v___x_5754_, v_initState_5744_);
return v___x_5755_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_5756_, lean_object* v_as_5757_){
_start:
{
lean_object* v_res_5758_; 
v_res_5758_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_5756_, v_as_5757_);
lean_dec_ref(v_as_5757_);
return v_res_5758_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5759_){
_start:
{
lean_object* v___x_5760_; lean_object* v___x_5761_; 
v___x_5760_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5761_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_5760_, v_es_5759_);
return v___x_5761_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_5762_){
_start:
{
lean_object* v_res_5763_; 
v_res_5763_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_5762_);
lean_dec_ref(v_es_5762_);
return v_res_5763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5784_; lean_object* v___x_5785_; 
v___x_5784_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5785_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5784_);
return v___x_5785_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_5786_){
_start:
{
lean_object* v_res_5787_; 
v_res_5787_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_5787_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5788_, lean_object* v___y_5789_, lean_object* v___y_5790_){
_start:
{
lean_object* v___x_5792_; lean_object* v_nextMacroScope_5793_; lean_object* v_ngen_5794_; lean_object* v_auxDeclNGen_5795_; lean_object* v_traceState_5796_; lean_object* v_messages_5797_; lean_object* v_infoState_5798_; lean_object* v_snapshotTasks_5799_; lean_object* v___x_5801_; uint8_t v_isShared_5802_; uint8_t v_isSharedCheck_5825_; 
v___x_5792_ = lean_st_ref_take(v___y_5790_);
v_nextMacroScope_5793_ = lean_ctor_get(v___x_5792_, 1);
v_ngen_5794_ = lean_ctor_get(v___x_5792_, 2);
v_auxDeclNGen_5795_ = lean_ctor_get(v___x_5792_, 3);
v_traceState_5796_ = lean_ctor_get(v___x_5792_, 4);
v_messages_5797_ = lean_ctor_get(v___x_5792_, 6);
v_infoState_5798_ = lean_ctor_get(v___x_5792_, 7);
v_snapshotTasks_5799_ = lean_ctor_get(v___x_5792_, 8);
v_isSharedCheck_5825_ = !lean_is_exclusive(v___x_5792_);
if (v_isSharedCheck_5825_ == 0)
{
lean_object* v_unused_5826_; lean_object* v_unused_5827_; 
v_unused_5826_ = lean_ctor_get(v___x_5792_, 5);
lean_dec(v_unused_5826_);
v_unused_5827_ = lean_ctor_get(v___x_5792_, 0);
lean_dec(v_unused_5827_);
v___x_5801_ = v___x_5792_;
v_isShared_5802_ = v_isSharedCheck_5825_;
goto v_resetjp_5800_;
}
else
{
lean_inc(v_snapshotTasks_5799_);
lean_inc(v_infoState_5798_);
lean_inc(v_messages_5797_);
lean_inc(v_traceState_5796_);
lean_inc(v_auxDeclNGen_5795_);
lean_inc(v_ngen_5794_);
lean_inc(v_nextMacroScope_5793_);
lean_dec(v___x_5792_);
v___x_5801_ = lean_box(0);
v_isShared_5802_ = v_isSharedCheck_5825_;
goto v_resetjp_5800_;
}
v_resetjp_5800_:
{
lean_object* v___x_5803_; lean_object* v___x_5805_; 
v___x_5803_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5802_ == 0)
{
lean_ctor_set(v___x_5801_, 5, v___x_5803_);
lean_ctor_set(v___x_5801_, 0, v_env_5788_);
v___x_5805_ = v___x_5801_;
goto v_reusejp_5804_;
}
else
{
lean_object* v_reuseFailAlloc_5824_; 
v_reuseFailAlloc_5824_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5824_, 0, v_env_5788_);
lean_ctor_set(v_reuseFailAlloc_5824_, 1, v_nextMacroScope_5793_);
lean_ctor_set(v_reuseFailAlloc_5824_, 2, v_ngen_5794_);
lean_ctor_set(v_reuseFailAlloc_5824_, 3, v_auxDeclNGen_5795_);
lean_ctor_set(v_reuseFailAlloc_5824_, 4, v_traceState_5796_);
lean_ctor_set(v_reuseFailAlloc_5824_, 5, v___x_5803_);
lean_ctor_set(v_reuseFailAlloc_5824_, 6, v_messages_5797_);
lean_ctor_set(v_reuseFailAlloc_5824_, 7, v_infoState_5798_);
lean_ctor_set(v_reuseFailAlloc_5824_, 8, v_snapshotTasks_5799_);
v___x_5805_ = v_reuseFailAlloc_5824_;
goto v_reusejp_5804_;
}
v_reusejp_5804_:
{
lean_object* v___x_5806_; lean_object* v___x_5807_; lean_object* v_mctx_5808_; lean_object* v_zetaDeltaFVarIds_5809_; lean_object* v_postponed_5810_; lean_object* v_diag_5811_; lean_object* v___x_5813_; uint8_t v_isShared_5814_; uint8_t v_isSharedCheck_5822_; 
v___x_5806_ = lean_st_ref_set(v___y_5790_, v___x_5805_);
v___x_5807_ = lean_st_ref_take(v___y_5789_);
v_mctx_5808_ = lean_ctor_get(v___x_5807_, 0);
v_zetaDeltaFVarIds_5809_ = lean_ctor_get(v___x_5807_, 2);
v_postponed_5810_ = lean_ctor_get(v___x_5807_, 3);
v_diag_5811_ = lean_ctor_get(v___x_5807_, 4);
v_isSharedCheck_5822_ = !lean_is_exclusive(v___x_5807_);
if (v_isSharedCheck_5822_ == 0)
{
lean_object* v_unused_5823_; 
v_unused_5823_ = lean_ctor_get(v___x_5807_, 1);
lean_dec(v_unused_5823_);
v___x_5813_ = v___x_5807_;
v_isShared_5814_ = v_isSharedCheck_5822_;
goto v_resetjp_5812_;
}
else
{
lean_inc(v_diag_5811_);
lean_inc(v_postponed_5810_);
lean_inc(v_zetaDeltaFVarIds_5809_);
lean_inc(v_mctx_5808_);
lean_dec(v___x_5807_);
v___x_5813_ = lean_box(0);
v_isShared_5814_ = v_isSharedCheck_5822_;
goto v_resetjp_5812_;
}
v_resetjp_5812_:
{
lean_object* v___x_5815_; lean_object* v___x_5817_; 
v___x_5815_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5814_ == 0)
{
lean_ctor_set(v___x_5813_, 1, v___x_5815_);
v___x_5817_ = v___x_5813_;
goto v_reusejp_5816_;
}
else
{
lean_object* v_reuseFailAlloc_5821_; 
v_reuseFailAlloc_5821_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5821_, 0, v_mctx_5808_);
lean_ctor_set(v_reuseFailAlloc_5821_, 1, v___x_5815_);
lean_ctor_set(v_reuseFailAlloc_5821_, 2, v_zetaDeltaFVarIds_5809_);
lean_ctor_set(v_reuseFailAlloc_5821_, 3, v_postponed_5810_);
lean_ctor_set(v_reuseFailAlloc_5821_, 4, v_diag_5811_);
v___x_5817_ = v_reuseFailAlloc_5821_;
goto v_reusejp_5816_;
}
v_reusejp_5816_:
{
lean_object* v___x_5818_; lean_object* v___x_5819_; lean_object* v___x_5820_; 
v___x_5818_ = lean_st_ref_set(v___y_5789_, v___x_5817_);
v___x_5819_ = lean_box(0);
v___x_5820_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5820_, 0, v___x_5819_);
return v___x_5820_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5828_, lean_object* v___y_5829_, lean_object* v___y_5830_, lean_object* v___y_5831_){
_start:
{
lean_object* v_res_5832_; 
v_res_5832_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5828_, v___y_5829_, v___y_5830_);
lean_dec(v___y_5830_);
lean_dec(v___y_5829_);
return v_res_5832_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5833_, lean_object* v___y_5834_, lean_object* v___y_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_){
_start:
{
lean_object* v___x_5839_; 
v___x_5839_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5833_, v___y_5835_, v___y_5837_);
return v___x_5839_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5840_, lean_object* v___y_5841_, lean_object* v___y_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_){
_start:
{
lean_object* v_res_5846_; 
v_res_5846_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5840_, v___y_5841_, v___y_5842_, v___y_5843_, v___y_5844_);
lean_dec(v___y_5844_);
lean_dec_ref(v___y_5843_);
lean_dec(v___y_5842_);
lean_dec_ref(v___y_5841_);
return v_res_5846_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5848_; lean_object* v___x_5849_; 
v___x_5848_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5849_ = l_Lean_stringToMessageData(v___x_5848_);
return v___x_5849_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5851_; lean_object* v___x_5852_; 
v___x_5851_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5852_ = l_Lean_stringToMessageData(v___x_5851_);
return v___x_5852_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5854_; lean_object* v___x_5855_; 
v___x_5854_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5855_ = l_Lean_stringToMessageData(v___x_5854_);
return v___x_5855_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5857_; lean_object* v___x_5858_; 
v___x_5857_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5858_ = l_Lean_stringToMessageData(v___x_5857_);
return v___x_5858_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5860_; lean_object* v___x_5861_; 
v___x_5860_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5861_ = l_Lean_stringToMessageData(v___x_5860_);
return v___x_5861_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5862_, lean_object* v_prio_5863_, lean_object* v_x_5864_, lean_object* v_type_5865_, lean_object* v___y_5866_, lean_object* v___y_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_){
_start:
{
lean_object* v___x_5871_; 
v___x_5871_ = l_Lean_Expr_getAppFn(v_type_5865_);
if (lean_obj_tag(v___x_5871_) == 4)
{
lean_object* v_declName_5872_; lean_object* v___y_5874_; lean_object* v___y_5875_; lean_object* v___y_5876_; lean_object* v___y_5877_; lean_object* v___x_5887_; lean_object* v_env_5888_; uint8_t v___x_5889_; 
v_declName_5872_ = lean_ctor_get(v___x_5871_, 0);
lean_inc(v_declName_5872_);
lean_dec_ref_known(v___x_5871_, 2);
v___x_5887_ = lean_st_ref_get(v___y_5869_);
v_env_5888_ = lean_ctor_get(v___x_5887_, 0);
lean_inc_ref(v_env_5888_);
lean_dec(v___x_5887_);
v___x_5889_ = l_Lean_isClass(v_env_5888_, v_declName_5872_);
if (v___x_5889_ == 0)
{
lean_object* v___x_5890_; lean_object* v___x_5891_; lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; 
lean_dec(v_prio_5863_);
v___x_5890_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5891_ = l_Lean_MessageData_ofConstName(v_declName_5862_, v___x_5889_);
v___x_5892_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5892_, 0, v___x_5890_);
lean_ctor_set(v___x_5892_, 1, v___x_5891_);
v___x_5893_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5894_, 0, v___x_5892_);
lean_ctor_set(v___x_5894_, 1, v___x_5893_);
lean_inc(v_declName_5872_);
v___x_5895_ = l_Lean_MessageData_ofName(v_declName_5872_);
v___x_5896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5896_, 0, v___x_5894_);
lean_ctor_set(v___x_5896_, 1, v___x_5895_);
v___x_5897_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5898_, 0, v___x_5896_);
lean_ctor_set(v___x_5898_, 1, v___x_5897_);
v___x_5899_ = l_Lean_MessageData_ofConstName(v_declName_5872_, v___x_5889_);
v___x_5900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5898_);
lean_ctor_set(v___x_5900_, 1, v___x_5899_);
v___x_5901_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5902_, 0, v___x_5900_);
lean_ctor_set(v___x_5902_, 1, v___x_5901_);
v___x_5903_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5902_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_);
return v___x_5903_;
}
else
{
v___y_5874_ = v___y_5866_;
v___y_5875_ = v___y_5867_;
v___y_5876_ = v___y_5868_;
v___y_5877_ = v___y_5869_;
goto v___jp_5873_;
}
v___jp_5873_:
{
lean_object* v___x_5878_; lean_object* v_env_5879_; lean_object* v___x_5880_; lean_object* v_toEnvExtension_5881_; lean_object* v_asyncMode_5882_; lean_object* v___x_5883_; lean_object* v___x_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; 
v___x_5878_ = lean_st_ref_get(v___y_5877_);
v_env_5879_ = lean_ctor_get(v___x_5878_, 0);
lean_inc_ref(v_env_5879_);
lean_dec(v___x_5878_);
v___x_5880_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5881_ = lean_ctor_get(v___x_5880_, 0);
v_asyncMode_5882_ = lean_ctor_get(v_toEnvExtension_5881_, 2);
v___x_5883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5883_, 0, v_declName_5872_);
lean_ctor_set(v___x_5883_, 1, v_declName_5862_);
lean_ctor_set(v___x_5883_, 2, v_prio_5863_);
v___x_5884_ = lean_box(0);
v___x_5885_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5880_, v_env_5879_, v___x_5883_, v_asyncMode_5882_, v___x_5884_);
v___x_5886_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5885_, v___y_5875_, v___y_5877_);
return v___x_5886_;
}
}
else
{
lean_object* v___x_5904_; uint8_t v___x_5905_; lean_object* v___x_5906_; lean_object* v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; 
lean_dec_ref(v___x_5871_);
lean_dec(v_prio_5863_);
v___x_5904_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5905_ = 0;
v___x_5906_ = l_Lean_MessageData_ofConstName(v_declName_5862_, v___x_5905_);
v___x_5907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5907_, 0, v___x_5904_);
lean_ctor_set(v___x_5907_, 1, v___x_5906_);
v___x_5908_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5909_, 0, v___x_5907_);
lean_ctor_set(v___x_5909_, 1, v___x_5908_);
v___x_5910_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5909_, v___y_5866_, v___y_5867_, v___y_5868_, v___y_5869_);
return v___x_5910_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5911_, lean_object* v_prio_5912_, lean_object* v_x_5913_, lean_object* v_type_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_){
_start:
{
lean_object* v_res_5920_; 
v_res_5920_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5911_, v_prio_5912_, v_x_5913_, v_type_5914_, v___y_5915_, v___y_5916_, v___y_5917_, v___y_5918_);
lean_dec(v___y_5918_);
lean_dec_ref(v___y_5917_);
lean_dec(v___y_5916_);
lean_dec_ref(v___y_5915_);
lean_dec_ref(v_type_5914_);
lean_dec_ref(v_x_5913_);
return v_res_5920_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5921_, lean_object* v_prio_5922_, lean_object* v_a_5923_, lean_object* v_a_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_){
_start:
{
lean_object* v___x_5928_; lean_object* v_env_5929_; uint8_t v___x_5930_; lean_object* v___x_5931_; 
v___x_5928_ = lean_st_ref_get(v_a_5926_);
v_env_5929_ = lean_ctor_get(v___x_5928_, 0);
lean_inc_ref(v_env_5929_);
lean_dec(v___x_5928_);
v___x_5930_ = 0;
lean_inc(v_declName_5921_);
v___x_5931_ = l_Lean_Environment_find_x3f(v_env_5929_, v_declName_5921_, v___x_5930_);
if (lean_obj_tag(v___x_5931_) == 0)
{
lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; 
lean_dec(v_prio_5922_);
v___x_5932_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5933_ = l_Lean_MessageData_ofConstName(v_declName_5921_, v___x_5930_);
v___x_5934_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5934_, 0, v___x_5932_);
lean_ctor_set(v___x_5934_, 1, v___x_5933_);
v___x_5935_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5934_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5936_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_);
return v___x_5937_;
}
else
{
lean_object* v_val_5938_; lean_object* v___f_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; 
v_val_5938_ = lean_ctor_get(v___x_5931_, 0);
lean_inc(v_val_5938_);
lean_dec_ref_known(v___x_5931_, 1);
v___f_5939_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5939_, 0, v_declName_5921_);
lean_closure_set(v___f_5939_, 1, v_prio_5922_);
v___x_5940_ = l_Lean_ConstantInfo_type(v_val_5938_);
lean_dec(v_val_5938_);
v___x_5941_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5940_, v___f_5939_, v___x_5930_, v___x_5930_, v_a_5923_, v_a_5924_, v_a_5925_, v_a_5926_);
return v___x_5941_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5942_, lean_object* v_prio_5943_, lean_object* v_a_5944_, lean_object* v_a_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_){
_start:
{
lean_object* v_res_5949_; 
v_res_5949_ = l_Lean_Meta_addDefaultInstance(v_declName_5942_, v_prio_5943_, v_a_5944_, v_a_5945_, v_a_5946_, v_a_5947_);
lean_dec(v_a_5947_);
lean_dec_ref(v_a_5946_);
lean_dec(v_a_5945_);
lean_dec_ref(v_a_5944_);
return v_res_5949_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5951_; lean_object* v___x_5952_; 
v___x_5951_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5952_ = l_Lean_stringToMessageData(v___x_5951_);
return v___x_5952_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5954_; lean_object* v___x_5955_; 
v___x_5954_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5955_ = l_Lean_stringToMessageData(v___x_5954_);
return v___x_5955_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5959_, uint8_t v_kind_5960_, lean_object* v___y_5961_, lean_object* v___y_5962_){
_start:
{
lean_object* v___x_5964_; lean_object* v___x_5965_; lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___y_5970_; 
v___x_5964_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5965_ = l_Lean_MessageData_ofName(v_name_5959_);
v___x_5966_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5966_, 0, v___x_5964_);
lean_ctor_set(v___x_5966_, 1, v___x_5965_);
v___x_5967_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5966_);
lean_ctor_set(v___x_5968_, 1, v___x_5967_);
switch(v_kind_5960_)
{
case 0:
{
lean_object* v___x_5977_; 
v___x_5977_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5970_ = v___x_5977_;
goto v___jp_5969_;
}
case 1:
{
lean_object* v___x_5978_; 
v___x_5978_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5970_ = v___x_5978_;
goto v___jp_5969_;
}
default: 
{
lean_object* v___x_5979_; 
v___x_5979_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5970_ = v___x_5979_;
goto v___jp_5969_;
}
}
v___jp_5969_:
{
lean_object* v___x_5971_; lean_object* v___x_5972_; lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; 
lean_inc_ref(v___y_5970_);
v___x_5971_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5971_, 0, v___y_5970_);
v___x_5972_ = l_Lean_MessageData_ofFormat(v___x_5971_);
v___x_5973_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5973_, 0, v___x_5968_);
lean_ctor_set(v___x_5973_, 1, v___x_5972_);
v___x_5974_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5973_);
lean_ctor_set(v___x_5975_, 1, v___x_5974_);
v___x_5976_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5975_, v___y_5961_, v___y_5962_);
return v___x_5976_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_5980_, lean_object* v_kind_5981_, lean_object* v___y_5982_, lean_object* v___y_5983_, lean_object* v___y_5984_){
_start:
{
uint8_t v_kind_boxed_5985_; lean_object* v_res_5986_; 
v_kind_boxed_5985_ = lean_unbox(v_kind_5981_);
v_res_5986_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5980_, v_kind_boxed_5985_, v___y_5982_, v___y_5983_);
lean_dec(v___y_5983_);
lean_dec_ref(v___y_5982_);
return v_res_5986_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5987_, lean_object* v___x_5988_, lean_object* v___x_5989_, lean_object* v_declName_5990_, lean_object* v_stx_5991_, uint8_t v_kind_5992_, lean_object* v___y_5993_, lean_object* v___y_5994_){
_start:
{
lean_object* v___x_5996_; lean_object* v___x_5997_; lean_object* v___x_5998_; 
v___x_5996_ = lean_unsigned_to_nat(1u);
v___x_5997_ = l_Lean_Syntax_getArg(v_stx_5991_, v___x_5996_);
v___x_5998_ = l_Lean_getAttrParamOptPrio(v___x_5997_, v___y_5993_, v___y_5994_);
if (lean_obj_tag(v___x_5998_) == 0)
{
lean_object* v_a_5999_; lean_object* v___y_6001_; lean_object* v___y_6002_; uint8_t v___x_6033_; uint8_t v___x_6034_; 
v_a_5999_ = lean_ctor_get(v___x_5998_, 0);
lean_inc(v_a_5999_);
lean_dec_ref_known(v___x_5998_, 1);
v___x_6033_ = 0;
v___x_6034_ = l_Lean_instBEqAttributeKind_beq(v_kind_5992_, v___x_6033_);
if (v___x_6034_ == 0)
{
lean_object* v___x_6035_; 
lean_dec(v_a_5999_);
lean_dec(v_declName_5990_);
lean_dec(v___x_5988_);
lean_dec(v___x_5987_);
v___x_6035_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_5989_, v_kind_5992_, v___y_5993_, v___y_5994_);
return v___x_6035_;
}
else
{
lean_dec(v___x_5989_);
v___y_6001_ = v___y_5993_;
v___y_6002_ = v___y_5994_;
goto v___jp_6000_;
}
v___jp_6000_:
{
uint8_t v___x_6003_; uint8_t v___x_6004_; lean_object* v___x_6005_; lean_object* v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; size_t v___x_6010_; lean_object* v___x_6011_; lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; 
v___x_6003_ = 0;
v___x_6004_ = 1;
v___x_6005_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6006_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6007_ = lean_unsigned_to_nat(32u);
v___x_6008_ = lean_mk_empty_array_with_capacity(v___x_6007_);
v___x_6009_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_6010_ = ((size_t)5ULL);
lean_inc_n(v___x_5987_, 6);
v___x_6011_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6011_, 0, v___x_6009_);
lean_ctor_set(v___x_6011_, 1, v___x_6008_);
lean_ctor_set(v___x_6011_, 2, v___x_5987_);
lean_ctor_set(v___x_6011_, 3, v___x_5987_);
lean_ctor_set_usize(v___x_6011_, 4, v___x_6010_);
v___x_6012_ = lean_box(1);
lean_inc_ref(v___x_6011_);
v___x_6013_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6013_, 0, v___x_6006_);
lean_ctor_set(v___x_6013_, 1, v___x_6011_);
lean_ctor_set(v___x_6013_, 2, v___x_6012_);
v___x_6014_ = lean_mk_empty_array_with_capacity(v___x_5987_);
v___x_6015_ = lean_box(0);
lean_inc(v___x_5988_);
v___x_6016_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6016_, 0, v___x_6005_);
lean_ctor_set(v___x_6016_, 1, v___x_5988_);
lean_ctor_set(v___x_6016_, 2, v___x_6013_);
lean_ctor_set(v___x_6016_, 3, v___x_6014_);
lean_ctor_set(v___x_6016_, 4, v___x_6015_);
lean_ctor_set(v___x_6016_, 5, v___x_5987_);
lean_ctor_set(v___x_6016_, 6, v___x_6015_);
lean_ctor_set_uint8(v___x_6016_, sizeof(void*)*7, v___x_6003_);
lean_ctor_set_uint8(v___x_6016_, sizeof(void*)*7 + 1, v___x_6003_);
lean_ctor_set_uint8(v___x_6016_, sizeof(void*)*7 + 2, v___x_6003_);
lean_ctor_set_uint8(v___x_6016_, sizeof(void*)*7 + 3, v___x_6004_);
v___x_6017_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6017_, 0, v___x_5987_);
lean_ctor_set(v___x_6017_, 1, v___x_5987_);
lean_ctor_set(v___x_6017_, 2, v___x_5987_);
lean_ctor_set(v___x_6017_, 3, v___x_5987_);
lean_ctor_set(v___x_6017_, 4, v___x_6006_);
lean_ctor_set(v___x_6017_, 5, v___x_6006_);
lean_ctor_set(v___x_6017_, 6, v___x_6006_);
lean_ctor_set(v___x_6017_, 7, v___x_6006_);
lean_ctor_set(v___x_6017_, 8, v___x_6006_);
lean_ctor_set(v___x_6017_, 9, v___x_6006_);
v___x_6018_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6019_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6020_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6020_, 0, v___x_6017_);
lean_ctor_set(v___x_6020_, 1, v___x_6018_);
lean_ctor_set(v___x_6020_, 2, v___x_5988_);
lean_ctor_set(v___x_6020_, 3, v___x_6011_);
lean_ctor_set(v___x_6020_, 4, v___x_6019_);
v___x_6021_ = lean_st_mk_ref(v___x_6020_);
v___x_6022_ = l_Lean_Meta_addDefaultInstance(v_declName_5990_, v_a_5999_, v___x_6016_, v___x_6021_, v___y_6001_, v___y_6002_);
lean_dec_ref_known(v___x_6016_, 7);
if (lean_obj_tag(v___x_6022_) == 0)
{
lean_object* v___x_6024_; uint8_t v_isShared_6025_; uint8_t v_isSharedCheck_6031_; 
v_isSharedCheck_6031_ = !lean_is_exclusive(v___x_6022_);
if (v_isSharedCheck_6031_ == 0)
{
lean_object* v_unused_6032_; 
v_unused_6032_ = lean_ctor_get(v___x_6022_, 0);
lean_dec(v_unused_6032_);
v___x_6024_ = v___x_6022_;
v_isShared_6025_ = v_isSharedCheck_6031_;
goto v_resetjp_6023_;
}
else
{
lean_dec(v___x_6022_);
v___x_6024_ = lean_box(0);
v_isShared_6025_ = v_isSharedCheck_6031_;
goto v_resetjp_6023_;
}
v_resetjp_6023_:
{
lean_object* v___x_6026_; lean_object* v___x_6027_; lean_object* v___x_6029_; 
v___x_6026_ = lean_st_ref_get(v___x_6021_);
lean_dec(v___x_6021_);
lean_dec(v___x_6026_);
v___x_6027_ = lean_box(0);
if (v_isShared_6025_ == 0)
{
lean_ctor_set(v___x_6024_, 0, v___x_6027_);
v___x_6029_ = v___x_6024_;
goto v_reusejp_6028_;
}
else
{
lean_object* v_reuseFailAlloc_6030_; 
v_reuseFailAlloc_6030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6030_, 0, v___x_6027_);
v___x_6029_ = v_reuseFailAlloc_6030_;
goto v_reusejp_6028_;
}
v_reusejp_6028_:
{
return v___x_6029_;
}
}
}
else
{
lean_dec(v___x_6021_);
return v___x_6022_;
}
}
}
else
{
lean_object* v_a_6036_; lean_object* v___x_6038_; uint8_t v_isShared_6039_; uint8_t v_isSharedCheck_6043_; 
lean_dec(v_declName_5990_);
lean_dec(v___x_5989_);
lean_dec(v___x_5988_);
lean_dec(v___x_5987_);
v_a_6036_ = lean_ctor_get(v___x_5998_, 0);
v_isSharedCheck_6043_ = !lean_is_exclusive(v___x_5998_);
if (v_isSharedCheck_6043_ == 0)
{
v___x_6038_ = v___x_5998_;
v_isShared_6039_ = v_isSharedCheck_6043_;
goto v_resetjp_6037_;
}
else
{
lean_inc(v_a_6036_);
lean_dec(v___x_5998_);
v___x_6038_ = lean_box(0);
v_isShared_6039_ = v_isSharedCheck_6043_;
goto v_resetjp_6037_;
}
v_resetjp_6037_:
{
lean_object* v___x_6041_; 
if (v_isShared_6039_ == 0)
{
v___x_6041_ = v___x_6038_;
goto v_reusejp_6040_;
}
else
{
lean_object* v_reuseFailAlloc_6042_; 
v_reuseFailAlloc_6042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6042_, 0, v_a_6036_);
v___x_6041_ = v_reuseFailAlloc_6042_;
goto v_reusejp_6040_;
}
v_reusejp_6040_:
{
return v___x_6041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6044_, lean_object* v___x_6045_, lean_object* v___x_6046_, lean_object* v_declName_6047_, lean_object* v_stx_6048_, lean_object* v_kind_6049_, lean_object* v___y_6050_, lean_object* v___y_6051_, lean_object* v___y_6052_){
_start:
{
uint8_t v_kind_boxed_6053_; lean_object* v_res_6054_; 
v_kind_boxed_6053_ = lean_unbox(v_kind_6049_);
v_res_6054_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6044_, v___x_6045_, v___x_6046_, v_declName_6047_, v_stx_6048_, v_kind_boxed_6053_, v___y_6050_, v___y_6051_);
lean_dec(v___y_6051_);
lean_dec_ref(v___y_6050_);
lean_dec(v_stx_6048_);
return v_res_6054_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6056_; lean_object* v___x_6057_; 
v___x_6056_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6057_ = l_Lean_stringToMessageData(v___x_6056_);
return v___x_6057_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6059_; lean_object* v___x_6060_; 
v___x_6059_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6060_ = l_Lean_stringToMessageData(v___x_6059_);
return v___x_6060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6061_, lean_object* v_decl_6062_, lean_object* v___y_6063_, lean_object* v___y_6064_){
_start:
{
lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; 
v___x_6066_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6067_ = l_Lean_MessageData_ofName(v___x_6061_);
v___x_6068_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6066_);
lean_ctor_set(v___x_6068_, 1, v___x_6067_);
v___x_6069_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6068_);
lean_ctor_set(v___x_6070_, 1, v___x_6069_);
v___x_6071_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6070_, v___y_6063_, v___y_6064_);
return v___x_6071_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6072_, lean_object* v_decl_6073_, lean_object* v___y_6074_, lean_object* v___y_6075_, lean_object* v___y_6076_){
_start:
{
lean_object* v_res_6077_; 
v_res_6077_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6072_, v_decl_6073_, v___y_6074_, v___y_6075_);
lean_dec(v___y_6075_);
lean_dec_ref(v___y_6074_);
lean_dec(v_decl_6073_);
return v_res_6077_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6110_; lean_object* v___x_6111_; lean_object* v___x_6112_; 
v___x_6110_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6111_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6112_ = l_Lean_registerBuiltinAttribute(v___x_6111_);
if (lean_obj_tag(v___x_6112_) == 0)
{
lean_object* v___x_6113_; uint8_t v___x_6114_; lean_object* v___x_6115_; 
lean_dec_ref_known(v___x_6112_, 1);
v___x_6113_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_6114_ = 0;
v___x_6115_ = l_Lean_registerTraceClass(v___x_6113_, v___x_6114_, v___x_6110_);
return v___x_6115_;
}
else
{
return v___x_6112_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_6116_){
_start:
{
lean_object* v_res_6117_; 
v_res_6117_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_6117_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_6118_, lean_object* v_name_6119_, uint8_t v_kind_6120_, lean_object* v___y_6121_, lean_object* v___y_6122_){
_start:
{
lean_object* v___x_6124_; 
v___x_6124_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6119_, v_kind_6120_, v___y_6121_, v___y_6122_);
return v___x_6124_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_6125_, lean_object* v_name_6126_, lean_object* v_kind_6127_, lean_object* v___y_6128_, lean_object* v___y_6129_, lean_object* v___y_6130_){
_start:
{
uint8_t v_kind_boxed_6131_; lean_object* v_res_6132_; 
v_kind_boxed_6131_ = lean_unbox(v_kind_6127_);
v_res_6132_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_6125_, v_name_6126_, v_kind_boxed_6131_, v___y_6128_, v___y_6129_);
lean_dec(v___y_6129_);
lean_dec_ref(v___y_6128_);
return v_res_6132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_6133_, lean_object* v_toPure_6134_, lean_object* v_____do__lift_6135_){
_start:
{
lean_object* v___x_6136_; lean_object* v_toEnvExtension_6137_; lean_object* v_asyncMode_6138_; lean_object* v___x_6139_; lean_object* v___x_6140_; lean_object* v_priorities_6141_; lean_object* v___x_6142_; 
v___x_6136_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6137_ = lean_ctor_get(v___x_6136_, 0);
v_asyncMode_6138_ = lean_ctor_get(v_toEnvExtension_6137_, 2);
v___x_6139_ = lean_box(0);
v___x_6140_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6133_, v___x_6136_, v_____do__lift_6135_, v_asyncMode_6138_, v___x_6139_);
v_priorities_6141_ = lean_ctor_get(v___x_6140_, 1);
lean_inc(v_priorities_6141_);
lean_dec(v___x_6140_);
v___x_6142_ = lean_apply_2(v_toPure_6134_, lean_box(0), v_priorities_6141_);
return v___x_6142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_6143_, lean_object* v_inst_6144_){
_start:
{
lean_object* v_toApplicative_6145_; lean_object* v_toBind_6146_; lean_object* v_getEnv_6147_; lean_object* v_toPure_6148_; lean_object* v___x_6149_; lean_object* v___f_6150_; lean_object* v___x_6151_; 
v_toApplicative_6145_ = lean_ctor_get(v_inst_6143_, 0);
lean_inc_ref(v_toApplicative_6145_);
v_toBind_6146_ = lean_ctor_get(v_inst_6143_, 1);
lean_inc(v_toBind_6146_);
lean_dec_ref(v_inst_6143_);
v_getEnv_6147_ = lean_ctor_get(v_inst_6144_, 0);
lean_inc(v_getEnv_6147_);
lean_dec_ref(v_inst_6144_);
v_toPure_6148_ = lean_ctor_get(v_toApplicative_6145_, 1);
lean_inc(v_toPure_6148_);
lean_dec_ref(v_toApplicative_6145_);
v___x_6149_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6150_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6150_, 0, v___x_6149_);
lean_closure_set(v___f_6150_, 1, v_toPure_6148_);
v___x_6151_ = lean_apply_4(v_toBind_6146_, lean_box(0), lean_box(0), v_getEnv_6147_, v___f_6150_);
return v___x_6151_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_6152_, lean_object* v_inst_6153_, lean_object* v_inst_6154_){
_start:
{
lean_object* v___x_6155_; 
v___x_6155_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_6153_, v_inst_6154_);
return v___x_6155_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_6156_, uint8_t v_isExporting_6157_, lean_object* v_x_6158_){
_start:
{
lean_object* v_fst_6159_; uint8_t v___x_6160_; 
v_fst_6159_ = lean_ctor_get(v_x_6158_, 0);
lean_inc(v_fst_6159_);
lean_dec_ref(v_x_6158_);
v___x_6160_ = l_Lean_Environment_contains(v_env_6156_, v_fst_6159_, v_isExporting_6157_);
return v___x_6160_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_6161_, lean_object* v_isExporting_6162_, lean_object* v_x_6163_){
_start:
{
uint8_t v_isExporting_boxed_6164_; uint8_t v_res_6165_; lean_object* v_r_6166_; 
v_isExporting_boxed_6164_ = lean_unbox(v_isExporting_6162_);
v_res_6165_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_6161_, v_isExporting_boxed_6164_, v_x_6163_);
v_r_6166_ = lean_box(v_res_6165_);
return v_r_6166_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_6167_, lean_object* v_toApplicative_6168_, lean_object* v_className_6169_, lean_object* v_env_6170_){
_start:
{
lean_object* v___y_6172_; lean_object* v___x_6182_; lean_object* v_toEnvExtension_6183_; lean_object* v_asyncMode_6184_; lean_object* v___x_6185_; lean_object* v___x_6186_; lean_object* v_defaultInstances_6187_; lean_object* v___x_6188_; 
v___x_6182_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6183_ = lean_ctor_get(v___x_6182_, 0);
v_asyncMode_6184_ = lean_ctor_get(v_toEnvExtension_6183_, 2);
v___x_6185_ = lean_box(0);
lean_inc_ref(v_env_6170_);
v___x_6186_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6167_, v___x_6182_, v_env_6170_, v_asyncMode_6184_, v___x_6185_);
v_defaultInstances_6187_ = lean_ctor_get(v___x_6186_, 0);
lean_inc(v_defaultInstances_6187_);
lean_dec(v___x_6186_);
v___x_6188_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_6187_, v_className_6169_);
lean_dec(v_defaultInstances_6187_);
if (lean_obj_tag(v___x_6188_) == 0)
{
lean_object* v___x_6189_; 
v___x_6189_ = lean_box(0);
v___y_6172_ = v___x_6189_;
goto v___jp_6171_;
}
else
{
lean_object* v_val_6190_; 
v_val_6190_ = lean_ctor_get(v___x_6188_, 0);
lean_inc(v_val_6190_);
lean_dec_ref_known(v___x_6188_, 1);
v___y_6172_ = v_val_6190_;
goto v___jp_6171_;
}
v___jp_6171_:
{
uint8_t v_isExporting_6173_; 
v_isExporting_6173_ = lean_ctor_get_uint8(v_env_6170_, sizeof(void*)*8);
if (v_isExporting_6173_ == 0)
{
lean_object* v_toPure_6174_; lean_object* v___x_6175_; 
lean_dec_ref(v_env_6170_);
v_toPure_6174_ = lean_ctor_get(v_toApplicative_6168_, 1);
lean_inc(v_toPure_6174_);
lean_dec_ref(v_toApplicative_6168_);
v___x_6175_ = lean_apply_2(v_toPure_6174_, lean_box(0), v___y_6172_);
return v___x_6175_;
}
else
{
lean_object* v_toPure_6176_; lean_object* v___x_6177_; lean_object* v___f_6178_; lean_object* v___x_6179_; lean_object* v___x_6180_; lean_object* v___x_6181_; 
v_toPure_6176_ = lean_ctor_get(v_toApplicative_6168_, 1);
lean_inc(v_toPure_6176_);
lean_dec_ref(v_toApplicative_6168_);
v___x_6177_ = lean_box(v_isExporting_6173_);
v___f_6178_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6178_, 0, v_env_6170_);
lean_closure_set(v___f_6178_, 1, v___x_6177_);
v___x_6179_ = lean_box(0);
v___x_6180_ = l_List_filterTR_loop___redArg(v___f_6178_, v___y_6172_, v___x_6179_);
v___x_6181_ = lean_apply_2(v_toPure_6176_, lean_box(0), v___x_6180_);
return v___x_6181_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_6191_, lean_object* v_toApplicative_6192_, lean_object* v_className_6193_, lean_object* v_env_6194_){
_start:
{
lean_object* v_res_6195_; 
v_res_6195_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_6191_, v_toApplicative_6192_, v_className_6193_, v_env_6194_);
lean_dec(v_className_6193_);
return v_res_6195_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_6196_, lean_object* v_inst_6197_, lean_object* v_className_6198_){
_start:
{
lean_object* v_toApplicative_6199_; lean_object* v_toBind_6200_; lean_object* v_getEnv_6201_; lean_object* v___x_6202_; lean_object* v___f_6203_; lean_object* v___x_6204_; 
v_toApplicative_6199_ = lean_ctor_get(v_inst_6196_, 0);
lean_inc_ref(v_toApplicative_6199_);
v_toBind_6200_ = lean_ctor_get(v_inst_6196_, 1);
lean_inc(v_toBind_6200_);
lean_dec_ref(v_inst_6196_);
v_getEnv_6201_ = lean_ctor_get(v_inst_6197_, 0);
lean_inc(v_getEnv_6201_);
lean_dec_ref(v_inst_6197_);
v___x_6202_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6203_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_6203_, 0, v___x_6202_);
lean_closure_set(v___f_6203_, 1, v_toApplicative_6199_);
lean_closure_set(v___f_6203_, 2, v_className_6198_);
v___x_6204_ = lean_apply_4(v_toBind_6200_, lean_box(0), lean_box(0), v_getEnv_6201_, v___f_6203_);
return v___x_6204_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6205_, lean_object* v_inst_6206_, lean_object* v_inst_6207_, lean_object* v_className_6208_){
_start:
{
lean_object* v___x_6209_; 
v___x_6209_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6206_, v_inst_6207_, v_className_6208_);
return v___x_6209_;
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
