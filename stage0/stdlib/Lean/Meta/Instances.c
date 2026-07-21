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
uint64_t lean_uint64_of_nat(lean_object*);
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
static lean_once_cell_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0;
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
static uint64_t _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_155_; uint64_t v___x_156_; 
v___x_155_ = lean_unsigned_to_nat(1723u);
v___x_156_ = lean_uint64_of_nat(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0(void){
_start:
{
lean_object* v___x_157_; 
v___x_157_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(lean_object* v_x_158_, size_t v_x_159_, size_t v_x_160_, lean_object* v_x_161_, lean_object* v_x_162_){
_start:
{
if (lean_obj_tag(v_x_158_) == 0)
{
lean_object* v_es_163_; size_t v___x_164_; size_t v___x_165_; lean_object* v_j_166_; lean_object* v___x_167_; uint8_t v___x_168_; 
v_es_163_ = lean_ctor_get(v_x_158_, 0);
v___x_164_ = ((size_t)31ULL);
v___x_165_ = lean_usize_land(v_x_159_, v___x_164_);
v_j_166_ = lean_usize_to_nat(v___x_165_);
v___x_167_ = lean_array_get_size(v_es_163_);
v___x_168_ = lean_nat_dec_lt(v_j_166_, v___x_167_);
if (v___x_168_ == 0)
{
lean_dec(v_j_166_);
lean_dec(v_x_162_);
lean_dec(v_x_161_);
return v_x_158_;
}
else
{
lean_object* v___x_170_; uint8_t v_isShared_171_; uint8_t v_isSharedCheck_207_; 
lean_inc_ref(v_es_163_);
v_isSharedCheck_207_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_207_ == 0)
{
lean_object* v_unused_208_; 
v_unused_208_ = lean_ctor_get(v_x_158_, 0);
lean_dec(v_unused_208_);
v___x_170_ = v_x_158_;
v_isShared_171_ = v_isSharedCheck_207_;
goto v_resetjp_169_;
}
else
{
lean_dec(v_x_158_);
v___x_170_ = lean_box(0);
v_isShared_171_ = v_isSharedCheck_207_;
goto v_resetjp_169_;
}
v_resetjp_169_:
{
lean_object* v_v_172_; lean_object* v___x_173_; lean_object* v_xs_x27_174_; lean_object* v___y_176_; 
v_v_172_ = lean_array_fget(v_es_163_, v_j_166_);
v___x_173_ = lean_box(0);
v_xs_x27_174_ = lean_array_fset(v_es_163_, v_j_166_, v___x_173_);
switch(lean_obj_tag(v_v_172_))
{
case 0:
{
lean_object* v_key_181_; lean_object* v_val_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_192_; 
v_key_181_ = lean_ctor_get(v_v_172_, 0);
v_val_182_ = lean_ctor_get(v_v_172_, 1);
v_isSharedCheck_192_ = !lean_is_exclusive(v_v_172_);
if (v_isSharedCheck_192_ == 0)
{
v___x_184_ = v_v_172_;
v_isShared_185_ = v_isSharedCheck_192_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_val_182_);
lean_inc(v_key_181_);
lean_dec(v_v_172_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_192_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
uint8_t v___x_186_; 
v___x_186_ = lean_name_eq(v_x_161_, v_key_181_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_del_object(v___x_184_);
v___x_187_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_181_, v_val_182_, v_x_161_, v_x_162_);
v___x_188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
v___y_176_ = v___x_188_;
goto v___jp_175_;
}
else
{
lean_object* v___x_190_; 
lean_dec(v_val_182_);
lean_dec(v_key_181_);
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 1, v_x_162_);
lean_ctor_set(v___x_184_, 0, v_x_161_);
v___x_190_ = v___x_184_;
goto v_reusejp_189_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_x_161_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_x_162_);
v___x_190_ = v_reuseFailAlloc_191_;
goto v_reusejp_189_;
}
v_reusejp_189_:
{
v___y_176_ = v___x_190_;
goto v___jp_175_;
}
}
}
}
case 1:
{
lean_object* v_node_193_; lean_object* v___x_195_; uint8_t v_isShared_196_; uint8_t v_isSharedCheck_205_; 
v_node_193_ = lean_ctor_get(v_v_172_, 0);
v_isSharedCheck_205_ = !lean_is_exclusive(v_v_172_);
if (v_isSharedCheck_205_ == 0)
{
v___x_195_ = v_v_172_;
v_isShared_196_ = v_isSharedCheck_205_;
goto v_resetjp_194_;
}
else
{
lean_inc(v_node_193_);
lean_dec(v_v_172_);
v___x_195_ = lean_box(0);
v_isShared_196_ = v_isSharedCheck_205_;
goto v_resetjp_194_;
}
v_resetjp_194_:
{
size_t v___x_197_; size_t v___x_198_; size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; lean_object* v___x_203_; 
v___x_197_ = ((size_t)5ULL);
v___x_198_ = lean_usize_shift_right(v_x_159_, v___x_197_);
v___x_199_ = ((size_t)1ULL);
v___x_200_ = lean_usize_add(v_x_160_, v___x_199_);
v___x_201_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_node_193_, v___x_198_, v___x_200_, v_x_161_, v_x_162_);
if (v_isShared_196_ == 0)
{
lean_ctor_set(v___x_195_, 0, v___x_201_);
v___x_203_ = v___x_195_;
goto v_reusejp_202_;
}
else
{
lean_object* v_reuseFailAlloc_204_; 
v_reuseFailAlloc_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_204_, 0, v___x_201_);
v___x_203_ = v_reuseFailAlloc_204_;
goto v_reusejp_202_;
}
v_reusejp_202_:
{
v___y_176_ = v___x_203_;
goto v___jp_175_;
}
}
}
default: 
{
lean_object* v___x_206_; 
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v_x_161_);
lean_ctor_set(v___x_206_, 1, v_x_162_);
v___y_176_ = v___x_206_;
goto v___jp_175_;
}
}
v___jp_175_:
{
lean_object* v___x_177_; lean_object* v___x_179_; 
v___x_177_ = lean_array_fset(v_xs_x27_174_, v_j_166_, v___y_176_);
lean_dec(v_j_166_);
if (v_isShared_171_ == 0)
{
lean_ctor_set(v___x_170_, 0, v___x_177_);
v___x_179_ = v___x_170_;
goto v_reusejp_178_;
}
else
{
lean_object* v_reuseFailAlloc_180_; 
v_reuseFailAlloc_180_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_180_, 0, v___x_177_);
v___x_179_ = v_reuseFailAlloc_180_;
goto v_reusejp_178_;
}
v_reusejp_178_:
{
return v___x_179_;
}
}
}
}
}
else
{
lean_object* v_ks_209_; lean_object* v_vs_210_; lean_object* v___x_212_; uint8_t v_isShared_213_; uint8_t v_isSharedCheck_230_; 
v_ks_209_ = lean_ctor_get(v_x_158_, 0);
v_vs_210_ = lean_ctor_get(v_x_158_, 1);
v_isSharedCheck_230_ = !lean_is_exclusive(v_x_158_);
if (v_isSharedCheck_230_ == 0)
{
v___x_212_ = v_x_158_;
v_isShared_213_ = v_isSharedCheck_230_;
goto v_resetjp_211_;
}
else
{
lean_inc(v_vs_210_);
lean_inc(v_ks_209_);
lean_dec(v_x_158_);
v___x_212_ = lean_box(0);
v_isShared_213_ = v_isSharedCheck_230_;
goto v_resetjp_211_;
}
v_resetjp_211_:
{
lean_object* v___x_215_; 
if (v_isShared_213_ == 0)
{
v___x_215_ = v___x_212_;
goto v_reusejp_214_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v_ks_209_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v_vs_210_);
v___x_215_ = v_reuseFailAlloc_229_;
goto v_reusejp_214_;
}
v_reusejp_214_:
{
lean_object* v_newNode_216_; uint8_t v___y_218_; size_t v___x_224_; uint8_t v___x_225_; 
v_newNode_216_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9___redArg(v___x_215_, v_x_161_, v_x_162_);
v___x_224_ = ((size_t)7ULL);
v___x_225_ = lean_usize_dec_le(v___x_224_, v_x_160_);
if (v___x_225_ == 0)
{
lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_226_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_216_);
v___x_227_ = lean_unsigned_to_nat(4u);
v___x_228_ = lean_nat_dec_lt(v___x_226_, v___x_227_);
lean_dec(v___x_226_);
v___y_218_ = v___x_228_;
goto v___jp_217_;
}
else
{
v___y_218_ = v___x_225_;
goto v___jp_217_;
}
v___jp_217_:
{
if (v___y_218_ == 0)
{
lean_object* v_ks_219_; lean_object* v_vs_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v_ks_219_ = lean_ctor_get(v_newNode_216_, 0);
lean_inc_ref(v_ks_219_);
v_vs_220_ = lean_ctor_get(v_newNode_216_, 1);
lean_inc_ref(v_vs_220_);
lean_dec_ref(v_newNode_216_);
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0);
v___x_223_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_x_160_, v_ks_219_, v_vs_220_, v___x_221_, v___x_222_);
lean_dec_ref(v_vs_220_);
lean_dec_ref(v_ks_219_);
return v___x_223_;
}
else
{
return v_newNode_216_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(size_t v_depth_231_, lean_object* v_keys_232_, lean_object* v_vals_233_, lean_object* v_i_234_, lean_object* v_entries_235_){
_start:
{
lean_object* v___x_236_; uint8_t v___x_237_; 
v___x_236_ = lean_array_get_size(v_keys_232_);
v___x_237_ = lean_nat_dec_lt(v_i_234_, v___x_236_);
if (v___x_237_ == 0)
{
lean_dec(v_i_234_);
return v_entries_235_;
}
else
{
lean_object* v_k_238_; lean_object* v_v_239_; uint64_t v___y_241_; 
v_k_238_ = lean_array_fget_borrowed(v_keys_232_, v_i_234_);
v_v_239_ = lean_array_fget_borrowed(v_vals_233_, v_i_234_);
if (lean_obj_tag(v_k_238_) == 0)
{
uint64_t v___x_252_; 
v___x_252_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0);
v___y_241_ = v___x_252_;
goto v___jp_240_;
}
else
{
uint64_t v_hash_253_; 
v_hash_253_ = lean_ctor_get_uint64(v_k_238_, sizeof(void*)*2);
v___y_241_ = v_hash_253_;
goto v___jp_240_;
}
v___jp_240_:
{
size_t v_h_242_; size_t v___x_243_; lean_object* v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v_h_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v_h_242_ = lean_uint64_to_usize(v___y_241_);
v___x_243_ = ((size_t)5ULL);
v___x_244_ = lean_unsigned_to_nat(1u);
v___x_245_ = ((size_t)1ULL);
v___x_246_ = lean_usize_sub(v_depth_231_, v___x_245_);
v___x_247_ = lean_usize_mul(v___x_243_, v___x_246_);
v_h_248_ = lean_usize_shift_right(v_h_242_, v___x_247_);
v___x_249_ = lean_nat_add(v_i_234_, v___x_244_);
lean_dec(v_i_234_);
lean_inc(v_v_239_);
lean_inc(v_k_238_);
v___x_250_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_entries_235_, v_h_248_, v_depth_231_, v_k_238_, v_v_239_);
v_i_234_ = v___x_249_;
v_entries_235_ = v___x_250_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___boxed(lean_object* v_depth_254_, lean_object* v_keys_255_, lean_object* v_vals_256_, lean_object* v_i_257_, lean_object* v_entries_258_){
_start:
{
size_t v_depth_boxed_259_; lean_object* v_res_260_; 
v_depth_boxed_259_ = lean_unbox_usize(v_depth_254_);
lean_dec(v_depth_254_);
v_res_260_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_depth_boxed_259_, v_keys_255_, v_vals_256_, v_i_257_, v_entries_258_);
lean_dec_ref(v_vals_256_);
lean_dec_ref(v_keys_255_);
return v_res_260_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___boxed(lean_object* v_x_261_, lean_object* v_x_262_, lean_object* v_x_263_, lean_object* v_x_264_, lean_object* v_x_265_){
_start:
{
size_t v_x_2101__boxed_266_; size_t v_x_2102__boxed_267_; lean_object* v_res_268_; 
v_x_2101__boxed_266_ = lean_unbox_usize(v_x_262_);
lean_dec(v_x_262_);
v_x_2102__boxed_267_ = lean_unbox_usize(v_x_263_);
lean_dec(v_x_263_);
v_res_268_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_261_, v_x_2101__boxed_266_, v_x_2102__boxed_267_, v_x_264_, v_x_265_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(lean_object* v_x_269_, lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
uint64_t v___y_273_; 
if (lean_obj_tag(v_x_270_) == 0)
{
uint64_t v___x_277_; 
v___x_277_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0);
v___y_273_ = v___x_277_;
goto v___jp_272_;
}
else
{
uint64_t v_hash_278_; 
v_hash_278_ = lean_ctor_get_uint64(v_x_270_, sizeof(void*)*2);
v___y_273_ = v_hash_278_;
goto v___jp_272_;
}
v___jp_272_:
{
size_t v___x_274_; size_t v___x_275_; lean_object* v___x_276_; 
v___x_274_ = lean_uint64_to_usize(v___y_273_);
v___x_275_ = ((size_t)1ULL);
v___x_276_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_269_, v___x_274_, v___x_275_, v_x_270_, v_x_271_);
return v___x_276_;
}
}
}
static lean_object* _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0(void){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Lean_Meta_DiscrTree_instInhabited(lean_box(0));
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(lean_object* v_msg_280_){
_start:
{
lean_object* v___x_281_; lean_object* v___x_282_; 
v___x_281_ = lean_obj_once(&l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0, &l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0_once, _init_l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2___closed__0);
v___x_282_ = lean_panic_fn_borrowed(v___x_281_, v_msg_280_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(lean_object* v_xs_283_, lean_object* v_v_284_, lean_object* v_i_285_){
_start:
{
lean_object* v___x_286_; uint8_t v___x_287_; 
v___x_286_ = lean_array_get_size(v_xs_283_);
v___x_287_ = lean_nat_dec_lt(v_i_285_, v___x_286_);
if (v___x_287_ == 0)
{
lean_object* v___x_288_; 
lean_dec(v_i_285_);
v___x_288_ = lean_box(0);
return v___x_288_;
}
else
{
lean_object* v___x_289_; uint8_t v___x_290_; 
v___x_289_ = lean_array_fget_borrowed(v_xs_283_, v_i_285_);
v___x_290_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v___x_289_, v_v_284_);
if (v___x_290_ == 0)
{
lean_object* v___x_291_; lean_object* v___x_292_; 
v___x_291_ = lean_unsigned_to_nat(1u);
v___x_292_ = lean_nat_add(v_i_285_, v___x_291_);
lean_dec(v_i_285_);
v_i_285_ = v___x_292_;
goto _start;
}
else
{
lean_object* v___x_294_; 
v___x_294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_294_, 0, v_i_285_);
return v___x_294_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10___boxed(lean_object* v_xs_295_, lean_object* v_v_296_, lean_object* v_i_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(v_xs_295_, v_v_296_, v_i_297_);
lean_dec(v_v_296_);
lean_dec_ref(v_xs_295_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(lean_object* v_xs_299_, lean_object* v_v_300_){
_start:
{
lean_object* v___x_301_; lean_object* v___x_302_; 
v___x_301_ = lean_unsigned_to_nat(0u);
v___x_302_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4_spec__10(v_xs_299_, v_v_300_, v___x_301_);
return v___x_302_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4___boxed(lean_object* v_xs_303_, lean_object* v_v_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(v_xs_303_, v_v_304_);
lean_dec(v_v_304_);
lean_dec_ref(v_xs_303_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(lean_object* v_x_306_, lean_object* v_x_307_, lean_object* v_x_308_, lean_object* v_x_309_){
_start:
{
lean_object* v_ks_310_; lean_object* v_vs_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_335_; 
v_ks_310_ = lean_ctor_get(v_x_306_, 0);
v_vs_311_ = lean_ctor_get(v_x_306_, 1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_306_);
if (v_isSharedCheck_335_ == 0)
{
v___x_313_ = v_x_306_;
v_isShared_314_ = v_isSharedCheck_335_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_vs_311_);
lean_inc(v_ks_310_);
lean_dec(v_x_306_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_335_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_315_; uint8_t v___x_316_; 
v___x_315_ = lean_array_get_size(v_ks_310_);
v___x_316_ = lean_nat_dec_lt(v_x_307_, v___x_315_);
if (v___x_316_ == 0)
{
lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_320_; 
lean_dec(v_x_307_);
v___x_317_ = lean_array_push(v_ks_310_, v_x_308_);
v___x_318_ = lean_array_push(v_vs_311_, v_x_309_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___x_318_);
lean_ctor_set(v___x_313_, 0, v___x_317_);
v___x_320_ = v___x_313_;
goto v_reusejp_319_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v___x_318_);
v___x_320_ = v_reuseFailAlloc_321_;
goto v_reusejp_319_;
}
v_reusejp_319_:
{
return v___x_320_;
}
}
else
{
lean_object* v_k_x27_322_; uint8_t v___x_323_; 
v_k_x27_322_ = lean_array_fget_borrowed(v_ks_310_, v_x_307_);
v___x_323_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_308_, v_k_x27_322_);
if (v___x_323_ == 0)
{
lean_object* v___x_325_; 
if (v_isShared_314_ == 0)
{
v___x_325_ = v___x_313_;
goto v_reusejp_324_;
}
else
{
lean_object* v_reuseFailAlloc_329_; 
v_reuseFailAlloc_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_329_, 0, v_ks_310_);
lean_ctor_set(v_reuseFailAlloc_329_, 1, v_vs_311_);
v___x_325_ = v_reuseFailAlloc_329_;
goto v_reusejp_324_;
}
v_reusejp_324_:
{
lean_object* v___x_326_; lean_object* v___x_327_; 
v___x_326_ = lean_unsigned_to_nat(1u);
v___x_327_ = lean_nat_add(v_x_307_, v___x_326_);
lean_dec(v_x_307_);
v_x_306_ = v___x_325_;
v_x_307_ = v___x_327_;
goto _start;
}
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_333_; 
v___x_330_ = lean_array_fset(v_ks_310_, v_x_307_, v_x_308_);
v___x_331_ = lean_array_fset(v_vs_311_, v_x_307_, v_x_309_);
lean_dec(v_x_307_);
if (v_isShared_314_ == 0)
{
lean_ctor_set(v___x_313_, 1, v___x_331_);
lean_ctor_set(v___x_313_, 0, v___x_330_);
v___x_333_ = v___x_313_;
goto v_reusejp_332_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_330_);
lean_ctor_set(v_reuseFailAlloc_334_, 1, v___x_331_);
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
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(lean_object* v_n_336_, lean_object* v_k_337_, lean_object* v_v_338_){
_start:
{
lean_object* v___x_339_; lean_object* v___x_340_; 
v___x_339_ = lean_unsigned_to_nat(0u);
v___x_340_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(v_n_336_, v___x_339_, v_k_337_, v_v_338_);
return v___x_340_;
}
}
static lean_object* _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0(void){
_start:
{
lean_object* v___x_341_; 
v___x_341_ = l_Lean_PersistentHashMap_mkEmptyEntries(lean_box(0), lean_box(0));
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(lean_object* v_x_342_, size_t v_x_343_, size_t v_x_344_, lean_object* v_x_345_, lean_object* v_x_346_){
_start:
{
if (lean_obj_tag(v_x_342_) == 0)
{
lean_object* v_es_347_; size_t v___x_348_; size_t v___x_349_; lean_object* v_j_350_; lean_object* v___x_351_; uint8_t v___x_352_; 
v_es_347_ = lean_ctor_get(v_x_342_, 0);
v___x_348_ = ((size_t)31ULL);
v___x_349_ = lean_usize_land(v_x_343_, v___x_348_);
v_j_350_ = lean_usize_to_nat(v___x_349_);
v___x_351_ = lean_array_get_size(v_es_347_);
v___x_352_ = lean_nat_dec_lt(v_j_350_, v___x_351_);
if (v___x_352_ == 0)
{
lean_dec(v_j_350_);
lean_dec(v_x_346_);
lean_dec(v_x_345_);
return v_x_342_;
}
else
{
lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_391_; 
lean_inc_ref(v_es_347_);
v_isSharedCheck_391_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_391_ == 0)
{
lean_object* v_unused_392_; 
v_unused_392_ = lean_ctor_get(v_x_342_, 0);
lean_dec(v_unused_392_);
v___x_354_ = v_x_342_;
v_isShared_355_ = v_isSharedCheck_391_;
goto v_resetjp_353_;
}
else
{
lean_dec(v_x_342_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_391_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v_v_356_; lean_object* v___x_357_; lean_object* v_xs_x27_358_; lean_object* v___y_360_; 
v_v_356_ = lean_array_fget(v_es_347_, v_j_350_);
v___x_357_ = lean_box(0);
v_xs_x27_358_ = lean_array_fset(v_es_347_, v_j_350_, v___x_357_);
switch(lean_obj_tag(v_v_356_))
{
case 0:
{
lean_object* v_key_365_; lean_object* v_val_366_; lean_object* v___x_368_; uint8_t v_isShared_369_; uint8_t v_isSharedCheck_376_; 
v_key_365_ = lean_ctor_get(v_v_356_, 0);
v_val_366_ = lean_ctor_get(v_v_356_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_v_356_);
if (v_isSharedCheck_376_ == 0)
{
v___x_368_ = v_v_356_;
v_isShared_369_ = v_isSharedCheck_376_;
goto v_resetjp_367_;
}
else
{
lean_inc(v_val_366_);
lean_inc(v_key_365_);
lean_dec(v_v_356_);
v___x_368_ = lean_box(0);
v_isShared_369_ = v_isSharedCheck_376_;
goto v_resetjp_367_;
}
v_resetjp_367_:
{
uint8_t v___x_370_; 
v___x_370_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_345_, v_key_365_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; lean_object* v___x_372_; 
lean_del_object(v___x_368_);
v___x_371_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_365_, v_val_366_, v_x_345_, v_x_346_);
v___x_372_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_372_, 0, v___x_371_);
v___y_360_ = v___x_372_;
goto v___jp_359_;
}
else
{
lean_object* v___x_374_; 
lean_dec(v_val_366_);
lean_dec(v_key_365_);
if (v_isShared_369_ == 0)
{
lean_ctor_set(v___x_368_, 1, v_x_346_);
lean_ctor_set(v___x_368_, 0, v_x_345_);
v___x_374_ = v___x_368_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v_x_345_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v_x_346_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
v___y_360_ = v___x_374_;
goto v___jp_359_;
}
}
}
}
case 1:
{
lean_object* v_node_377_; lean_object* v___x_379_; uint8_t v_isShared_380_; uint8_t v_isSharedCheck_389_; 
v_node_377_ = lean_ctor_get(v_v_356_, 0);
v_isSharedCheck_389_ = !lean_is_exclusive(v_v_356_);
if (v_isSharedCheck_389_ == 0)
{
v___x_379_ = v_v_356_;
v_isShared_380_ = v_isSharedCheck_389_;
goto v_resetjp_378_;
}
else
{
lean_inc(v_node_377_);
lean_dec(v_v_356_);
v___x_379_ = lean_box(0);
v_isShared_380_ = v_isSharedCheck_389_;
goto v_resetjp_378_;
}
v_resetjp_378_:
{
size_t v___x_381_; size_t v___x_382_; size_t v___x_383_; size_t v___x_384_; lean_object* v___x_385_; lean_object* v___x_387_; 
v___x_381_ = ((size_t)5ULL);
v___x_382_ = lean_usize_shift_right(v_x_343_, v___x_381_);
v___x_383_ = ((size_t)1ULL);
v___x_384_ = lean_usize_add(v_x_344_, v___x_383_);
v___x_385_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_node_377_, v___x_382_, v___x_384_, v_x_345_, v_x_346_);
if (v_isShared_380_ == 0)
{
lean_ctor_set(v___x_379_, 0, v___x_385_);
v___x_387_ = v___x_379_;
goto v_reusejp_386_;
}
else
{
lean_object* v_reuseFailAlloc_388_; 
v_reuseFailAlloc_388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_388_, 0, v___x_385_);
v___x_387_ = v_reuseFailAlloc_388_;
goto v_reusejp_386_;
}
v_reusejp_386_:
{
v___y_360_ = v___x_387_;
goto v___jp_359_;
}
}
}
default: 
{
lean_object* v___x_390_; 
v___x_390_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_390_, 0, v_x_345_);
lean_ctor_set(v___x_390_, 1, v_x_346_);
v___y_360_ = v___x_390_;
goto v___jp_359_;
}
}
v___jp_359_:
{
lean_object* v___x_361_; lean_object* v___x_363_; 
v___x_361_ = lean_array_fset(v_xs_x27_358_, v_j_350_, v___y_360_);
lean_dec(v_j_350_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 0, v___x_361_);
v___x_363_ = v___x_354_;
goto v_reusejp_362_;
}
else
{
lean_object* v_reuseFailAlloc_364_; 
v_reuseFailAlloc_364_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_364_, 0, v___x_361_);
v___x_363_ = v_reuseFailAlloc_364_;
goto v_reusejp_362_;
}
v_reusejp_362_:
{
return v___x_363_;
}
}
}
}
}
else
{
lean_object* v_ks_393_; lean_object* v_vs_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_414_; 
v_ks_393_ = lean_ctor_get(v_x_342_, 0);
v_vs_394_ = lean_ctor_get(v_x_342_, 1);
v_isSharedCheck_414_ = !lean_is_exclusive(v_x_342_);
if (v_isSharedCheck_414_ == 0)
{
v___x_396_ = v_x_342_;
v_isShared_397_ = v_isSharedCheck_414_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_vs_394_);
lean_inc(v_ks_393_);
lean_dec(v_x_342_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_414_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_399_; 
if (v_isShared_397_ == 0)
{
v___x_399_ = v___x_396_;
goto v_reusejp_398_;
}
else
{
lean_object* v_reuseFailAlloc_413_; 
v_reuseFailAlloc_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_413_, 0, v_ks_393_);
lean_ctor_set(v_reuseFailAlloc_413_, 1, v_vs_394_);
v___x_399_ = v_reuseFailAlloc_413_;
goto v_reusejp_398_;
}
v_reusejp_398_:
{
lean_object* v_newNode_400_; uint8_t v___y_402_; size_t v___x_408_; uint8_t v___x_409_; 
v_newNode_400_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(v___x_399_, v_x_345_, v_x_346_);
v___x_408_ = ((size_t)7ULL);
v___x_409_ = lean_usize_dec_le(v___x_408_, v_x_344_);
if (v___x_409_ == 0)
{
lean_object* v___x_410_; lean_object* v___x_411_; uint8_t v___x_412_; 
v___x_410_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_400_);
v___x_411_ = lean_unsigned_to_nat(4u);
v___x_412_ = lean_nat_dec_lt(v___x_410_, v___x_411_);
lean_dec(v___x_410_);
v___y_402_ = v___x_412_;
goto v___jp_401_;
}
else
{
v___y_402_ = v___x_409_;
goto v___jp_401_;
}
v___jp_401_:
{
if (v___y_402_ == 0)
{
lean_object* v_ks_403_; lean_object* v_vs_404_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; 
v_ks_403_ = lean_ctor_get(v_newNode_400_, 0);
lean_inc_ref(v_ks_403_);
v_vs_404_ = lean_ctor_get(v_newNode_400_, 1);
lean_inc_ref(v_vs_404_);
lean_dec_ref(v_newNode_400_);
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___closed__0);
v___x_407_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(v_x_344_, v_ks_403_, v_vs_404_, v___x_405_, v___x_406_);
lean_dec_ref(v_vs_404_);
lean_dec_ref(v_ks_403_);
return v___x_407_;
}
else
{
return v_newNode_400_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(size_t v_depth_415_, lean_object* v_keys_416_, lean_object* v_vals_417_, lean_object* v_i_418_, lean_object* v_entries_419_){
_start:
{
lean_object* v___x_420_; uint8_t v___x_421_; 
v___x_420_ = lean_array_get_size(v_keys_416_);
v___x_421_ = lean_nat_dec_lt(v_i_418_, v___x_420_);
if (v___x_421_ == 0)
{
lean_dec(v_i_418_);
return v_entries_419_;
}
else
{
lean_object* v_k_422_; lean_object* v_v_423_; uint64_t v___x_424_; size_t v_h_425_; size_t v___x_426_; lean_object* v___x_427_; size_t v___x_428_; size_t v___x_429_; size_t v___x_430_; size_t v_h_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
v_k_422_ = lean_array_fget_borrowed(v_keys_416_, v_i_418_);
v_v_423_ = lean_array_fget_borrowed(v_vals_417_, v_i_418_);
v___x_424_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_422_);
v_h_425_ = lean_uint64_to_usize(v___x_424_);
v___x_426_ = ((size_t)5ULL);
v___x_427_ = lean_unsigned_to_nat(1u);
v___x_428_ = ((size_t)1ULL);
v___x_429_ = lean_usize_sub(v_depth_415_, v___x_428_);
v___x_430_ = lean_usize_mul(v___x_426_, v___x_429_);
v_h_431_ = lean_usize_shift_right(v_h_425_, v___x_430_);
v___x_432_ = lean_nat_add(v_i_418_, v___x_427_);
lean_dec(v_i_418_);
lean_inc(v_v_423_);
lean_inc(v_k_422_);
v___x_433_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_entries_419_, v_h_431_, v_depth_415_, v_k_422_, v_v_423_);
v_i_418_ = v___x_432_;
v_entries_419_ = v___x_433_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg___boxed(lean_object* v_depth_435_, lean_object* v_keys_436_, lean_object* v_vals_437_, lean_object* v_i_438_, lean_object* v_entries_439_){
_start:
{
size_t v_depth_boxed_440_; lean_object* v_res_441_; 
v_depth_boxed_440_ = lean_unbox_usize(v_depth_435_);
lean_dec(v_depth_435_);
v_res_441_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(v_depth_boxed_440_, v_keys_436_, v_vals_437_, v_i_438_, v_entries_439_);
lean_dec_ref(v_vals_437_);
lean_dec_ref(v_keys_436_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg___boxed(lean_object* v_x_442_, lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_x_445_, lean_object* v_x_446_){
_start:
{
size_t v_x_2387__boxed_447_; size_t v_x_2388__boxed_448_; lean_object* v_res_449_; 
v_x_2387__boxed_447_ = lean_unbox_usize(v_x_443_);
lean_dec(v_x_443_);
v_x_2388__boxed_448_ = lean_unbox_usize(v_x_444_);
lean_dec(v_x_444_);
v_res_449_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_x_442_, v_x_2387__boxed_447_, v_x_2388__boxed_448_, v_x_445_, v_x_446_);
return v_res_449_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(lean_object* v_x_450_, lean_object* v_keys_451_, lean_object* v_v_452_, lean_object* v_k_453_, lean_object* v_x_454_){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; lean_object* v_c_457_; lean_object* v___x_458_; 
v___x_455_ = lean_unsigned_to_nat(1u);
v___x_456_ = lean_nat_add(v_x_450_, v___x_455_);
v_c_457_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_451_, v_v_452_, v___x_456_);
lean_dec(v___x_456_);
v___x_458_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_458_, 0, v_k_453_);
lean_ctor_set(v___x_458_, 1, v_c_457_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0___boxed(lean_object* v_x_459_, lean_object* v_keys_460_, lean_object* v_v_461_, lean_object* v_k_462_, lean_object* v_x_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_459_, v_keys_460_, v_v_461_, v_k_462_, v_x_463_);
lean_dec_ref(v_keys_460_);
lean_dec(v_x_459_);
return v_res_464_;
}
}
LEAN_EXPORT uint8_t l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(lean_object* v_a_465_, lean_object* v_b_466_){
_start:
{
lean_object* v_fst_467_; lean_object* v_fst_468_; uint8_t v___x_469_; 
v_fst_467_ = lean_ctor_get(v_a_465_, 0);
v_fst_468_ = lean_ctor_get(v_b_466_, 0);
v___x_469_ = l_Lean_Meta_DiscrTree_Key_lt(v_fst_467_, v_fst_468_);
return v___x_469_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1___boxed(lean_object* v_a_470_, lean_object* v_b_471_){
_start:
{
uint8_t v_res_472_; lean_object* v_r_473_; 
v_res_472_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_a_470_, v_b_471_);
lean_dec_ref(v_b_471_);
lean_dec_ref(v_a_470_);
v_r_473_ = lean_box(v_res_472_);
return v_r_473_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(lean_object* v_vs_474_, lean_object* v_v_475_, lean_object* v_i_476_){
_start:
{
lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_477_ = lean_array_get_size(v_vs_474_);
v___x_478_ = lean_nat_dec_lt(v_i_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; 
lean_dec(v_i_476_);
v___x_479_ = lean_array_push(v_vs_474_, v_v_475_);
return v___x_479_;
}
else
{
lean_object* v_val_480_; lean_object* v___x_481_; lean_object* v_val_482_; uint8_t v___x_483_; 
v_val_480_ = lean_ctor_get(v_v_475_, 1);
v___x_481_ = lean_array_fget_borrowed(v_vs_474_, v_i_476_);
v_val_482_ = lean_ctor_get(v___x_481_, 1);
v___x_483_ = lean_expr_eqv(v_val_480_, v_val_482_);
if (v___x_483_ == 0)
{
lean_object* v___x_484_; lean_object* v___x_485_; 
v___x_484_ = lean_unsigned_to_nat(1u);
v___x_485_ = lean_nat_add(v_i_476_, v___x_484_);
lean_dec(v_i_476_);
v_i_476_ = v___x_485_;
goto _start;
}
else
{
lean_object* v___x_487_; 
v___x_487_ = lean_array_fset(v_vs_474_, v_i_476_, v_v_475_);
lean_dec(v_i_476_);
return v___x_487_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(lean_object* v_vs_488_, lean_object* v_v_489_){
_start:
{
lean_object* v___x_490_; lean_object* v___x_491_; 
v___x_490_ = lean_unsigned_to_nat(0u);
v___x_491_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal_loop___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1_spec__5(v_vs_488_, v_v_489_, v___x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(lean_object* v_x_496_, lean_object* v_keys_497_, lean_object* v_v_498_, lean_object* v_k_499_, lean_object* v_as_500_, lean_object* v_k_501_, lean_object* v_x_502_, lean_object* v_x_503_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v_mid_506_; lean_object* v_midVal_507_; uint8_t v___x_508_; 
v___x_504_ = lean_nat_add(v_x_502_, v_x_503_);
v___x_505_ = lean_unsigned_to_nat(1u);
v_mid_506_ = lean_nat_shiftr(v___x_504_, v___x_505_);
lean_dec(v___x_504_);
v_midVal_507_ = lean_array_fget(v_as_500_, v_mid_506_);
v___x_508_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_midVal_507_, v_k_501_);
if (v___x_508_ == 0)
{
uint8_t v___x_509_; 
lean_dec(v_x_503_);
v___x_509_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_501_, v_midVal_507_);
if (v___x_509_ == 0)
{
lean_object* v___x_510_; uint8_t v___x_511_; 
lean_dec(v_x_502_);
v___x_510_ = lean_array_get_size(v_as_500_);
v___x_511_ = lean_nat_dec_lt(v_mid_506_, v___x_510_);
if (v___x_511_ == 0)
{
lean_dec(v_midVal_507_);
lean_dec(v_mid_506_);
lean_dec(v_k_499_);
lean_dec_ref(v_v_498_);
return v_as_500_;
}
else
{
lean_object* v_snd_512_; lean_object* v___x_514_; uint8_t v_isShared_515_; uint8_t v_isSharedCheck_524_; 
v_snd_512_ = lean_ctor_get(v_midVal_507_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_midVal_507_);
if (v_isSharedCheck_524_ == 0)
{
lean_object* v_unused_525_; 
v_unused_525_ = lean_ctor_get(v_midVal_507_, 0);
lean_dec(v_unused_525_);
v___x_514_ = v_midVal_507_;
v_isShared_515_ = v_isSharedCheck_524_;
goto v_resetjp_513_;
}
else
{
lean_inc(v_snd_512_);
lean_dec(v_midVal_507_);
v___x_514_ = lean_box(0);
v_isShared_515_ = v_isSharedCheck_524_;
goto v_resetjp_513_;
}
v_resetjp_513_:
{
lean_object* v___x_516_; lean_object* v_xs_x27_517_; lean_object* v___x_518_; lean_object* v_c_519_; lean_object* v___x_521_; 
v___x_516_ = lean_box(0);
v_xs_x27_517_ = lean_array_fset(v_as_500_, v_mid_506_, v___x_516_);
v___x_518_ = lean_nat_add(v_x_496_, v___x_505_);
v_c_519_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_497_, v_v_498_, v___x_518_, v_snd_512_);
lean_dec(v___x_518_);
if (v_isShared_515_ == 0)
{
lean_ctor_set(v___x_514_, 1, v_c_519_);
lean_ctor_set(v___x_514_, 0, v_k_499_);
v___x_521_ = v___x_514_;
goto v_reusejp_520_;
}
else
{
lean_object* v_reuseFailAlloc_523_; 
v_reuseFailAlloc_523_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_523_, 0, v_k_499_);
lean_ctor_set(v_reuseFailAlloc_523_, 1, v_c_519_);
v___x_521_ = v_reuseFailAlloc_523_;
goto v_reusejp_520_;
}
v_reusejp_520_:
{
lean_object* v___x_522_; 
v___x_522_ = lean_array_fset(v_xs_x27_517_, v_mid_506_, v___x_521_);
lean_dec(v_mid_506_);
return v___x_522_;
}
}
}
}
else
{
lean_dec(v_midVal_507_);
v_x_503_ = v_mid_506_;
goto _start;
}
}
else
{
uint8_t v___x_527_; 
lean_dec(v_midVal_507_);
v___x_527_ = lean_nat_dec_eq(v_mid_506_, v_x_502_);
if (v___x_527_ == 0)
{
lean_dec(v_x_502_);
v_x_502_ = v_mid_506_;
goto _start;
}
else
{
lean_object* v___x_529_; lean_object* v_c_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v_j_533_; lean_object* v_as_534_; lean_object* v___x_535_; 
lean_dec(v_mid_506_);
lean_dec(v_x_503_);
v___x_529_ = lean_nat_add(v_x_496_, v___x_505_);
v_c_530_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_497_, v_v_498_, v___x_529_);
lean_dec(v___x_529_);
v___x_531_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_531_, 0, v_k_499_);
lean_ctor_set(v___x_531_, 1, v_c_530_);
v___x_532_ = lean_nat_add(v_x_502_, v___x_505_);
lean_dec(v_x_502_);
v_j_533_ = lean_array_get_size(v_as_500_);
v_as_534_ = lean_array_push(v_as_500_, v___x_531_);
v___x_535_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_532_, v_as_534_, v_j_533_);
lean_dec(v___x_532_);
return v___x_535_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(lean_object* v_x_536_, lean_object* v_keys_537_, lean_object* v_v_538_, lean_object* v_k_539_, lean_object* v_as_540_, lean_object* v_k_541_){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; uint8_t v___x_544_; 
v___x_542_ = lean_array_get_size(v_as_540_);
v___x_543_ = lean_unsigned_to_nat(0u);
v___x_544_ = lean_nat_dec_eq(v___x_542_, v___x_543_);
if (v___x_544_ == 0)
{
lean_object* v___x_545_; uint8_t v___x_546_; 
v___x_545_ = lean_array_fget_borrowed(v_as_540_, v___x_543_);
v___x_546_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_541_, v___x_545_);
if (v___x_546_ == 0)
{
uint8_t v___x_547_; 
v___x_547_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v___x_545_, v_k_541_);
if (v___x_547_ == 0)
{
uint8_t v___x_548_; 
v___x_548_ = lean_nat_dec_lt(v___x_543_, v___x_542_);
if (v___x_548_ == 0)
{
lean_dec(v_k_539_);
lean_dec_ref(v_v_538_);
return v_as_540_;
}
else
{
lean_object* v___x_549_; lean_object* v_xs_x27_550_; lean_object* v___x_551_; lean_object* v___x_552_; 
lean_inc(v___x_545_);
v___x_549_ = lean_box(0);
v_xs_x27_550_ = lean_array_fset(v_as_540_, v___x_543_, v___x_549_);
v___x_551_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_536_, v_keys_537_, v_v_538_, v_k_539_, v___x_545_);
v___x_552_ = lean_array_fset(v_xs_x27_550_, v___x_543_, v___x_551_);
return v___x_552_;
}
}
else
{
lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; uint8_t v___x_556_; 
v___x_553_ = lean_unsigned_to_nat(1u);
v___x_554_ = lean_nat_sub(v___x_542_, v___x_553_);
v___x_555_ = lean_array_fget_borrowed(v_as_540_, v___x_554_);
v___x_556_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v___x_555_, v_k_541_);
if (v___x_556_ == 0)
{
uint8_t v___x_557_; 
v___x_557_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_541_, v___x_555_);
if (v___x_557_ == 0)
{
uint8_t v___x_558_; 
v___x_558_ = lean_nat_dec_lt(v___x_554_, v___x_542_);
if (v___x_558_ == 0)
{
lean_dec(v___x_554_);
lean_dec(v_k_539_);
lean_dec_ref(v_v_538_);
return v_as_540_;
}
else
{
lean_object* v___x_559_; lean_object* v_xs_x27_560_; lean_object* v___x_561_; lean_object* v___x_562_; 
lean_inc(v___x_555_);
v___x_559_ = lean_box(0);
v_xs_x27_560_ = lean_array_fset(v_as_540_, v___x_554_, v___x_559_);
v___x_561_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_536_, v_keys_537_, v_v_538_, v_k_539_, v___x_555_);
v___x_562_ = lean_array_fset(v_xs_x27_560_, v___x_554_, v___x_561_);
lean_dec(v___x_554_);
return v___x_562_;
}
}
else
{
lean_object* v___x_563_; 
v___x_563_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_536_, v_keys_537_, v_v_538_, v_k_539_, v_as_540_, v_k_541_, v___x_543_, v___x_554_);
return v___x_563_;
}
}
else
{
lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; 
lean_dec(v___x_554_);
v___x_564_ = lean_box(0);
v___x_565_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_536_, v_keys_537_, v_v_538_, v_k_539_, v___x_564_);
v___x_566_ = lean_array_push(v_as_540_, v___x_565_);
return v___x_566_;
}
}
}
else
{
lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v_as_569_; lean_object* v___x_570_; 
v___x_567_ = lean_box(0);
v___x_568_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_536_, v_keys_537_, v_v_538_, v_k_539_, v___x_567_);
v_as_569_ = lean_array_push(v_as_540_, v___x_568_);
v___x_570_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_543_, v_as_569_, v___x_542_);
return v___x_570_;
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_571_ = lean_box(0);
v___x_572_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_536_, v_keys_537_, v_v_538_, v_k_539_, v___x_571_);
v___x_573_ = lean_array_push(v_as_540_, v___x_572_);
return v___x_573_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object* v_keys_574_, lean_object* v_v_575_, lean_object* v_x_576_, lean_object* v_x_577_){
_start:
{
lean_object* v_vs_578_; lean_object* v_children_579_; lean_object* v___x_581_; uint8_t v_isShared_582_; uint8_t v_isSharedCheck_596_; 
v_vs_578_ = lean_ctor_get(v_x_577_, 0);
v_children_579_ = lean_ctor_get(v_x_577_, 1);
v_isSharedCheck_596_ = !lean_is_exclusive(v_x_577_);
if (v_isSharedCheck_596_ == 0)
{
v___x_581_ = v_x_577_;
v_isShared_582_ = v_isSharedCheck_596_;
goto v_resetjp_580_;
}
else
{
lean_inc(v_children_579_);
lean_inc(v_vs_578_);
lean_dec(v_x_577_);
v___x_581_ = lean_box(0);
v_isShared_582_ = v_isSharedCheck_596_;
goto v_resetjp_580_;
}
v_resetjp_580_:
{
lean_object* v___x_583_; uint8_t v___x_584_; 
v___x_583_ = lean_array_get_size(v_keys_574_);
v___x_584_ = lean_nat_dec_lt(v_x_576_, v___x_583_);
if (v___x_584_ == 0)
{
lean_object* v___x_585_; lean_object* v___x_587_; 
v___x_585_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(v_vs_578_, v_v_575_);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 0, v___x_585_);
v___x_587_ = v___x_581_;
goto v_reusejp_586_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v___x_585_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_children_579_);
v___x_587_ = v_reuseFailAlloc_588_;
goto v_reusejp_586_;
}
v_reusejp_586_:
{
return v___x_587_;
}
}
else
{
lean_object* v_k_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v_c_592_; lean_object* v___x_594_; 
v_k_589_ = lean_array_fget_borrowed(v_keys_574_, v_x_576_);
v___x_590_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__1));
lean_inc_n(v_k_589_, 2);
v___x_591_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_591_, 0, v_k_589_);
lean_ctor_set(v___x_591_, 1, v___x_590_);
v_c_592_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(v_x_576_, v_keys_574_, v_v_575_, v_k_589_, v_children_579_, v___x_591_);
lean_dec_ref_known(v___x_591_, 2);
if (v_isShared_582_ == 0)
{
lean_ctor_set(v___x_581_, 1, v_c_592_);
v___x_594_ = v___x_581_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_vs_578_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_c_592_);
v___x_594_ = v_reuseFailAlloc_595_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
return v___x_594_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(lean_object* v_x_597_, lean_object* v_keys_598_, lean_object* v_v_599_, lean_object* v_k_600_, lean_object* v_x_601_){
_start:
{
lean_object* v_snd_602_; lean_object* v___x_604_; uint8_t v_isShared_605_; uint8_t v_isSharedCheck_612_; 
v_snd_602_ = lean_ctor_get(v_x_601_, 1);
v_isSharedCheck_612_ = !lean_is_exclusive(v_x_601_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v_x_601_, 0);
lean_dec(v_unused_613_);
v___x_604_ = v_x_601_;
v_isShared_605_ = v_isSharedCheck_612_;
goto v_resetjp_603_;
}
else
{
lean_inc(v_snd_602_);
lean_dec(v_x_601_);
v___x_604_ = lean_box(0);
v_isShared_605_ = v_isSharedCheck_612_;
goto v_resetjp_603_;
}
v_resetjp_603_:
{
lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v_c_608_; lean_object* v___x_610_; 
v___x_606_ = lean_unsigned_to_nat(1u);
v___x_607_ = lean_nat_add(v_x_597_, v___x_606_);
v_c_608_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_598_, v_v_599_, v___x_607_, v_snd_602_);
lean_dec(v___x_607_);
if (v_isShared_605_ == 0)
{
lean_ctor_set(v___x_604_, 1, v_c_608_);
lean_ctor_set(v___x_604_, 0, v_k_600_);
v___x_610_ = v___x_604_;
goto v_reusejp_609_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_k_600_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_c_608_);
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
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* v_x_614_, lean_object* v_keys_615_, lean_object* v_v_616_, lean_object* v_k_617_, lean_object* v_x_618_){
_start:
{
lean_object* v_res_619_; 
v_res_619_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_614_, v_keys_615_, v_v_616_, v_k_617_, v_x_618_);
lean_dec_ref(v_keys_615_);
lean_dec(v_x_614_);
return v_res_619_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object* v_keys_620_, lean_object* v_v_621_, lean_object* v_x_622_, lean_object* v_x_623_){
_start:
{
lean_object* v_res_624_; 
v_res_624_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_620_, v_v_621_, v_x_622_, v_x_623_);
lean_dec(v_x_622_);
lean_dec_ref(v_keys_620_);
return v_res_624_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_x_625_, lean_object* v_keys_626_, lean_object* v_v_627_, lean_object* v_k_628_, lean_object* v_as_629_, lean_object* v_k_630_, lean_object* v_x_631_, lean_object* v_x_632_){
_start:
{
lean_object* v_res_633_; 
v_res_633_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_625_, v_keys_626_, v_v_627_, v_k_628_, v_as_629_, v_k_630_, v_x_631_, v_x_632_);
lean_dec_ref(v_k_630_);
lean_dec_ref(v_keys_626_);
lean_dec(v_x_625_);
return v_res_633_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_x_634_, lean_object* v_keys_635_, lean_object* v_v_636_, lean_object* v_k_637_, lean_object* v_as_638_, lean_object* v_k_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(v_x_634_, v_keys_635_, v_v_636_, v_k_637_, v_as_638_, v_k_639_);
lean_dec_ref(v_k_639_);
lean_dec_ref(v_keys_635_);
lean_dec(v_x_634_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(lean_object* v_keys_641_, lean_object* v_v_642_, lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_643_) == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_644_ = lean_unsigned_to_nat(1u);
v___x_645_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_641_, v_v_642_, v___x_644_);
v___x_646_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_646_, 0, v___x_645_);
return v___x_646_;
}
else
{
lean_object* v_val_647_; lean_object* v___x_649_; uint8_t v_isShared_650_; uint8_t v_isSharedCheck_656_; 
v_val_647_ = lean_ctor_get(v_x_643_, 0);
v_isSharedCheck_656_ = !lean_is_exclusive(v_x_643_);
if (v_isSharedCheck_656_ == 0)
{
v___x_649_ = v_x_643_;
v_isShared_650_ = v_isSharedCheck_656_;
goto v_resetjp_648_;
}
else
{
lean_inc(v_val_647_);
lean_dec(v_x_643_);
v___x_649_ = lean_box(0);
v_isShared_650_ = v_isSharedCheck_656_;
goto v_resetjp_648_;
}
v_resetjp_648_:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_654_; 
v___x_651_ = lean_unsigned_to_nat(1u);
v___x_652_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_641_, v_v_642_, v___x_651_, v_val_647_);
if (v_isShared_650_ == 0)
{
lean_ctor_set(v___x_649_, 0, v___x_652_);
v___x_654_ = v___x_649_;
goto v_reusejp_653_;
}
else
{
lean_object* v_reuseFailAlloc_655_; 
v_reuseFailAlloc_655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_655_, 0, v___x_652_);
v___x_654_ = v_reuseFailAlloc_655_;
goto v_reusejp_653_;
}
v_reusejp_653_:
{
return v___x_654_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0___boxed(lean_object* v_keys_657_, lean_object* v_v_658_, lean_object* v_x_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_657_, v_v_658_, v_x_659_);
lean_dec_ref(v_keys_657_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(lean_object* v_keys_661_, lean_object* v_v_662_, lean_object* v_x_663_, size_t v_x_664_, size_t v_x_665_, lean_object* v_x_666_){
_start:
{
if (lean_obj_tag(v_x_663_) == 0)
{
lean_object* v_es_667_; size_t v___x_668_; size_t v___x_669_; lean_object* v_j_670_; lean_object* v___x_671_; uint8_t v___x_672_; 
v_es_667_ = lean_ctor_get(v_x_663_, 0);
v___x_668_ = ((size_t)31ULL);
v___x_669_ = lean_usize_land(v_x_664_, v___x_668_);
v_j_670_ = lean_usize_to_nat(v___x_669_);
v___x_671_ = lean_array_get_size(v_es_667_);
v___x_672_ = lean_nat_dec_lt(v_j_670_, v___x_671_);
if (v___x_672_ == 0)
{
lean_dec(v_j_670_);
lean_dec(v_x_666_);
lean_dec_ref(v_v_662_);
return v_x_663_;
}
else
{
lean_object* v___x_674_; uint8_t v_isShared_675_; uint8_t v_isSharedCheck_740_; 
lean_inc_ref(v_es_667_);
v_isSharedCheck_740_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_740_ == 0)
{
lean_object* v_unused_741_; 
v_unused_741_ = lean_ctor_get(v_x_663_, 0);
lean_dec(v_unused_741_);
v___x_674_ = v_x_663_;
v_isShared_675_ = v_isSharedCheck_740_;
goto v_resetjp_673_;
}
else
{
lean_dec(v_x_663_);
v___x_674_ = lean_box(0);
v_isShared_675_ = v_isSharedCheck_740_;
goto v_resetjp_673_;
}
v_resetjp_673_:
{
lean_object* v_v_676_; lean_object* v___x_677_; lean_object* v_xs_x27_678_; lean_object* v___y_680_; 
v_v_676_ = lean_array_fget(v_es_667_, v_j_670_);
v___x_677_ = lean_box(0);
v_xs_x27_678_ = lean_array_fset(v_es_667_, v_j_670_, v___x_677_);
switch(lean_obj_tag(v_v_676_))
{
case 0:
{
lean_object* v_key_685_; lean_object* v_val_686_; uint8_t v___x_687_; 
v_key_685_ = lean_ctor_get(v_v_676_, 0);
v_val_686_ = lean_ctor_get(v_v_676_, 1);
v___x_687_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_666_, v_key_685_);
if (v___x_687_ == 0)
{
lean_object* v___x_688_; lean_object* v___x_689_; 
v___x_688_ = lean_box(0);
v___x_689_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_661_, v_v_662_, v___x_688_);
if (lean_obj_tag(v___x_689_) == 0)
{
lean_dec(v_x_666_);
v___y_680_ = v_v_676_;
goto v___jp_679_;
}
else
{
lean_object* v_val_690_; lean_object* v___x_692_; uint8_t v_isShared_693_; uint8_t v_isSharedCheck_698_; 
lean_inc(v_val_686_);
lean_inc(v_key_685_);
lean_dec_ref_known(v_v_676_, 2);
v_val_690_ = lean_ctor_get(v___x_689_, 0);
v_isSharedCheck_698_ = !lean_is_exclusive(v___x_689_);
if (v_isSharedCheck_698_ == 0)
{
v___x_692_ = v___x_689_;
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
else
{
lean_inc(v_val_690_);
lean_dec(v___x_689_);
v___x_692_ = lean_box(0);
v_isShared_693_ = v_isSharedCheck_698_;
goto v_resetjp_691_;
}
v_resetjp_691_:
{
lean_object* v___x_694_; lean_object* v___x_696_; 
v___x_694_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_685_, v_val_686_, v_x_666_, v_val_690_);
if (v_isShared_693_ == 0)
{
lean_ctor_set(v___x_692_, 0, v___x_694_);
v___x_696_ = v___x_692_;
goto v_reusejp_695_;
}
else
{
lean_object* v_reuseFailAlloc_697_; 
v_reuseFailAlloc_697_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_697_, 0, v___x_694_);
v___x_696_ = v_reuseFailAlloc_697_;
goto v_reusejp_695_;
}
v_reusejp_695_:
{
v___y_680_ = v___x_696_;
goto v___jp_679_;
}
}
}
}
else
{
lean_object* v___x_700_; uint8_t v_isShared_701_; uint8_t v_isSharedCheck_709_; 
lean_inc(v_val_686_);
v_isSharedCheck_709_ = !lean_is_exclusive(v_v_676_);
if (v_isSharedCheck_709_ == 0)
{
lean_object* v_unused_710_; lean_object* v_unused_711_; 
v_unused_710_ = lean_ctor_get(v_v_676_, 1);
lean_dec(v_unused_710_);
v_unused_711_ = lean_ctor_get(v_v_676_, 0);
lean_dec(v_unused_711_);
v___x_700_ = v_v_676_;
v_isShared_701_ = v_isSharedCheck_709_;
goto v_resetjp_699_;
}
else
{
lean_dec(v_v_676_);
v___x_700_ = lean_box(0);
v_isShared_701_ = v_isSharedCheck_709_;
goto v_resetjp_699_;
}
v_resetjp_699_:
{
lean_object* v___x_702_; lean_object* v___x_703_; 
v___x_702_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_702_, 0, v_val_686_);
v___x_703_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_661_, v_v_662_, v___x_702_);
if (lean_obj_tag(v___x_703_) == 0)
{
lean_object* v___x_704_; 
lean_del_object(v___x_700_);
lean_dec(v_x_666_);
v___x_704_ = lean_box(2);
v___y_680_ = v___x_704_;
goto v___jp_679_;
}
else
{
lean_object* v_val_705_; lean_object* v___x_707_; 
v_val_705_ = lean_ctor_get(v___x_703_, 0);
lean_inc(v_val_705_);
lean_dec_ref_known(v___x_703_, 1);
if (v_isShared_701_ == 0)
{
lean_ctor_set(v___x_700_, 1, v_val_705_);
lean_ctor_set(v___x_700_, 0, v_x_666_);
v___x_707_ = v___x_700_;
goto v_reusejp_706_;
}
else
{
lean_object* v_reuseFailAlloc_708_; 
v_reuseFailAlloc_708_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_708_, 0, v_x_666_);
lean_ctor_set(v_reuseFailAlloc_708_, 1, v_val_705_);
v___x_707_ = v_reuseFailAlloc_708_;
goto v_reusejp_706_;
}
v_reusejp_706_:
{
v___y_680_ = v___x_707_;
goto v___jp_679_;
}
}
}
}
}
case 1:
{
lean_object* v_node_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_735_; 
v_node_712_ = lean_ctor_get(v_v_676_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v_v_676_);
if (v_isSharedCheck_735_ == 0)
{
v___x_714_ = v_v_676_;
v_isShared_715_ = v_isSharedCheck_735_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_node_712_);
lean_dec(v_v_676_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_735_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
size_t v___x_716_; size_t v___x_717_; size_t v___x_718_; size_t v___x_719_; lean_object* v_newNode_720_; lean_object* v___x_721_; 
v___x_716_ = ((size_t)5ULL);
v___x_717_ = lean_usize_shift_right(v_x_664_, v___x_716_);
v___x_718_ = ((size_t)1ULL);
v___x_719_ = lean_usize_add(v_x_665_, v___x_718_);
v_newNode_720_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_661_, v_v_662_, v_node_712_, v___x_717_, v___x_719_, v_x_666_);
lean_inc_ref(v_newNode_720_);
v___x_721_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_720_);
if (lean_obj_tag(v___x_721_) == 0)
{
lean_object* v___x_723_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 0, v_newNode_720_);
v___x_723_ = v___x_714_;
goto v_reusejp_722_;
}
else
{
lean_object* v_reuseFailAlloc_724_; 
v_reuseFailAlloc_724_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_724_, 0, v_newNode_720_);
v___x_723_ = v_reuseFailAlloc_724_;
goto v_reusejp_722_;
}
v_reusejp_722_:
{
v___y_680_ = v___x_723_;
goto v___jp_679_;
}
}
else
{
lean_object* v_val_725_; lean_object* v_fst_726_; lean_object* v_snd_727_; lean_object* v___x_729_; uint8_t v_isShared_730_; uint8_t v_isSharedCheck_734_; 
lean_dec_ref(v_newNode_720_);
lean_del_object(v___x_714_);
v_val_725_ = lean_ctor_get(v___x_721_, 0);
lean_inc(v_val_725_);
lean_dec_ref_known(v___x_721_, 1);
v_fst_726_ = lean_ctor_get(v_val_725_, 0);
v_snd_727_ = lean_ctor_get(v_val_725_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_val_725_);
if (v_isSharedCheck_734_ == 0)
{
v___x_729_ = v_val_725_;
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
else
{
lean_inc(v_snd_727_);
lean_inc(v_fst_726_);
lean_dec(v_val_725_);
v___x_729_ = lean_box(0);
v_isShared_730_ = v_isSharedCheck_734_;
goto v_resetjp_728_;
}
v_resetjp_728_:
{
lean_object* v___x_732_; 
if (v_isShared_730_ == 0)
{
v___x_732_ = v___x_729_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v_fst_726_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_snd_727_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
v___y_680_ = v___x_732_;
goto v___jp_679_;
}
}
}
}
}
default: 
{
lean_object* v___x_736_; lean_object* v___x_737_; 
v___x_736_ = lean_box(0);
v___x_737_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_661_, v_v_662_, v___x_736_);
if (lean_obj_tag(v___x_737_) == 0)
{
lean_dec(v_x_666_);
v___y_680_ = v_v_676_;
goto v___jp_679_;
}
else
{
lean_object* v_val_738_; lean_object* v___x_739_; 
v_val_738_ = lean_ctor_get(v___x_737_, 0);
lean_inc(v_val_738_);
lean_dec_ref_known(v___x_737_, 1);
v___x_739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_739_, 0, v_x_666_);
lean_ctor_set(v___x_739_, 1, v_val_738_);
v___y_680_ = v___x_739_;
goto v___jp_679_;
}
}
}
v___jp_679_:
{
lean_object* v___x_681_; lean_object* v___x_683_; 
v___x_681_ = lean_array_fset(v_xs_x27_678_, v_j_670_, v___y_680_);
lean_dec(v_j_670_);
if (v_isShared_675_ == 0)
{
lean_ctor_set(v___x_674_, 0, v___x_681_);
v___x_683_ = v___x_674_;
goto v_reusejp_682_;
}
else
{
lean_object* v_reuseFailAlloc_684_; 
v_reuseFailAlloc_684_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_684_, 0, v___x_681_);
v___x_683_ = v_reuseFailAlloc_684_;
goto v_reusejp_682_;
}
v_reusejp_682_:
{
return v___x_683_;
}
}
}
}
}
else
{
lean_object* v_ks_742_; lean_object* v_vs_743_; lean_object* v___x_745_; uint8_t v_isShared_746_; uint8_t v_isSharedCheck_776_; 
v_ks_742_ = lean_ctor_get(v_x_663_, 0);
v_vs_743_ = lean_ctor_get(v_x_663_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_x_663_);
if (v_isSharedCheck_776_ == 0)
{
v___x_745_ = v_x_663_;
v_isShared_746_ = v_isSharedCheck_776_;
goto v_resetjp_744_;
}
else
{
lean_inc(v_vs_743_);
lean_inc(v_ks_742_);
lean_dec(v_x_663_);
v___x_745_ = lean_box(0);
v_isShared_746_ = v_isSharedCheck_776_;
goto v_resetjp_744_;
}
v_resetjp_744_:
{
lean_object* v___x_747_; 
v___x_747_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(v_ks_742_, v_x_666_);
if (lean_obj_tag(v___x_747_) == 0)
{
lean_object* v___x_749_; 
if (v_isShared_746_ == 0)
{
v___x_749_ = v___x_745_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_754_; 
v_reuseFailAlloc_754_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_754_, 0, v_ks_742_);
lean_ctor_set(v_reuseFailAlloc_754_, 1, v_vs_743_);
v___x_749_ = v_reuseFailAlloc_754_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
lean_object* v___x_750_; lean_object* v___x_751_; 
v___x_750_ = lean_box(0);
v___x_751_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_661_, v_v_662_, v___x_750_);
if (lean_obj_tag(v___x_751_) == 0)
{
lean_dec(v_x_666_);
return v___x_749_;
}
else
{
lean_object* v_val_752_; lean_object* v___x_753_; 
v_val_752_ = lean_ctor_get(v___x_751_, 0);
lean_inc(v_val_752_);
lean_dec_ref_known(v___x_751_, 1);
v___x_753_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v___x_749_, v_x_664_, v_x_665_, v_x_666_, v_val_752_);
return v___x_753_;
}
}
}
else
{
lean_object* v_val_755_; lean_object* v___x_757_; uint8_t v_isShared_758_; uint8_t v_isSharedCheck_775_; 
v_val_755_ = lean_ctor_get(v___x_747_, 0);
v_isSharedCheck_775_ = !lean_is_exclusive(v___x_747_);
if (v_isSharedCheck_775_ == 0)
{
v___x_757_ = v___x_747_;
v_isShared_758_ = v_isSharedCheck_775_;
goto v_resetjp_756_;
}
else
{
lean_inc(v_val_755_);
lean_dec(v___x_747_);
v___x_757_ = lean_box(0);
v_isShared_758_ = v_isSharedCheck_775_;
goto v_resetjp_756_;
}
v_resetjp_756_:
{
lean_object* v_v_x27_759_; lean_object* v_keys_760_; lean_object* v_vals_761_; lean_object* v___x_763_; 
v_v_x27_759_ = lean_array_fget(v_vs_743_, v_val_755_);
lean_inc(v_val_755_);
v_keys_760_ = l_Array_eraseIdx___redArg(v_ks_742_, v_val_755_);
v_vals_761_ = l_Array_eraseIdx___redArg(v_vs_743_, v_val_755_);
if (v_isShared_758_ == 0)
{
lean_ctor_set(v___x_757_, 0, v_v_x27_759_);
v___x_763_ = v___x_757_;
goto v_reusejp_762_;
}
else
{
lean_object* v_reuseFailAlloc_774_; 
v_reuseFailAlloc_774_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_774_, 0, v_v_x27_759_);
v___x_763_ = v_reuseFailAlloc_774_;
goto v_reusejp_762_;
}
v_reusejp_762_:
{
lean_object* v___x_764_; 
v___x_764_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_661_, v_v_662_, v___x_763_);
if (lean_obj_tag(v___x_764_) == 0)
{
lean_object* v___x_766_; 
lean_dec(v_x_666_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v_vals_761_);
lean_ctor_set(v___x_745_, 0, v_keys_760_);
v___x_766_ = v___x_745_;
goto v_reusejp_765_;
}
else
{
lean_object* v_reuseFailAlloc_767_; 
v_reuseFailAlloc_767_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_767_, 0, v_keys_760_);
lean_ctor_set(v_reuseFailAlloc_767_, 1, v_vals_761_);
v___x_766_ = v_reuseFailAlloc_767_;
goto v_reusejp_765_;
}
v_reusejp_765_:
{
return v___x_766_;
}
}
else
{
lean_object* v_val_768_; lean_object* v_keys_769_; lean_object* v_vals_770_; lean_object* v___x_772_; 
v_val_768_ = lean_ctor_get(v___x_764_, 0);
lean_inc(v_val_768_);
lean_dec_ref_known(v___x_764_, 1);
v_keys_769_ = lean_array_push(v_keys_760_, v_x_666_);
v_vals_770_ = lean_array_push(v_vals_761_, v_val_768_);
if (v_isShared_746_ == 0)
{
lean_ctor_set(v___x_745_, 1, v_vals_770_);
lean_ctor_set(v___x_745_, 0, v_keys_769_);
v___x_772_ = v___x_745_;
goto v_reusejp_771_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_keys_769_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_vals_770_);
v___x_772_ = v_reuseFailAlloc_773_;
goto v_reusejp_771_;
}
v_reusejp_771_:
{
return v___x_772_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___boxed(lean_object* v_keys_777_, lean_object* v_v_778_, lean_object* v_x_779_, lean_object* v_x_780_, lean_object* v_x_781_, lean_object* v_x_782_){
_start:
{
size_t v_x_2812__boxed_783_; size_t v_x_2813__boxed_784_; lean_object* v_res_785_; 
v_x_2812__boxed_783_ = lean_unbox_usize(v_x_780_);
lean_dec(v_x_780_);
v_x_2813__boxed_784_ = lean_unbox_usize(v_x_781_);
lean_dec(v_x_781_);
v_res_785_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_777_, v_v_778_, v_x_779_, v_x_2812__boxed_783_, v_x_2813__boxed_784_, v_x_782_);
lean_dec_ref(v_keys_777_);
return v_res_785_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; 
v___x_789_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2));
v___x_790_ = lean_unsigned_to_nat(23u);
v___x_791_ = lean_unsigned_to_nat(166u);
v___x_792_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1));
v___x_793_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0));
v___x_794_ = l_mkPanicMessageWithDecl(v___x_793_, v___x_792_, v___x_791_, v___x_790_, v___x_789_);
return v___x_794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(lean_object* v_d_795_, lean_object* v_keys_796_, lean_object* v_v_797_){
_start:
{
lean_object* v___x_798_; lean_object* v___x_799_; uint8_t v___x_800_; 
v___x_798_ = lean_array_get_size(v_keys_796_);
v___x_799_ = lean_unsigned_to_nat(0u);
v___x_800_ = lean_nat_dec_eq(v___x_798_, v___x_799_);
if (v___x_800_ == 0)
{
lean_object* v___x_801_; lean_object* v_k_802_; uint64_t v___x_803_; size_t v_h_804_; size_t v___x_805_; lean_object* v___x_806_; 
v___x_801_ = lean_box(0);
v_k_802_ = lean_array_get_borrowed(v___x_801_, v_keys_796_, v___x_799_);
v___x_803_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_802_);
v_h_804_ = lean_uint64_to_usize(v___x_803_);
v___x_805_ = ((size_t)1ULL);
lean_inc(v_k_802_);
v___x_806_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_796_, v_v_797_, v_d_795_, v_h_804_, v___x_805_, v_k_802_);
return v___x_806_;
}
else
{
lean_object* v___x_807_; lean_object* v___x_808_; 
lean_dec_ref(v_v_797_);
lean_dec_ref(v_d_795_);
v___x_807_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3);
v___x_808_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v___x_807_);
return v___x_808_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___boxed(lean_object* v_d_809_, lean_object* v_keys_810_, lean_object* v_v_811_){
_start:
{
lean_object* v_res_812_; 
v_res_812_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_d_809_, v_keys_810_, v_v_811_);
lean_dec_ref(v_keys_810_);
return v_res_812_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(lean_object* v_xs_813_, lean_object* v_v_814_, lean_object* v_i_815_){
_start:
{
lean_object* v___x_816_; uint8_t v___x_817_; 
v___x_816_ = lean_array_get_size(v_xs_813_);
v___x_817_ = lean_nat_dec_lt(v_i_815_, v___x_816_);
if (v___x_817_ == 0)
{
lean_object* v___x_818_; 
lean_dec(v_i_815_);
v___x_818_ = lean_box(0);
return v___x_818_;
}
else
{
lean_object* v___x_819_; uint8_t v___x_820_; 
v___x_819_ = lean_array_fget_borrowed(v_xs_813_, v_i_815_);
v___x_820_ = lean_name_eq(v___x_819_, v_v_814_);
if (v___x_820_ == 0)
{
lean_object* v___x_821_; lean_object* v___x_822_; 
v___x_821_ = lean_unsigned_to_nat(1u);
v___x_822_ = lean_nat_add(v_i_815_, v___x_821_);
lean_dec(v_i_815_);
v_i_815_ = v___x_822_;
goto _start;
}
else
{
lean_object* v___x_824_; 
v___x_824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_824_, 0, v_i_815_);
return v___x_824_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20___boxed(lean_object* v_xs_825_, lean_object* v_v_826_, lean_object* v_i_827_){
_start:
{
lean_object* v_res_828_; 
v_res_828_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(v_xs_825_, v_v_826_, v_i_827_);
lean_dec(v_v_826_);
lean_dec_ref(v_xs_825_);
return v_res_828_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(lean_object* v_xs_829_, lean_object* v_v_830_){
_start:
{
lean_object* v___x_831_; lean_object* v___x_832_; 
v___x_831_ = lean_unsigned_to_nat(0u);
v___x_832_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(v_xs_829_, v_v_830_, v___x_831_);
return v___x_832_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13___boxed(lean_object* v_xs_833_, lean_object* v_v_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(v_xs_833_, v_v_834_);
lean_dec(v_v_834_);
lean_dec_ref(v_xs_833_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(lean_object* v_x_836_, size_t v_x_837_, lean_object* v_x_838_){
_start:
{
if (lean_obj_tag(v_x_836_) == 0)
{
lean_object* v_es_839_; lean_object* v___x_840_; size_t v___x_841_; size_t v___x_842_; lean_object* v_j_843_; lean_object* v_entry_844_; 
v_es_839_ = lean_ctor_get(v_x_836_, 0);
v___x_840_ = lean_box(2);
v___x_841_ = ((size_t)31ULL);
v___x_842_ = lean_usize_land(v_x_837_, v___x_841_);
v_j_843_ = lean_usize_to_nat(v___x_842_);
v_entry_844_ = lean_array_get(v___x_840_, v_es_839_, v_j_843_);
switch(lean_obj_tag(v_entry_844_))
{
case 0:
{
lean_object* v_key_845_; uint8_t v___x_846_; 
v_key_845_ = lean_ctor_get(v_entry_844_, 0);
lean_inc(v_key_845_);
lean_dec_ref_known(v_entry_844_, 2);
v___x_846_ = lean_name_eq(v_x_838_, v_key_845_);
lean_dec(v_key_845_);
if (v___x_846_ == 0)
{
lean_dec(v_j_843_);
return v_x_836_;
}
else
{
lean_object* v___x_848_; uint8_t v_isShared_849_; uint8_t v_isSharedCheck_854_; 
lean_inc_ref(v_es_839_);
v_isSharedCheck_854_ = !lean_is_exclusive(v_x_836_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v_x_836_, 0);
lean_dec(v_unused_855_);
v___x_848_ = v_x_836_;
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
else
{
lean_dec(v_x_836_);
v___x_848_ = lean_box(0);
v_isShared_849_ = v_isSharedCheck_854_;
goto v_resetjp_847_;
}
v_resetjp_847_:
{
lean_object* v___x_850_; lean_object* v___x_852_; 
v___x_850_ = lean_array_set(v_es_839_, v_j_843_, v___x_840_);
lean_dec(v_j_843_);
if (v_isShared_849_ == 0)
{
lean_ctor_set(v___x_848_, 0, v___x_850_);
v___x_852_ = v___x_848_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v___x_850_);
v___x_852_ = v_reuseFailAlloc_853_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
return v___x_852_;
}
}
}
}
case 1:
{
lean_object* v___x_857_; uint8_t v_isShared_858_; uint8_t v_isSharedCheck_890_; 
lean_inc_ref(v_es_839_);
v_isSharedCheck_890_ = !lean_is_exclusive(v_x_836_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v_x_836_, 0);
lean_dec(v_unused_891_);
v___x_857_ = v_x_836_;
v_isShared_858_ = v_isSharedCheck_890_;
goto v_resetjp_856_;
}
else
{
lean_dec(v_x_836_);
v___x_857_ = lean_box(0);
v_isShared_858_ = v_isSharedCheck_890_;
goto v_resetjp_856_;
}
v_resetjp_856_:
{
lean_object* v_node_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_889_; 
v_node_859_ = lean_ctor_get(v_entry_844_, 0);
v_isSharedCheck_889_ = !lean_is_exclusive(v_entry_844_);
if (v_isSharedCheck_889_ == 0)
{
v___x_861_ = v_entry_844_;
v_isShared_862_ = v_isSharedCheck_889_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_node_859_);
lean_dec(v_entry_844_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_889_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
size_t v___x_863_; lean_object* v_entries_864_; size_t v___x_865_; lean_object* v_newNode_866_; lean_object* v___x_867_; 
v___x_863_ = ((size_t)5ULL);
v_entries_864_ = lean_array_set(v_es_839_, v_j_843_, v___x_840_);
v___x_865_ = lean_usize_shift_right(v_x_837_, v___x_863_);
v_newNode_866_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_node_859_, v___x_865_, v_x_838_);
lean_inc_ref(v_newNode_866_);
v___x_867_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_866_);
if (lean_obj_tag(v___x_867_) == 0)
{
lean_object* v___x_869_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v_newNode_866_);
v___x_869_ = v___x_861_;
goto v_reusejp_868_;
}
else
{
lean_object* v_reuseFailAlloc_874_; 
v_reuseFailAlloc_874_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_874_, 0, v_newNode_866_);
v___x_869_ = v_reuseFailAlloc_874_;
goto v_reusejp_868_;
}
v_reusejp_868_:
{
lean_object* v___x_870_; lean_object* v___x_872_; 
v___x_870_ = lean_array_set(v_entries_864_, v_j_843_, v___x_869_);
lean_dec(v_j_843_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_870_);
v___x_872_ = v___x_857_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v___x_870_);
v___x_872_ = v_reuseFailAlloc_873_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
return v___x_872_;
}
}
}
else
{
lean_object* v_val_875_; lean_object* v_fst_876_; lean_object* v_snd_877_; lean_object* v___x_879_; uint8_t v_isShared_880_; uint8_t v_isSharedCheck_888_; 
lean_dec_ref(v_newNode_866_);
lean_del_object(v___x_861_);
v_val_875_ = lean_ctor_get(v___x_867_, 0);
lean_inc(v_val_875_);
lean_dec_ref_known(v___x_867_, 1);
v_fst_876_ = lean_ctor_get(v_val_875_, 0);
v_snd_877_ = lean_ctor_get(v_val_875_, 1);
v_isSharedCheck_888_ = !lean_is_exclusive(v_val_875_);
if (v_isSharedCheck_888_ == 0)
{
v___x_879_ = v_val_875_;
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
else
{
lean_inc(v_snd_877_);
lean_inc(v_fst_876_);
lean_dec(v_val_875_);
v___x_879_ = lean_box(0);
v_isShared_880_ = v_isSharedCheck_888_;
goto v_resetjp_878_;
}
v_resetjp_878_:
{
lean_object* v___x_882_; 
if (v_isShared_880_ == 0)
{
v___x_882_ = v___x_879_;
goto v_reusejp_881_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v_fst_876_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_snd_877_);
v___x_882_ = v_reuseFailAlloc_887_;
goto v_reusejp_881_;
}
v_reusejp_881_:
{
lean_object* v___x_883_; lean_object* v___x_885_; 
v___x_883_ = lean_array_set(v_entries_864_, v_j_843_, v___x_882_);
lean_dec(v_j_843_);
if (v_isShared_858_ == 0)
{
lean_ctor_set(v___x_857_, 0, v___x_883_);
v___x_885_ = v___x_857_;
goto v_reusejp_884_;
}
else
{
lean_object* v_reuseFailAlloc_886_; 
v_reuseFailAlloc_886_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_886_, 0, v___x_883_);
v___x_885_ = v_reuseFailAlloc_886_;
goto v_reusejp_884_;
}
v_reusejp_884_:
{
return v___x_885_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_843_);
return v_x_836_;
}
}
}
else
{
lean_object* v_ks_892_; lean_object* v_vs_893_; lean_object* v___x_895_; uint8_t v_isShared_896_; uint8_t v_isSharedCheck_907_; 
v_ks_892_ = lean_ctor_get(v_x_836_, 0);
v_vs_893_ = lean_ctor_get(v_x_836_, 1);
v_isSharedCheck_907_ = !lean_is_exclusive(v_x_836_);
if (v_isSharedCheck_907_ == 0)
{
v___x_895_ = v_x_836_;
v_isShared_896_ = v_isSharedCheck_907_;
goto v_resetjp_894_;
}
else
{
lean_inc(v_vs_893_);
lean_inc(v_ks_892_);
lean_dec(v_x_836_);
v___x_895_ = lean_box(0);
v_isShared_896_ = v_isSharedCheck_907_;
goto v_resetjp_894_;
}
v_resetjp_894_:
{
lean_object* v___x_897_; 
v___x_897_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(v_ks_892_, v_x_838_);
if (lean_obj_tag(v___x_897_) == 0)
{
lean_object* v___x_899_; 
if (v_isShared_896_ == 0)
{
v___x_899_ = v___x_895_;
goto v_reusejp_898_;
}
else
{
lean_object* v_reuseFailAlloc_900_; 
v_reuseFailAlloc_900_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_900_, 0, v_ks_892_);
lean_ctor_set(v_reuseFailAlloc_900_, 1, v_vs_893_);
v___x_899_ = v_reuseFailAlloc_900_;
goto v_reusejp_898_;
}
v_reusejp_898_:
{
return v___x_899_;
}
}
else
{
lean_object* v_val_901_; lean_object* v_keys_x27_902_; lean_object* v_vals_x27_903_; lean_object* v___x_905_; 
v_val_901_ = lean_ctor_get(v___x_897_, 0);
lean_inc_n(v_val_901_, 2);
lean_dec_ref_known(v___x_897_, 1);
v_keys_x27_902_ = l_Array_eraseIdx___redArg(v_ks_892_, v_val_901_);
v_vals_x27_903_ = l_Array_eraseIdx___redArg(v_vs_893_, v_val_901_);
if (v_isShared_896_ == 0)
{
lean_ctor_set(v___x_895_, 1, v_vals_x27_903_);
lean_ctor_set(v___x_895_, 0, v_keys_x27_902_);
v___x_905_ = v___x_895_;
goto v_reusejp_904_;
}
else
{
lean_object* v_reuseFailAlloc_906_; 
v_reuseFailAlloc_906_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_906_, 0, v_keys_x27_902_);
lean_ctor_set(v_reuseFailAlloc_906_, 1, v_vals_x27_903_);
v___x_905_ = v_reuseFailAlloc_906_;
goto v_reusejp_904_;
}
v_reusejp_904_:
{
return v___x_905_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg___boxed(lean_object* v_x_908_, lean_object* v_x_909_, lean_object* v_x_910_){
_start:
{
size_t v_x_3093__boxed_911_; lean_object* v_res_912_; 
v_x_3093__boxed_911_ = lean_unbox_usize(v_x_909_);
lean_dec(v_x_909_);
v_res_912_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_908_, v_x_3093__boxed_911_, v_x_910_);
lean_dec(v_x_910_);
return v_res_912_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(lean_object* v_x_913_, lean_object* v_x_914_){
_start:
{
uint64_t v___y_916_; 
if (lean_obj_tag(v_x_914_) == 0)
{
uint64_t v___x_919_; 
v___x_919_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0);
v___y_916_ = v___x_919_;
goto v___jp_915_;
}
else
{
uint64_t v_hash_920_; 
v_hash_920_ = lean_ctor_get_uint64(v_x_914_, sizeof(void*)*2);
v___y_916_ = v_hash_920_;
goto v___jp_915_;
}
v___jp_915_:
{
size_t v_h_917_; lean_object* v___x_918_; 
v_h_917_ = lean_uint64_to_usize(v___y_916_);
v___x_918_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_913_, v_h_917_, v_x_914_);
return v___x_918_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg___boxed(lean_object* v_x_921_, lean_object* v_x_922_){
_start:
{
lean_object* v_res_923_; 
v_res_923_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_921_, v_x_922_);
lean_dec(v_x_922_);
return v_res_923_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object* v_d_924_, lean_object* v_e_925_){
_start:
{
lean_object* v_globalName_x3f_926_; 
v_globalName_x3f_926_ = lean_ctor_get(v_e_925_, 3);
if (lean_obj_tag(v_globalName_x3f_926_) == 0)
{
lean_object* v_keys_927_; lean_object* v_discrTree_928_; lean_object* v_instanceNames_929_; lean_object* v_erased_930_; lean_object* v___x_932_; uint8_t v_isShared_933_; uint8_t v_isSharedCheck_938_; 
v_keys_927_ = lean_ctor_get(v_e_925_, 0);
lean_inc_ref(v_keys_927_);
v_discrTree_928_ = lean_ctor_get(v_d_924_, 0);
v_instanceNames_929_ = lean_ctor_get(v_d_924_, 1);
v_erased_930_ = lean_ctor_get(v_d_924_, 2);
v_isSharedCheck_938_ = !lean_is_exclusive(v_d_924_);
if (v_isSharedCheck_938_ == 0)
{
v___x_932_ = v_d_924_;
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
else
{
lean_inc(v_erased_930_);
lean_inc(v_instanceNames_929_);
lean_inc(v_discrTree_928_);
lean_dec(v_d_924_);
v___x_932_ = lean_box(0);
v_isShared_933_ = v_isSharedCheck_938_;
goto v_resetjp_931_;
}
v_resetjp_931_:
{
lean_object* v___x_934_; lean_object* v___x_936_; 
v___x_934_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_928_, v_keys_927_, v_e_925_);
lean_dec_ref(v_keys_927_);
if (v_isShared_933_ == 0)
{
lean_ctor_set(v___x_932_, 0, v___x_934_);
v___x_936_ = v___x_932_;
goto v_reusejp_935_;
}
else
{
lean_object* v_reuseFailAlloc_937_; 
v_reuseFailAlloc_937_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_937_, 0, v___x_934_);
lean_ctor_set(v_reuseFailAlloc_937_, 1, v_instanceNames_929_);
lean_ctor_set(v_reuseFailAlloc_937_, 2, v_erased_930_);
v___x_936_ = v_reuseFailAlloc_937_;
goto v_reusejp_935_;
}
v_reusejp_935_:
{
return v___x_936_;
}
}
}
else
{
lean_object* v_keys_939_; lean_object* v_val_940_; lean_object* v_discrTree_941_; lean_object* v_instanceNames_942_; lean_object* v_erased_943_; lean_object* v___x_945_; uint8_t v_isShared_946_; uint8_t v_isSharedCheck_953_; 
v_keys_939_ = lean_ctor_get(v_e_925_, 0);
v_val_940_ = lean_ctor_get(v_globalName_x3f_926_, 0);
lean_inc(v_val_940_);
v_discrTree_941_ = lean_ctor_get(v_d_924_, 0);
v_instanceNames_942_ = lean_ctor_get(v_d_924_, 1);
v_erased_943_ = lean_ctor_get(v_d_924_, 2);
v_isSharedCheck_953_ = !lean_is_exclusive(v_d_924_);
if (v_isSharedCheck_953_ == 0)
{
v___x_945_ = v_d_924_;
v_isShared_946_ = v_isSharedCheck_953_;
goto v_resetjp_944_;
}
else
{
lean_inc(v_erased_943_);
lean_inc(v_instanceNames_942_);
lean_inc(v_discrTree_941_);
lean_dec(v_d_924_);
v___x_945_ = lean_box(0);
v_isShared_946_ = v_isSharedCheck_953_;
goto v_resetjp_944_;
}
v_resetjp_944_:
{
lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_951_; 
lean_inc_ref(v_e_925_);
v___x_947_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_941_, v_keys_939_, v_e_925_);
lean_inc(v_val_940_);
v___x_948_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_instanceNames_942_, v_val_940_, v_e_925_);
v___x_949_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_erased_943_, v_val_940_);
lean_dec(v_val_940_);
if (v_isShared_946_ == 0)
{
lean_ctor_set(v___x_945_, 2, v___x_949_);
lean_ctor_set(v___x_945_, 1, v___x_948_);
lean_ctor_set(v___x_945_, 0, v___x_947_);
v___x_951_ = v___x_945_;
goto v_reusejp_950_;
}
else
{
lean_object* v_reuseFailAlloc_952_; 
v_reuseFailAlloc_952_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_952_, 0, v___x_947_);
lean_ctor_set(v_reuseFailAlloc_952_, 1, v___x_948_);
lean_ctor_set(v_reuseFailAlloc_952_, 2, v___x_949_);
v___x_951_ = v_reuseFailAlloc_952_;
goto v_reusejp_950_;
}
v_reusejp_950_:
{
return v___x_951_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1(lean_object* v_00_u03b2_954_, lean_object* v_x_955_, lean_object* v_x_956_, lean_object* v_x_957_){
_start:
{
lean_object* v___x_958_; 
v___x_958_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_x_955_, v_x_956_, v_x_957_);
return v___x_958_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(lean_object* v_00_u03b2_959_, lean_object* v_x_960_, lean_object* v_x_961_){
_start:
{
lean_object* v___x_962_; 
v___x_962_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_960_, v_x_961_);
return v___x_962_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___boxed(lean_object* v_00_u03b2_963_, lean_object* v_x_964_, lean_object* v_x_965_){
_start:
{
lean_object* v_res_966_; 
v_res_966_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(v_00_u03b2_963_, v_x_964_, v_x_965_);
lean_dec(v_x_965_);
return v_res_966_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4(lean_object* v_00_u03b2_967_, lean_object* v_x_968_, size_t v_x_969_, size_t v_x_970_, lean_object* v_x_971_, lean_object* v_x_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_968_, v_x_969_, v_x_970_, v_x_971_, v_x_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___boxed(lean_object* v_00_u03b2_974_, lean_object* v_x_975_, lean_object* v_x_976_, lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v_x_979_){
_start:
{
size_t v_x_3300__boxed_980_; size_t v_x_3301__boxed_981_; lean_object* v_res_982_; 
v_x_3300__boxed_980_ = lean_unbox_usize(v_x_976_);
lean_dec(v_x_976_);
v_x_3301__boxed_981_ = lean_unbox_usize(v_x_977_);
lean_dec(v_x_977_);
v_res_982_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4(v_00_u03b2_974_, v_x_975_, v_x_3300__boxed_980_, v_x_3301__boxed_981_, v_x_978_, v_x_979_);
return v_res_982_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6(lean_object* v_00_u03b2_983_, lean_object* v_x_984_, size_t v_x_985_, lean_object* v_x_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_984_, v_x_985_, v_x_986_);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___boxed(lean_object* v_00_u03b2_988_, lean_object* v_x_989_, lean_object* v_x_990_, lean_object* v_x_991_){
_start:
{
size_t v_x_3317__boxed_992_; lean_object* v_res_993_; 
v_x_3317__boxed_992_ = lean_unbox_usize(v_x_990_);
lean_dec(v_x_990_);
v_res_993_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6(v_00_u03b2_988_, v_x_989_, v_x_3317__boxed_992_, v_x_991_);
lean_dec(v_x_991_);
return v_res_993_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_994_, lean_object* v_x_995_, size_t v_x_996_, size_t v_x_997_, lean_object* v_x_998_, lean_object* v_x_999_){
_start:
{
lean_object* v___x_1000_; 
v___x_1000_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_x_995_, v_x_996_, v_x_997_, v_x_998_, v_x_999_);
return v___x_1000_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_1001_, lean_object* v_x_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_){
_start:
{
size_t v_x_3328__boxed_1007_; size_t v_x_3329__boxed_1008_; lean_object* v_res_1009_; 
v_x_3328__boxed_1007_ = lean_unbox_usize(v_x_1003_);
lean_dec(v_x_1003_);
v_x_3329__boxed_1008_ = lean_unbox_usize(v_x_1004_);
lean_dec(v_x_1004_);
v_res_1009_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(v_00_u03b2_1001_, v_x_1002_, v_x_3328__boxed_1007_, v_x_3329__boxed_1008_, v_x_1005_, v_x_1006_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_1010_, lean_object* v_n_1011_, lean_object* v_k_1012_, lean_object* v_v_1013_){
_start:
{
lean_object* v___x_1014_; 
v___x_1014_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9___redArg(v_n_1011_, v_k_1012_, v_v_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_1015_, size_t v_depth_1016_, lean_object* v_keys_1017_, lean_object* v_vals_1018_, lean_object* v_heq_1019_, lean_object* v_i_1020_, lean_object* v_entries_1021_){
_start:
{
lean_object* v___x_1022_; 
v___x_1022_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_depth_1016_, v_keys_1017_, v_vals_1018_, v_i_1020_, v_entries_1021_);
return v___x_1022_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___boxed(lean_object* v_00_u03b2_1023_, lean_object* v_depth_1024_, lean_object* v_keys_1025_, lean_object* v_vals_1026_, lean_object* v_heq_1027_, lean_object* v_i_1028_, lean_object* v_entries_1029_){
_start:
{
size_t v_depth_boxed_1030_; lean_object* v_res_1031_; 
v_depth_boxed_1030_ = lean_unbox_usize(v_depth_1024_);
lean_dec(v_depth_1024_);
v_res_1031_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10(v_00_u03b2_1023_, v_depth_boxed_1030_, v_keys_1025_, v_vals_1026_, v_heq_1027_, v_i_1028_, v_entries_1029_);
lean_dec_ref(v_vals_1026_);
lean_dec_ref(v_keys_1025_);
return v_res_1031_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7(lean_object* v_x_1032_, lean_object* v_keys_1033_, lean_object* v_v_1034_, lean_object* v_k_1035_, lean_object* v_as_1036_, lean_object* v_k_1037_, lean_object* v_x_1038_, lean_object* v_x_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_){
_start:
{
lean_object* v___x_1042_; 
v___x_1042_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_1032_, v_keys_1033_, v_v_1034_, v_k_1035_, v_as_1036_, v_k_1037_, v_x_1038_, v_x_1039_);
return v___x_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_x_1043_, lean_object* v_keys_1044_, lean_object* v_v_1045_, lean_object* v_k_1046_, lean_object* v_as_1047_, lean_object* v_k_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_){
_start:
{
lean_object* v_res_1053_; 
v_res_1053_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7(v_x_1043_, v_keys_1044_, v_v_1045_, v_k_1046_, v_as_1047_, v_k_1048_, v_x_1049_, v_x_1050_, v_x_1051_, v_x_1052_);
lean_dec_ref(v_k_1048_);
lean_dec_ref(v_keys_1044_);
lean_dec(v_x_1043_);
return v_res_1053_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12(lean_object* v_00_u03b2_1054_, lean_object* v_n_1055_, lean_object* v_k_1056_, lean_object* v_v_1057_){
_start:
{
lean_object* v___x_1058_; 
v___x_1058_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(v_n_1055_, v_k_1056_, v_v_1057_);
return v___x_1058_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13(lean_object* v_00_u03b2_1059_, size_t v_depth_1060_, lean_object* v_keys_1061_, lean_object* v_vals_1062_, lean_object* v_heq_1063_, lean_object* v_i_1064_, lean_object* v_entries_1065_){
_start:
{
lean_object* v___x_1066_; 
v___x_1066_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(v_depth_1060_, v_keys_1061_, v_vals_1062_, v_i_1064_, v_entries_1065_);
return v___x_1066_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___boxed(lean_object* v_00_u03b2_1067_, lean_object* v_depth_1068_, lean_object* v_keys_1069_, lean_object* v_vals_1070_, lean_object* v_heq_1071_, lean_object* v_i_1072_, lean_object* v_entries_1073_){
_start:
{
size_t v_depth_boxed_1074_; lean_object* v_res_1075_; 
v_depth_boxed_1074_ = lean_unbox_usize(v_depth_1068_);
lean_dec(v_depth_1068_);
v_res_1075_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13(v_00_u03b2_1067_, v_depth_boxed_1074_, v_keys_1069_, v_vals_1070_, v_heq_1071_, v_i_1072_, v_entries_1073_);
lean_dec_ref(v_vals_1070_);
lean_dec_ref(v_keys_1069_);
return v_res_1075_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16(lean_object* v_00_u03b2_1076_, lean_object* v_x_1077_, lean_object* v_x_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_){
_start:
{
lean_object* v___x_1081_; 
v___x_1081_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16___redArg(v_x_1077_, v_x_1078_, v_x_1079_, v_x_1080_);
return v___x_1081_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1082_, lean_object* v_x_1083_, lean_object* v_x_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_){
_start:
{
lean_object* v___x_1087_; 
v___x_1087_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(v_x_1083_, v_x_1084_, v_x_1085_, v_x_1086_);
return v___x_1087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_eraseCore(lean_object* v_d_1088_, lean_object* v_declName_1089_){
_start:
{
lean_object* v_discrTree_1090_; lean_object* v_instanceNames_1091_; lean_object* v_erased_1092_; lean_object* v___x_1094_; uint8_t v_isShared_1095_; uint8_t v_isSharedCheck_1102_; 
v_discrTree_1090_ = lean_ctor_get(v_d_1088_, 0);
v_instanceNames_1091_ = lean_ctor_get(v_d_1088_, 1);
v_erased_1092_ = lean_ctor_get(v_d_1088_, 2);
v_isSharedCheck_1102_ = !lean_is_exclusive(v_d_1088_);
if (v_isSharedCheck_1102_ == 0)
{
v___x_1094_ = v_d_1088_;
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
else
{
lean_inc(v_erased_1092_);
lean_inc(v_instanceNames_1091_);
lean_inc(v_discrTree_1090_);
lean_dec(v_d_1088_);
v___x_1094_ = lean_box(0);
v_isShared_1095_ = v_isSharedCheck_1102_;
goto v_resetjp_1093_;
}
v_resetjp_1093_:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1100_; 
v___x_1096_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_instanceNames_1091_, v_declName_1089_);
v___x_1097_ = lean_box(0);
v___x_1098_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_erased_1092_, v_declName_1089_, v___x_1097_);
if (v_isShared_1095_ == 0)
{
lean_ctor_set(v___x_1094_, 2, v___x_1098_);
lean_ctor_set(v___x_1094_, 1, v___x_1096_);
v___x_1100_ = v___x_1094_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1101_; 
v_reuseFailAlloc_1101_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1101_, 0, v_discrTree_1090_);
lean_ctor_set(v_reuseFailAlloc_1101_, 1, v___x_1096_);
lean_ctor_set(v_reuseFailAlloc_1101_, 2, v___x_1098_);
v___x_1100_ = v_reuseFailAlloc_1101_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
return v___x_1100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__0(lean_object* v_d_1103_, lean_object* v_declName_1104_, lean_object* v_toPure_1105_, lean_object* v_____r_1106_){
_start:
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
v___x_1107_ = l_Lean_Meta_Instances_eraseCore(v_d_1103_, v_declName_1104_);
v___x_1108_ = lean_apply_2(v_toPure_1105_, lean_box(0), v___x_1107_);
return v___x_1108_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__1(lean_object* v___f_1109_, lean_object* v_____r_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_apply_1(v___f_1109_, v_____r_1110_);
return v___x_1111_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1115_; lean_object* v___x_1116_; 
v___x_1115_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__2));
v___x_1116_ = l_Lean_stringToMessageData(v___x_1115_);
return v___x_1116_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__5(void){
_start:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; 
v___x_1118_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__4));
v___x_1119_ = l_Lean_stringToMessageData(v___x_1118_);
return v___x_1119_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg(lean_object* v_inst_1120_, lean_object* v_inst_1121_, lean_object* v_d_1122_, lean_object* v_declName_1123_){
_start:
{
lean_object* v_toApplicative_1124_; lean_object* v_toBind_1125_; lean_object* v_toPure_1126_; lean_object* v_instanceNames_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___f_1130_; uint8_t v___x_1131_; 
v_toApplicative_1124_ = lean_ctor_get(v_inst_1120_, 0);
v_toBind_1125_ = lean_ctor_get(v_inst_1120_, 1);
lean_inc(v_toBind_1125_);
v_toPure_1126_ = lean_ctor_get(v_toApplicative_1124_, 1);
v_instanceNames_1127_ = lean_ctor_get(v_d_1122_, 1);
v___x_1128_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__0));
v___x_1129_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__1));
lean_inc(v_toPure_1126_);
lean_inc_n(v_declName_1123_, 2);
lean_inc_ref(v_d_1122_);
v___f_1130_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1130_, 0, v_d_1122_);
lean_closure_set(v___f_1130_, 1, v_declName_1123_);
lean_closure_set(v___f_1130_, 2, v_toPure_1126_);
lean_inc_ref(v_instanceNames_1127_);
v___x_1131_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1128_, v___x_1129_, v_instanceNames_1127_, v_declName_1123_);
if (v___x_1131_ == 0)
{
lean_object* v___f_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_dec_ref(v_d_1122_);
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1132_, 0, v___f_1130_);
v___x_1133_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_1134_ = l_Lean_MessageData_ofConstName(v_declName_1123_, v___x_1131_);
v___x_1135_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1135_, 0, v___x_1133_);
lean_ctor_set(v___x_1135_, 1, v___x_1134_);
v___x_1136_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = l_Lean_throwError___redArg(v_inst_1120_, v_inst_1121_, v___x_1137_);
v___x_1139_ = lean_apply_4(v_toBind_1125_, lean_box(0), lean_box(0), v___x_1138_, v___f_1132_);
return v___x_1139_;
}
else
{
lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_inc(v_toPure_1126_);
lean_dec_ref(v___f_1130_);
lean_dec(v_toBind_1125_);
lean_dec_ref(v_inst_1121_);
lean_dec_ref(v_inst_1120_);
v___x_1140_ = lean_box(0);
v___x_1141_ = l_Lean_Meta_Instances_erase___redArg___lam__0(v_d_1122_, v_declName_1123_, v_toPure_1126_, v___x_1140_);
return v___x_1141_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase(lean_object* v_m_1142_, lean_object* v_inst_1143_, lean_object* v_inst_1144_, lean_object* v_d_1145_, lean_object* v_declName_1146_){
_start:
{
lean_object* v___x_1147_; 
v___x_1147_ = l_Lean_Meta_Instances_erase___redArg(v_inst_1143_, v_inst_1144_, v_d_1145_, v_declName_1146_);
return v___x_1147_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(lean_object* v_x_1148_, lean_object* v_e_1149_){
_start:
{
lean_object* v_globalName_x3f_1154_; 
v_globalName_x3f_1154_ = lean_ctor_get(v_e_1149_, 3);
lean_inc(v_globalName_x3f_1154_);
if (lean_obj_tag(v_globalName_x3f_1154_) == 0)
{
goto v___jp_1150_;
}
else
{
lean_object* v_val_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1164_; 
v_val_1155_ = lean_ctor_get(v_globalName_x3f_1154_, 0);
v_isSharedCheck_1164_ = !lean_is_exclusive(v_globalName_x3f_1154_);
if (v_isSharedCheck_1164_ == 0)
{
v___x_1157_ = v_globalName_x3f_1154_;
v_isShared_1158_ = v_isSharedCheck_1164_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_val_1155_);
lean_dec(v_globalName_x3f_1154_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1164_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
uint8_t v___x_1159_; 
v___x_1159_ = l_Lean_isPrivateName(v_val_1155_);
lean_dec(v_val_1155_);
if (v___x_1159_ == 0)
{
lean_object* v___x_1161_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 0, v_e_1149_);
v___x_1161_ = v___x_1157_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1163_; 
v_reuseFailAlloc_1163_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1163_, 0, v_e_1149_);
v___x_1161_ = v_reuseFailAlloc_1163_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
lean_object* v___x_1162_; 
lean_inc_ref_n(v___x_1161_, 2);
v___x_1162_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1162_, 0, v___x_1161_);
lean_ctor_set(v___x_1162_, 1, v___x_1161_);
lean_ctor_set(v___x_1162_, 2, v___x_1161_);
return v___x_1162_;
}
}
else
{
lean_del_object(v___x_1157_);
goto v___jp_1150_;
}
}
}
v___jp_1150_:
{
lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1151_ = lean_box(0);
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v_e_1149_);
v___x_1153_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1153_, 0, v___x_1151_);
lean_ctor_set(v___x_1153_, 1, v___x_1151_);
lean_ctor_set(v___x_1153_, 2, v___x_1152_);
return v___x_1153_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v_x_1165_, lean_object* v_e_1166_){
_start:
{
lean_object* v_res_1167_; 
v_res_1167_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(v_x_1165_, v_e_1166_);
lean_dec_ref(v_x_1165_);
return v_res_1167_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(lean_object* v___y_1168_){
_start:
{
lean_inc_ref(v___y_1168_);
return v___y_1168_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v___y_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(v___y_1169_);
lean_dec_ref(v___y_1169_);
return v_res_1170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1179_; lean_object* v___f_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; 
v___f_1179_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___f_1180_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1181_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__4, &l_Lean_Meta_instInhabitedInstances_default___closed__4_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__4);
v___x_1182_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1183_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1184_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1184_, 0, v___x_1183_);
lean_ctor_set(v___x_1184_, 1, v___x_1182_);
lean_ctor_set(v___x_1184_, 2, v___x_1181_);
lean_ctor_set(v___x_1184_, 3, v___f_1180_);
lean_ctor_set(v___x_1184_, 4, v___f_1179_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___x_1186_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_);
v___x_1187_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1186_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v_a_1188_){
_start:
{
lean_object* v_res_1189_; 
v_res_1189_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_();
return v_res_1189_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object* v_k_1190_, uint8_t v_allowLevelAssignments_1191_, lean_object* v___y_1192_, lean_object* v___y_1193_, lean_object* v___y_1194_, lean_object* v___y_1195_){
_start:
{
lean_object* v___x_1197_; 
v___x_1197_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1191_, v_k_1190_, v___y_1192_, v___y_1193_, v___y_1194_, v___y_1195_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v_a_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1205_; 
v_a_1198_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1205_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1205_ == 0)
{
v___x_1200_ = v___x_1197_;
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_a_1198_);
lean_dec(v___x_1197_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1205_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v___x_1203_; 
if (v_isShared_1201_ == 0)
{
v___x_1203_ = v___x_1200_;
goto v_reusejp_1202_;
}
else
{
lean_object* v_reuseFailAlloc_1204_; 
v_reuseFailAlloc_1204_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1204_, 0, v_a_1198_);
v___x_1203_ = v_reuseFailAlloc_1204_;
goto v_reusejp_1202_;
}
v_reusejp_1202_:
{
return v___x_1203_;
}
}
}
else
{
lean_object* v_a_1206_; lean_object* v___x_1208_; uint8_t v_isShared_1209_; uint8_t v_isSharedCheck_1213_; 
v_a_1206_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1213_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1213_ == 0)
{
v___x_1208_ = v___x_1197_;
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
else
{
lean_inc(v_a_1206_);
lean_dec(v___x_1197_);
v___x_1208_ = lean_box(0);
v_isShared_1209_ = v_isSharedCheck_1213_;
goto v_resetjp_1207_;
}
v_resetjp_1207_:
{
lean_object* v___x_1211_; 
if (v_isShared_1209_ == 0)
{
v___x_1211_ = v___x_1208_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1212_; 
v_reuseFailAlloc_1212_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1212_, 0, v_a_1206_);
v___x_1211_ = v_reuseFailAlloc_1212_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
return v___x_1211_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object* v_k_1214_, lean_object* v_allowLevelAssignments_1215_, lean_object* v___y_1216_, lean_object* v___y_1217_, lean_object* v___y_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1221_; lean_object* v_res_1222_; 
v_allowLevelAssignments_boxed_1221_ = lean_unbox(v_allowLevelAssignments_1215_);
v_res_1222_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1214_, v_allowLevelAssignments_boxed_1221_, v___y_1216_, v___y_1217_, v___y_1218_, v___y_1219_);
lean_dec(v___y_1219_);
lean_dec_ref(v___y_1218_);
lean_dec(v___y_1217_);
lean_dec_ref(v___y_1216_);
return v_res_1222_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object* v_00_u03b1_1223_, lean_object* v_k_1224_, uint8_t v_allowLevelAssignments_1225_, lean_object* v___y_1226_, lean_object* v___y_1227_, lean_object* v___y_1228_, lean_object* v___y_1229_){
_start:
{
lean_object* v___x_1231_; 
v___x_1231_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1224_, v_allowLevelAssignments_1225_, v___y_1226_, v___y_1227_, v___y_1228_, v___y_1229_);
return v___x_1231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object* v_00_u03b1_1232_, lean_object* v_k_1233_, lean_object* v_allowLevelAssignments_1234_, lean_object* v___y_1235_, lean_object* v___y_1236_, lean_object* v___y_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1240_; lean_object* v_res_1241_; 
v_allowLevelAssignments_boxed_1240_ = lean_unbox(v_allowLevelAssignments_1234_);
v_res_1241_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(v_00_u03b1_1232_, v_k_1233_, v_allowLevelAssignments_boxed_1240_, v___y_1235_, v___y_1236_, v___y_1237_, v___y_1238_);
lean_dec(v___y_1238_);
lean_dec_ref(v___y_1237_);
lean_dec(v___y_1236_);
lean_dec_ref(v___y_1235_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1242_, lean_object* v___x_1243_, uint8_t v___x_1244_, lean_object* v___y_1245_, lean_object* v___y_1246_, lean_object* v___y_1247_, lean_object* v___y_1248_){
_start:
{
lean_object* v___x_1250_; 
v___x_1250_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1242_, v___x_1243_, v___x_1244_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
if (lean_obj_tag(v___x_1250_) == 0)
{
lean_object* v_a_1251_; lean_object* v_snd_1252_; lean_object* v_snd_1253_; uint8_t v___x_1254_; lean_object* v___x_1255_; 
v_a_1251_ = lean_ctor_get(v___x_1250_, 0);
lean_inc(v_a_1251_);
lean_dec_ref_known(v___x_1250_, 1);
v_snd_1252_ = lean_ctor_get(v_a_1251_, 1);
lean_inc(v_snd_1252_);
lean_dec(v_a_1251_);
v_snd_1253_ = lean_ctor_get(v_snd_1252_, 1);
lean_inc(v_snd_1253_);
lean_dec(v_snd_1252_);
v___x_1254_ = 0;
v___x_1255_ = l_Lean_Meta_DiscrTree_mkPath(v_snd_1253_, v___x_1254_, v___y_1245_, v___y_1246_, v___y_1247_, v___y_1248_);
return v___x_1255_;
}
else
{
lean_object* v_a_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1263_; 
v_a_1256_ = lean_ctor_get(v___x_1250_, 0);
v_isSharedCheck_1263_ = !lean_is_exclusive(v___x_1250_);
if (v_isSharedCheck_1263_ == 0)
{
v___x_1258_ = v___x_1250_;
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_a_1256_);
lean_dec(v___x_1250_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1263_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1261_; 
if (v_isShared_1259_ == 0)
{
v___x_1261_ = v___x_1258_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1262_; 
v_reuseFailAlloc_1262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1262_, 0, v_a_1256_);
v___x_1261_ = v_reuseFailAlloc_1262_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
return v___x_1261_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object* v_a_1264_, lean_object* v___x_1265_, lean_object* v___x_1266_, lean_object* v___y_1267_, lean_object* v___y_1268_, lean_object* v___y_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_){
_start:
{
uint8_t v___x_497__boxed_1272_; lean_object* v_res_1273_; 
v___x_497__boxed_1272_ = lean_unbox(v___x_1266_);
v_res_1273_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1264_, v___x_1265_, v___x_497__boxed_1272_, v___y_1267_, v___y_1268_, v___y_1269_, v___y_1270_);
lean_dec(v___y_1270_);
lean_dec_ref(v___y_1269_);
lean_dec(v___y_1268_);
lean_dec_ref(v___y_1267_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object* v_e_1274_, lean_object* v_a_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_, lean_object* v_a_1278_){
_start:
{
lean_object* v___x_1280_; 
lean_inc(v_a_1278_);
lean_inc_ref(v_a_1277_);
lean_inc(v_a_1276_);
lean_inc_ref(v_a_1275_);
v___x_1280_ = lean_infer_type(v_e_1274_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
if (lean_obj_tag(v___x_1280_) == 0)
{
lean_object* v_a_1281_; lean_object* v___x_1282_; uint8_t v___x_1283_; lean_object* v___x_1284_; lean_object* v___f_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; 
v_a_1281_ = lean_ctor_get(v___x_1280_, 0);
lean_inc(v_a_1281_);
lean_dec_ref_known(v___x_1280_, 1);
v___x_1282_ = lean_box(0);
v___x_1283_ = 0;
v___x_1284_ = lean_box(v___x_1283_);
v___f_1285_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1285_, 0, v_a_1281_);
lean_closure_set(v___f_1285_, 1, v___x_1282_);
lean_closure_set(v___f_1285_, 2, v___x_1284_);
v___x_1286_ = 0;
v___x_1287_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v___f_1285_, v___x_1286_, v_a_1275_, v_a_1276_, v_a_1277_, v_a_1278_);
return v___x_1287_;
}
else
{
lean_object* v_a_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1295_; 
v_a_1288_ = lean_ctor_get(v___x_1280_, 0);
v_isSharedCheck_1295_ = !lean_is_exclusive(v___x_1280_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1290_ = v___x_1280_;
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_a_1288_);
lean_dec(v___x_1280_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1295_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1293_; 
if (v_isShared_1291_ == 0)
{
v___x_1293_ = v___x_1290_;
goto v_reusejp_1292_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_a_1288_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object* v_e_1296_, lean_object* v_a_1297_, lean_object* v_a_1298_, lean_object* v_a_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_e_1296_, v_a_1297_, v_a_1298_, v_a_1299_, v_a_1300_);
lean_dec(v_a_1300_);
lean_dec_ref(v_a_1299_);
lean_dec(v_a_1298_);
lean_dec_ref(v_a_1297_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1303_, lean_object* v_b_1304_, lean_object* v_c_1305_, lean_object* v___y_1306_, lean_object* v___y_1307_, lean_object* v___y_1308_, lean_object* v___y_1309_){
_start:
{
lean_object* v___x_1311_; 
lean_inc(v___y_1309_);
lean_inc_ref(v___y_1308_);
lean_inc(v___y_1307_);
lean_inc_ref(v___y_1306_);
v___x_1311_ = lean_apply_7(v_k_1303_, v_b_1304_, v_c_1305_, v___y_1306_, v___y_1307_, v___y_1308_, v___y_1309_, lean_box(0));
return v___x_1311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1312_, lean_object* v_b_1313_, lean_object* v_c_1314_, lean_object* v___y_1315_, lean_object* v___y_1316_, lean_object* v___y_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_){
_start:
{
lean_object* v_res_1320_; 
v_res_1320_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1312_, v_b_1313_, v_c_1314_, v___y_1315_, v___y_1316_, v___y_1317_, v___y_1318_);
lean_dec(v___y_1318_);
lean_dec_ref(v___y_1317_);
lean_dec(v___y_1316_);
lean_dec_ref(v___y_1315_);
return v_res_1320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object* v_type_1321_, lean_object* v_k_1322_, uint8_t v_cleanupAnnotations_1323_, uint8_t v_whnfType_1324_, lean_object* v___y_1325_, lean_object* v___y_1326_, lean_object* v___y_1327_, lean_object* v___y_1328_){
_start:
{
lean_object* v___f_1330_; lean_object* v___x_1331_; 
v___f_1330_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1330_, 0, v_k_1322_);
v___x_1331_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1321_, v___f_1330_, v_cleanupAnnotations_1323_, v_whnfType_1324_, v___y_1325_, v___y_1326_, v___y_1327_, v___y_1328_);
if (lean_obj_tag(v___x_1331_) == 0)
{
lean_object* v_a_1332_; lean_object* v___x_1334_; uint8_t v_isShared_1335_; uint8_t v_isSharedCheck_1339_; 
v_a_1332_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1339_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1339_ == 0)
{
v___x_1334_ = v___x_1331_;
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
else
{
lean_inc(v_a_1332_);
lean_dec(v___x_1331_);
v___x_1334_ = lean_box(0);
v_isShared_1335_ = v_isSharedCheck_1339_;
goto v_resetjp_1333_;
}
v_resetjp_1333_:
{
lean_object* v___x_1337_; 
if (v_isShared_1335_ == 0)
{
v___x_1337_ = v___x_1334_;
goto v_reusejp_1336_;
}
else
{
lean_object* v_reuseFailAlloc_1338_; 
v_reuseFailAlloc_1338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1338_, 0, v_a_1332_);
v___x_1337_ = v_reuseFailAlloc_1338_;
goto v_reusejp_1336_;
}
v_reusejp_1336_:
{
return v___x_1337_;
}
}
}
else
{
lean_object* v_a_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1347_; 
v_a_1340_ = lean_ctor_get(v___x_1331_, 0);
v_isSharedCheck_1347_ = !lean_is_exclusive(v___x_1331_);
if (v_isSharedCheck_1347_ == 0)
{
v___x_1342_ = v___x_1331_;
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_a_1340_);
lean_dec(v___x_1331_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1347_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v___x_1345_; 
if (v_isShared_1343_ == 0)
{
v___x_1345_ = v___x_1342_;
goto v_reusejp_1344_;
}
else
{
lean_object* v_reuseFailAlloc_1346_; 
v_reuseFailAlloc_1346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1346_, 0, v_a_1340_);
v___x_1345_ = v_reuseFailAlloc_1346_;
goto v_reusejp_1344_;
}
v_reusejp_1344_:
{
return v___x_1345_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object* v_type_1348_, lean_object* v_k_1349_, lean_object* v_cleanupAnnotations_1350_, lean_object* v_whnfType_1351_, lean_object* v___y_1352_, lean_object* v___y_1353_, lean_object* v___y_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1357_; uint8_t v_whnfType_boxed_1358_; lean_object* v_res_1359_; 
v_cleanupAnnotations_boxed_1357_ = lean_unbox(v_cleanupAnnotations_1350_);
v_whnfType_boxed_1358_ = lean_unbox(v_whnfType_1351_);
v_res_1359_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1348_, v_k_1349_, v_cleanupAnnotations_boxed_1357_, v_whnfType_boxed_1358_, v___y_1352_, v___y_1353_, v___y_1354_, v___y_1355_);
lean_dec(v___y_1355_);
lean_dec_ref(v___y_1354_);
lean_dec(v___y_1353_);
lean_dec_ref(v___y_1352_);
return v_res_1359_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object* v_00_u03b1_1360_, lean_object* v_type_1361_, lean_object* v_k_1362_, uint8_t v_cleanupAnnotations_1363_, uint8_t v_whnfType_1364_, lean_object* v___y_1365_, lean_object* v___y_1366_, lean_object* v___y_1367_, lean_object* v___y_1368_){
_start:
{
lean_object* v___x_1370_; 
v___x_1370_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1361_, v_k_1362_, v_cleanupAnnotations_1363_, v_whnfType_1364_, v___y_1365_, v___y_1366_, v___y_1367_, v___y_1368_);
return v___x_1370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object* v_00_u03b1_1371_, lean_object* v_type_1372_, lean_object* v_k_1373_, lean_object* v_cleanupAnnotations_1374_, lean_object* v_whnfType_1375_, lean_object* v___y_1376_, lean_object* v___y_1377_, lean_object* v___y_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1381_; uint8_t v_whnfType_boxed_1382_; lean_object* v_res_1383_; 
v_cleanupAnnotations_boxed_1381_ = lean_unbox(v_cleanupAnnotations_1374_);
v_whnfType_boxed_1382_ = lean_unbox(v_whnfType_1375_);
v_res_1383_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(v_00_u03b1_1371_, v_type_1372_, v_k_1373_, v_cleanupAnnotations_boxed_1381_, v_whnfType_boxed_1382_, v___y_1376_, v___y_1377_, v___y_1378_, v___y_1379_);
lean_dec(v___y_1379_);
lean_dec_ref(v___y_1378_);
lean_dec(v___y_1377_);
lean_dec_ref(v___y_1376_);
return v_res_1383_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object* v_as_1387_, size_t v_sz_1388_, size_t v_i_1389_, lean_object* v_b_1390_, lean_object* v___y_1391_, lean_object* v___y_1392_, lean_object* v___y_1393_, lean_object* v___y_1394_){
_start:
{
uint8_t v___x_1396_; 
v___x_1396_ = lean_usize_dec_lt(v_i_1389_, v_sz_1388_);
if (v___x_1396_ == 0)
{
lean_object* v___x_1397_; 
v___x_1397_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1397_, 0, v_b_1390_);
return v___x_1397_;
}
else
{
lean_object* v_fst_1398_; lean_object* v_snd_1399_; lean_object* v___x_1401_; uint8_t v_isShared_1402_; uint8_t v_isSharedCheck_1451_; 
v_fst_1398_ = lean_ctor_get(v_b_1390_, 0);
v_snd_1399_ = lean_ctor_get(v_b_1390_, 1);
v_isSharedCheck_1451_ = !lean_is_exclusive(v_b_1390_);
if (v_isSharedCheck_1451_ == 0)
{
v___x_1401_ = v_b_1390_;
v_isShared_1402_ = v_isSharedCheck_1451_;
goto v_resetjp_1400_;
}
else
{
lean_inc(v_snd_1399_);
lean_inc(v_fst_1398_);
lean_dec(v_b_1390_);
v___x_1401_ = lean_box(0);
v_isShared_1402_ = v_isSharedCheck_1451_;
goto v_resetjp_1400_;
}
v_resetjp_1400_:
{
lean_object* v_next_1408_; 
v_next_1408_ = lean_ctor_get(v_snd_1399_, 0);
lean_inc(v_next_1408_);
if (lean_obj_tag(v_next_1408_) == 0)
{
goto v___jp_1403_;
}
else
{
lean_object* v_upperBound_1409_; lean_object* v_val_1410_; lean_object* v___x_1412_; uint8_t v_isShared_1413_; uint8_t v_isSharedCheck_1450_; 
v_upperBound_1409_ = lean_ctor_get(v_snd_1399_, 1);
v_val_1410_ = lean_ctor_get(v_next_1408_, 0);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_next_1408_);
if (v_isSharedCheck_1450_ == 0)
{
v___x_1412_ = v_next_1408_;
v_isShared_1413_ = v_isSharedCheck_1450_;
goto v_resetjp_1411_;
}
else
{
lean_inc(v_val_1410_);
lean_dec(v_next_1408_);
v___x_1412_ = lean_box(0);
v_isShared_1413_ = v_isSharedCheck_1450_;
goto v_resetjp_1411_;
}
v_resetjp_1411_:
{
uint8_t v___x_1414_; 
v___x_1414_ = lean_nat_dec_lt(v_val_1410_, v_upperBound_1409_);
if (v___x_1414_ == 0)
{
lean_del_object(v___x_1412_);
lean_dec(v_val_1410_);
goto v___jp_1403_;
}
else
{
lean_object* v___x_1416_; uint8_t v_isShared_1417_; uint8_t v_isSharedCheck_1447_; 
lean_inc(v_upperBound_1409_);
lean_del_object(v___x_1401_);
v_isSharedCheck_1447_ = !lean_is_exclusive(v_snd_1399_);
if (v_isSharedCheck_1447_ == 0)
{
lean_object* v_unused_1448_; lean_object* v_unused_1449_; 
v_unused_1448_ = lean_ctor_get(v_snd_1399_, 1);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_snd_1399_, 0);
lean_dec(v_unused_1449_);
v___x_1416_ = v_snd_1399_;
v_isShared_1417_ = v_isSharedCheck_1447_;
goto v_resetjp_1415_;
}
else
{
lean_dec(v_snd_1399_);
v___x_1416_ = lean_box(0);
v_isShared_1417_ = v_isSharedCheck_1447_;
goto v_resetjp_1415_;
}
v_resetjp_1415_:
{
lean_object* v_a_1418_; lean_object* v___x_1419_; 
v_a_1418_ = lean_array_uget_borrowed(v_as_1387_, v_i_1389_);
lean_inc(v___y_1394_);
lean_inc_ref(v___y_1393_);
lean_inc(v___y_1392_);
lean_inc_ref(v___y_1391_);
lean_inc(v_a_1418_);
v___x_1419_ = lean_infer_type(v_a_1418_, v___y_1391_, v___y_1392_, v___y_1393_, v___y_1394_);
if (lean_obj_tag(v___x_1419_) == 0)
{
lean_object* v_a_1420_; lean_object* v_a_1422_; lean_object* v___x_1426_; lean_object* v___x_1427_; lean_object* v___x_1429_; 
v_a_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_a_1420_);
lean_dec_ref_known(v___x_1419_, 1);
v___x_1426_ = lean_unsigned_to_nat(1u);
v___x_1427_ = lean_nat_add(v_val_1410_, v___x_1426_);
if (v_isShared_1413_ == 0)
{
lean_ctor_set(v___x_1412_, 0, v___x_1427_);
v___x_1429_ = v___x_1412_;
goto v_reusejp_1428_;
}
else
{
lean_object* v_reuseFailAlloc_1438_; 
v_reuseFailAlloc_1438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1438_, 0, v___x_1427_);
v___x_1429_ = v_reuseFailAlloc_1438_;
goto v_reusejp_1428_;
}
v___jp_1421_:
{
size_t v___x_1423_; size_t v___x_1424_; 
v___x_1423_ = ((size_t)1ULL);
v___x_1424_ = lean_usize_add(v_i_1389_, v___x_1423_);
v_i_1389_ = v___x_1424_;
v_b_1390_ = v_a_1422_;
goto _start;
}
v_reusejp_1428_:
{
lean_object* v___x_1431_; 
if (v_isShared_1417_ == 0)
{
lean_ctor_set(v___x_1416_, 0, v___x_1429_);
v___x_1431_ = v___x_1416_;
goto v_reusejp_1430_;
}
else
{
lean_object* v_reuseFailAlloc_1437_; 
v_reuseFailAlloc_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1437_, 0, v___x_1429_);
lean_ctor_set(v_reuseFailAlloc_1437_, 1, v_upperBound_1409_);
v___x_1431_ = v_reuseFailAlloc_1437_;
goto v_reusejp_1430_;
}
v_reusejp_1430_:
{
lean_object* v___x_1432_; uint8_t v___x_1433_; 
v___x_1432_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1));
v___x_1433_ = l_Lean_Expr_isAppOf(v_a_1420_, v___x_1432_);
lean_dec(v_a_1420_);
if (v___x_1433_ == 0)
{
lean_object* v___x_1434_; 
lean_dec(v_val_1410_);
v___x_1434_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1434_, 0, v_fst_1398_);
lean_ctor_set(v___x_1434_, 1, v___x_1431_);
v_a_1422_ = v___x_1434_;
goto v___jp_1421_;
}
else
{
lean_object* v___x_1435_; lean_object* v___x_1436_; 
v___x_1435_ = lean_array_push(v_fst_1398_, v_val_1410_);
v___x_1436_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
lean_ctor_set(v___x_1436_, 1, v___x_1431_);
v_a_1422_ = v___x_1436_;
goto v___jp_1421_;
}
}
}
}
else
{
lean_object* v_a_1439_; lean_object* v___x_1441_; uint8_t v_isShared_1442_; uint8_t v_isSharedCheck_1446_; 
lean_del_object(v___x_1416_);
lean_del_object(v___x_1412_);
lean_dec(v_val_1410_);
lean_dec(v_upperBound_1409_);
lean_dec(v_fst_1398_);
v_a_1439_ = lean_ctor_get(v___x_1419_, 0);
v_isSharedCheck_1446_ = !lean_is_exclusive(v___x_1419_);
if (v_isSharedCheck_1446_ == 0)
{
v___x_1441_ = v___x_1419_;
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
else
{
lean_inc(v_a_1439_);
lean_dec(v___x_1419_);
v___x_1441_ = lean_box(0);
v_isShared_1442_ = v_isSharedCheck_1446_;
goto v_resetjp_1440_;
}
v_resetjp_1440_:
{
lean_object* v___x_1444_; 
if (v_isShared_1442_ == 0)
{
v___x_1444_ = v___x_1441_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_a_1439_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
}
}
}
v___jp_1403_:
{
lean_object* v___x_1405_; 
if (v_isShared_1402_ == 0)
{
v___x_1405_ = v___x_1401_;
goto v_reusejp_1404_;
}
else
{
lean_object* v_reuseFailAlloc_1407_; 
v_reuseFailAlloc_1407_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1407_, 0, v_fst_1398_);
lean_ctor_set(v_reuseFailAlloc_1407_, 1, v_snd_1399_);
v___x_1405_ = v_reuseFailAlloc_1407_;
goto v_reusejp_1404_;
}
v_reusejp_1404_:
{
lean_object* v___x_1406_; 
v___x_1406_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1406_, 0, v___x_1405_);
return v___x_1406_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object* v_as_1452_, lean_object* v_sz_1453_, lean_object* v_i_1454_, lean_object* v_b_1455_, lean_object* v___y_1456_, lean_object* v___y_1457_, lean_object* v___y_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_){
_start:
{
size_t v_sz_boxed_1461_; size_t v_i_boxed_1462_; lean_object* v_res_1463_; 
v_sz_boxed_1461_ = lean_unbox_usize(v_sz_1453_);
lean_dec(v_sz_1453_);
v_i_boxed_1462_ = lean_unbox_usize(v_i_1454_);
lean_dec(v_i_1454_);
v_res_1463_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_as_1452_, v_sz_boxed_1461_, v_i_boxed_1462_, v_b_1455_, v___y_1456_, v___y_1457_, v___y_1458_, v___y_1459_);
lean_dec(v___y_1459_);
lean_dec_ref(v___y_1458_);
lean_dec(v___y_1457_);
lean_dec_ref(v___y_1456_);
lean_dec_ref(v_as_1452_);
return v_res_1463_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object* v_declName_1468_, lean_object* v_args_1469_, lean_object* v_x_1470_, lean_object* v___y_1471_, lean_object* v___y_1472_, lean_object* v___y_1473_, lean_object* v___y_1474_){
_start:
{
lean_object* v___x_1476_; lean_object* v___y_1478_; lean_object* v_env_1503_; lean_object* v___x_1504_; 
v___x_1476_ = lean_st_ref_get(v___y_1474_);
v_env_1503_ = lean_ctor_get(v___x_1476_, 0);
lean_inc_ref(v_env_1503_);
lean_dec(v___x_1476_);
v___x_1504_ = l_Lean_getOutParamPositions_x3f(v_env_1503_, v_declName_1468_);
if (lean_obj_tag(v___x_1504_) == 0)
{
lean_object* v___x_1505_; 
v___x_1505_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___y_1478_ = v___x_1505_;
goto v___jp_1477_;
}
else
{
lean_object* v_val_1506_; 
v_val_1506_ = lean_ctor_get(v___x_1504_, 0);
lean_inc(v_val_1506_);
lean_dec_ref_known(v___x_1504_, 1);
v___y_1478_ = v_val_1506_;
goto v___jp_1477_;
}
v___jp_1477_:
{
lean_object* v___x_1479_; lean_object* v___x_1480_; lean_object* v___x_1481_; lean_object* v___x_1482_; size_t v_sz_1483_; size_t v___x_1484_; lean_object* v___x_1485_; 
v___x_1479_ = lean_array_get_size(v_args_1469_);
v___x_1480_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_1481_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1481_, 0, v___x_1480_);
lean_ctor_set(v___x_1481_, 1, v___x_1479_);
v___x_1482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1482_, 0, v___y_1478_);
lean_ctor_set(v___x_1482_, 1, v___x_1481_);
v_sz_1483_ = lean_array_size(v_args_1469_);
v___x_1484_ = ((size_t)0ULL);
v___x_1485_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_args_1469_, v_sz_1483_, v___x_1484_, v___x_1482_, v___y_1471_, v___y_1472_, v___y_1473_, v___y_1474_);
if (lean_obj_tag(v___x_1485_) == 0)
{
lean_object* v_a_1486_; lean_object* v___x_1488_; uint8_t v_isShared_1489_; uint8_t v_isSharedCheck_1494_; 
v_a_1486_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1494_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1494_ == 0)
{
v___x_1488_ = v___x_1485_;
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
else
{
lean_inc(v_a_1486_);
lean_dec(v___x_1485_);
v___x_1488_ = lean_box(0);
v_isShared_1489_ = v_isSharedCheck_1494_;
goto v_resetjp_1487_;
}
v_resetjp_1487_:
{
lean_object* v_fst_1490_; lean_object* v___x_1492_; 
v_fst_1490_ = lean_ctor_get(v_a_1486_, 0);
lean_inc(v_fst_1490_);
lean_dec(v_a_1486_);
if (v_isShared_1489_ == 0)
{
lean_ctor_set(v___x_1488_, 0, v_fst_1490_);
v___x_1492_ = v___x_1488_;
goto v_reusejp_1491_;
}
else
{
lean_object* v_reuseFailAlloc_1493_; 
v_reuseFailAlloc_1493_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1493_, 0, v_fst_1490_);
v___x_1492_ = v_reuseFailAlloc_1493_;
goto v_reusejp_1491_;
}
v_reusejp_1491_:
{
return v___x_1492_;
}
}
}
else
{
lean_object* v_a_1495_; lean_object* v___x_1497_; uint8_t v_isShared_1498_; uint8_t v_isSharedCheck_1502_; 
v_a_1495_ = lean_ctor_get(v___x_1485_, 0);
v_isSharedCheck_1502_ = !lean_is_exclusive(v___x_1485_);
if (v_isSharedCheck_1502_ == 0)
{
v___x_1497_ = v___x_1485_;
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
else
{
lean_inc(v_a_1495_);
lean_dec(v___x_1485_);
v___x_1497_ = lean_box(0);
v_isShared_1498_ = v_isSharedCheck_1502_;
goto v_resetjp_1496_;
}
v_resetjp_1496_:
{
lean_object* v___x_1500_; 
if (v_isShared_1498_ == 0)
{
v___x_1500_ = v___x_1497_;
goto v_reusejp_1499_;
}
else
{
lean_object* v_reuseFailAlloc_1501_; 
v_reuseFailAlloc_1501_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1501_, 0, v_a_1495_);
v___x_1500_ = v_reuseFailAlloc_1501_;
goto v_reusejp_1499_;
}
v_reusejp_1499_:
{
return v___x_1500_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object* v_declName_1507_, lean_object* v_args_1508_, lean_object* v_x_1509_, lean_object* v___y_1510_, lean_object* v___y_1511_, lean_object* v___y_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_){
_start:
{
lean_object* v_res_1515_; 
v_res_1515_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(v_declName_1507_, v_args_1508_, v_x_1509_, v___y_1510_, v___y_1511_, v___y_1512_, v___y_1513_);
lean_dec(v___y_1513_);
lean_dec_ref(v___y_1512_);
lean_dec(v___y_1511_);
lean_dec_ref(v___y_1510_);
lean_dec_ref(v_x_1509_);
lean_dec_ref(v_args_1508_);
lean_dec(v_declName_1507_);
return v_res_1515_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object* v_classTy_1516_, lean_object* v_a_1517_, lean_object* v_a_1518_, lean_object* v_a_1519_, lean_object* v_a_1520_){
_start:
{
lean_object* v___x_1522_; 
v___x_1522_ = l_Lean_Expr_getAppFn(v_classTy_1516_);
if (lean_obj_tag(v___x_1522_) == 4)
{
lean_object* v_declName_1523_; lean_object* v___x_1524_; 
v_declName_1523_ = lean_ctor_get(v___x_1522_, 0);
lean_inc(v_declName_1523_);
lean_inc(v_a_1520_);
lean_inc_ref(v_a_1519_);
lean_inc(v_a_1518_);
lean_inc_ref(v_a_1517_);
v___x_1524_ = lean_infer_type(v___x_1522_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
if (lean_obj_tag(v___x_1524_) == 0)
{
lean_object* v_a_1525_; lean_object* v___f_1526_; uint8_t v___x_1527_; lean_object* v___x_1528_; 
v_a_1525_ = lean_ctor_get(v___x_1524_, 0);
lean_inc(v_a_1525_);
lean_dec_ref_known(v___x_1524_, 1);
v___f_1526_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1526_, 0, v_declName_1523_);
v___x_1527_ = 0;
v___x_1528_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_1525_, v___f_1526_, v___x_1527_, v___x_1527_, v_a_1517_, v_a_1518_, v_a_1519_, v_a_1520_);
return v___x_1528_;
}
else
{
lean_object* v_a_1529_; lean_object* v___x_1531_; uint8_t v_isShared_1532_; uint8_t v_isSharedCheck_1536_; 
lean_dec(v_declName_1523_);
v_a_1529_ = lean_ctor_get(v___x_1524_, 0);
v_isSharedCheck_1536_ = !lean_is_exclusive(v___x_1524_);
if (v_isSharedCheck_1536_ == 0)
{
v___x_1531_ = v___x_1524_;
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
else
{
lean_inc(v_a_1529_);
lean_dec(v___x_1524_);
v___x_1531_ = lean_box(0);
v_isShared_1532_ = v_isSharedCheck_1536_;
goto v_resetjp_1530_;
}
v_resetjp_1530_:
{
lean_object* v___x_1534_; 
if (v_isShared_1532_ == 0)
{
v___x_1534_ = v___x_1531_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_a_1529_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
else
{
lean_object* v___x_1537_; lean_object* v___x_1538_; 
lean_dec_ref(v___x_1522_);
v___x_1537_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_1538_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1538_, 0, v___x_1537_);
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object* v_classTy_1539_, lean_object* v_a_1540_, lean_object* v_a_1541_, lean_object* v_a_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_classTy_1539_, v_a_1540_, v_a_1541_, v_a_1542_, v_a_1543_);
lean_dec(v_a_1543_);
lean_dec_ref(v_a_1542_);
lean_dec(v_a_1541_);
lean_dec_ref(v_a_1540_);
lean_dec_ref(v_classTy_1539_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_a_1546_, lean_object* v_as_1547_, lean_object* v_j_1548_){
_start:
{
lean_object* v___x_1549_; uint8_t v___x_1550_; 
v___x_1549_ = lean_array_get_size(v_as_1547_);
v___x_1550_ = lean_nat_dec_lt(v_j_1548_, v___x_1549_);
if (v___x_1550_ == 0)
{
lean_object* v___x_1551_; 
lean_dec(v_j_1548_);
v___x_1551_ = lean_box(0);
return v___x_1551_;
}
else
{
lean_object* v___x_1552_; lean_object* v___x_1553_; uint8_t v___x_1554_; 
v___x_1552_ = lean_array_fget_borrowed(v_as_1547_, v_j_1548_);
v___x_1553_ = l_Lean_Expr_mvarId_x21(v___x_1552_);
v___x_1554_ = l_Lean_instBEqMVarId_beq(v___x_1553_, v_a_1546_);
lean_dec(v___x_1553_);
if (v___x_1554_ == 0)
{
lean_object* v___x_1555_; lean_object* v___x_1556_; 
v___x_1555_ = lean_unsigned_to_nat(1u);
v___x_1556_ = lean_nat_add(v_j_1548_, v___x_1555_);
lean_dec(v_j_1548_);
v_j_1548_ = v___x_1556_;
goto _start;
}
else
{
lean_object* v___x_1558_; 
v___x_1558_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1558_, 0, v_j_1548_);
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_a_1559_, lean_object* v_as_1560_, lean_object* v_j_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1559_, v_as_1560_, v_j_1561_);
lean_dec_ref(v_as_1560_);
lean_dec(v_a_1559_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1563_, lean_object* v_x_1564_, lean_object* v_x_1565_, lean_object* v_x_1566_){
_start:
{
lean_object* v_ks_1567_; lean_object* v_vs_1568_; lean_object* v___x_1570_; uint8_t v_isShared_1571_; uint8_t v_isSharedCheck_1592_; 
v_ks_1567_ = lean_ctor_get(v_x_1563_, 0);
v_vs_1568_ = lean_ctor_get(v_x_1563_, 1);
v_isSharedCheck_1592_ = !lean_is_exclusive(v_x_1563_);
if (v_isSharedCheck_1592_ == 0)
{
v___x_1570_ = v_x_1563_;
v_isShared_1571_ = v_isSharedCheck_1592_;
goto v_resetjp_1569_;
}
else
{
lean_inc(v_vs_1568_);
lean_inc(v_ks_1567_);
lean_dec(v_x_1563_);
v___x_1570_ = lean_box(0);
v_isShared_1571_ = v_isSharedCheck_1592_;
goto v_resetjp_1569_;
}
v_resetjp_1569_:
{
lean_object* v___x_1572_; uint8_t v___x_1573_; 
v___x_1572_ = lean_array_get_size(v_ks_1567_);
v___x_1573_ = lean_nat_dec_lt(v_x_1564_, v___x_1572_);
if (v___x_1573_ == 0)
{
lean_object* v___x_1574_; lean_object* v___x_1575_; lean_object* v___x_1577_; 
lean_dec(v_x_1564_);
v___x_1574_ = lean_array_push(v_ks_1567_, v_x_1565_);
v___x_1575_ = lean_array_push(v_vs_1568_, v_x_1566_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 1, v___x_1575_);
lean_ctor_set(v___x_1570_, 0, v___x_1574_);
v___x_1577_ = v___x_1570_;
goto v_reusejp_1576_;
}
else
{
lean_object* v_reuseFailAlloc_1578_; 
v_reuseFailAlloc_1578_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1578_, 0, v___x_1574_);
lean_ctor_set(v_reuseFailAlloc_1578_, 1, v___x_1575_);
v___x_1577_ = v_reuseFailAlloc_1578_;
goto v_reusejp_1576_;
}
v_reusejp_1576_:
{
return v___x_1577_;
}
}
else
{
lean_object* v_k_x27_1579_; uint8_t v___x_1580_; 
v_k_x27_1579_ = lean_array_fget_borrowed(v_ks_1567_, v_x_1564_);
v___x_1580_ = l_Lean_instBEqMVarId_beq(v_x_1565_, v_k_x27_1579_);
if (v___x_1580_ == 0)
{
lean_object* v___x_1582_; 
if (v_isShared_1571_ == 0)
{
v___x_1582_ = v___x_1570_;
goto v_reusejp_1581_;
}
else
{
lean_object* v_reuseFailAlloc_1586_; 
v_reuseFailAlloc_1586_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1586_, 0, v_ks_1567_);
lean_ctor_set(v_reuseFailAlloc_1586_, 1, v_vs_1568_);
v___x_1582_ = v_reuseFailAlloc_1586_;
goto v_reusejp_1581_;
}
v_reusejp_1581_:
{
lean_object* v___x_1583_; lean_object* v___x_1584_; 
v___x_1583_ = lean_unsigned_to_nat(1u);
v___x_1584_ = lean_nat_add(v_x_1564_, v___x_1583_);
lean_dec(v_x_1564_);
v_x_1563_ = v___x_1582_;
v_x_1564_ = v___x_1584_;
goto _start;
}
}
else
{
lean_object* v___x_1587_; lean_object* v___x_1588_; lean_object* v___x_1590_; 
v___x_1587_ = lean_array_fset(v_ks_1567_, v_x_1564_, v_x_1565_);
v___x_1588_ = lean_array_fset(v_vs_1568_, v_x_1564_, v_x_1566_);
lean_dec(v_x_1564_);
if (v_isShared_1571_ == 0)
{
lean_ctor_set(v___x_1570_, 1, v___x_1588_);
lean_ctor_set(v___x_1570_, 0, v___x_1587_);
v___x_1590_ = v___x_1570_;
goto v_reusejp_1589_;
}
else
{
lean_object* v_reuseFailAlloc_1591_; 
v_reuseFailAlloc_1591_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1591_, 0, v___x_1587_);
lean_ctor_set(v_reuseFailAlloc_1591_, 1, v___x_1588_);
v___x_1590_ = v_reuseFailAlloc_1591_;
goto v_reusejp_1589_;
}
v_reusejp_1589_:
{
return v___x_1590_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1593_, lean_object* v_k_1594_, lean_object* v_v_1595_){
_start:
{
lean_object* v___x_1596_; lean_object* v___x_1597_; 
v___x_1596_ = lean_unsigned_to_nat(0u);
v___x_1597_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1593_, v___x_1596_, v_k_1594_, v_v_1595_);
return v___x_1597_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1598_, size_t v_x_1599_, size_t v_x_1600_, lean_object* v_x_1601_, lean_object* v_x_1602_){
_start:
{
if (lean_obj_tag(v_x_1598_) == 0)
{
lean_object* v_es_1603_; size_t v___x_1604_; size_t v___x_1605_; lean_object* v_j_1606_; lean_object* v___x_1607_; uint8_t v___x_1608_; 
v_es_1603_ = lean_ctor_get(v_x_1598_, 0);
v___x_1604_ = ((size_t)31ULL);
v___x_1605_ = lean_usize_land(v_x_1599_, v___x_1604_);
v_j_1606_ = lean_usize_to_nat(v___x_1605_);
v___x_1607_ = lean_array_get_size(v_es_1603_);
v___x_1608_ = lean_nat_dec_lt(v_j_1606_, v___x_1607_);
if (v___x_1608_ == 0)
{
lean_dec(v_j_1606_);
lean_dec(v_x_1602_);
lean_dec(v_x_1601_);
return v_x_1598_;
}
else
{
lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1647_; 
lean_inc_ref(v_es_1603_);
v_isSharedCheck_1647_ = !lean_is_exclusive(v_x_1598_);
if (v_isSharedCheck_1647_ == 0)
{
lean_object* v_unused_1648_; 
v_unused_1648_ = lean_ctor_get(v_x_1598_, 0);
lean_dec(v_unused_1648_);
v___x_1610_ = v_x_1598_;
v_isShared_1611_ = v_isSharedCheck_1647_;
goto v_resetjp_1609_;
}
else
{
lean_dec(v_x_1598_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1647_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v_v_1612_; lean_object* v___x_1613_; lean_object* v_xs_x27_1614_; lean_object* v___y_1616_; 
v_v_1612_ = lean_array_fget(v_es_1603_, v_j_1606_);
v___x_1613_ = lean_box(0);
v_xs_x27_1614_ = lean_array_fset(v_es_1603_, v_j_1606_, v___x_1613_);
switch(lean_obj_tag(v_v_1612_))
{
case 0:
{
lean_object* v_key_1621_; lean_object* v_val_1622_; lean_object* v___x_1624_; uint8_t v_isShared_1625_; uint8_t v_isSharedCheck_1632_; 
v_key_1621_ = lean_ctor_get(v_v_1612_, 0);
v_val_1622_ = lean_ctor_get(v_v_1612_, 1);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_v_1612_);
if (v_isSharedCheck_1632_ == 0)
{
v___x_1624_ = v_v_1612_;
v_isShared_1625_ = v_isSharedCheck_1632_;
goto v_resetjp_1623_;
}
else
{
lean_inc(v_val_1622_);
lean_inc(v_key_1621_);
lean_dec(v_v_1612_);
v___x_1624_ = lean_box(0);
v_isShared_1625_ = v_isSharedCheck_1632_;
goto v_resetjp_1623_;
}
v_resetjp_1623_:
{
uint8_t v___x_1626_; 
v___x_1626_ = l_Lean_instBEqMVarId_beq(v_x_1601_, v_key_1621_);
if (v___x_1626_ == 0)
{
lean_object* v___x_1627_; lean_object* v___x_1628_; 
lean_del_object(v___x_1624_);
v___x_1627_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1621_, v_val_1622_, v_x_1601_, v_x_1602_);
v___x_1628_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1628_, 0, v___x_1627_);
v___y_1616_ = v___x_1628_;
goto v___jp_1615_;
}
else
{
lean_object* v___x_1630_; 
lean_dec(v_val_1622_);
lean_dec(v_key_1621_);
if (v_isShared_1625_ == 0)
{
lean_ctor_set(v___x_1624_, 1, v_x_1602_);
lean_ctor_set(v___x_1624_, 0, v_x_1601_);
v___x_1630_ = v___x_1624_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_x_1601_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v_x_1602_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
v___y_1616_ = v___x_1630_;
goto v___jp_1615_;
}
}
}
}
case 1:
{
lean_object* v_node_1633_; lean_object* v___x_1635_; uint8_t v_isShared_1636_; uint8_t v_isSharedCheck_1645_; 
v_node_1633_ = lean_ctor_get(v_v_1612_, 0);
v_isSharedCheck_1645_ = !lean_is_exclusive(v_v_1612_);
if (v_isSharedCheck_1645_ == 0)
{
v___x_1635_ = v_v_1612_;
v_isShared_1636_ = v_isSharedCheck_1645_;
goto v_resetjp_1634_;
}
else
{
lean_inc(v_node_1633_);
lean_dec(v_v_1612_);
v___x_1635_ = lean_box(0);
v_isShared_1636_ = v_isSharedCheck_1645_;
goto v_resetjp_1634_;
}
v_resetjp_1634_:
{
size_t v___x_1637_; size_t v___x_1638_; size_t v___x_1639_; size_t v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; 
v___x_1637_ = ((size_t)5ULL);
v___x_1638_ = lean_usize_shift_right(v_x_1599_, v___x_1637_);
v___x_1639_ = ((size_t)1ULL);
v___x_1640_ = lean_usize_add(v_x_1600_, v___x_1639_);
v___x_1641_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_node_1633_, v___x_1638_, v___x_1640_, v_x_1601_, v_x_1602_);
if (v_isShared_1636_ == 0)
{
lean_ctor_set(v___x_1635_, 0, v___x_1641_);
v___x_1643_ = v___x_1635_;
goto v_reusejp_1642_;
}
else
{
lean_object* v_reuseFailAlloc_1644_; 
v_reuseFailAlloc_1644_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1644_, 0, v___x_1641_);
v___x_1643_ = v_reuseFailAlloc_1644_;
goto v_reusejp_1642_;
}
v_reusejp_1642_:
{
v___y_1616_ = v___x_1643_;
goto v___jp_1615_;
}
}
}
default: 
{
lean_object* v___x_1646_; 
v___x_1646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1646_, 0, v_x_1601_);
lean_ctor_set(v___x_1646_, 1, v_x_1602_);
v___y_1616_ = v___x_1646_;
goto v___jp_1615_;
}
}
v___jp_1615_:
{
lean_object* v___x_1617_; lean_object* v___x_1619_; 
v___x_1617_ = lean_array_fset(v_xs_x27_1614_, v_j_1606_, v___y_1616_);
lean_dec(v_j_1606_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 0, v___x_1617_);
v___x_1619_ = v___x_1610_;
goto v_reusejp_1618_;
}
else
{
lean_object* v_reuseFailAlloc_1620_; 
v_reuseFailAlloc_1620_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1620_, 0, v___x_1617_);
v___x_1619_ = v_reuseFailAlloc_1620_;
goto v_reusejp_1618_;
}
v_reusejp_1618_:
{
return v___x_1619_;
}
}
}
}
}
else
{
lean_object* v_ks_1649_; lean_object* v_vs_1650_; lean_object* v___x_1652_; uint8_t v_isShared_1653_; uint8_t v_isSharedCheck_1670_; 
v_ks_1649_ = lean_ctor_get(v_x_1598_, 0);
v_vs_1650_ = lean_ctor_get(v_x_1598_, 1);
v_isSharedCheck_1670_ = !lean_is_exclusive(v_x_1598_);
if (v_isSharedCheck_1670_ == 0)
{
v___x_1652_ = v_x_1598_;
v_isShared_1653_ = v_isSharedCheck_1670_;
goto v_resetjp_1651_;
}
else
{
lean_inc(v_vs_1650_);
lean_inc(v_ks_1649_);
lean_dec(v_x_1598_);
v___x_1652_ = lean_box(0);
v_isShared_1653_ = v_isSharedCheck_1670_;
goto v_resetjp_1651_;
}
v_resetjp_1651_:
{
lean_object* v___x_1655_; 
if (v_isShared_1653_ == 0)
{
v___x_1655_ = v___x_1652_;
goto v_reusejp_1654_;
}
else
{
lean_object* v_reuseFailAlloc_1669_; 
v_reuseFailAlloc_1669_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1669_, 0, v_ks_1649_);
lean_ctor_set(v_reuseFailAlloc_1669_, 1, v_vs_1650_);
v___x_1655_ = v_reuseFailAlloc_1669_;
goto v_reusejp_1654_;
}
v_reusejp_1654_:
{
lean_object* v_newNode_1656_; uint8_t v___y_1658_; size_t v___x_1664_; uint8_t v___x_1665_; 
v_newNode_1656_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v___x_1655_, v_x_1601_, v_x_1602_);
v___x_1664_ = ((size_t)7ULL);
v___x_1665_ = lean_usize_dec_le(v___x_1664_, v_x_1600_);
if (v___x_1665_ == 0)
{
lean_object* v___x_1666_; lean_object* v___x_1667_; uint8_t v___x_1668_; 
v___x_1666_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1656_);
v___x_1667_ = lean_unsigned_to_nat(4u);
v___x_1668_ = lean_nat_dec_lt(v___x_1666_, v___x_1667_);
lean_dec(v___x_1666_);
v___y_1658_ = v___x_1668_;
goto v___jp_1657_;
}
else
{
v___y_1658_ = v___x_1665_;
goto v___jp_1657_;
}
v___jp_1657_:
{
if (v___y_1658_ == 0)
{
lean_object* v_ks_1659_; lean_object* v_vs_1660_; lean_object* v___x_1661_; lean_object* v___x_1662_; lean_object* v___x_1663_; 
v_ks_1659_ = lean_ctor_get(v_newNode_1656_, 0);
lean_inc_ref(v_ks_1659_);
v_vs_1660_ = lean_ctor_get(v_newNode_1656_, 1);
lean_inc_ref(v_vs_1660_);
lean_dec_ref(v_newNode_1656_);
v___x_1661_ = lean_unsigned_to_nat(0u);
v___x_1662_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0);
v___x_1663_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_x_1600_, v_ks_1659_, v_vs_1660_, v___x_1661_, v___x_1662_);
lean_dec_ref(v_vs_1660_);
lean_dec_ref(v_ks_1659_);
return v___x_1663_;
}
else
{
return v_newNode_1656_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(size_t v_depth_1671_, lean_object* v_keys_1672_, lean_object* v_vals_1673_, lean_object* v_i_1674_, lean_object* v_entries_1675_){
_start:
{
lean_object* v___x_1676_; uint8_t v___x_1677_; 
v___x_1676_ = lean_array_get_size(v_keys_1672_);
v___x_1677_ = lean_nat_dec_lt(v_i_1674_, v___x_1676_);
if (v___x_1677_ == 0)
{
lean_dec(v_i_1674_);
return v_entries_1675_;
}
else
{
lean_object* v_k_1678_; lean_object* v_v_1679_; uint64_t v___x_1680_; size_t v_h_1681_; size_t v___x_1682_; lean_object* v___x_1683_; size_t v___x_1684_; size_t v___x_1685_; size_t v___x_1686_; size_t v_h_1687_; lean_object* v___x_1688_; lean_object* v___x_1689_; 
v_k_1678_ = lean_array_fget_borrowed(v_keys_1672_, v_i_1674_);
v_v_1679_ = lean_array_fget_borrowed(v_vals_1673_, v_i_1674_);
v___x_1680_ = l_Lean_instHashableMVarId_hash(v_k_1678_);
v_h_1681_ = lean_uint64_to_usize(v___x_1680_);
v___x_1682_ = ((size_t)5ULL);
v___x_1683_ = lean_unsigned_to_nat(1u);
v___x_1684_ = ((size_t)1ULL);
v___x_1685_ = lean_usize_sub(v_depth_1671_, v___x_1684_);
v___x_1686_ = lean_usize_mul(v___x_1682_, v___x_1685_);
v_h_1687_ = lean_usize_shift_right(v_h_1681_, v___x_1686_);
v___x_1688_ = lean_nat_add(v_i_1674_, v___x_1683_);
lean_dec(v_i_1674_);
lean_inc(v_v_1679_);
lean_inc(v_k_1678_);
v___x_1689_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_entries_1675_, v_h_1687_, v_depth_1671_, v_k_1678_, v_v_1679_);
v_i_1674_ = v___x_1688_;
v_entries_1675_ = v___x_1689_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1691_, lean_object* v_keys_1692_, lean_object* v_vals_1693_, lean_object* v_i_1694_, lean_object* v_entries_1695_){
_start:
{
size_t v_depth_boxed_1696_; lean_object* v_res_1697_; 
v_depth_boxed_1696_ = lean_unbox_usize(v_depth_1691_);
lean_dec(v_depth_1691_);
v_res_1697_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1696_, v_keys_1692_, v_vals_1693_, v_i_1694_, v_entries_1695_);
lean_dec_ref(v_vals_1693_);
lean_dec_ref(v_keys_1692_);
return v_res_1697_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1698_, lean_object* v_x_1699_, lean_object* v_x_1700_, lean_object* v_x_1701_, lean_object* v_x_1702_){
_start:
{
size_t v_x_1620__boxed_1703_; size_t v_x_1621__boxed_1704_; lean_object* v_res_1705_; 
v_x_1620__boxed_1703_ = lean_unbox_usize(v_x_1699_);
lean_dec(v_x_1699_);
v_x_1621__boxed_1704_ = lean_unbox_usize(v_x_1700_);
lean_dec(v_x_1700_);
v_res_1705_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1698_, v_x_1620__boxed_1703_, v_x_1621__boxed_1704_, v_x_1701_, v_x_1702_);
return v_res_1705_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(lean_object* v_x_1706_, lean_object* v_x_1707_, lean_object* v_x_1708_){
_start:
{
uint64_t v___x_1709_; size_t v___x_1710_; size_t v___x_1711_; lean_object* v___x_1712_; 
v___x_1709_ = l_Lean_instHashableMVarId_hash(v_x_1707_);
v___x_1710_ = lean_uint64_to_usize(v___x_1709_);
v___x_1711_ = ((size_t)1ULL);
v___x_1712_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1706_, v___x_1710_, v___x_1711_, v_x_1707_, v_x_1708_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(lean_object* v_mvarId_1713_, lean_object* v_val_1714_, lean_object* v___y_1715_){
_start:
{
lean_object* v___x_1717_; lean_object* v_mctx_1718_; lean_object* v_cache_1719_; lean_object* v_zetaDeltaFVarIds_1720_; lean_object* v_postponed_1721_; lean_object* v_diag_1722_; lean_object* v___x_1724_; uint8_t v_isShared_1725_; uint8_t v_isSharedCheck_1750_; 
v___x_1717_ = lean_st_ref_take(v___y_1715_);
v_mctx_1718_ = lean_ctor_get(v___x_1717_, 0);
v_cache_1719_ = lean_ctor_get(v___x_1717_, 1);
v_zetaDeltaFVarIds_1720_ = lean_ctor_get(v___x_1717_, 2);
v_postponed_1721_ = lean_ctor_get(v___x_1717_, 3);
v_diag_1722_ = lean_ctor_get(v___x_1717_, 4);
v_isSharedCheck_1750_ = !lean_is_exclusive(v___x_1717_);
if (v_isSharedCheck_1750_ == 0)
{
v___x_1724_ = v___x_1717_;
v_isShared_1725_ = v_isSharedCheck_1750_;
goto v_resetjp_1723_;
}
else
{
lean_inc(v_diag_1722_);
lean_inc(v_postponed_1721_);
lean_inc(v_zetaDeltaFVarIds_1720_);
lean_inc(v_cache_1719_);
lean_inc(v_mctx_1718_);
lean_dec(v___x_1717_);
v___x_1724_ = lean_box(0);
v_isShared_1725_ = v_isSharedCheck_1750_;
goto v_resetjp_1723_;
}
v_resetjp_1723_:
{
lean_object* v_depth_1726_; lean_object* v_levelAssignDepth_1727_; lean_object* v_lmvarCounter_1728_; lean_object* v_mvarCounter_1729_; lean_object* v_lDecls_1730_; lean_object* v_decls_1731_; lean_object* v_userNames_1732_; lean_object* v_lAssignment_1733_; lean_object* v_eAssignment_1734_; lean_object* v_dAssignment_1735_; lean_object* v___x_1737_; uint8_t v_isShared_1738_; uint8_t v_isSharedCheck_1749_; 
v_depth_1726_ = lean_ctor_get(v_mctx_1718_, 0);
v_levelAssignDepth_1727_ = lean_ctor_get(v_mctx_1718_, 1);
v_lmvarCounter_1728_ = lean_ctor_get(v_mctx_1718_, 2);
v_mvarCounter_1729_ = lean_ctor_get(v_mctx_1718_, 3);
v_lDecls_1730_ = lean_ctor_get(v_mctx_1718_, 4);
v_decls_1731_ = lean_ctor_get(v_mctx_1718_, 5);
v_userNames_1732_ = lean_ctor_get(v_mctx_1718_, 6);
v_lAssignment_1733_ = lean_ctor_get(v_mctx_1718_, 7);
v_eAssignment_1734_ = lean_ctor_get(v_mctx_1718_, 8);
v_dAssignment_1735_ = lean_ctor_get(v_mctx_1718_, 9);
v_isSharedCheck_1749_ = !lean_is_exclusive(v_mctx_1718_);
if (v_isSharedCheck_1749_ == 0)
{
v___x_1737_ = v_mctx_1718_;
v_isShared_1738_ = v_isSharedCheck_1749_;
goto v_resetjp_1736_;
}
else
{
lean_inc(v_dAssignment_1735_);
lean_inc(v_eAssignment_1734_);
lean_inc(v_lAssignment_1733_);
lean_inc(v_userNames_1732_);
lean_inc(v_decls_1731_);
lean_inc(v_lDecls_1730_);
lean_inc(v_mvarCounter_1729_);
lean_inc(v_lmvarCounter_1728_);
lean_inc(v_levelAssignDepth_1727_);
lean_inc(v_depth_1726_);
lean_dec(v_mctx_1718_);
v___x_1737_ = lean_box(0);
v_isShared_1738_ = v_isSharedCheck_1749_;
goto v_resetjp_1736_;
}
v_resetjp_1736_:
{
lean_object* v___x_1739_; lean_object* v___x_1741_; 
v___x_1739_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_eAssignment_1734_, v_mvarId_1713_, v_val_1714_);
if (v_isShared_1738_ == 0)
{
lean_ctor_set(v___x_1737_, 8, v___x_1739_);
v___x_1741_ = v___x_1737_;
goto v_reusejp_1740_;
}
else
{
lean_object* v_reuseFailAlloc_1748_; 
v_reuseFailAlloc_1748_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1748_, 0, v_depth_1726_);
lean_ctor_set(v_reuseFailAlloc_1748_, 1, v_levelAssignDepth_1727_);
lean_ctor_set(v_reuseFailAlloc_1748_, 2, v_lmvarCounter_1728_);
lean_ctor_set(v_reuseFailAlloc_1748_, 3, v_mvarCounter_1729_);
lean_ctor_set(v_reuseFailAlloc_1748_, 4, v_lDecls_1730_);
lean_ctor_set(v_reuseFailAlloc_1748_, 5, v_decls_1731_);
lean_ctor_set(v_reuseFailAlloc_1748_, 6, v_userNames_1732_);
lean_ctor_set(v_reuseFailAlloc_1748_, 7, v_lAssignment_1733_);
lean_ctor_set(v_reuseFailAlloc_1748_, 8, v___x_1739_);
lean_ctor_set(v_reuseFailAlloc_1748_, 9, v_dAssignment_1735_);
v___x_1741_ = v_reuseFailAlloc_1748_;
goto v_reusejp_1740_;
}
v_reusejp_1740_:
{
lean_object* v___x_1743_; 
if (v_isShared_1725_ == 0)
{
lean_ctor_set(v___x_1724_, 0, v___x_1741_);
v___x_1743_ = v___x_1724_;
goto v_reusejp_1742_;
}
else
{
lean_object* v_reuseFailAlloc_1747_; 
v_reuseFailAlloc_1747_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1747_, 0, v___x_1741_);
lean_ctor_set(v_reuseFailAlloc_1747_, 1, v_cache_1719_);
lean_ctor_set(v_reuseFailAlloc_1747_, 2, v_zetaDeltaFVarIds_1720_);
lean_ctor_set(v_reuseFailAlloc_1747_, 3, v_postponed_1721_);
lean_ctor_set(v_reuseFailAlloc_1747_, 4, v_diag_1722_);
v___x_1743_ = v_reuseFailAlloc_1747_;
goto v_reusejp_1742_;
}
v_reusejp_1742_:
{
lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; 
v___x_1744_ = lean_st_ref_set(v___y_1715_, v___x_1743_);
v___x_1745_ = lean_box(0);
v___x_1746_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1746_, 0, v___x_1745_);
return v___x_1746_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg___boxed(lean_object* v_mvarId_1751_, lean_object* v_val_1752_, lean_object* v___y_1753_, lean_object* v___y_1754_){
_start:
{
lean_object* v_res_1755_; 
v_res_1755_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1751_, v_val_1752_, v___y_1753_);
lean_dec(v___y_1753_);
return v_res_1755_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(lean_object* v_argMVars_1756_, lean_object* v_argVars_1757_, lean_object* v_as_1758_, size_t v_sz_1759_, size_t v_i_1760_, lean_object* v_b_1761_, lean_object* v___y_1762_, lean_object* v___y_1763_, lean_object* v___y_1764_, lean_object* v___y_1765_){
_start:
{
uint8_t v___x_1767_; 
v___x_1767_ = lean_usize_dec_lt(v_i_1760_, v_sz_1759_);
if (v___x_1767_ == 0)
{
lean_object* v___x_1768_; 
v___x_1768_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1768_, 0, v_b_1761_);
return v___x_1768_;
}
else
{
lean_object* v___x_1769_; lean_object* v_a_1770_; lean_object* v___y_1772_; lean_object* v___y_1773_; lean_object* v___y_1774_; lean_object* v___y_1775_; lean_object* v___x_1791_; lean_object* v___x_1792_; 
v___x_1769_ = lean_box(0);
v_a_1770_ = lean_array_uget_borrowed(v_as_1758_, v_i_1760_);
v___x_1791_ = lean_unsigned_to_nat(0u);
v___x_1792_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1770_, v_argMVars_1756_, v___x_1791_);
if (lean_obj_tag(v___x_1792_) == 1)
{
lean_object* v_val_1793_; lean_object* v___x_1794_; lean_object* v___x_1795_; lean_object* v___x_1796_; 
v_val_1793_ = lean_ctor_get(v___x_1792_, 0);
lean_inc(v_val_1793_);
lean_dec_ref_known(v___x_1792_, 1);
v___x_1794_ = l_Lean_instInhabitedExpr;
v___x_1795_ = lean_array_get_borrowed(v___x_1794_, v_argVars_1757_, v_val_1793_);
lean_dec(v_val_1793_);
lean_inc(v___x_1795_);
lean_inc(v_a_1770_);
v___x_1796_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_a_1770_, v___x_1795_, v___y_1763_);
if (lean_obj_tag(v___x_1796_) == 0)
{
lean_dec_ref_known(v___x_1796_, 1);
v___y_1772_ = v___y_1762_;
v___y_1773_ = v___y_1763_;
v___y_1774_ = v___y_1764_;
v___y_1775_ = v___y_1765_;
goto v___jp_1771_;
}
else
{
return v___x_1796_;
}
}
else
{
lean_dec(v___x_1792_);
v___y_1772_ = v___y_1762_;
v___y_1773_ = v___y_1763_;
v___y_1774_ = v___y_1764_;
v___y_1775_ = v___y_1765_;
goto v___jp_1771_;
}
v___jp_1771_:
{
lean_object* v___x_1776_; lean_object* v___x_1777_; 
lean_inc(v_a_1770_);
v___x_1776_ = l_Lean_Expr_mvar___override(v_a_1770_);
lean_inc(v___y_1775_);
lean_inc_ref(v___y_1774_);
lean_inc(v___y_1773_);
lean_inc_ref(v___y_1772_);
v___x_1777_ = lean_infer_type(v___x_1776_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
if (lean_obj_tag(v___x_1777_) == 0)
{
lean_object* v_a_1778_; lean_object* v___x_1779_; 
v_a_1778_ = lean_ctor_get(v___x_1777_, 0);
lean_inc(v_a_1778_);
lean_dec_ref_known(v___x_1777_, 1);
v___x_1779_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1756_, v_argVars_1757_, v_a_1778_, v___y_1772_, v___y_1773_, v___y_1774_, v___y_1775_);
if (lean_obj_tag(v___x_1779_) == 0)
{
size_t v___x_1780_; size_t v___x_1781_; 
lean_dec_ref_known(v___x_1779_, 1);
v___x_1780_ = ((size_t)1ULL);
v___x_1781_ = lean_usize_add(v_i_1760_, v___x_1780_);
v_i_1760_ = v___x_1781_;
v_b_1761_ = v___x_1769_;
goto _start;
}
else
{
return v___x_1779_;
}
}
else
{
lean_object* v_a_1783_; lean_object* v___x_1785_; uint8_t v_isShared_1786_; uint8_t v_isSharedCheck_1790_; 
v_a_1783_ = lean_ctor_get(v___x_1777_, 0);
v_isSharedCheck_1790_ = !lean_is_exclusive(v___x_1777_);
if (v_isSharedCheck_1790_ == 0)
{
v___x_1785_ = v___x_1777_;
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
else
{
lean_inc(v_a_1783_);
lean_dec(v___x_1777_);
v___x_1785_ = lean_box(0);
v_isShared_1786_ = v_isSharedCheck_1790_;
goto v_resetjp_1784_;
}
v_resetjp_1784_:
{
lean_object* v___x_1788_; 
if (v_isShared_1786_ == 0)
{
v___x_1788_ = v___x_1785_;
goto v_reusejp_1787_;
}
else
{
lean_object* v_reuseFailAlloc_1789_; 
v_reuseFailAlloc_1789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1789_, 0, v_a_1783_);
v___x_1788_ = v_reuseFailAlloc_1789_;
goto v_reusejp_1787_;
}
v_reusejp_1787_:
{
return v___x_1788_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1797_, lean_object* v_argVars_1798_, lean_object* v_e_1799_, lean_object* v_a_1800_, lean_object* v_a_1801_, lean_object* v_a_1802_, lean_object* v_a_1803_){
_start:
{
lean_object* v___x_1805_; 
v___x_1805_ = l_Lean_Meta_getMVars(v_e_1799_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
if (lean_obj_tag(v___x_1805_) == 0)
{
lean_object* v_a_1806_; lean_object* v___x_1807_; size_t v_sz_1808_; size_t v___x_1809_; lean_object* v___x_1810_; 
v_a_1806_ = lean_ctor_get(v___x_1805_, 0);
lean_inc(v_a_1806_);
lean_dec_ref_known(v___x_1805_, 1);
v___x_1807_ = lean_box(0);
v_sz_1808_ = lean_array_size(v_a_1806_);
v___x_1809_ = ((size_t)0ULL);
v___x_1810_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1797_, v_argVars_1798_, v_a_1806_, v_sz_1808_, v___x_1809_, v___x_1807_, v_a_1800_, v_a_1801_, v_a_1802_, v_a_1803_);
lean_dec(v_a_1806_);
if (lean_obj_tag(v___x_1810_) == 0)
{
lean_object* v___x_1812_; uint8_t v_isShared_1813_; uint8_t v_isSharedCheck_1817_; 
v_isSharedCheck_1817_ = !lean_is_exclusive(v___x_1810_);
if (v_isSharedCheck_1817_ == 0)
{
lean_object* v_unused_1818_; 
v_unused_1818_ = lean_ctor_get(v___x_1810_, 0);
lean_dec(v_unused_1818_);
v___x_1812_ = v___x_1810_;
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
else
{
lean_dec(v___x_1810_);
v___x_1812_ = lean_box(0);
v_isShared_1813_ = v_isSharedCheck_1817_;
goto v_resetjp_1811_;
}
v_resetjp_1811_:
{
lean_object* v___x_1815_; 
if (v_isShared_1813_ == 0)
{
lean_ctor_set(v___x_1812_, 0, v___x_1807_);
v___x_1815_ = v___x_1812_;
goto v_reusejp_1814_;
}
else
{
lean_object* v_reuseFailAlloc_1816_; 
v_reuseFailAlloc_1816_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1816_, 0, v___x_1807_);
v___x_1815_ = v_reuseFailAlloc_1816_;
goto v_reusejp_1814_;
}
v_reusejp_1814_:
{
return v___x_1815_;
}
}
}
else
{
return v___x_1810_;
}
}
else
{
lean_object* v_a_1819_; lean_object* v___x_1821_; uint8_t v_isShared_1822_; uint8_t v_isSharedCheck_1826_; 
v_a_1819_ = lean_ctor_get(v___x_1805_, 0);
v_isSharedCheck_1826_ = !lean_is_exclusive(v___x_1805_);
if (v_isSharedCheck_1826_ == 0)
{
v___x_1821_ = v___x_1805_;
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
else
{
lean_inc(v_a_1819_);
lean_dec(v___x_1805_);
v___x_1821_ = lean_box(0);
v_isShared_1822_ = v_isSharedCheck_1826_;
goto v_resetjp_1820_;
}
v_resetjp_1820_:
{
lean_object* v___x_1824_; 
if (v_isShared_1822_ == 0)
{
v___x_1824_ = v___x_1821_;
goto v_reusejp_1823_;
}
else
{
lean_object* v_reuseFailAlloc_1825_; 
v_reuseFailAlloc_1825_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1825_, 0, v_a_1819_);
v___x_1824_ = v_reuseFailAlloc_1825_;
goto v_reusejp_1823_;
}
v_reusejp_1823_:
{
return v___x_1824_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1827_, lean_object* v_argVars_1828_, lean_object* v_e_1829_, lean_object* v_a_1830_, lean_object* v_a_1831_, lean_object* v_a_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1827_, v_argVars_1828_, v_e_1829_, v_a_1830_, v_a_1831_, v_a_1832_, v_a_1833_);
lean_dec(v_a_1833_);
lean_dec_ref(v_a_1832_);
lean_dec(v_a_1831_);
lean_dec_ref(v_a_1830_);
lean_dec_ref(v_argVars_1828_);
lean_dec_ref(v_argMVars_1827_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2___boxed(lean_object* v_argMVars_1836_, lean_object* v_argVars_1837_, lean_object* v_as_1838_, lean_object* v_sz_1839_, lean_object* v_i_1840_, lean_object* v_b_1841_, lean_object* v___y_1842_, lean_object* v___y_1843_, lean_object* v___y_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_){
_start:
{
size_t v_sz_boxed_1847_; size_t v_i_boxed_1848_; lean_object* v_res_1849_; 
v_sz_boxed_1847_ = lean_unbox_usize(v_sz_1839_);
lean_dec(v_sz_1839_);
v_i_boxed_1848_ = lean_unbox_usize(v_i_1840_);
lean_dec(v_i_1840_);
v_res_1849_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1836_, v_argVars_1837_, v_as_1838_, v_sz_boxed_1847_, v_i_boxed_1848_, v_b_1841_, v___y_1842_, v___y_1843_, v___y_1844_, v___y_1845_);
lean_dec(v___y_1845_);
lean_dec_ref(v___y_1844_);
lean_dec(v___y_1843_);
lean_dec_ref(v___y_1842_);
lean_dec_ref(v_as_1838_);
lean_dec_ref(v_argVars_1837_);
lean_dec_ref(v_argMVars_1836_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_mvarId_1850_, lean_object* v_val_1851_, lean_object* v___y_1852_, lean_object* v___y_1853_, lean_object* v___y_1854_, lean_object* v___y_1855_){
_start:
{
lean_object* v___x_1857_; 
v___x_1857_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1850_, v_val_1851_, v___y_1853_);
return v___x_1857_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_mvarId_1858_, lean_object* v_val_1859_, lean_object* v___y_1860_, lean_object* v___y_1861_, lean_object* v___y_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_){
_start:
{
lean_object* v_res_1865_; 
v_res_1865_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_mvarId_1858_, v_val_1859_, v___y_1860_, v___y_1861_, v___y_1862_, v___y_1863_);
lean_dec(v___y_1863_);
lean_dec_ref(v___y_1862_);
lean_dec(v___y_1861_);
lean_dec_ref(v___y_1860_);
return v_res_1865_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1(lean_object* v_00_u03b2_1866_, lean_object* v_x_1867_, lean_object* v_x_1868_, lean_object* v_x_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_x_1867_, v_x_1868_, v_x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1871_, lean_object* v_x_1872_, size_t v_x_1873_, size_t v_x_1874_, lean_object* v_x_1875_, lean_object* v_x_1876_){
_start:
{
lean_object* v___x_1877_; 
v___x_1877_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1872_, v_x_1873_, v_x_1874_, v_x_1875_, v_x_1876_);
return v___x_1877_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1878_, lean_object* v_x_1879_, lean_object* v_x_1880_, lean_object* v_x_1881_, lean_object* v_x_1882_, lean_object* v_x_1883_){
_start:
{
size_t v_x_1982__boxed_1884_; size_t v_x_1983__boxed_1885_; lean_object* v_res_1886_; 
v_x_1982__boxed_1884_ = lean_unbox_usize(v_x_1880_);
lean_dec(v_x_1880_);
v_x_1983__boxed_1885_ = lean_unbox_usize(v_x_1881_);
lean_dec(v_x_1881_);
v_res_1886_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(v_00_u03b2_1878_, v_x_1879_, v_x_1982__boxed_1884_, v_x_1983__boxed_1885_, v_x_1882_, v_x_1883_);
return v_res_1886_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1887_, lean_object* v_n_1888_, lean_object* v_k_1889_, lean_object* v_v_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v_n_1888_, v_k_1889_, v_v_1890_);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1892_, size_t v_depth_1893_, lean_object* v_keys_1894_, lean_object* v_vals_1895_, lean_object* v_heq_1896_, lean_object* v_i_1897_, lean_object* v_entries_1898_){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_1893_, v_keys_1894_, v_vals_1895_, v_i_1897_, v_entries_1898_);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1900_, lean_object* v_depth_1901_, lean_object* v_keys_1902_, lean_object* v_vals_1903_, lean_object* v_heq_1904_, lean_object* v_i_1905_, lean_object* v_entries_1906_){
_start:
{
size_t v_depth_boxed_1907_; lean_object* v_res_1908_; 
v_depth_boxed_1907_ = lean_unbox_usize(v_depth_1901_);
lean_dec(v_depth_1901_);
v_res_1908_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_1900_, v_depth_boxed_1907_, v_keys_1902_, v_vals_1903_, v_heq_1904_, v_i_1905_, v_entries_1906_);
lean_dec_ref(v_vals_1903_);
lean_dec_ref(v_keys_1902_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1909_, lean_object* v_x_1910_, lean_object* v_x_1911_, lean_object* v_x_1912_, lean_object* v_x_1913_){
_start:
{
lean_object* v___x_1914_; 
v___x_1914_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1910_, v_x_1911_, v_x_1912_, v_x_1913_);
return v___x_1914_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_1915_, lean_object* v___y_1916_){
_start:
{
uint8_t v___x_1918_; 
v___x_1918_ = l_Lean_Expr_hasMVar(v_e_1915_);
if (v___x_1918_ == 0)
{
lean_object* v___x_1919_; 
v___x_1919_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1919_, 0, v_e_1915_);
return v___x_1919_;
}
else
{
lean_object* v___x_1920_; lean_object* v_mctx_1921_; lean_object* v___x_1922_; lean_object* v_fst_1923_; lean_object* v_snd_1924_; lean_object* v___x_1925_; lean_object* v_cache_1926_; lean_object* v_zetaDeltaFVarIds_1927_; lean_object* v_postponed_1928_; lean_object* v_diag_1929_; lean_object* v___x_1931_; uint8_t v_isShared_1932_; uint8_t v_isSharedCheck_1938_; 
v___x_1920_ = lean_st_ref_get(v___y_1916_);
v_mctx_1921_ = lean_ctor_get(v___x_1920_, 0);
lean_inc_ref(v_mctx_1921_);
lean_dec(v___x_1920_);
v___x_1922_ = l_Lean_instantiateMVarsCore(v_mctx_1921_, v_e_1915_);
v_fst_1923_ = lean_ctor_get(v___x_1922_, 0);
lean_inc(v_fst_1923_);
v_snd_1924_ = lean_ctor_get(v___x_1922_, 1);
lean_inc(v_snd_1924_);
lean_dec_ref(v___x_1922_);
v___x_1925_ = lean_st_ref_take(v___y_1916_);
v_cache_1926_ = lean_ctor_get(v___x_1925_, 1);
v_zetaDeltaFVarIds_1927_ = lean_ctor_get(v___x_1925_, 2);
v_postponed_1928_ = lean_ctor_get(v___x_1925_, 3);
v_diag_1929_ = lean_ctor_get(v___x_1925_, 4);
v_isSharedCheck_1938_ = !lean_is_exclusive(v___x_1925_);
if (v_isSharedCheck_1938_ == 0)
{
lean_object* v_unused_1939_; 
v_unused_1939_ = lean_ctor_get(v___x_1925_, 0);
lean_dec(v_unused_1939_);
v___x_1931_ = v___x_1925_;
v_isShared_1932_ = v_isSharedCheck_1938_;
goto v_resetjp_1930_;
}
else
{
lean_inc(v_diag_1929_);
lean_inc(v_postponed_1928_);
lean_inc(v_zetaDeltaFVarIds_1927_);
lean_inc(v_cache_1926_);
lean_dec(v___x_1925_);
v___x_1931_ = lean_box(0);
v_isShared_1932_ = v_isSharedCheck_1938_;
goto v_resetjp_1930_;
}
v_resetjp_1930_:
{
lean_object* v___x_1934_; 
if (v_isShared_1932_ == 0)
{
lean_ctor_set(v___x_1931_, 0, v_snd_1924_);
v___x_1934_ = v___x_1931_;
goto v_reusejp_1933_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_snd_1924_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_cache_1926_);
lean_ctor_set(v_reuseFailAlloc_1937_, 2, v_zetaDeltaFVarIds_1927_);
lean_ctor_set(v_reuseFailAlloc_1937_, 3, v_postponed_1928_);
lean_ctor_set(v_reuseFailAlloc_1937_, 4, v_diag_1929_);
v___x_1934_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1933_;
}
v_reusejp_1933_:
{
lean_object* v___x_1935_; lean_object* v___x_1936_; 
v___x_1935_ = lean_st_ref_set(v___y_1916_, v___x_1934_);
v___x_1936_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1936_, 0, v_fst_1923_);
return v___x_1936_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_1940_, lean_object* v___y_1941_, lean_object* v___y_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1940_, v___y_1941_);
lean_dec(v___y_1941_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_, lean_object* v___y_1947_, lean_object* v___y_1948_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1944_, v___y_1946_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_1951_, lean_object* v___y_1952_, lean_object* v___y_1953_, lean_object* v___y_1954_, lean_object* v___y_1955_, lean_object* v___y_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_1951_, v___y_1952_, v___y_1953_, v___y_1954_, v___y_1955_);
lean_dec(v___y_1955_);
lean_dec_ref(v___y_1954_);
lean_dec(v___y_1953_);
lean_dec_ref(v___y_1952_);
return v_res_1957_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_1958_, lean_object* v_opt_1959_){
_start:
{
lean_object* v_name_1960_; lean_object* v_defValue_1961_; lean_object* v_map_1962_; lean_object* v___x_1963_; 
v_name_1960_ = lean_ctor_get(v_opt_1959_, 0);
v_defValue_1961_ = lean_ctor_get(v_opt_1959_, 1);
v_map_1962_ = lean_ctor_get(v_opts_1958_, 0);
v___x_1963_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1962_, v_name_1960_);
if (lean_obj_tag(v___x_1963_) == 0)
{
uint8_t v___x_1964_; 
v___x_1964_ = lean_unbox(v_defValue_1961_);
return v___x_1964_;
}
else
{
lean_object* v_val_1965_; 
v_val_1965_ = lean_ctor_get(v___x_1963_, 0);
lean_inc(v_val_1965_);
lean_dec_ref_known(v___x_1963_, 1);
if (lean_obj_tag(v_val_1965_) == 1)
{
uint8_t v_v_1966_; 
v_v_1966_ = lean_ctor_get_uint8(v_val_1965_, 0);
lean_dec_ref_known(v_val_1965_, 0);
return v_v_1966_;
}
else
{
uint8_t v___x_1967_; 
lean_dec(v_val_1965_);
v___x_1967_ = lean_unbox(v_defValue_1961_);
return v___x_1967_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_1968_, lean_object* v_opt_1969_){
_start:
{
uint8_t v_res_1970_; lean_object* v_r_1971_; 
v_res_1970_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_1968_, v_opt_1969_);
lean_dec_ref(v_opt_1969_);
lean_dec_ref(v_opts_1968_);
v_r_1971_ = lean_box(v_res_1970_);
return v_r_1971_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_1972_, lean_object* v_as_1973_, size_t v_i_1974_, size_t v_stop_1975_){
_start:
{
uint8_t v___x_1976_; 
v___x_1976_ = lean_usize_dec_eq(v_i_1974_, v_stop_1975_);
if (v___x_1976_ == 0)
{
lean_object* v___x_1977_; uint8_t v___x_1978_; 
v___x_1977_ = lean_array_uget_borrowed(v_as_1973_, v_i_1974_);
v___x_1978_ = lean_nat_dec_eq(v_a_1972_, v___x_1977_);
if (v___x_1978_ == 0)
{
size_t v___x_1979_; size_t v___x_1980_; 
v___x_1979_ = ((size_t)1ULL);
v___x_1980_ = lean_usize_add(v_i_1974_, v___x_1979_);
v_i_1974_ = v___x_1980_;
goto _start;
}
else
{
return v___x_1978_;
}
}
else
{
uint8_t v___x_1982_; 
v___x_1982_ = 0;
return v___x_1982_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_1983_, lean_object* v_as_1984_, lean_object* v_i_1985_, lean_object* v_stop_1986_){
_start:
{
size_t v_i_boxed_1987_; size_t v_stop_boxed_1988_; uint8_t v_res_1989_; lean_object* v_r_1990_; 
v_i_boxed_1987_ = lean_unbox_usize(v_i_1985_);
lean_dec(v_i_1985_);
v_stop_boxed_1988_ = lean_unbox_usize(v_stop_1986_);
lean_dec(v_stop_1986_);
v_res_1989_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1983_, v_as_1984_, v_i_boxed_1987_, v_stop_boxed_1988_);
lean_dec_ref(v_as_1984_);
lean_dec(v_a_1983_);
v_r_1990_ = lean_box(v_res_1989_);
return v_r_1990_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_1991_, lean_object* v_a_1992_){
_start:
{
lean_object* v___x_1993_; lean_object* v___x_1994_; uint8_t v___x_1995_; 
v___x_1993_ = lean_unsigned_to_nat(0u);
v___x_1994_ = lean_array_get_size(v_as_1991_);
v___x_1995_ = lean_nat_dec_lt(v___x_1993_, v___x_1994_);
if (v___x_1995_ == 0)
{
return v___x_1995_;
}
else
{
if (v___x_1995_ == 0)
{
return v___x_1995_;
}
else
{
size_t v___x_1996_; size_t v___x_1997_; uint8_t v___x_1998_; 
v___x_1996_ = ((size_t)0ULL);
v___x_1997_ = lean_usize_of_nat(v___x_1994_);
v___x_1998_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1992_, v_as_1991_, v___x_1996_, v___x_1997_);
return v___x_1998_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_1999_, lean_object* v_a_2000_){
_start:
{
uint8_t v_res_2001_; lean_object* v_r_2002_; 
v_res_2001_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_1999_, v_a_2000_);
lean_dec(v_a_2000_);
lean_dec_ref(v_as_1999_);
v_r_2002_ = lean_box(v_res_2001_);
return v_r_2002_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_2003_, lean_object* v_fst_2004_, lean_object* v_argVars_2005_, lean_object* v_as_2006_, size_t v_sz_2007_, size_t v_i_2008_, lean_object* v_b_2009_, lean_object* v___y_2010_, lean_object* v___y_2011_, lean_object* v___y_2012_, lean_object* v___y_2013_){
_start:
{
lean_object* v_a_2016_; uint8_t v___x_2020_; 
v___x_2020_ = lean_usize_dec_lt(v_i_2008_, v_sz_2007_);
if (v___x_2020_ == 0)
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2021_, 0, v_b_2009_);
return v___x_2021_;
}
else
{
lean_object* v_next_2022_; 
v_next_2022_ = lean_ctor_get(v_b_2009_, 0);
lean_inc(v_next_2022_);
if (lean_obj_tag(v_next_2022_) == 0)
{
lean_object* v___x_2023_; 
v___x_2023_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2023_, 0, v_b_2009_);
return v___x_2023_;
}
else
{
lean_object* v_upperBound_2024_; lean_object* v_val_2025_; lean_object* v___x_2027_; uint8_t v_isShared_2028_; uint8_t v_isSharedCheck_2056_; 
v_upperBound_2024_ = lean_ctor_get(v_b_2009_, 1);
v_val_2025_ = lean_ctor_get(v_next_2022_, 0);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_next_2022_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2027_ = v_next_2022_;
v_isShared_2028_ = v_isSharedCheck_2056_;
goto v_resetjp_2026_;
}
else
{
lean_inc(v_val_2025_);
lean_dec(v_next_2022_);
v___x_2027_ = lean_box(0);
v_isShared_2028_ = v_isSharedCheck_2056_;
goto v_resetjp_2026_;
}
v_resetjp_2026_:
{
uint8_t v___x_2029_; 
v___x_2029_ = lean_nat_dec_lt(v_val_2025_, v_upperBound_2024_);
if (v___x_2029_ == 0)
{
lean_object* v___x_2030_; 
lean_del_object(v___x_2027_);
lean_dec(v_val_2025_);
v___x_2030_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2030_, 0, v_b_2009_);
return v___x_2030_;
}
else
{
lean_object* v___x_2032_; uint8_t v_isShared_2033_; uint8_t v_isSharedCheck_2053_; 
lean_inc(v_upperBound_2024_);
v_isSharedCheck_2053_ = !lean_is_exclusive(v_b_2009_);
if (v_isSharedCheck_2053_ == 0)
{
lean_object* v_unused_2054_; lean_object* v_unused_2055_; 
v_unused_2054_ = lean_ctor_get(v_b_2009_, 1);
lean_dec(v_unused_2054_);
v_unused_2055_ = lean_ctor_get(v_b_2009_, 0);
lean_dec(v_unused_2055_);
v___x_2032_ = v_b_2009_;
v_isShared_2033_ = v_isSharedCheck_2053_;
goto v_resetjp_2031_;
}
else
{
lean_dec(v_b_2009_);
v___x_2032_ = lean_box(0);
v_isShared_2033_ = v_isSharedCheck_2053_;
goto v_resetjp_2031_;
}
v_resetjp_2031_:
{
lean_object* v___x_2034_; lean_object* v___x_2035_; lean_object* v___x_2037_; 
v___x_2034_ = lean_unsigned_to_nat(1u);
v___x_2035_ = lean_nat_add(v_val_2025_, v___x_2034_);
if (v_isShared_2028_ == 0)
{
lean_ctor_set(v___x_2027_, 0, v___x_2035_);
v___x_2037_ = v___x_2027_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2052_; 
v_reuseFailAlloc_2052_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2052_, 0, v___x_2035_);
v___x_2037_ = v_reuseFailAlloc_2052_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2039_; 
if (v_isShared_2033_ == 0)
{
lean_ctor_set(v___x_2032_, 0, v___x_2037_);
v___x_2039_ = v___x_2032_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v___x_2037_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_upperBound_2024_);
v___x_2039_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
uint8_t v___x_2040_; 
v___x_2040_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2003_, v_val_2025_);
lean_dec(v_val_2025_);
if (v___x_2040_ == 0)
{
lean_object* v_a_2041_; lean_object* v___x_2042_; 
v_a_2041_ = lean_array_uget_borrowed(v_as_2006_, v_i_2008_);
lean_inc(v_a_2041_);
v___x_2042_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2004_, v_argVars_2005_, v_a_2041_, v___y_2010_, v___y_2011_, v___y_2012_, v___y_2013_);
if (lean_obj_tag(v___x_2042_) == 0)
{
lean_dec_ref_known(v___x_2042_, 1);
v_a_2016_ = v___x_2039_;
goto v___jp_2015_;
}
else
{
lean_object* v_a_2043_; lean_object* v___x_2045_; uint8_t v_isShared_2046_; uint8_t v_isSharedCheck_2050_; 
lean_dec_ref(v___x_2039_);
v_a_2043_ = lean_ctor_get(v___x_2042_, 0);
v_isSharedCheck_2050_ = !lean_is_exclusive(v___x_2042_);
if (v_isSharedCheck_2050_ == 0)
{
v___x_2045_ = v___x_2042_;
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
else
{
lean_inc(v_a_2043_);
lean_dec(v___x_2042_);
v___x_2045_ = lean_box(0);
v_isShared_2046_ = v_isSharedCheck_2050_;
goto v_resetjp_2044_;
}
v_resetjp_2044_:
{
lean_object* v___x_2048_; 
if (v_isShared_2046_ == 0)
{
v___x_2048_ = v___x_2045_;
goto v_reusejp_2047_;
}
else
{
lean_object* v_reuseFailAlloc_2049_; 
v_reuseFailAlloc_2049_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2049_, 0, v_a_2043_);
v___x_2048_ = v_reuseFailAlloc_2049_;
goto v_reusejp_2047_;
}
v_reusejp_2047_:
{
return v___x_2048_;
}
}
}
}
else
{
v_a_2016_ = v___x_2039_;
goto v___jp_2015_;
}
}
}
}
}
}
}
}
v___jp_2015_:
{
size_t v___x_2017_; size_t v___x_2018_; 
v___x_2017_ = ((size_t)1ULL);
v___x_2018_ = lean_usize_add(v_i_2008_, v___x_2017_);
v_i_2008_ = v___x_2018_;
v_b_2009_ = v_a_2016_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2057_, lean_object* v_fst_2058_, lean_object* v_argVars_2059_, lean_object* v_as_2060_, lean_object* v_sz_2061_, lean_object* v_i_2062_, lean_object* v_b_2063_, lean_object* v___y_2064_, lean_object* v___y_2065_, lean_object* v___y_2066_, lean_object* v___y_2067_, lean_object* v___y_2068_){
_start:
{
size_t v_sz_boxed_2069_; size_t v_i_boxed_2070_; lean_object* v_res_2071_; 
v_sz_boxed_2069_ = lean_unbox_usize(v_sz_2061_);
lean_dec(v_sz_2061_);
v_i_boxed_2070_ = lean_unbox_usize(v_i_2062_);
lean_dec(v_i_2062_);
v_res_2071_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2057_, v_fst_2058_, v_argVars_2059_, v_as_2060_, v_sz_boxed_2069_, v_i_boxed_2070_, v_b_2063_, v___y_2064_, v___y_2065_, v___y_2066_, v___y_2067_);
lean_dec(v___y_2067_);
lean_dec_ref(v___y_2066_);
lean_dec(v___y_2065_);
lean_dec_ref(v___y_2064_);
lean_dec_ref(v_as_2060_);
lean_dec_ref(v_argVars_2059_);
lean_dec_ref(v_fst_2058_);
lean_dec_ref(v_a_2057_);
return v_res_2071_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2072_, lean_object* v_as_2073_, size_t v_i_2074_, size_t v_stop_2075_, lean_object* v_b_2076_){
_start:
{
lean_object* v___y_2078_; uint8_t v___x_2082_; 
v___x_2082_ = lean_usize_dec_eq(v_i_2074_, v_stop_2075_);
if (v___x_2082_ == 0)
{
lean_object* v___x_2083_; uint8_t v___x_2084_; 
v___x_2083_ = lean_array_uget_borrowed(v_as_2073_, v_i_2074_);
v___x_2084_ = lean_nat_dec_eq(v___x_2083_, v_next_2072_);
if (v___x_2084_ == 0)
{
lean_object* v___x_2085_; 
lean_inc(v___x_2083_);
v___x_2085_ = lean_array_push(v_b_2076_, v___x_2083_);
v___y_2078_ = v___x_2085_;
goto v___jp_2077_;
}
else
{
v___y_2078_ = v_b_2076_;
goto v___jp_2077_;
}
}
else
{
return v_b_2076_;
}
v___jp_2077_:
{
size_t v___x_2079_; size_t v___x_2080_; 
v___x_2079_ = ((size_t)1ULL);
v___x_2080_ = lean_usize_add(v_i_2074_, v___x_2079_);
v_i_2074_ = v___x_2080_;
v_b_2076_ = v___y_2078_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2086_, lean_object* v_as_2087_, lean_object* v_i_2088_, lean_object* v_stop_2089_, lean_object* v_b_2090_){
_start:
{
size_t v_i_boxed_2091_; size_t v_stop_boxed_2092_; lean_object* v_res_2093_; 
v_i_boxed_2091_ = lean_unbox_usize(v_i_2088_);
lean_dec(v_i_2088_);
v_stop_boxed_2092_ = lean_unbox_usize(v_stop_2089_);
lean_dec(v_stop_2089_);
v_res_2093_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2086_, v_as_2087_, v_i_boxed_2091_, v_stop_boxed_2092_, v_b_2090_);
lean_dec_ref(v_as_2087_);
lean_dec(v_next_2086_);
return v_res_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object* v_fst_2094_, lean_object* v_fst_2095_, lean_object* v_argVars_2096_, lean_object* v_snd_2097_, lean_object* v_next_2098_, lean_object* v___y_2099_, lean_object* v___y_2100_, lean_object* v___y_2101_, lean_object* v___y_2102_){
_start:
{
lean_object* v___x_2104_; lean_object* v___y_2106_; lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; uint8_t v___x_2150_; 
lean_inc(v_next_2098_);
v___x_2104_ = lean_array_push(v_fst_2094_, v_next_2098_);
v___x_2147_ = lean_unsigned_to_nat(0u);
v___x_2148_ = lean_array_get_size(v_snd_2097_);
v___x_2149_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2150_ = lean_nat_dec_lt(v___x_2147_, v___x_2148_);
if (v___x_2150_ == 0)
{
v___y_2106_ = v___x_2149_;
goto v___jp_2105_;
}
else
{
uint8_t v___x_2151_; 
v___x_2151_ = lean_nat_dec_le(v___x_2148_, v___x_2148_);
if (v___x_2151_ == 0)
{
if (v___x_2150_ == 0)
{
v___y_2106_ = v___x_2149_;
goto v___jp_2105_;
}
else
{
size_t v___x_2152_; size_t v___x_2153_; lean_object* v___x_2154_; 
v___x_2152_ = ((size_t)0ULL);
v___x_2153_ = lean_usize_of_nat(v___x_2148_);
v___x_2154_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2098_, v_snd_2097_, v___x_2152_, v___x_2153_, v___x_2149_);
v___y_2106_ = v___x_2154_;
goto v___jp_2105_;
}
}
else
{
size_t v___x_2155_; size_t v___x_2156_; lean_object* v___x_2157_; 
v___x_2155_ = ((size_t)0ULL);
v___x_2156_ = lean_usize_of_nat(v___x_2148_);
v___x_2157_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2098_, v_snd_2097_, v___x_2155_, v___x_2156_, v___x_2149_);
v___y_2106_ = v___x_2157_;
goto v___jp_2105_;
}
}
v___jp_2105_:
{
lean_object* v___x_2107_; lean_object* v___x_2108_; lean_object* v___x_2109_; 
v___x_2107_ = l_Lean_instInhabitedExpr;
v___x_2108_ = lean_array_get_borrowed(v___x_2107_, v_fst_2095_, v_next_2098_);
lean_dec(v_next_2098_);
lean_inc(v___y_2102_);
lean_inc_ref(v___y_2101_);
lean_inc(v___y_2100_);
lean_inc_ref(v___y_2099_);
lean_inc(v___x_2108_);
v___x_2109_ = lean_infer_type(v___x_2108_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2109_) == 0)
{
lean_object* v_a_2110_; lean_object* v___x_2111_; 
v_a_2110_ = lean_ctor_get(v___x_2109_, 0);
lean_inc(v_a_2110_);
lean_dec_ref_known(v___x_2109_, 1);
v___x_2111_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2095_, v_argVars_2096_, v_a_2110_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2111_) == 0)
{
lean_object* v___x_2112_; 
lean_dec_ref_known(v___x_2111_, 1);
lean_inc(v___x_2108_);
v___x_2112_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2095_, v_argVars_2096_, v___x_2108_, v___y_2099_, v___y_2100_, v___y_2101_, v___y_2102_);
if (lean_obj_tag(v___x_2112_) == 0)
{
lean_object* v___x_2114_; uint8_t v_isShared_2115_; uint8_t v_isSharedCheck_2121_; 
v_isSharedCheck_2121_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2121_ == 0)
{
lean_object* v_unused_2122_; 
v_unused_2122_ = lean_ctor_get(v___x_2112_, 0);
lean_dec(v_unused_2122_);
v___x_2114_ = v___x_2112_;
v_isShared_2115_ = v_isSharedCheck_2121_;
goto v_resetjp_2113_;
}
else
{
lean_dec(v___x_2112_);
v___x_2114_ = lean_box(0);
v_isShared_2115_ = v_isSharedCheck_2121_;
goto v_resetjp_2113_;
}
v_resetjp_2113_:
{
lean_object* v___x_2116_; lean_object* v___x_2117_; lean_object* v___x_2119_; 
v___x_2116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2116_, 0, v___x_2104_);
lean_ctor_set(v___x_2116_, 1, v___y_2106_);
v___x_2117_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2117_, 0, v___x_2116_);
if (v_isShared_2115_ == 0)
{
lean_ctor_set(v___x_2114_, 0, v___x_2117_);
v___x_2119_ = v___x_2114_;
goto v_reusejp_2118_;
}
else
{
lean_object* v_reuseFailAlloc_2120_; 
v_reuseFailAlloc_2120_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2120_, 0, v___x_2117_);
v___x_2119_ = v_reuseFailAlloc_2120_;
goto v_reusejp_2118_;
}
v_reusejp_2118_:
{
return v___x_2119_;
}
}
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2125_; uint8_t v_isShared_2126_; uint8_t v_isSharedCheck_2130_; 
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___x_2104_);
v_a_2123_ = lean_ctor_get(v___x_2112_, 0);
v_isSharedCheck_2130_ = !lean_is_exclusive(v___x_2112_);
if (v_isSharedCheck_2130_ == 0)
{
v___x_2125_ = v___x_2112_;
v_isShared_2126_ = v_isSharedCheck_2130_;
goto v_resetjp_2124_;
}
else
{
lean_inc(v_a_2123_);
lean_dec(v___x_2112_);
v___x_2125_ = lean_box(0);
v_isShared_2126_ = v_isSharedCheck_2130_;
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
lean_object* v_reuseFailAlloc_2129_; 
v_reuseFailAlloc_2129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2129_, 0, v_a_2123_);
v___x_2128_ = v_reuseFailAlloc_2129_;
goto v_reusejp_2127_;
}
v_reusejp_2127_:
{
return v___x_2128_;
}
}
}
}
else
{
lean_object* v_a_2131_; lean_object* v___x_2133_; uint8_t v_isShared_2134_; uint8_t v_isSharedCheck_2138_; 
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___x_2104_);
v_a_2131_ = lean_ctor_get(v___x_2111_, 0);
v_isSharedCheck_2138_ = !lean_is_exclusive(v___x_2111_);
if (v_isSharedCheck_2138_ == 0)
{
v___x_2133_ = v___x_2111_;
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
else
{
lean_inc(v_a_2131_);
lean_dec(v___x_2111_);
v___x_2133_ = lean_box(0);
v_isShared_2134_ = v_isSharedCheck_2138_;
goto v_resetjp_2132_;
}
v_resetjp_2132_:
{
lean_object* v___x_2136_; 
if (v_isShared_2134_ == 0)
{
v___x_2136_ = v___x_2133_;
goto v_reusejp_2135_;
}
else
{
lean_object* v_reuseFailAlloc_2137_; 
v_reuseFailAlloc_2137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2137_, 0, v_a_2131_);
v___x_2136_ = v_reuseFailAlloc_2137_;
goto v_reusejp_2135_;
}
v_reusejp_2135_:
{
return v___x_2136_;
}
}
}
}
else
{
lean_object* v_a_2139_; lean_object* v___x_2141_; uint8_t v_isShared_2142_; uint8_t v_isSharedCheck_2146_; 
lean_dec_ref(v___y_2106_);
lean_dec_ref(v___x_2104_);
v_a_2139_ = lean_ctor_get(v___x_2109_, 0);
v_isSharedCheck_2146_ = !lean_is_exclusive(v___x_2109_);
if (v_isSharedCheck_2146_ == 0)
{
v___x_2141_ = v___x_2109_;
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
else
{
lean_inc(v_a_2139_);
lean_dec(v___x_2109_);
v___x_2141_ = lean_box(0);
v_isShared_2142_ = v_isSharedCheck_2146_;
goto v_resetjp_2140_;
}
v_resetjp_2140_:
{
lean_object* v___x_2144_; 
if (v_isShared_2142_ == 0)
{
v___x_2144_ = v___x_2141_;
goto v_reusejp_2143_;
}
else
{
lean_object* v_reuseFailAlloc_2145_; 
v_reuseFailAlloc_2145_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2145_, 0, v_a_2139_);
v___x_2144_ = v_reuseFailAlloc_2145_;
goto v_reusejp_2143_;
}
v_reusejp_2143_:
{
return v___x_2144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object* v_fst_2158_, lean_object* v_fst_2159_, lean_object* v_argVars_2160_, lean_object* v_snd_2161_, lean_object* v_next_2162_, lean_object* v___y_2163_, lean_object* v___y_2164_, lean_object* v___y_2165_, lean_object* v___y_2166_, lean_object* v___y_2167_){
_start:
{
lean_object* v_res_2168_; 
v_res_2168_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2158_, v_fst_2159_, v_argVars_2160_, v_snd_2161_, v_next_2162_, v___y_2163_, v___y_2164_, v___y_2165_, v___y_2166_);
lean_dec(v___y_2166_);
lean_dec_ref(v___y_2165_);
lean_dec(v___y_2164_);
lean_dec_ref(v___y_2163_);
lean_dec(v_snd_2161_);
lean_dec_ref(v_argVars_2160_);
lean_dec_ref(v_fst_2159_);
return v_res_2168_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2169_, lean_object* v___x_2170_, lean_object* v_a_2171_, lean_object* v_a_2172_, lean_object* v_b_2173_){
_start:
{
uint8_t v___x_2175_; 
v___x_2175_ = lean_nat_dec_lt(v_a_2172_, v_upperBound_2169_);
if (v___x_2175_ == 0)
{
lean_object* v___x_2176_; 
lean_dec(v_a_2172_);
v___x_2176_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2176_, 0, v_b_2173_);
return v___x_2176_;
}
else
{
lean_object* v_snd_2177_; lean_object* v___x_2179_; uint8_t v_isShared_2180_; uint8_t v_isSharedCheck_2218_; 
v_snd_2177_ = lean_ctor_get(v_b_2173_, 1);
v_isSharedCheck_2218_ = !lean_is_exclusive(v_b_2173_);
if (v_isSharedCheck_2218_ == 0)
{
lean_object* v_unused_2219_; 
v_unused_2219_ = lean_ctor_get(v_b_2173_, 0);
lean_dec(v_unused_2219_);
v___x_2179_ = v_b_2173_;
v_isShared_2180_ = v_isSharedCheck_2218_;
goto v_resetjp_2178_;
}
else
{
lean_inc(v_snd_2177_);
lean_dec(v_b_2173_);
v___x_2179_ = lean_box(0);
v_isShared_2180_ = v_isSharedCheck_2218_;
goto v_resetjp_2178_;
}
v_resetjp_2178_:
{
lean_object* v_array_2181_; lean_object* v_start_2182_; lean_object* v_stop_2183_; lean_object* v___x_2184_; uint8_t v___x_2185_; 
v_array_2181_ = lean_ctor_get(v_snd_2177_, 0);
v_start_2182_ = lean_ctor_get(v_snd_2177_, 1);
v_stop_2183_ = lean_ctor_get(v_snd_2177_, 2);
v___x_2184_ = lean_box(0);
v___x_2185_ = lean_nat_dec_lt(v_start_2182_, v_stop_2183_);
if (v___x_2185_ == 0)
{
lean_object* v___x_2187_; 
lean_dec(v_a_2172_);
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 0, v___x_2184_);
v___x_2187_ = v___x_2179_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2189_; 
v_reuseFailAlloc_2189_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2189_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2189_, 1, v_snd_2177_);
v___x_2187_ = v_reuseFailAlloc_2189_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2188_; 
v___x_2188_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2188_, 0, v___x_2187_);
return v___x_2188_;
}
}
else
{
lean_object* v___x_2191_; uint8_t v_isShared_2192_; uint8_t v_isSharedCheck_2214_; 
lean_inc(v_stop_2183_);
lean_inc(v_start_2182_);
lean_inc_ref(v_array_2181_);
v_isSharedCheck_2214_ = !lean_is_exclusive(v_snd_2177_);
if (v_isSharedCheck_2214_ == 0)
{
lean_object* v_unused_2215_; lean_object* v_unused_2216_; lean_object* v_unused_2217_; 
v_unused_2215_ = lean_ctor_get(v_snd_2177_, 2);
lean_dec(v_unused_2215_);
v_unused_2216_ = lean_ctor_get(v_snd_2177_, 1);
lean_dec(v_unused_2216_);
v_unused_2217_ = lean_ctor_get(v_snd_2177_, 0);
lean_dec(v_unused_2217_);
v___x_2191_ = v_snd_2177_;
v_isShared_2192_ = v_isSharedCheck_2214_;
goto v_resetjp_2190_;
}
else
{
lean_dec(v_snd_2177_);
v___x_2191_ = lean_box(0);
v_isShared_2192_ = v_isSharedCheck_2214_;
goto v_resetjp_2190_;
}
v_resetjp_2190_:
{
lean_object* v___x_2193_; uint8_t v___x_2194_; lean_object* v___x_2195_; lean_object* v___x_2196_; lean_object* v___x_2197_; lean_object* v___x_2199_; 
v___x_2193_ = lean_unsigned_to_nat(0u);
v___x_2194_ = lean_nat_dec_eq(v___x_2170_, v___x_2193_);
v___x_2195_ = lean_array_fget(v_array_2181_, v_start_2182_);
v___x_2196_ = lean_unsigned_to_nat(1u);
v___x_2197_ = lean_nat_add(v_start_2182_, v___x_2196_);
lean_dec(v_start_2182_);
if (v_isShared_2192_ == 0)
{
lean_ctor_set(v___x_2191_, 1, v___x_2197_);
v___x_2199_ = v___x_2191_;
goto v_reusejp_2198_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_array_2181_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v___x_2197_);
lean_ctor_set(v_reuseFailAlloc_2213_, 2, v_stop_2183_);
v___x_2199_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2198_;
}
v_reusejp_2198_:
{
uint8_t v___x_2212_; 
v___x_2212_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2171_, v_a_2172_);
if (v___x_2212_ == 0)
{
goto v___jp_2206_;
}
else
{
if (v___x_2194_ == 0)
{
lean_dec(v___x_2195_);
goto v___jp_2200_;
}
else
{
goto v___jp_2206_;
}
}
v___jp_2200_:
{
lean_object* v___x_2202_; 
if (v_isShared_2180_ == 0)
{
lean_ctor_set(v___x_2179_, 1, v___x_2199_);
lean_ctor_set(v___x_2179_, 0, v___x_2184_);
v___x_2202_ = v___x_2179_;
goto v_reusejp_2201_;
}
else
{
lean_object* v_reuseFailAlloc_2205_; 
v_reuseFailAlloc_2205_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2205_, 0, v___x_2184_);
lean_ctor_set(v_reuseFailAlloc_2205_, 1, v___x_2199_);
v___x_2202_ = v_reuseFailAlloc_2205_;
goto v_reusejp_2201_;
}
v_reusejp_2201_:
{
lean_object* v___x_2203_; 
v___x_2203_ = lean_nat_add(v_a_2172_, v___x_2196_);
lean_dec(v_a_2172_);
v_a_2172_ = v___x_2203_;
v_b_2173_ = v___x_2202_;
goto _start;
}
}
v___jp_2206_:
{
uint8_t v___x_2207_; 
v___x_2207_ = l_Lean_Expr_hasExprMVar(v___x_2195_);
lean_dec(v___x_2195_);
if (v___x_2207_ == 0)
{
goto v___jp_2200_;
}
else
{
lean_object* v___x_2208_; lean_object* v___x_2209_; lean_object* v___x_2210_; lean_object* v___x_2211_; 
lean_del_object(v___x_2179_);
lean_dec(v_a_2172_);
v___x_2208_ = lean_box(v___x_2194_);
v___x_2209_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2209_, 0, v___x_2208_);
v___x_2210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
lean_ctor_set(v___x_2210_, 1, v___x_2199_);
v___x_2211_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2211_, 0, v___x_2210_);
return v___x_2211_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2220_, lean_object* v___x_2221_, lean_object* v_a_2222_, lean_object* v_a_2223_, lean_object* v_b_2224_, lean_object* v___y_2225_){
_start:
{
lean_object* v_res_2226_; 
v_res_2226_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2220_, v___x_2221_, v_a_2222_, v_a_2223_, v_b_2224_);
lean_dec_ref(v_a_2222_);
lean_dec(v___x_2221_);
lean_dec(v_upperBound_2220_);
return v_res_2226_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2227_; lean_object* v_dummy_2228_; 
v___x_2227_ = lean_box(0);
v_dummy_2228_ = l_Lean_Expr_sort___override(v___x_2227_);
return v_dummy_2228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2229_, lean_object* v___x_2230_, uint8_t v___x_2231_, lean_object* v_x_2232_, lean_object* v_argTy_2233_, lean_object* v___y_2234_, lean_object* v___y_2235_, lean_object* v___y_2236_, lean_object* v___y_2237_){
_start:
{
lean_object* v___x_2239_; 
lean_inc(v___y_2237_);
lean_inc_ref(v___y_2236_);
lean_inc(v___y_2235_);
lean_inc_ref(v___y_2234_);
v___x_2239_ = lean_whnf(v_argTy_2233_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
if (lean_obj_tag(v___x_2239_) == 0)
{
lean_object* v_a_2240_; lean_object* v___x_2241_; 
v_a_2240_ = lean_ctor_get(v___x_2239_, 0);
lean_inc(v_a_2240_);
lean_dec_ref_known(v___x_2239_, 1);
v___x_2241_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2240_, v___y_2234_, v___y_2235_, v___y_2236_, v___y_2237_);
if (lean_obj_tag(v___x_2241_) == 0)
{
lean_object* v_a_2242_; lean_object* v_dummy_2243_; lean_object* v_nargs_2244_; lean_object* v___x_2245_; lean_object* v___x_2246_; lean_object* v___x_2247_; lean_object* v___x_2248_; lean_object* v___x_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; 
v_a_2242_ = lean_ctor_get(v___x_2241_, 0);
lean_inc(v_a_2242_);
lean_dec_ref_known(v___x_2241_, 1);
v_dummy_2243_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2244_ = l_Lean_Expr_getAppNumArgs(v_a_2240_);
lean_inc(v_nargs_2244_);
v___x_2245_ = lean_mk_array(v_nargs_2244_, v_dummy_2243_);
v___x_2246_ = lean_unsigned_to_nat(1u);
v___x_2247_ = lean_nat_sub(v_nargs_2244_, v___x_2246_);
lean_dec(v_nargs_2244_);
v___x_2248_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2240_, v___x_2245_, v___x_2247_);
v___x_2249_ = lean_array_get_size(v___x_2248_);
lean_inc(v___x_2229_);
v___x_2250_ = l_Array_toSubarray___redArg(v___x_2248_, v___x_2229_, v___x_2249_);
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2252_, 0, v___x_2251_);
lean_ctor_set(v___x_2252_, 1, v___x_2250_);
v___x_2253_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2249_, v___x_2230_, v_a_2242_, v___x_2229_, v___x_2252_);
lean_dec(v_a_2242_);
if (lean_obj_tag(v___x_2253_) == 0)
{
lean_object* v_a_2254_; lean_object* v___x_2256_; uint8_t v_isShared_2257_; uint8_t v_isSharedCheck_2267_; 
v_a_2254_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2267_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2267_ == 0)
{
v___x_2256_ = v___x_2253_;
v_isShared_2257_ = v_isSharedCheck_2267_;
goto v_resetjp_2255_;
}
else
{
lean_inc(v_a_2254_);
lean_dec(v___x_2253_);
v___x_2256_ = lean_box(0);
v_isShared_2257_ = v_isSharedCheck_2267_;
goto v_resetjp_2255_;
}
v_resetjp_2255_:
{
lean_object* v_fst_2258_; 
v_fst_2258_ = lean_ctor_get(v_a_2254_, 0);
lean_inc(v_fst_2258_);
lean_dec(v_a_2254_);
if (lean_obj_tag(v_fst_2258_) == 0)
{
lean_object* v___x_2259_; lean_object* v___x_2261_; 
v___x_2259_ = lean_box(v___x_2231_);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v___x_2259_);
v___x_2261_ = v___x_2256_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
else
{
lean_object* v_val_2263_; lean_object* v___x_2265_; 
v_val_2263_ = lean_ctor_get(v_fst_2258_, 0);
lean_inc(v_val_2263_);
lean_dec_ref_known(v_fst_2258_, 1);
if (v_isShared_2257_ == 0)
{
lean_ctor_set(v___x_2256_, 0, v_val_2263_);
v___x_2265_ = v___x_2256_;
goto v_reusejp_2264_;
}
else
{
lean_object* v_reuseFailAlloc_2266_; 
v_reuseFailAlloc_2266_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2266_, 0, v_val_2263_);
v___x_2265_ = v_reuseFailAlloc_2266_;
goto v_reusejp_2264_;
}
v_reusejp_2264_:
{
return v___x_2265_;
}
}
}
}
else
{
lean_object* v_a_2268_; lean_object* v___x_2270_; uint8_t v_isShared_2271_; uint8_t v_isSharedCheck_2275_; 
v_a_2268_ = lean_ctor_get(v___x_2253_, 0);
v_isSharedCheck_2275_ = !lean_is_exclusive(v___x_2253_);
if (v_isSharedCheck_2275_ == 0)
{
v___x_2270_ = v___x_2253_;
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
else
{
lean_inc(v_a_2268_);
lean_dec(v___x_2253_);
v___x_2270_ = lean_box(0);
v_isShared_2271_ = v_isSharedCheck_2275_;
goto v_resetjp_2269_;
}
v_resetjp_2269_:
{
lean_object* v___x_2273_; 
if (v_isShared_2271_ == 0)
{
v___x_2273_ = v___x_2270_;
goto v_reusejp_2272_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_a_2268_);
v___x_2273_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2272_;
}
v_reusejp_2272_:
{
return v___x_2273_;
}
}
}
}
else
{
lean_object* v_a_2276_; lean_object* v___x_2278_; uint8_t v_isShared_2279_; uint8_t v_isSharedCheck_2283_; 
lean_dec(v_a_2240_);
lean_dec(v___x_2229_);
v_a_2276_ = lean_ctor_get(v___x_2241_, 0);
v_isSharedCheck_2283_ = !lean_is_exclusive(v___x_2241_);
if (v_isSharedCheck_2283_ == 0)
{
v___x_2278_ = v___x_2241_;
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
else
{
lean_inc(v_a_2276_);
lean_dec(v___x_2241_);
v___x_2278_ = lean_box(0);
v_isShared_2279_ = v_isSharedCheck_2283_;
goto v_resetjp_2277_;
}
v_resetjp_2277_:
{
lean_object* v___x_2281_; 
if (v_isShared_2279_ == 0)
{
v___x_2281_ = v___x_2278_;
goto v_reusejp_2280_;
}
else
{
lean_object* v_reuseFailAlloc_2282_; 
v_reuseFailAlloc_2282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2282_, 0, v_a_2276_);
v___x_2281_ = v_reuseFailAlloc_2282_;
goto v_reusejp_2280_;
}
v_reusejp_2280_:
{
return v___x_2281_;
}
}
}
}
else
{
lean_object* v_a_2284_; lean_object* v___x_2286_; uint8_t v_isShared_2287_; uint8_t v_isSharedCheck_2291_; 
lean_dec(v___x_2229_);
v_a_2284_ = lean_ctor_get(v___x_2239_, 0);
v_isSharedCheck_2291_ = !lean_is_exclusive(v___x_2239_);
if (v_isSharedCheck_2291_ == 0)
{
v___x_2286_ = v___x_2239_;
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
else
{
lean_inc(v_a_2284_);
lean_dec(v___x_2239_);
v___x_2286_ = lean_box(0);
v_isShared_2287_ = v_isSharedCheck_2291_;
goto v_resetjp_2285_;
}
v_resetjp_2285_:
{
lean_object* v___x_2289_; 
if (v_isShared_2287_ == 0)
{
v___x_2289_ = v___x_2286_;
goto v_reusejp_2288_;
}
else
{
lean_object* v_reuseFailAlloc_2290_; 
v_reuseFailAlloc_2290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2290_, 0, v_a_2284_);
v___x_2289_ = v_reuseFailAlloc_2290_;
goto v_reusejp_2288_;
}
v_reusejp_2288_:
{
return v___x_2289_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2292_, lean_object* v___x_2293_, lean_object* v___x_2294_, lean_object* v_x_2295_, lean_object* v_argTy_2296_, lean_object* v___y_2297_, lean_object* v___y_2298_, lean_object* v___y_2299_, lean_object* v___y_2300_, lean_object* v___y_2301_){
_start:
{
uint8_t v___x_26128__boxed_2302_; lean_object* v_res_2303_; 
v___x_26128__boxed_2302_ = lean_unbox(v___x_2294_);
v_res_2303_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2292_, v___x_2293_, v___x_26128__boxed_2302_, v_x_2295_, v_argTy_2296_, v___y_2297_, v___y_2298_, v___y_2299_, v___y_2300_);
lean_dec(v___y_2300_);
lean_dec_ref(v___y_2299_);
lean_dec(v___y_2298_);
lean_dec_ref(v___y_2297_);
lean_dec_ref(v_x_2295_);
lean_dec(v___x_2293_);
return v_res_2303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2307_, lean_object* v_projInfo_x3f_2308_, lean_object* v___x_2309_, lean_object* v_argVars_2310_, lean_object* v_as_2311_, size_t v_sz_2312_, size_t v_i_2313_, lean_object* v_b_2314_, lean_object* v___y_2315_, lean_object* v___y_2316_, lean_object* v___y_2317_, lean_object* v___y_2318_){
_start:
{
uint8_t v___x_2320_; 
v___x_2320_ = lean_usize_dec_lt(v_i_2313_, v_sz_2312_);
if (v___x_2320_ == 0)
{
lean_object* v___x_2321_; 
lean_dec(v___x_2309_);
v___x_2321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2321_, 0, v_b_2314_);
return v___x_2321_;
}
else
{
lean_object* v_a_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; lean_object* v___x_2325_; 
lean_dec_ref(v_b_2314_);
v_a_2322_ = lean_array_uget_borrowed(v_as_2311_, v_i_2313_);
v___x_2323_ = l_Lean_instInhabitedExpr;
v___x_2324_ = lean_array_get_borrowed(v___x_2323_, v_fst_2307_, v_a_2322_);
lean_inc(v___y_2318_);
lean_inc_ref(v___y_2317_);
lean_inc(v___y_2316_);
lean_inc_ref(v___y_2315_);
lean_inc(v___x_2324_);
v___x_2325_ = lean_infer_type(v___x_2324_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2325_) == 0)
{
lean_object* v_a_2326_; lean_object* v___x_2327_; 
v_a_2326_ = lean_ctor_get(v___x_2325_, 0);
lean_inc(v_a_2326_);
lean_dec_ref_known(v___x_2325_, 1);
v___x_2327_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2326_, v___y_2316_);
if (lean_obj_tag(v___x_2327_) == 0)
{
lean_object* v_a_2328_; lean_object* v___x_2330_; uint8_t v_isShared_2331_; uint8_t v_isSharedCheck_2374_; 
v_a_2328_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2374_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2374_ == 0)
{
v___x_2330_ = v___x_2327_;
v_isShared_2331_ = v_isSharedCheck_2374_;
goto v_resetjp_2329_;
}
else
{
lean_inc(v_a_2328_);
lean_dec(v___x_2327_);
v___x_2330_ = lean_box(0);
v_isShared_2331_ = v_isSharedCheck_2374_;
goto v_resetjp_2329_;
}
v_resetjp_2329_:
{
lean_object* v___x_2332_; lean_object* v___x_2340_; lean_object* v___y_2342_; lean_object* v___x_2356_; lean_object* v___x_2357_; lean_object* v___f_2358_; uint8_t v___x_2359_; 
v___x_2332_ = lean_box(0);
v___x_2340_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2356_ = lean_unsigned_to_nat(0u);
v___x_2357_ = lean_box(v___x_2320_);
lean_inc(v___x_2309_);
v___f_2358_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 10, 3);
lean_closure_set(v___f_2358_, 0, v___x_2356_);
lean_closure_set(v___f_2358_, 1, v___x_2309_);
lean_closure_set(v___f_2358_, 2, v___x_2357_);
v___x_2359_ = lean_nat_dec_eq(v___x_2309_, v___x_2356_);
if (lean_obj_tag(v_projInfo_x3f_2308_) == 1)
{
lean_object* v_val_2360_; lean_object* v_numParams_2361_; uint8_t v___x_2362_; 
v_val_2360_ = lean_ctor_get(v_projInfo_x3f_2308_, 0);
v_numParams_2361_ = lean_ctor_get(v_val_2360_, 1);
v___x_2362_ = lean_nat_dec_eq(v_numParams_2361_, v_a_2322_);
if (v___x_2362_ == 0)
{
lean_object* v___x_2363_; 
v___x_2363_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2328_, v___f_2358_, v___x_2359_, v___x_2359_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
v___y_2342_ = v___x_2363_;
goto v___jp_2341_;
}
else
{
lean_object* v___x_2364_; 
lean_dec_ref(v___f_2358_);
lean_dec(v___x_2309_);
v___x_2364_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2307_, v_argVars_2310_, v_a_2328_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
if (lean_obj_tag(v___x_2364_) == 0)
{
lean_dec_ref_known(v___x_2364_, 1);
goto v___jp_2333_;
}
else
{
lean_object* v_a_2365_; lean_object* v___x_2367_; uint8_t v_isShared_2368_; uint8_t v_isSharedCheck_2372_; 
lean_del_object(v___x_2330_);
v_a_2365_ = lean_ctor_get(v___x_2364_, 0);
v_isSharedCheck_2372_ = !lean_is_exclusive(v___x_2364_);
if (v_isSharedCheck_2372_ == 0)
{
v___x_2367_ = v___x_2364_;
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
else
{
lean_inc(v_a_2365_);
lean_dec(v___x_2364_);
v___x_2367_ = lean_box(0);
v_isShared_2368_ = v_isSharedCheck_2372_;
goto v_resetjp_2366_;
}
v_resetjp_2366_:
{
lean_object* v___x_2370_; 
if (v_isShared_2368_ == 0)
{
v___x_2370_ = v___x_2367_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2371_; 
v_reuseFailAlloc_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2371_, 0, v_a_2365_);
v___x_2370_ = v_reuseFailAlloc_2371_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
return v___x_2370_;
}
}
}
}
}
else
{
lean_object* v___x_2373_; 
v___x_2373_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2328_, v___f_2358_, v___x_2359_, v___x_2359_, v___y_2315_, v___y_2316_, v___y_2317_, v___y_2318_);
v___y_2342_ = v___x_2373_;
goto v___jp_2341_;
}
v___jp_2333_:
{
lean_object* v___x_2334_; lean_object* v___x_2335_; lean_object* v___x_2336_; lean_object* v___x_2338_; 
lean_inc(v_a_2322_);
v___x_2334_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2334_, 0, v_a_2322_);
v___x_2335_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2335_, 0, v___x_2334_);
v___x_2336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2336_, 0, v___x_2335_);
lean_ctor_set(v___x_2336_, 1, v___x_2332_);
if (v_isShared_2331_ == 0)
{
lean_ctor_set(v___x_2330_, 0, v___x_2336_);
v___x_2338_ = v___x_2330_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2339_; 
v_reuseFailAlloc_2339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2339_, 0, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2339_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
return v___x_2338_;
}
}
v___jp_2341_:
{
if (lean_obj_tag(v___y_2342_) == 0)
{
lean_object* v_a_2343_; uint8_t v___x_2344_; 
v_a_2343_ = lean_ctor_get(v___y_2342_, 0);
lean_inc(v_a_2343_);
lean_dec_ref_known(v___y_2342_, 1);
v___x_2344_ = lean_unbox(v_a_2343_);
lean_dec(v_a_2343_);
if (v___x_2344_ == 0)
{
size_t v___x_2345_; size_t v___x_2346_; 
lean_del_object(v___x_2330_);
v___x_2345_ = ((size_t)1ULL);
v___x_2346_ = lean_usize_add(v_i_2313_, v___x_2345_);
v_i_2313_ = v___x_2346_;
v_b_2314_ = v___x_2340_;
goto _start;
}
else
{
lean_dec(v___x_2309_);
goto v___jp_2333_;
}
}
else
{
lean_object* v_a_2348_; lean_object* v___x_2350_; uint8_t v_isShared_2351_; uint8_t v_isSharedCheck_2355_; 
lean_del_object(v___x_2330_);
lean_dec(v___x_2309_);
v_a_2348_ = lean_ctor_get(v___y_2342_, 0);
v_isSharedCheck_2355_ = !lean_is_exclusive(v___y_2342_);
if (v_isSharedCheck_2355_ == 0)
{
v___x_2350_ = v___y_2342_;
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
else
{
lean_inc(v_a_2348_);
lean_dec(v___y_2342_);
v___x_2350_ = lean_box(0);
v_isShared_2351_ = v_isSharedCheck_2355_;
goto v_resetjp_2349_;
}
v_resetjp_2349_:
{
lean_object* v___x_2353_; 
if (v_isShared_2351_ == 0)
{
v___x_2353_ = v___x_2350_;
goto v_reusejp_2352_;
}
else
{
lean_object* v_reuseFailAlloc_2354_; 
v_reuseFailAlloc_2354_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2354_, 0, v_a_2348_);
v___x_2353_ = v_reuseFailAlloc_2354_;
goto v_reusejp_2352_;
}
v_reusejp_2352_:
{
return v___x_2353_;
}
}
}
}
}
}
else
{
lean_object* v_a_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2382_; 
lean_dec(v___x_2309_);
v_a_2375_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2382_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2382_ == 0)
{
v___x_2377_ = v___x_2327_;
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_a_2375_);
lean_dec(v___x_2327_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2382_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v___x_2380_; 
if (v_isShared_2378_ == 0)
{
v___x_2380_ = v___x_2377_;
goto v_reusejp_2379_;
}
else
{
lean_object* v_reuseFailAlloc_2381_; 
v_reuseFailAlloc_2381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2381_, 0, v_a_2375_);
v___x_2380_ = v_reuseFailAlloc_2381_;
goto v_reusejp_2379_;
}
v_reusejp_2379_:
{
return v___x_2380_;
}
}
}
}
else
{
lean_object* v_a_2383_; lean_object* v___x_2385_; uint8_t v_isShared_2386_; uint8_t v_isSharedCheck_2390_; 
lean_dec(v___x_2309_);
v_a_2383_ = lean_ctor_get(v___x_2325_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2325_);
if (v_isSharedCheck_2390_ == 0)
{
v___x_2385_ = v___x_2325_;
v_isShared_2386_ = v_isSharedCheck_2390_;
goto v_resetjp_2384_;
}
else
{
lean_inc(v_a_2383_);
lean_dec(v___x_2325_);
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
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2391_, lean_object* v_projInfo_x3f_2392_, lean_object* v___x_2393_, lean_object* v_argVars_2394_, lean_object* v_as_2395_, lean_object* v_sz_2396_, lean_object* v_i_2397_, lean_object* v_b_2398_, lean_object* v___y_2399_, lean_object* v___y_2400_, lean_object* v___y_2401_, lean_object* v___y_2402_, lean_object* v___y_2403_){
_start:
{
size_t v_sz_boxed_2404_; size_t v_i_boxed_2405_; lean_object* v_res_2406_; 
v_sz_boxed_2404_ = lean_unbox_usize(v_sz_2396_);
lean_dec(v_sz_2396_);
v_i_boxed_2405_ = lean_unbox_usize(v_i_2397_);
lean_dec(v_i_2397_);
v_res_2406_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2391_, v_projInfo_x3f_2392_, v___x_2393_, v_argVars_2394_, v_as_2395_, v_sz_boxed_2404_, v_i_boxed_2405_, v_b_2398_, v___y_2399_, v___y_2400_, v___y_2401_, v___y_2402_);
lean_dec(v___y_2402_);
lean_dec_ref(v___y_2401_);
lean_dec(v___y_2400_);
lean_dec_ref(v___y_2399_);
lean_dec_ref(v_as_2395_);
lean_dec_ref(v_argVars_2394_);
lean_dec(v_projInfo_x3f_2392_);
lean_dec_ref(v_fst_2391_);
return v_res_2406_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2407_, lean_object* v___y_2408_, lean_object* v___y_2409_, lean_object* v___y_2410_, lean_object* v___y_2411_){
_start:
{
lean_object* v___x_2413_; lean_object* v_env_2414_; lean_object* v___x_2415_; lean_object* v_mctx_2416_; lean_object* v_lctx_2417_; lean_object* v_options_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; lean_object* v___x_2421_; 
v___x_2413_ = lean_st_ref_get(v___y_2411_);
v_env_2414_ = lean_ctor_get(v___x_2413_, 0);
lean_inc_ref(v_env_2414_);
lean_dec(v___x_2413_);
v___x_2415_ = lean_st_ref_get(v___y_2409_);
v_mctx_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc_ref(v_mctx_2416_);
lean_dec(v___x_2415_);
v_lctx_2417_ = lean_ctor_get(v___y_2408_, 2);
v_options_2418_ = lean_ctor_get(v___y_2410_, 2);
lean_inc_ref(v_options_2418_);
lean_inc_ref(v_lctx_2417_);
v___x_2419_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2419_, 0, v_env_2414_);
lean_ctor_set(v___x_2419_, 1, v_mctx_2416_);
lean_ctor_set(v___x_2419_, 2, v_lctx_2417_);
lean_ctor_set(v___x_2419_, 3, v_options_2418_);
v___x_2420_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2420_, 0, v___x_2419_);
lean_ctor_set(v___x_2420_, 1, v_msgData_2407_);
v___x_2421_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2421_, 0, v___x_2420_);
return v___x_2421_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
lean_object* v_res_2428_; 
v_res_2428_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
return v_res_2428_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2429_, lean_object* v___y_2430_, lean_object* v___y_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_){
_start:
{
lean_object* v_ref_2435_; lean_object* v___x_2436_; lean_object* v_a_2437_; lean_object* v___x_2439_; uint8_t v_isShared_2440_; uint8_t v_isSharedCheck_2445_; 
v_ref_2435_ = lean_ctor_get(v___y_2432_, 5);
v___x_2436_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2429_, v___y_2430_, v___y_2431_, v___y_2432_, v___y_2433_);
v_a_2437_ = lean_ctor_get(v___x_2436_, 0);
v_isSharedCheck_2445_ = !lean_is_exclusive(v___x_2436_);
if (v_isSharedCheck_2445_ == 0)
{
v___x_2439_ = v___x_2436_;
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
else
{
lean_inc(v_a_2437_);
lean_dec(v___x_2436_);
v___x_2439_ = lean_box(0);
v_isShared_2440_ = v_isSharedCheck_2445_;
goto v_resetjp_2438_;
}
v_resetjp_2438_:
{
lean_object* v___x_2441_; lean_object* v___x_2443_; 
lean_inc(v_ref_2435_);
v___x_2441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2441_, 0, v_ref_2435_);
lean_ctor_set(v___x_2441_, 1, v_a_2437_);
if (v_isShared_2440_ == 0)
{
lean_ctor_set_tag(v___x_2439_, 1);
lean_ctor_set(v___x_2439_, 0, v___x_2441_);
v___x_2443_ = v___x_2439_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v___x_2441_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2453_, size_t v_sz_2454_, size_t v_i_2455_, lean_object* v_bs_2456_, lean_object* v___y_2457_, lean_object* v___y_2458_, lean_object* v___y_2459_, lean_object* v___y_2460_){
_start:
{
uint8_t v___x_2462_; 
v___x_2462_ = lean_usize_dec_lt(v_i_2455_, v_sz_2454_);
if (v___x_2462_ == 0)
{
lean_object* v___x_2463_; 
v___x_2463_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2463_, 0, v_bs_2456_);
return v___x_2463_;
}
else
{
lean_object* v_v_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; lean_object* v___x_2467_; 
v_v_2464_ = lean_array_uget_borrowed(v_bs_2456_, v_i_2455_);
v___x_2465_ = l_Lean_instInhabitedExpr;
v___x_2466_ = lean_array_get_borrowed(v___x_2465_, v_fst_2453_, v_v_2464_);
lean_inc(v___y_2460_);
lean_inc_ref(v___y_2459_);
lean_inc(v___y_2458_);
lean_inc_ref(v___y_2457_);
lean_inc(v___x_2466_);
v___x_2467_ = lean_infer_type(v___x_2466_, v___y_2457_, v___y_2458_, v___y_2459_, v___y_2460_);
if (lean_obj_tag(v___x_2467_) == 0)
{
lean_object* v_a_2468_; lean_object* v___x_2469_; 
v_a_2468_ = lean_ctor_get(v___x_2467_, 0);
lean_inc(v_a_2468_);
lean_dec_ref_known(v___x_2467_, 1);
v___x_2469_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2468_, v___y_2458_);
if (lean_obj_tag(v___x_2469_) == 0)
{
lean_object* v_a_2470_; lean_object* v___x_2471_; lean_object* v_bs_x27_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; size_t v___x_2475_; size_t v___x_2476_; lean_object* v___x_2477_; 
v_a_2470_ = lean_ctor_get(v___x_2469_, 0);
lean_inc(v_a_2470_);
lean_dec_ref_known(v___x_2469_, 1);
v___x_2471_ = lean_unsigned_to_nat(0u);
v_bs_x27_2472_ = lean_array_uset(v_bs_2456_, v_i_2455_, v___x_2471_);
v___x_2473_ = l_Lean_Expr_setPPExplicit(v_a_2470_, v___x_2462_);
v___x_2474_ = l_Lean_indentExpr(v___x_2473_);
v___x_2475_ = ((size_t)1ULL);
v___x_2476_ = lean_usize_add(v_i_2455_, v___x_2475_);
v___x_2477_ = lean_array_uset(v_bs_x27_2472_, v_i_2455_, v___x_2474_);
v_i_2455_ = v___x_2476_;
v_bs_2456_ = v___x_2477_;
goto _start;
}
else
{
lean_object* v_a_2479_; lean_object* v___x_2481_; uint8_t v_isShared_2482_; uint8_t v_isSharedCheck_2486_; 
lean_dec_ref(v_bs_2456_);
v_a_2479_ = lean_ctor_get(v___x_2469_, 0);
v_isSharedCheck_2486_ = !lean_is_exclusive(v___x_2469_);
if (v_isSharedCheck_2486_ == 0)
{
v___x_2481_ = v___x_2469_;
v_isShared_2482_ = v_isSharedCheck_2486_;
goto v_resetjp_2480_;
}
else
{
lean_inc(v_a_2479_);
lean_dec(v___x_2469_);
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
else
{
lean_object* v_a_2487_; lean_object* v___x_2489_; uint8_t v_isShared_2490_; uint8_t v_isSharedCheck_2494_; 
lean_dec_ref(v_bs_2456_);
v_a_2487_ = lean_ctor_get(v___x_2467_, 0);
v_isSharedCheck_2494_ = !lean_is_exclusive(v___x_2467_);
if (v_isSharedCheck_2494_ == 0)
{
v___x_2489_ = v___x_2467_;
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
else
{
lean_inc(v_a_2487_);
lean_dec(v___x_2467_);
v___x_2489_ = lean_box(0);
v_isShared_2490_ = v_isSharedCheck_2494_;
goto v_resetjp_2488_;
}
v_resetjp_2488_:
{
lean_object* v___x_2492_; 
if (v_isShared_2490_ == 0)
{
v___x_2492_ = v___x_2489_;
goto v_reusejp_2491_;
}
else
{
lean_object* v_reuseFailAlloc_2493_; 
v_reuseFailAlloc_2493_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2493_, 0, v_a_2487_);
v___x_2492_ = v_reuseFailAlloc_2493_;
goto v_reusejp_2491_;
}
v_reusejp_2491_:
{
return v___x_2492_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2495_, lean_object* v_sz_2496_, lean_object* v_i_2497_, lean_object* v_bs_2498_, lean_object* v___y_2499_, lean_object* v___y_2500_, lean_object* v___y_2501_, lean_object* v___y_2502_, lean_object* v___y_2503_){
_start:
{
size_t v_sz_boxed_2504_; size_t v_i_boxed_2505_; lean_object* v_res_2506_; 
v_sz_boxed_2504_ = lean_unbox_usize(v_sz_2496_);
lean_dec(v_sz_2496_);
v_i_boxed_2505_ = lean_unbox_usize(v_i_2497_);
lean_dec(v_i_2497_);
v_res_2506_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2495_, v_sz_boxed_2504_, v_i_boxed_2505_, v_bs_2498_, v___y_2499_, v___y_2500_, v___y_2501_, v___y_2502_);
lean_dec(v___y_2502_);
lean_dec_ref(v___y_2501_);
lean_dec(v___y_2500_);
lean_dec_ref(v___y_2499_);
lean_dec_ref(v_fst_2495_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object* v_snd_2507_, lean_object* v___f_2508_, lean_object* v_____r_2509_, lean_object* v___y_2510_, lean_object* v___y_2511_, lean_object* v___y_2512_, lean_object* v___y_2513_){
_start:
{
lean_object* v___x_2515_; lean_object* v___x_2516_; lean_object* v___x_2517_; 
v___x_2515_ = lean_unsigned_to_nat(0u);
v___x_2516_ = lean_array_get_borrowed(v___x_2515_, v_snd_2507_, v___x_2515_);
lean_inc(v___y_2513_);
lean_inc_ref(v___y_2512_);
lean_inc(v___y_2511_);
lean_inc_ref(v___y_2510_);
lean_inc(v___x_2516_);
v___x_2517_ = lean_apply_6(v___f_2508_, v___x_2516_, v___y_2510_, v___y_2511_, v___y_2512_, v___y_2513_, lean_box(0));
return v___x_2517_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object* v_snd_2518_, lean_object* v___f_2519_, lean_object* v_____r_2520_, lean_object* v___y_2521_, lean_object* v___y_2522_, lean_object* v___y_2523_, lean_object* v___y_2524_, lean_object* v___y_2525_){
_start:
{
lean_object* v_res_2526_; 
v_res_2526_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2518_, v___f_2519_, v_____r_2520_, v___y_2521_, v___y_2522_, v___y_2523_, v___y_2524_);
lean_dec(v___y_2524_);
lean_dec_ref(v___y_2523_);
lean_dec(v___y_2522_);
lean_dec_ref(v___y_2521_);
lean_dec(v_snd_2518_);
return v_res_2526_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2530_; lean_object* v___x_2531_; 
v___x_2530_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1));
v___x_2531_ = l_Lean_MessageData_ofFormat(v___x_2530_);
return v___x_2531_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2533_; lean_object* v___x_2534_; 
v___x_2533_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3));
v___x_2534_ = l_Lean_stringToMessageData(v___x_2533_);
return v___x_2534_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2536_; lean_object* v___x_2537_; 
v___x_2536_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5));
v___x_2537_ = l_Lean_stringToMessageData(v___x_2536_);
return v___x_2537_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2539_; lean_object* v___x_2540_; 
v___x_2539_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7));
v___x_2540_ = l_Lean_stringToMessageData(v___x_2539_);
return v___x_2540_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(lean_object* v_fst_2541_, lean_object* v_argVars_2542_, lean_object* v_inst_2543_, lean_object* v_a_2544_, lean_object* v_projInfo_x3f_2545_, lean_object* v_a_2546_, lean_object* v___y_2547_, lean_object* v___y_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_){
_start:
{
lean_object* v___y_2553_; lean_object* v_fst_2573_; lean_object* v_snd_2574_; lean_object* v___x_2576_; uint8_t v_isShared_2577_; uint8_t v_isSharedCheck_2650_; 
v_fst_2573_ = lean_ctor_get(v_a_2546_, 0);
v_snd_2574_ = lean_ctor_get(v_a_2546_, 1);
v_isSharedCheck_2650_ = !lean_is_exclusive(v_a_2546_);
if (v_isSharedCheck_2650_ == 0)
{
v___x_2576_ = v_a_2546_;
v_isShared_2577_ = v_isSharedCheck_2650_;
goto v_resetjp_2575_;
}
else
{
lean_inc(v_snd_2574_);
lean_inc(v_fst_2573_);
lean_dec(v_a_2546_);
v___x_2576_ = lean_box(0);
v_isShared_2577_ = v_isSharedCheck_2650_;
goto v_resetjp_2575_;
}
v___jp_2552_:
{
if (lean_obj_tag(v___y_2553_) == 0)
{
lean_object* v_a_2554_; lean_object* v___x_2556_; uint8_t v_isShared_2557_; uint8_t v_isSharedCheck_2564_; 
v_a_2554_ = lean_ctor_get(v___y_2553_, 0);
v_isSharedCheck_2564_ = !lean_is_exclusive(v___y_2553_);
if (v_isSharedCheck_2564_ == 0)
{
v___x_2556_ = v___y_2553_;
v_isShared_2557_ = v_isSharedCheck_2564_;
goto v_resetjp_2555_;
}
else
{
lean_inc(v_a_2554_);
lean_dec(v___y_2553_);
v___x_2556_ = lean_box(0);
v_isShared_2557_ = v_isSharedCheck_2564_;
goto v_resetjp_2555_;
}
v_resetjp_2555_:
{
if (lean_obj_tag(v_a_2554_) == 0)
{
lean_object* v_a_2558_; lean_object* v___x_2560_; 
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_argVars_2542_);
lean_dec_ref(v_fst_2541_);
v_a_2558_ = lean_ctor_get(v_a_2554_, 0);
lean_inc(v_a_2558_);
lean_dec_ref_known(v_a_2554_, 1);
if (v_isShared_2557_ == 0)
{
lean_ctor_set(v___x_2556_, 0, v_a_2558_);
v___x_2560_ = v___x_2556_;
goto v_reusejp_2559_;
}
else
{
lean_object* v_reuseFailAlloc_2561_; 
v_reuseFailAlloc_2561_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2561_, 0, v_a_2558_);
v___x_2560_ = v_reuseFailAlloc_2561_;
goto v_reusejp_2559_;
}
v_reusejp_2559_:
{
return v___x_2560_;
}
}
else
{
lean_object* v_a_2562_; 
lean_del_object(v___x_2556_);
v_a_2562_ = lean_ctor_get(v_a_2554_, 0);
lean_inc(v_a_2562_);
lean_dec_ref_known(v_a_2554_, 1);
v_a_2546_ = v_a_2562_;
goto _start;
}
}
}
else
{
lean_object* v_a_2565_; lean_object* v___x_2567_; uint8_t v_isShared_2568_; uint8_t v_isSharedCheck_2572_; 
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_argVars_2542_);
lean_dec_ref(v_fst_2541_);
v_a_2565_ = lean_ctor_get(v___y_2553_, 0);
v_isSharedCheck_2572_ = !lean_is_exclusive(v___y_2553_);
if (v_isSharedCheck_2572_ == 0)
{
v___x_2567_ = v___y_2553_;
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
else
{
lean_inc(v_a_2565_);
lean_dec(v___y_2553_);
v___x_2567_ = lean_box(0);
v_isShared_2568_ = v_isSharedCheck_2572_;
goto v_resetjp_2566_;
}
v_resetjp_2566_:
{
lean_object* v___x_2570_; 
if (v_isShared_2568_ == 0)
{
v___x_2570_ = v___x_2567_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2571_; 
v_reuseFailAlloc_2571_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2571_, 0, v_a_2565_);
v___x_2570_ = v_reuseFailAlloc_2571_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
return v___x_2570_;
}
}
}
}
v_resetjp_2575_:
{
lean_object* v___x_2578_; lean_object* v___x_2579_; uint8_t v___x_2580_; 
v___x_2578_ = lean_array_get_size(v_snd_2574_);
v___x_2579_ = lean_unsigned_to_nat(0u);
v___x_2580_ = lean_nat_dec_eq(v___x_2578_, v___x_2579_);
if (v___x_2580_ == 0)
{
lean_object* v___x_2581_; lean_object* v___x_2582_; size_t v_sz_2583_; size_t v___x_2584_; lean_object* v___x_2585_; 
lean_del_object(v___x_2576_);
v___x_2581_ = lean_box(0);
v___x_2582_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2583_ = lean_array_size(v_snd_2574_);
v___x_2584_ = ((size_t)0ULL);
v___x_2585_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2541_, v_projInfo_x3f_2545_, v___x_2578_, v_argVars_2542_, v_snd_2574_, v_sz_2583_, v___x_2584_, v___x_2582_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2585_) == 0)
{
lean_object* v_a_2586_; lean_object* v_fst_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2636_; 
v_a_2586_ = lean_ctor_get(v___x_2585_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v___x_2585_, 1);
v_fst_2587_ = lean_ctor_get(v_a_2586_, 0);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_a_2586_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; 
v_unused_2637_ = lean_ctor_get(v_a_2586_, 1);
lean_dec(v_unused_2637_);
v___x_2589_ = v_a_2586_;
v_isShared_2590_ = v_isSharedCheck_2636_;
goto v_resetjp_2588_;
}
else
{
lean_inc(v_fst_2587_);
lean_dec(v_a_2586_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2636_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___f_2591_; 
lean_inc(v_snd_2574_);
lean_inc_ref(v_argVars_2542_);
lean_inc_ref(v_fst_2541_);
lean_inc(v_fst_2573_);
v___f_2591_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2591_, 0, v_fst_2573_);
lean_closure_set(v___f_2591_, 1, v_fst_2541_);
lean_closure_set(v___f_2591_, 2, v_argVars_2542_);
lean_closure_set(v___f_2591_, 3, v_snd_2574_);
if (lean_obj_tag(v_fst_2587_) == 0)
{
lean_dec(v_fst_2573_);
goto v___jp_2592_;
}
else
{
lean_object* v_val_2633_; 
v_val_2633_ = lean_ctor_get(v_fst_2587_, 0);
lean_inc(v_val_2633_);
lean_dec_ref_known(v_fst_2587_, 1);
if (lean_obj_tag(v_val_2633_) == 0)
{
lean_dec(v_fst_2573_);
goto v___jp_2592_;
}
else
{
lean_object* v_val_2634_; lean_object* v___x_2635_; 
lean_dec_ref(v___f_2591_);
lean_del_object(v___x_2589_);
v_val_2634_ = lean_ctor_get(v_val_2633_, 0);
lean_inc(v_val_2634_);
lean_dec_ref_known(v_val_2633_, 1);
v___x_2635_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2573_, v_fst_2541_, v_argVars_2542_, v_snd_2574_, v_val_2634_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v_snd_2574_);
v___y_2553_ = v___x_2635_;
goto v___jp_2552_;
}
}
v___jp_2592_:
{
lean_object* v_options_2593_; lean_object* v___x_2594_; uint8_t v___x_2595_; 
v_options_2593_ = lean_ctor_get(v___y_2549_, 2);
v___x_2594_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2595_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2593_, v___x_2594_);
if (v___x_2595_ == 0)
{
lean_object* v___x_2596_; 
lean_del_object(v___x_2589_);
v___x_2596_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2574_, v___f_2591_, v___x_2581_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v_snd_2574_);
v___y_2553_ = v___x_2596_;
goto v___jp_2552_;
}
else
{
lean_object* v___x_2597_; 
lean_inc(v_snd_2574_);
v___x_2597_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2541_, v_sz_2583_, v___x_2584_, v_snd_2574_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2597_) == 0)
{
lean_object* v_a_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; lean_object* v___x_2602_; lean_object* v___x_2603_; lean_object* v___x_2605_; 
v_a_2598_ = lean_ctor_get(v___x_2597_, 0);
lean_inc(v_a_2598_);
lean_dec_ref_known(v___x_2597_, 1);
v___x_2599_ = lean_array_to_list(v_a_2598_);
v___x_2600_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2601_ = l_Lean_MessageData_joinSep(v___x_2599_, v___x_2600_);
v___x_2602_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4);
lean_inc_ref(v_inst_2543_);
v___x_2603_ = l_Lean_MessageData_ofExpr(v_inst_2543_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set_tag(v___x_2589_, 7);
lean_ctor_set(v___x_2589_, 1, v___x_2603_);
lean_ctor_set(v___x_2589_, 0, v___x_2602_);
v___x_2605_ = v___x_2589_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v___x_2602_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2608_; lean_object* v___x_2609_; lean_object* v___x_2610_; lean_object* v___x_2611_; lean_object* v___x_2612_; lean_object* v___x_2613_; 
v___x_2606_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6);
v___x_2607_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2607_, 0, v___x_2605_);
lean_ctor_set(v___x_2607_, 1, v___x_2606_);
lean_inc_ref(v_a_2544_);
v___x_2608_ = l_Lean_indentExpr(v_a_2544_);
v___x_2609_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2609_, 0, v___x_2607_);
lean_ctor_set(v___x_2609_, 1, v___x_2608_);
v___x_2610_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8);
v___x_2611_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2611_, 0, v___x_2609_);
lean_ctor_set(v___x_2611_, 1, v___x_2610_);
v___x_2612_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
lean_ctor_set(v___x_2612_, 1, v___x_2601_);
v___x_2613_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2612_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
if (lean_obj_tag(v___x_2613_) == 0)
{
lean_object* v_a_2614_; lean_object* v___x_2615_; 
v_a_2614_ = lean_ctor_get(v___x_2613_, 0);
lean_inc(v_a_2614_);
lean_dec_ref_known(v___x_2613_, 1);
v___x_2615_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2574_, v___f_2591_, v_a_2614_, v___y_2547_, v___y_2548_, v___y_2549_, v___y_2550_);
lean_dec(v_snd_2574_);
v___y_2553_ = v___x_2615_;
goto v___jp_2552_;
}
else
{
lean_object* v_a_2616_; lean_object* v___x_2618_; uint8_t v_isShared_2619_; uint8_t v_isSharedCheck_2623_; 
lean_dec_ref(v___f_2591_);
lean_dec(v_snd_2574_);
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_argVars_2542_);
lean_dec_ref(v_fst_2541_);
v_a_2616_ = lean_ctor_get(v___x_2613_, 0);
v_isSharedCheck_2623_ = !lean_is_exclusive(v___x_2613_);
if (v_isSharedCheck_2623_ == 0)
{
v___x_2618_ = v___x_2613_;
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
else
{
lean_inc(v_a_2616_);
lean_dec(v___x_2613_);
v___x_2618_ = lean_box(0);
v_isShared_2619_ = v_isSharedCheck_2623_;
goto v_resetjp_2617_;
}
v_resetjp_2617_:
{
lean_object* v___x_2621_; 
if (v_isShared_2619_ == 0)
{
v___x_2621_ = v___x_2618_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_a_2616_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
}
else
{
lean_object* v_a_2625_; lean_object* v___x_2627_; uint8_t v_isShared_2628_; uint8_t v_isSharedCheck_2632_; 
lean_dec_ref(v___f_2591_);
lean_del_object(v___x_2589_);
lean_dec(v_snd_2574_);
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_argVars_2542_);
lean_dec_ref(v_fst_2541_);
v_a_2625_ = lean_ctor_get(v___x_2597_, 0);
v_isSharedCheck_2632_ = !lean_is_exclusive(v___x_2597_);
if (v_isSharedCheck_2632_ == 0)
{
v___x_2627_ = v___x_2597_;
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
else
{
lean_inc(v_a_2625_);
lean_dec(v___x_2597_);
v___x_2627_ = lean_box(0);
v_isShared_2628_ = v_isSharedCheck_2632_;
goto v_resetjp_2626_;
}
v_resetjp_2626_:
{
lean_object* v___x_2630_; 
if (v_isShared_2628_ == 0)
{
v___x_2630_ = v___x_2627_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_a_2625_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2638_; lean_object* v___x_2640_; uint8_t v_isShared_2641_; uint8_t v_isSharedCheck_2645_; 
lean_dec(v_snd_2574_);
lean_dec(v_fst_2573_);
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_argVars_2542_);
lean_dec_ref(v_fst_2541_);
v_a_2638_ = lean_ctor_get(v___x_2585_, 0);
v_isSharedCheck_2645_ = !lean_is_exclusive(v___x_2585_);
if (v_isSharedCheck_2645_ == 0)
{
v___x_2640_ = v___x_2585_;
v_isShared_2641_ = v_isSharedCheck_2645_;
goto v_resetjp_2639_;
}
else
{
lean_inc(v_a_2638_);
lean_dec(v___x_2585_);
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
lean_object* v___x_2647_; 
lean_dec_ref(v_a_2544_);
lean_dec_ref(v_inst_2543_);
lean_dec_ref(v_argVars_2542_);
lean_dec_ref(v_fst_2541_);
if (v_isShared_2577_ == 0)
{
v___x_2647_ = v___x_2576_;
goto v_reusejp_2646_;
}
else
{
lean_object* v_reuseFailAlloc_2649_; 
v_reuseFailAlloc_2649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2649_, 0, v_fst_2573_);
lean_ctor_set(v_reuseFailAlloc_2649_, 1, v_snd_2574_);
v___x_2647_ = v_reuseFailAlloc_2649_;
goto v_reusejp_2646_;
}
v_reusejp_2646_:
{
lean_object* v___x_2648_; 
v___x_2648_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2648_, 0, v___x_2647_);
return v___x_2648_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___boxed(lean_object* v_fst_2651_, lean_object* v_argVars_2652_, lean_object* v_inst_2653_, lean_object* v_a_2654_, lean_object* v_projInfo_x3f_2655_, lean_object* v_a_2656_, lean_object* v___y_2657_, lean_object* v___y_2658_, lean_object* v___y_2659_, lean_object* v___y_2660_, lean_object* v___y_2661_){
_start:
{
lean_object* v_res_2662_; 
v_res_2662_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2651_, v_argVars_2652_, v_inst_2653_, v_a_2654_, v_projInfo_x3f_2655_, v_a_2656_, v___y_2657_, v___y_2658_, v___y_2659_, v___y_2660_);
lean_dec(v___y_2660_);
lean_dec_ref(v___y_2659_);
lean_dec(v___y_2658_);
lean_dec_ref(v___y_2657_);
lean_dec(v_projInfo_x3f_2655_);
return v_res_2662_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2663_, lean_object* v_a_2664_, lean_object* v_a_2665_){
_start:
{
if (lean_obj_tag(v_a_2664_) == 0)
{
lean_object* v___x_2666_; 
v___x_2666_ = l_List_reverse___redArg(v_a_2665_);
return v___x_2666_;
}
else
{
lean_object* v_head_2667_; lean_object* v_tail_2668_; lean_object* v___x_2670_; uint8_t v_isShared_2671_; uint8_t v_isSharedCheck_2683_; 
v_head_2667_ = lean_ctor_get(v_a_2664_, 0);
v_tail_2668_ = lean_ctor_get(v_a_2664_, 1);
v_isSharedCheck_2683_ = !lean_is_exclusive(v_a_2664_);
if (v_isSharedCheck_2683_ == 0)
{
v___x_2670_ = v_a_2664_;
v_isShared_2671_ = v_isSharedCheck_2683_;
goto v_resetjp_2669_;
}
else
{
lean_inc(v_tail_2668_);
lean_inc(v_head_2667_);
lean_dec(v_a_2664_);
v___x_2670_ = lean_box(0);
v_isShared_2671_ = v_isSharedCheck_2683_;
goto v_resetjp_2669_;
}
v_resetjp_2669_:
{
uint8_t v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint8_t v___x_2675_; uint8_t v___x_2676_; uint8_t v___x_2677_; 
v___x_2672_ = 0;
v___x_2673_ = lean_box(v___x_2672_);
v___x_2674_ = lean_array_get(v___x_2673_, v_fst_2663_, v_head_2667_);
lean_dec(v___x_2673_);
v___x_2675_ = 3;
v___x_2676_ = lean_unbox(v___x_2674_);
lean_dec(v___x_2674_);
v___x_2677_ = l_Lean_instBEqBinderInfo_beq(v___x_2676_, v___x_2675_);
if (v___x_2677_ == 0)
{
lean_del_object(v___x_2670_);
lean_dec(v_head_2667_);
v_a_2664_ = v_tail_2668_;
goto _start;
}
else
{
lean_object* v___x_2680_; 
if (v_isShared_2671_ == 0)
{
lean_ctor_set(v___x_2670_, 1, v_a_2665_);
v___x_2680_ = v___x_2670_;
goto v_reusejp_2679_;
}
else
{
lean_object* v_reuseFailAlloc_2682_; 
v_reuseFailAlloc_2682_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2682_, 0, v_head_2667_);
lean_ctor_set(v_reuseFailAlloc_2682_, 1, v_a_2665_);
v___x_2680_ = v_reuseFailAlloc_2682_;
goto v_reusejp_2679_;
}
v_reusejp_2679_:
{
v_a_2664_ = v_tail_2668_;
v_a_2665_ = v___x_2680_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2684_, lean_object* v_a_2685_, lean_object* v_a_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2684_, v_a_2685_, v_a_2686_);
lean_dec_ref(v_fst_2684_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2688_, size_t v_sz_2689_, size_t v_i_2690_, lean_object* v_bs_2691_, lean_object* v___y_2692_, lean_object* v___y_2693_, lean_object* v___y_2694_, lean_object* v___y_2695_){
_start:
{
uint8_t v___x_2697_; 
v___x_2697_ = lean_usize_dec_lt(v_i_2690_, v_sz_2689_);
if (v___x_2697_ == 0)
{
lean_object* v___x_2698_; 
v___x_2698_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2698_, 0, v_bs_2691_);
return v___x_2698_;
}
else
{
lean_object* v_v_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2702_; 
v_v_2699_ = lean_array_uget_borrowed(v_bs_2691_, v_i_2690_);
v___x_2700_ = l_Lean_instInhabitedExpr;
v___x_2701_ = lean_array_get_borrowed(v___x_2700_, v_argVars_2688_, v_v_2699_);
lean_inc(v___y_2695_);
lean_inc_ref(v___y_2694_);
lean_inc(v___y_2693_);
lean_inc_ref(v___y_2692_);
lean_inc(v___x_2701_);
v___x_2702_ = lean_infer_type(v___x_2701_, v___y_2692_, v___y_2693_, v___y_2694_, v___y_2695_);
if (lean_obj_tag(v___x_2702_) == 0)
{
lean_object* v_a_2703_; lean_object* v___x_2704_; lean_object* v_bs_x27_2705_; lean_object* v___x_2706_; size_t v___x_2707_; size_t v___x_2708_; lean_object* v___x_2709_; 
v_a_2703_ = lean_ctor_get(v___x_2702_, 0);
lean_inc(v_a_2703_);
lean_dec_ref_known(v___x_2702_, 1);
v___x_2704_ = lean_unsigned_to_nat(0u);
v_bs_x27_2705_ = lean_array_uset(v_bs_2691_, v_i_2690_, v___x_2704_);
v___x_2706_ = l_Lean_indentExpr(v_a_2703_);
v___x_2707_ = ((size_t)1ULL);
v___x_2708_ = lean_usize_add(v_i_2690_, v___x_2707_);
v___x_2709_ = lean_array_uset(v_bs_x27_2705_, v_i_2690_, v___x_2706_);
v_i_2690_ = v___x_2708_;
v_bs_2691_ = v___x_2709_;
goto _start;
}
else
{
lean_object* v_a_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2718_; 
lean_dec_ref(v_bs_2691_);
v_a_2711_ = lean_ctor_get(v___x_2702_, 0);
v_isSharedCheck_2718_ = !lean_is_exclusive(v___x_2702_);
if (v_isSharedCheck_2718_ == 0)
{
v___x_2713_ = v___x_2702_;
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
else
{
lean_inc(v_a_2711_);
lean_dec(v___x_2702_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2718_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2716_; 
if (v_isShared_2714_ == 0)
{
v___x_2716_ = v___x_2713_;
goto v_reusejp_2715_;
}
else
{
lean_object* v_reuseFailAlloc_2717_; 
v_reuseFailAlloc_2717_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2717_, 0, v_a_2711_);
v___x_2716_ = v_reuseFailAlloc_2717_;
goto v_reusejp_2715_;
}
v_reusejp_2715_:
{
return v___x_2716_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2719_, lean_object* v_sz_2720_, lean_object* v_i_2721_, lean_object* v_bs_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_, lean_object* v___y_2725_, lean_object* v___y_2726_, lean_object* v___y_2727_){
_start:
{
size_t v_sz_boxed_2728_; size_t v_i_boxed_2729_; lean_object* v_res_2730_; 
v_sz_boxed_2728_ = lean_unbox_usize(v_sz_2720_);
lean_dec(v_sz_2720_);
v_i_boxed_2729_ = lean_unbox_usize(v_i_2721_);
lean_dec(v_i_2721_);
v_res_2730_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2719_, v_sz_boxed_2728_, v_i_boxed_2729_, v_bs_2722_, v___y_2723_, v___y_2724_, v___y_2725_, v___y_2726_);
lean_dec(v___y_2726_);
lean_dec_ref(v___y_2725_);
lean_dec(v___y_2724_);
lean_dec_ref(v___y_2723_);
lean_dec_ref(v_argVars_2719_);
return v_res_2730_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2731_, lean_object* v_a_2732_){
_start:
{
if (lean_obj_tag(v_a_2731_) == 0)
{
lean_object* v___x_2733_; 
v___x_2733_ = l_List_reverse___redArg(v_a_2732_);
return v___x_2733_;
}
else
{
lean_object* v_head_2734_; lean_object* v_tail_2735_; lean_object* v___x_2737_; uint8_t v_isShared_2738_; uint8_t v_isSharedCheck_2746_; 
v_head_2734_ = lean_ctor_get(v_a_2731_, 0);
v_tail_2735_ = lean_ctor_get(v_a_2731_, 1);
v_isSharedCheck_2746_ = !lean_is_exclusive(v_a_2731_);
if (v_isSharedCheck_2746_ == 0)
{
v___x_2737_ = v_a_2731_;
v_isShared_2738_ = v_isSharedCheck_2746_;
goto v_resetjp_2736_;
}
else
{
lean_inc(v_tail_2735_);
lean_inc(v_head_2734_);
lean_dec(v_a_2731_);
v___x_2737_ = lean_box(0);
v_isShared_2738_ = v_isSharedCheck_2746_;
goto v_resetjp_2736_;
}
v_resetjp_2736_:
{
lean_object* v___x_2739_; lean_object* v___x_2740_; lean_object* v___x_2741_; lean_object* v___x_2743_; 
v___x_2739_ = l_Nat_reprFast(v_head_2734_);
v___x_2740_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2740_, 0, v___x_2739_);
v___x_2741_ = l_Lean_MessageData_ofFormat(v___x_2740_);
if (v_isShared_2738_ == 0)
{
lean_ctor_set(v___x_2737_, 1, v_a_2732_);
lean_ctor_set(v___x_2737_, 0, v___x_2741_);
v___x_2743_ = v___x_2737_;
goto v_reusejp_2742_;
}
else
{
lean_object* v_reuseFailAlloc_2745_; 
v_reuseFailAlloc_2745_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2745_, 0, v___x_2741_);
lean_ctor_set(v_reuseFailAlloc_2745_, 1, v_a_2732_);
v___x_2743_ = v_reuseFailAlloc_2745_;
goto v_reusejp_2742_;
}
v_reusejp_2742_:
{
v_a_2731_ = v_tail_2735_;
v_a_2732_ = v___x_2743_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2747_; double v___x_2748_; 
v___x_2747_ = lean_unsigned_to_nat(0u);
v___x_2748_ = lean_float_of_nat(v___x_2747_);
return v___x_2748_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2751_, lean_object* v_msg_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
lean_object* v_ref_2758_; lean_object* v___x_2759_; lean_object* v_a_2760_; lean_object* v___x_2762_; uint8_t v_isShared_2763_; uint8_t v_isSharedCheck_2804_; 
v_ref_2758_ = lean_ctor_get(v___y_2755_, 5);
v___x_2759_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2752_, v___y_2753_, v___y_2754_, v___y_2755_, v___y_2756_);
v_a_2760_ = lean_ctor_get(v___x_2759_, 0);
v_isSharedCheck_2804_ = !lean_is_exclusive(v___x_2759_);
if (v_isSharedCheck_2804_ == 0)
{
v___x_2762_ = v___x_2759_;
v_isShared_2763_ = v_isSharedCheck_2804_;
goto v_resetjp_2761_;
}
else
{
lean_inc(v_a_2760_);
lean_dec(v___x_2759_);
v___x_2762_ = lean_box(0);
v_isShared_2763_ = v_isSharedCheck_2804_;
goto v_resetjp_2761_;
}
v_resetjp_2761_:
{
lean_object* v___x_2764_; lean_object* v_traceState_2765_; lean_object* v_env_2766_; lean_object* v_nextMacroScope_2767_; lean_object* v_ngen_2768_; lean_object* v_auxDeclNGen_2769_; lean_object* v_cache_2770_; lean_object* v_messages_2771_; lean_object* v_infoState_2772_; lean_object* v_snapshotTasks_2773_; lean_object* v___x_2775_; uint8_t v_isShared_2776_; uint8_t v_isSharedCheck_2803_; 
v___x_2764_ = lean_st_ref_take(v___y_2756_);
v_traceState_2765_ = lean_ctor_get(v___x_2764_, 4);
v_env_2766_ = lean_ctor_get(v___x_2764_, 0);
v_nextMacroScope_2767_ = lean_ctor_get(v___x_2764_, 1);
v_ngen_2768_ = lean_ctor_get(v___x_2764_, 2);
v_auxDeclNGen_2769_ = lean_ctor_get(v___x_2764_, 3);
v_cache_2770_ = lean_ctor_get(v___x_2764_, 5);
v_messages_2771_ = lean_ctor_get(v___x_2764_, 6);
v_infoState_2772_ = lean_ctor_get(v___x_2764_, 7);
v_snapshotTasks_2773_ = lean_ctor_get(v___x_2764_, 8);
v_isSharedCheck_2803_ = !lean_is_exclusive(v___x_2764_);
if (v_isSharedCheck_2803_ == 0)
{
v___x_2775_ = v___x_2764_;
v_isShared_2776_ = v_isSharedCheck_2803_;
goto v_resetjp_2774_;
}
else
{
lean_inc(v_snapshotTasks_2773_);
lean_inc(v_infoState_2772_);
lean_inc(v_messages_2771_);
lean_inc(v_cache_2770_);
lean_inc(v_traceState_2765_);
lean_inc(v_auxDeclNGen_2769_);
lean_inc(v_ngen_2768_);
lean_inc(v_nextMacroScope_2767_);
lean_inc(v_env_2766_);
lean_dec(v___x_2764_);
v___x_2775_ = lean_box(0);
v_isShared_2776_ = v_isSharedCheck_2803_;
goto v_resetjp_2774_;
}
v_resetjp_2774_:
{
uint64_t v_tid_2777_; lean_object* v_traces_2778_; lean_object* v___x_2780_; uint8_t v_isShared_2781_; uint8_t v_isSharedCheck_2802_; 
v_tid_2777_ = lean_ctor_get_uint64(v_traceState_2765_, sizeof(void*)*1);
v_traces_2778_ = lean_ctor_get(v_traceState_2765_, 0);
v_isSharedCheck_2802_ = !lean_is_exclusive(v_traceState_2765_);
if (v_isSharedCheck_2802_ == 0)
{
v___x_2780_ = v_traceState_2765_;
v_isShared_2781_ = v_isSharedCheck_2802_;
goto v_resetjp_2779_;
}
else
{
lean_inc(v_traces_2778_);
lean_dec(v_traceState_2765_);
v___x_2780_ = lean_box(0);
v_isShared_2781_ = v_isSharedCheck_2802_;
goto v_resetjp_2779_;
}
v_resetjp_2779_:
{
lean_object* v___x_2782_; double v___x_2783_; uint8_t v___x_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___x_2792_; 
v___x_2782_ = lean_box(0);
v___x_2783_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2784_ = 0;
v___x_2785_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___x_2786_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2786_, 0, v_cls_2751_);
lean_ctor_set(v___x_2786_, 1, v___x_2782_);
lean_ctor_set(v___x_2786_, 2, v___x_2785_);
lean_ctor_set_float(v___x_2786_, sizeof(void*)*3, v___x_2783_);
lean_ctor_set_float(v___x_2786_, sizeof(void*)*3 + 8, v___x_2783_);
lean_ctor_set_uint8(v___x_2786_, sizeof(void*)*3 + 16, v___x_2784_);
v___x_2787_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2788_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2788_, 0, v___x_2786_);
lean_ctor_set(v___x_2788_, 1, v_a_2760_);
lean_ctor_set(v___x_2788_, 2, v___x_2787_);
lean_inc(v_ref_2758_);
v___x_2789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2789_, 0, v_ref_2758_);
lean_ctor_set(v___x_2789_, 1, v___x_2788_);
v___x_2790_ = l_Lean_PersistentArray_push___redArg(v_traces_2778_, v___x_2789_);
if (v_isShared_2781_ == 0)
{
lean_ctor_set(v___x_2780_, 0, v___x_2790_);
v___x_2792_ = v___x_2780_;
goto v_reusejp_2791_;
}
else
{
lean_object* v_reuseFailAlloc_2801_; 
v_reuseFailAlloc_2801_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2801_, 0, v___x_2790_);
lean_ctor_set_uint64(v_reuseFailAlloc_2801_, sizeof(void*)*1, v_tid_2777_);
v___x_2792_ = v_reuseFailAlloc_2801_;
goto v_reusejp_2791_;
}
v_reusejp_2791_:
{
lean_object* v___x_2794_; 
if (v_isShared_2776_ == 0)
{
lean_ctor_set(v___x_2775_, 4, v___x_2792_);
v___x_2794_ = v___x_2775_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_env_2766_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_nextMacroScope_2767_);
lean_ctor_set(v_reuseFailAlloc_2800_, 2, v_ngen_2768_);
lean_ctor_set(v_reuseFailAlloc_2800_, 3, v_auxDeclNGen_2769_);
lean_ctor_set(v_reuseFailAlloc_2800_, 4, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2800_, 5, v_cache_2770_);
lean_ctor_set(v_reuseFailAlloc_2800_, 6, v_messages_2771_);
lean_ctor_set(v_reuseFailAlloc_2800_, 7, v_infoState_2772_);
lean_ctor_set(v_reuseFailAlloc_2800_, 8, v_snapshotTasks_2773_);
v___x_2794_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2795_ = lean_st_ref_set(v___y_2756_, v___x_2794_);
v___x_2796_ = lean_box(0);
if (v_isShared_2763_ == 0)
{
lean_ctor_set(v___x_2762_, 0, v___x_2796_);
v___x_2798_ = v___x_2762_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v___x_2796_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2805_, lean_object* v_msg_2806_, lean_object* v___y_2807_, lean_object* v___y_2808_, lean_object* v___y_2809_, lean_object* v___y_2810_, lean_object* v___y_2811_){
_start:
{
lean_object* v_res_2812_; 
v_res_2812_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2805_, v_msg_2806_, v___y_2807_, v___y_2808_, v___y_2809_, v___y_2810_);
lean_dec(v___y_2810_);
lean_dec_ref(v___y_2809_);
lean_dec(v___y_2808_);
lean_dec_ref(v___y_2807_);
return v_res_2812_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2820_; lean_object* v___x_2821_; lean_object* v___x_2822_; 
v___x_2820_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2821_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2822_ = l_Lean_Name_append(v___x_2821_, v___x_2820_);
return v___x_2822_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; 
v___x_2824_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2825_ = l_Lean_stringToMessageData(v___x_2824_);
return v___x_2825_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2827_; lean_object* v___x_2828_; 
v___x_2827_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2828_ = l_Lean_stringToMessageData(v___x_2827_);
return v___x_2828_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; 
v___x_2830_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2831_ = l_Lean_stringToMessageData(v___x_2830_);
return v___x_2831_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2833_; lean_object* v___x_2834_; 
v___x_2833_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2834_ = l_Lean_stringToMessageData(v___x_2833_);
return v___x_2834_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2835_, lean_object* v_fst_2836_, lean_object* v_fst_2837_, lean_object* v_inst_2838_, lean_object* v_a_2839_, lean_object* v_projInfo_x3f_2840_, lean_object* v_argVars_2841_, lean_object* v_x_2842_, lean_object* v___y_2843_, lean_object* v___y_2844_, lean_object* v___y_2845_, lean_object* v___y_2846_){
_start:
{
lean_object* v___x_2848_; 
v___x_2848_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2835_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2848_) == 0)
{
lean_object* v_a_2849_; lean_object* v_dummy_2850_; lean_object* v_nargs_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2854_; lean_object* v___x_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; size_t v_sz_2859_; size_t v___x_2860_; lean_object* v___x_2861_; 
v_a_2849_ = lean_ctor_get(v___x_2848_, 0);
lean_inc(v_a_2849_);
lean_dec_ref_known(v___x_2848_, 1);
v_dummy_2850_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2851_ = l_Lean_Expr_getAppNumArgs(v_a_2835_);
lean_inc(v_nargs_2851_);
v___x_2852_ = lean_mk_array(v_nargs_2851_, v_dummy_2850_);
v___x_2853_ = lean_unsigned_to_nat(1u);
v___x_2854_ = lean_nat_sub(v_nargs_2851_, v___x_2853_);
lean_dec(v_nargs_2851_);
lean_inc_ref(v_a_2835_);
v___x_2855_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2835_, v___x_2852_, v___x_2854_);
v___x_2856_ = lean_array_get_size(v___x_2855_);
v___x_2857_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2858_, 0, v___x_2857_);
lean_ctor_set(v___x_2858_, 1, v___x_2856_);
v_sz_2859_ = lean_array_size(v___x_2855_);
v___x_2860_ = ((size_t)0ULL);
v___x_2861_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2849_, v_fst_2836_, v_argVars_2841_, v___x_2855_, v_sz_2859_, v___x_2860_, v___x_2858_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
lean_dec_ref(v___x_2855_);
lean_dec(v_a_2849_);
if (lean_obj_tag(v___x_2861_) == 0)
{
lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; lean_object* v___x_2869_; 
lean_dec_ref_known(v___x_2861_, 1);
v___x_2862_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2863_ = lean_array_get_size(v_fst_2836_);
v___x_2864_ = l_List_range(v___x_2863_);
v___x_2865_ = lean_box(0);
v___x_2866_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2837_, v___x_2864_, v___x_2865_);
v___x_2867_ = lean_array_mk(v___x_2866_);
v___x_2868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2868_, 0, v___x_2862_);
lean_ctor_set(v___x_2868_, 1, v___x_2867_);
lean_inc_ref(v_inst_2838_);
lean_inc_ref(v_argVars_2841_);
v___x_2869_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2836_, v_argVars_2841_, v_inst_2838_, v_a_2839_, v_projInfo_x3f_2840_, v___x_2868_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
if (lean_obj_tag(v___x_2869_) == 0)
{
lean_object* v_a_2870_; lean_object* v___x_2872_; uint8_t v_isShared_2873_; uint8_t v_isSharedCheck_2962_; 
v_a_2870_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2962_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2962_ == 0)
{
v___x_2872_ = v___x_2869_;
v_isShared_2873_ = v_isSharedCheck_2962_;
goto v_resetjp_2871_;
}
else
{
lean_inc(v_a_2870_);
lean_dec(v___x_2869_);
v___x_2872_ = lean_box(0);
v_isShared_2873_ = v_isSharedCheck_2962_;
goto v_resetjp_2871_;
}
v_resetjp_2871_:
{
lean_object* v_fst_2874_; lean_object* v___x_2876_; uint8_t v_isShared_2877_; uint8_t v_isSharedCheck_2960_; 
v_fst_2874_ = lean_ctor_get(v_a_2870_, 0);
v_isSharedCheck_2960_ = !lean_is_exclusive(v_a_2870_);
if (v_isSharedCheck_2960_ == 0)
{
lean_object* v_unused_2961_; 
v_unused_2961_ = lean_ctor_get(v_a_2870_, 1);
lean_dec(v_unused_2961_);
v___x_2876_ = v_a_2870_;
v_isShared_2877_ = v_isSharedCheck_2960_;
goto v_resetjp_2875_;
}
else
{
lean_inc(v_fst_2874_);
lean_dec(v_a_2870_);
v___x_2876_ = lean_box(0);
v_isShared_2877_ = v_isSharedCheck_2960_;
goto v_resetjp_2875_;
}
v_resetjp_2875_:
{
lean_object* v___y_2879_; lean_object* v___y_2880_; lean_object* v___y_2881_; lean_object* v_options_2882_; lean_object* v_inheritedTraceOptions_2883_; lean_object* v___y_2884_; lean_object* v_options_2940_; lean_object* v_inheritedTraceOptions_2941_; lean_object* v___x_2942_; uint8_t v___x_2943_; 
v_options_2940_ = lean_ctor_get(v___y_2845_, 2);
v_inheritedTraceOptions_2941_ = lean_ctor_get(v___y_2845_, 13);
v___x_2942_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2943_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2940_, v___x_2942_);
if (v___x_2943_ == 0)
{
lean_dec_ref(v_a_2835_);
v___y_2879_ = v___y_2843_;
v___y_2880_ = v___y_2844_;
v___y_2881_ = v___y_2845_;
v_options_2882_ = v_options_2940_;
v_inheritedTraceOptions_2883_ = v_inheritedTraceOptions_2941_;
v___y_2884_ = v___y_2846_;
goto v___jp_2878_;
}
else
{
lean_object* v___x_2944_; lean_object* v_a_2945_; uint8_t v___x_2946_; 
v___x_2944_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2835_, v___y_2844_);
v_a_2945_ = lean_ctor_get(v___x_2944_, 0);
lean_inc(v_a_2945_);
lean_dec_ref(v___x_2944_);
v___x_2946_ = l_Lean_Expr_hasExprMVar(v_a_2945_);
if (v___x_2946_ == 0)
{
lean_dec(v_a_2945_);
v___y_2879_ = v___y_2843_;
v___y_2880_ = v___y_2844_;
v___y_2881_ = v___y_2845_;
v_options_2882_ = v_options_2940_;
v_inheritedTraceOptions_2883_ = v_inheritedTraceOptions_2941_;
v___y_2884_ = v___y_2846_;
goto v___jp_2878_;
}
else
{
lean_object* v___x_2947_; lean_object* v___x_2948_; lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2951_; lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_del_object(v___x_2876_);
lean_dec(v_fst_2874_);
lean_del_object(v___x_2872_);
lean_dec_ref(v_argVars_2841_);
lean_dec_ref(v_inst_2838_);
v___x_2947_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_2948_ = l_Lean_Expr_setPPExplicit(v_a_2945_, v___x_2946_);
v___x_2949_ = l_Lean_indentExpr(v___x_2948_);
v___x_2950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2947_);
lean_ctor_set(v___x_2950_, 1, v___x_2949_);
v___x_2951_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2950_, v___y_2843_, v___y_2844_, v___y_2845_, v___y_2846_);
v_a_2952_ = lean_ctor_get(v___x_2951_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2951_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2951_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2951_);
v___x_2954_ = lean_box(0);
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
v_resetjp_2953_:
{
lean_object* v___x_2957_; 
if (v_isShared_2955_ == 0)
{
v___x_2957_ = v___x_2954_;
goto v_reusejp_2956_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v_a_2952_);
v___x_2957_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2956_;
}
v_reusejp_2956_:
{
return v___x_2957_;
}
}
}
}
v___jp_2878_:
{
uint8_t v_hasTrace_2885_; 
v_hasTrace_2885_ = lean_ctor_get_uint8(v_options_2882_, sizeof(void*)*1);
if (v_hasTrace_2885_ == 0)
{
lean_object* v___x_2887_; 
lean_del_object(v___x_2876_);
lean_dec_ref(v_argVars_2841_);
lean_dec_ref(v_inst_2838_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v_fst_2874_);
v___x_2887_ = v___x_2872_;
goto v_reusejp_2886_;
}
else
{
lean_object* v_reuseFailAlloc_2888_; 
v_reuseFailAlloc_2888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2888_, 0, v_fst_2874_);
v___x_2887_ = v_reuseFailAlloc_2888_;
goto v_reusejp_2886_;
}
v_reusejp_2886_:
{
return v___x_2887_;
}
}
else
{
lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v___x_2889_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2890_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2891_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2883_, v_options_2882_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2893_; 
lean_del_object(v___x_2876_);
lean_dec_ref(v_argVars_2841_);
lean_dec_ref(v_inst_2838_);
if (v_isShared_2873_ == 0)
{
lean_ctor_set(v___x_2872_, 0, v_fst_2874_);
v___x_2893_ = v___x_2872_;
goto v_reusejp_2892_;
}
else
{
lean_object* v_reuseFailAlloc_2894_; 
v_reuseFailAlloc_2894_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2894_, 0, v_fst_2874_);
v___x_2893_ = v_reuseFailAlloc_2894_;
goto v_reusejp_2892_;
}
v_reusejp_2892_:
{
return v___x_2893_;
}
}
else
{
size_t v_sz_2895_; lean_object* v___x_2896_; 
lean_del_object(v___x_2872_);
v_sz_2895_ = lean_array_size(v_fst_2874_);
lean_inc(v_fst_2874_);
v___x_2896_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2841_, v_sz_2895_, v___x_2860_, v_fst_2874_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2884_);
lean_dec_ref(v_argVars_2841_);
if (lean_obj_tag(v___x_2896_) == 0)
{
lean_object* v_a_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2901_; 
v_a_2897_ = lean_ctor_get(v___x_2896_, 0);
lean_inc(v_a_2897_);
lean_dec_ref_known(v___x_2896_, 1);
v___x_2898_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_2899_ = l_Lean_MessageData_ofExpr(v_inst_2838_);
if (v_isShared_2877_ == 0)
{
lean_ctor_set_tag(v___x_2876_, 7);
lean_ctor_set(v___x_2876_, 1, v___x_2899_);
lean_ctor_set(v___x_2876_, 0, v___x_2898_);
v___x_2901_ = v___x_2876_;
goto v_reusejp_2900_;
}
else
{
lean_object* v_reuseFailAlloc_2931_; 
v_reuseFailAlloc_2931_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2931_, 0, v___x_2898_);
lean_ctor_set(v_reuseFailAlloc_2931_, 1, v___x_2899_);
v___x_2901_ = v_reuseFailAlloc_2931_;
goto v_reusejp_2900_;
}
v_reusejp_2900_:
{
lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; lean_object* v___x_2909_; lean_object* v___x_2910_; lean_object* v___x_2911_; lean_object* v___x_2912_; lean_object* v___x_2913_; lean_object* v___x_2914_; 
v___x_2902_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_2903_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2903_, 0, v___x_2901_);
lean_ctor_set(v___x_2903_, 1, v___x_2902_);
lean_inc(v_fst_2874_);
v___x_2904_ = lean_array_to_list(v_fst_2874_);
v___x_2905_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_2904_, v___x_2865_);
v___x_2906_ = l_Lean_MessageData_ofList(v___x_2905_);
v___x_2907_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2907_, 0, v___x_2903_);
lean_ctor_set(v___x_2907_, 1, v___x_2906_);
v___x_2908_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_2909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2909_, 0, v___x_2907_);
lean_ctor_set(v___x_2909_, 1, v___x_2908_);
v___x_2910_ = lean_array_to_list(v_a_2897_);
v___x_2911_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2912_ = l_Lean_MessageData_joinSep(v___x_2910_, v___x_2911_);
v___x_2913_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2913_, 0, v___x_2909_);
lean_ctor_set(v___x_2913_, 1, v___x_2912_);
v___x_2914_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2889_, v___x_2913_, v___y_2879_, v___y_2880_, v___y_2881_, v___y_2884_);
if (lean_obj_tag(v___x_2914_) == 0)
{
lean_object* v___x_2916_; uint8_t v_isShared_2917_; uint8_t v_isSharedCheck_2921_; 
v_isSharedCheck_2921_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2921_ == 0)
{
lean_object* v_unused_2922_; 
v_unused_2922_ = lean_ctor_get(v___x_2914_, 0);
lean_dec(v_unused_2922_);
v___x_2916_ = v___x_2914_;
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
else
{
lean_dec(v___x_2914_);
v___x_2916_ = lean_box(0);
v_isShared_2917_ = v_isSharedCheck_2921_;
goto v_resetjp_2915_;
}
v_resetjp_2915_:
{
lean_object* v___x_2919_; 
if (v_isShared_2917_ == 0)
{
lean_ctor_set(v___x_2916_, 0, v_fst_2874_);
v___x_2919_ = v___x_2916_;
goto v_reusejp_2918_;
}
else
{
lean_object* v_reuseFailAlloc_2920_; 
v_reuseFailAlloc_2920_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2920_, 0, v_fst_2874_);
v___x_2919_ = v_reuseFailAlloc_2920_;
goto v_reusejp_2918_;
}
v_reusejp_2918_:
{
return v___x_2919_;
}
}
}
else
{
lean_object* v_a_2923_; lean_object* v___x_2925_; uint8_t v_isShared_2926_; uint8_t v_isSharedCheck_2930_; 
lean_dec(v_fst_2874_);
v_a_2923_ = lean_ctor_get(v___x_2914_, 0);
v_isSharedCheck_2930_ = !lean_is_exclusive(v___x_2914_);
if (v_isSharedCheck_2930_ == 0)
{
v___x_2925_ = v___x_2914_;
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
else
{
lean_inc(v_a_2923_);
lean_dec(v___x_2914_);
v___x_2925_ = lean_box(0);
v_isShared_2926_ = v_isSharedCheck_2930_;
goto v_resetjp_2924_;
}
v_resetjp_2924_:
{
lean_object* v___x_2928_; 
if (v_isShared_2926_ == 0)
{
v___x_2928_ = v___x_2925_;
goto v_reusejp_2927_;
}
else
{
lean_object* v_reuseFailAlloc_2929_; 
v_reuseFailAlloc_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2929_, 0, v_a_2923_);
v___x_2928_ = v_reuseFailAlloc_2929_;
goto v_reusejp_2927_;
}
v_reusejp_2927_:
{
return v___x_2928_;
}
}
}
}
}
else
{
lean_object* v_a_2932_; lean_object* v___x_2934_; uint8_t v_isShared_2935_; uint8_t v_isSharedCheck_2939_; 
lean_del_object(v___x_2876_);
lean_dec(v_fst_2874_);
lean_dec_ref(v_inst_2838_);
v_a_2932_ = lean_ctor_get(v___x_2896_, 0);
v_isSharedCheck_2939_ = !lean_is_exclusive(v___x_2896_);
if (v_isSharedCheck_2939_ == 0)
{
v___x_2934_ = v___x_2896_;
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
else
{
lean_inc(v_a_2932_);
lean_dec(v___x_2896_);
v___x_2934_ = lean_box(0);
v_isShared_2935_ = v_isSharedCheck_2939_;
goto v_resetjp_2933_;
}
v_resetjp_2933_:
{
lean_object* v___x_2937_; 
if (v_isShared_2935_ == 0)
{
v___x_2937_ = v___x_2934_;
goto v_reusejp_2936_;
}
else
{
lean_object* v_reuseFailAlloc_2938_; 
v_reuseFailAlloc_2938_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2938_, 0, v_a_2932_);
v___x_2937_ = v_reuseFailAlloc_2938_;
goto v_reusejp_2936_;
}
v_reusejp_2936_:
{
return v___x_2937_;
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
lean_object* v_a_2963_; lean_object* v___x_2965_; uint8_t v_isShared_2966_; uint8_t v_isSharedCheck_2970_; 
lean_dec_ref(v_argVars_2841_);
lean_dec_ref(v_inst_2838_);
lean_dec_ref(v_a_2835_);
v_a_2963_ = lean_ctor_get(v___x_2869_, 0);
v_isSharedCheck_2970_ = !lean_is_exclusive(v___x_2869_);
if (v_isSharedCheck_2970_ == 0)
{
v___x_2965_ = v___x_2869_;
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
else
{
lean_inc(v_a_2963_);
lean_dec(v___x_2869_);
v___x_2965_ = lean_box(0);
v_isShared_2966_ = v_isSharedCheck_2970_;
goto v_resetjp_2964_;
}
v_resetjp_2964_:
{
lean_object* v___x_2968_; 
if (v_isShared_2966_ == 0)
{
v___x_2968_ = v___x_2965_;
goto v_reusejp_2967_;
}
else
{
lean_object* v_reuseFailAlloc_2969_; 
v_reuseFailAlloc_2969_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2969_, 0, v_a_2963_);
v___x_2968_ = v_reuseFailAlloc_2969_;
goto v_reusejp_2967_;
}
v_reusejp_2967_:
{
return v___x_2968_;
}
}
}
}
else
{
lean_object* v_a_2971_; lean_object* v___x_2973_; uint8_t v_isShared_2974_; uint8_t v_isSharedCheck_2978_; 
lean_dec_ref(v_argVars_2841_);
lean_dec_ref(v_a_2839_);
lean_dec_ref(v_inst_2838_);
lean_dec_ref(v_fst_2836_);
lean_dec_ref(v_a_2835_);
v_a_2971_ = lean_ctor_get(v___x_2861_, 0);
v_isSharedCheck_2978_ = !lean_is_exclusive(v___x_2861_);
if (v_isSharedCheck_2978_ == 0)
{
v___x_2973_ = v___x_2861_;
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
else
{
lean_inc(v_a_2971_);
lean_dec(v___x_2861_);
v___x_2973_ = lean_box(0);
v_isShared_2974_ = v_isSharedCheck_2978_;
goto v_resetjp_2972_;
}
v_resetjp_2972_:
{
lean_object* v___x_2976_; 
if (v_isShared_2974_ == 0)
{
v___x_2976_ = v___x_2973_;
goto v_reusejp_2975_;
}
else
{
lean_object* v_reuseFailAlloc_2977_; 
v_reuseFailAlloc_2977_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2977_, 0, v_a_2971_);
v___x_2976_ = v_reuseFailAlloc_2977_;
goto v_reusejp_2975_;
}
v_reusejp_2975_:
{
return v___x_2976_;
}
}
}
}
else
{
lean_dec_ref(v_argVars_2841_);
lean_dec_ref(v_a_2839_);
lean_dec_ref(v_inst_2838_);
lean_dec_ref(v_fst_2836_);
lean_dec_ref(v_a_2835_);
return v___x_2848_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_2979_, lean_object* v_fst_2980_, lean_object* v_fst_2981_, lean_object* v_inst_2982_, lean_object* v_a_2983_, lean_object* v_projInfo_x3f_2984_, lean_object* v_argVars_2985_, lean_object* v_x_2986_, lean_object* v___y_2987_, lean_object* v___y_2988_, lean_object* v___y_2989_, lean_object* v___y_2990_, lean_object* v___y_2991_){
_start:
{
lean_object* v_res_2992_; 
v_res_2992_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_2979_, v_fst_2980_, v_fst_2981_, v_inst_2982_, v_a_2983_, v_projInfo_x3f_2984_, v_argVars_2985_, v_x_2986_, v___y_2987_, v___y_2988_, v___y_2989_, v___y_2990_);
lean_dec(v___y_2990_);
lean_dec_ref(v___y_2989_);
lean_dec(v___y_2988_);
lean_dec_ref(v___y_2987_);
lean_dec_ref(v_x_2986_);
lean_dec(v_projInfo_x3f_2984_);
lean_dec_ref(v_fst_2981_);
return v_res_2992_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_2993_, lean_object* v_projInfo_x3f_2994_, lean_object* v_a_2995_, lean_object* v_a_2996_, lean_object* v_a_2997_, lean_object* v_a_2998_){
_start:
{
lean_object* v_keyedConfig_3000_; uint8_t v_trackZetaDelta_3001_; lean_object* v_zetaDeltaSet_3002_; lean_object* v_lctx_3003_; lean_object* v_localInstances_3004_; lean_object* v_defEqCtx_x3f_3005_; lean_object* v_synthPendingDepth_3006_; lean_object* v_customCanUnfoldPredicate_x3f_3007_; uint8_t v_univApprox_3008_; uint8_t v_inTypeClassResolution_3009_; uint8_t v_cacheInferType_3010_; uint8_t v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; 
v_keyedConfig_3000_ = lean_ctor_get(v_a_2995_, 0);
v_trackZetaDelta_3001_ = lean_ctor_get_uint8(v_a_2995_, sizeof(void*)*7);
v_zetaDeltaSet_3002_ = lean_ctor_get(v_a_2995_, 1);
v_lctx_3003_ = lean_ctor_get(v_a_2995_, 2);
v_localInstances_3004_ = lean_ctor_get(v_a_2995_, 3);
v_defEqCtx_x3f_3005_ = lean_ctor_get(v_a_2995_, 4);
v_synthPendingDepth_3006_ = lean_ctor_get(v_a_2995_, 5);
v_customCanUnfoldPredicate_x3f_3007_ = lean_ctor_get(v_a_2995_, 6);
v_univApprox_3008_ = lean_ctor_get_uint8(v_a_2995_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3009_ = lean_ctor_get_uint8(v_a_2995_, sizeof(void*)*7 + 2);
v_cacheInferType_3010_ = lean_ctor_get_uint8(v_a_2995_, sizeof(void*)*7 + 3);
v___x_3011_ = 2;
lean_inc_ref(v_keyedConfig_3000_);
v___x_3012_ = l_Lean_Meta_ConfigWithKey_setTransparency(v___x_3011_, v_keyedConfig_3000_);
lean_inc(v_customCanUnfoldPredicate_x3f_3007_);
lean_inc(v_synthPendingDepth_3006_);
lean_inc(v_defEqCtx_x3f_3005_);
lean_inc_ref(v_localInstances_3004_);
lean_inc_ref(v_lctx_3003_);
lean_inc(v_zetaDeltaSet_3002_);
v___x_3013_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3013_, 0, v___x_3012_);
lean_ctor_set(v___x_3013_, 1, v_zetaDeltaSet_3002_);
lean_ctor_set(v___x_3013_, 2, v_lctx_3003_);
lean_ctor_set(v___x_3013_, 3, v_localInstances_3004_);
lean_ctor_set(v___x_3013_, 4, v_defEqCtx_x3f_3005_);
lean_ctor_set(v___x_3013_, 5, v_synthPendingDepth_3006_);
lean_ctor_set(v___x_3013_, 6, v_customCanUnfoldPredicate_x3f_3007_);
lean_ctor_set_uint8(v___x_3013_, sizeof(void*)*7, v_trackZetaDelta_3001_);
lean_ctor_set_uint8(v___x_3013_, sizeof(void*)*7 + 1, v_univApprox_3008_);
lean_ctor_set_uint8(v___x_3013_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3009_);
lean_ctor_set_uint8(v___x_3013_, sizeof(void*)*7 + 3, v_cacheInferType_3010_);
lean_inc(v_a_2998_);
lean_inc_ref(v_a_2997_);
lean_inc(v_a_2996_);
lean_inc_ref(v___x_3013_);
lean_inc_ref(v_inst_2993_);
v___x_3014_ = lean_infer_type(v_inst_2993_, v___x_3013_, v_a_2996_, v_a_2997_, v_a_2998_);
if (lean_obj_tag(v___x_3014_) == 0)
{
lean_object* v_a_3015_; lean_object* v___x_3016_; uint8_t v___x_3017_; lean_object* v___x_3018_; 
v_a_3015_ = lean_ctor_get(v___x_3014_, 0);
lean_inc_n(v_a_3015_, 2);
lean_dec_ref_known(v___x_3014_, 1);
v___x_3016_ = lean_box(0);
v___x_3017_ = 0;
v___x_3018_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3015_, v___x_3016_, v___x_3017_, v___x_3013_, v_a_2996_, v_a_2997_, v_a_2998_);
if (lean_obj_tag(v___x_3018_) == 0)
{
lean_object* v_a_3019_; lean_object* v_snd_3020_; lean_object* v_fst_3021_; lean_object* v_fst_3022_; lean_object* v_snd_3023_; lean_object* v___x_3024_; 
v_a_3019_ = lean_ctor_get(v___x_3018_, 0);
lean_inc(v_a_3019_);
lean_dec_ref_known(v___x_3018_, 1);
v_snd_3020_ = lean_ctor_get(v_a_3019_, 1);
lean_inc(v_snd_3020_);
v_fst_3021_ = lean_ctor_get(v_a_3019_, 0);
lean_inc(v_fst_3021_);
lean_dec(v_a_3019_);
v_fst_3022_ = lean_ctor_get(v_snd_3020_, 0);
lean_inc(v_fst_3022_);
v_snd_3023_ = lean_ctor_get(v_snd_3020_, 1);
lean_inc(v_snd_3023_);
lean_dec(v_snd_3020_);
lean_inc(v_a_2998_);
lean_inc_ref(v_a_2997_);
lean_inc(v_a_2996_);
lean_inc_ref(v___x_3013_);
v___x_3024_ = lean_whnf(v_snd_3023_, v___x_3013_, v_a_2996_, v_a_2997_, v_a_2998_);
if (lean_obj_tag(v___x_3024_) == 0)
{
lean_object* v_a_3025_; lean_object* v___f_3026_; uint8_t v___x_3027_; lean_object* v___x_3028_; 
v_a_3025_ = lean_ctor_get(v___x_3024_, 0);
lean_inc(v_a_3025_);
lean_dec_ref_known(v___x_3024_, 1);
lean_inc(v_a_3015_);
v___f_3026_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3026_, 0, v_a_3025_);
lean_closure_set(v___f_3026_, 1, v_fst_3021_);
lean_closure_set(v___f_3026_, 2, v_fst_3022_);
lean_closure_set(v___f_3026_, 3, v_inst_2993_);
lean_closure_set(v___f_3026_, 4, v_a_3015_);
lean_closure_set(v___f_3026_, 5, v_projInfo_x3f_2994_);
v___x_3027_ = 0;
v___x_3028_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3015_, v___f_3026_, v___x_3027_, v___x_3027_, v___x_3013_, v_a_2996_, v_a_2997_, v_a_2998_);
lean_dec_ref_known(v___x_3013_, 7);
return v___x_3028_;
}
else
{
lean_object* v_a_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3036_; 
lean_dec(v_fst_3022_);
lean_dec(v_fst_3021_);
lean_dec(v_a_3015_);
lean_dec_ref_known(v___x_3013_, 7);
lean_dec(v_projInfo_x3f_2994_);
lean_dec_ref(v_inst_2993_);
v_a_3029_ = lean_ctor_get(v___x_3024_, 0);
v_isSharedCheck_3036_ = !lean_is_exclusive(v___x_3024_);
if (v_isSharedCheck_3036_ == 0)
{
v___x_3031_ = v___x_3024_;
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_a_3029_);
lean_dec(v___x_3024_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3036_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3034_; 
if (v_isShared_3032_ == 0)
{
v___x_3034_ = v___x_3031_;
goto v_reusejp_3033_;
}
else
{
lean_object* v_reuseFailAlloc_3035_; 
v_reuseFailAlloc_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3035_, 0, v_a_3029_);
v___x_3034_ = v_reuseFailAlloc_3035_;
goto v_reusejp_3033_;
}
v_reusejp_3033_:
{
return v___x_3034_;
}
}
}
}
else
{
lean_object* v_a_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3044_; 
lean_dec(v_a_3015_);
lean_dec_ref_known(v___x_3013_, 7);
lean_dec(v_projInfo_x3f_2994_);
lean_dec_ref(v_inst_2993_);
v_a_3037_ = lean_ctor_get(v___x_3018_, 0);
v_isSharedCheck_3044_ = !lean_is_exclusive(v___x_3018_);
if (v_isSharedCheck_3044_ == 0)
{
v___x_3039_ = v___x_3018_;
v_isShared_3040_ = v_isSharedCheck_3044_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_a_3037_);
lean_dec(v___x_3018_);
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
else
{
lean_object* v_a_3045_; lean_object* v___x_3047_; uint8_t v_isShared_3048_; uint8_t v_isSharedCheck_3052_; 
lean_dec_ref_known(v___x_3013_, 7);
lean_dec(v_projInfo_x3f_2994_);
lean_dec_ref(v_inst_2993_);
v_a_3045_ = lean_ctor_get(v___x_3014_, 0);
v_isSharedCheck_3052_ = !lean_is_exclusive(v___x_3014_);
if (v_isSharedCheck_3052_ == 0)
{
v___x_3047_ = v___x_3014_;
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
else
{
lean_inc(v_a_3045_);
lean_dec(v___x_3014_);
v___x_3047_ = lean_box(0);
v_isShared_3048_ = v_isSharedCheck_3052_;
goto v_resetjp_3046_;
}
v_resetjp_3046_:
{
lean_object* v___x_3050_; 
if (v_isShared_3048_ == 0)
{
v___x_3050_ = v___x_3047_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v_a_3045_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_3053_, lean_object* v_projInfo_x3f_3054_, lean_object* v_a_3055_, lean_object* v_a_3056_, lean_object* v_a_3057_, lean_object* v_a_3058_, lean_object* v_a_3059_){
_start:
{
lean_object* v_res_3060_; 
v_res_3060_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_3053_, v_projInfo_x3f_3054_, v_a_3055_, v_a_3056_, v_a_3057_, v_a_3058_);
lean_dec(v_a_3058_);
lean_dec_ref(v_a_3057_);
lean_dec(v_a_3056_);
lean_dec_ref(v_a_3055_);
return v_res_3060_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_3061_, lean_object* v___x_3062_, lean_object* v_a_3063_, lean_object* v_inst_3064_, lean_object* v_R_3065_, lean_object* v_a_3066_, lean_object* v_b_3067_, lean_object* v_c_3068_, lean_object* v___y_3069_, lean_object* v___y_3070_, lean_object* v___y_3071_, lean_object* v___y_3072_){
_start:
{
lean_object* v___x_3074_; 
v___x_3074_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_3061_, v___x_3062_, v_a_3063_, v_a_3066_, v_b_3067_);
return v___x_3074_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_3075_, lean_object* v___x_3076_, lean_object* v_a_3077_, lean_object* v_inst_3078_, lean_object* v_R_3079_, lean_object* v_a_3080_, lean_object* v_b_3081_, lean_object* v_c_3082_, lean_object* v___y_3083_, lean_object* v___y_3084_, lean_object* v___y_3085_, lean_object* v___y_3086_, lean_object* v___y_3087_){
_start:
{
lean_object* v_res_3088_; 
v_res_3088_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_3075_, v___x_3076_, v_a_3077_, v_inst_3078_, v_R_3079_, v_a_3080_, v_b_3081_, v_c_3082_, v___y_3083_, v___y_3084_, v___y_3085_, v___y_3086_);
lean_dec(v___y_3086_);
lean_dec_ref(v___y_3085_);
lean_dec(v___y_3084_);
lean_dec_ref(v___y_3083_);
lean_dec_ref(v_a_3077_);
lean_dec(v___x_3076_);
lean_dec(v_upperBound_3075_);
return v_res_3088_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3089_, lean_object* v_msg_3090_, lean_object* v___y_3091_, lean_object* v___y_3092_, lean_object* v___y_3093_, lean_object* v___y_3094_){
_start:
{
lean_object* v___x_3096_; 
v___x_3096_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3090_, v___y_3091_, v___y_3092_, v___y_3093_, v___y_3094_);
return v___x_3096_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3097_, lean_object* v_msg_3098_, lean_object* v___y_3099_, lean_object* v___y_3100_, lean_object* v___y_3101_, lean_object* v___y_3102_, lean_object* v___y_3103_){
_start:
{
lean_object* v_res_3104_; 
v_res_3104_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3097_, v_msg_3098_, v___y_3099_, v___y_3100_, v___y_3101_, v___y_3102_);
lean_dec(v___y_3102_);
lean_dec_ref(v___y_3101_);
lean_dec(v___y_3100_);
lean_dec_ref(v___y_3099_);
return v_res_3104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_3105_, lean_object* v_argVars_3106_, lean_object* v_inst_3107_, lean_object* v_a_3108_, lean_object* v_projInfo_x3f_3109_, lean_object* v_inst_3110_, lean_object* v_a_3111_, lean_object* v___y_3112_, lean_object* v___y_3113_, lean_object* v___y_3114_, lean_object* v___y_3115_){
_start:
{
lean_object* v___x_3117_; 
v___x_3117_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_3105_, v_argVars_3106_, v_inst_3107_, v_a_3108_, v_projInfo_x3f_3109_, v_a_3111_, v___y_3112_, v___y_3113_, v___y_3114_, v___y_3115_);
return v___x_3117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_3118_, lean_object* v_argVars_3119_, lean_object* v_inst_3120_, lean_object* v_a_3121_, lean_object* v_projInfo_x3f_3122_, lean_object* v_inst_3123_, lean_object* v_a_3124_, lean_object* v___y_3125_, lean_object* v___y_3126_, lean_object* v___y_3127_, lean_object* v___y_3128_, lean_object* v___y_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_3118_, v_argVars_3119_, v_inst_3120_, v_a_3121_, v_projInfo_x3f_3122_, v_inst_3123_, v_a_3124_, v___y_3125_, v___y_3126_, v___y_3127_, v___y_3128_);
lean_dec(v___y_3128_);
lean_dec_ref(v___y_3127_);
lean_dec(v___y_3126_);
lean_dec_ref(v___y_3125_);
lean_dec(v_projInfo_x3f_3122_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(lean_object* v_type_3131_, lean_object* v_k_3132_, uint8_t v_cleanupAnnotations_3133_, lean_object* v___y_3134_, lean_object* v___y_3135_, lean_object* v___y_3136_, lean_object* v___y_3137_){
_start:
{
lean_object* v___f_3139_; uint8_t v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___f_3139_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3139_, 0, v_k_3132_);
v___x_3140_ = 0;
v___x_3141_ = lean_box(0);
v___x_3142_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3140_, v___x_3141_, v_type_3131_, v___f_3139_, v_cleanupAnnotations_3133_, v___x_3140_, v___y_3134_, v___y_3135_, v___y_3136_, v___y_3137_);
if (lean_obj_tag(v___x_3142_) == 0)
{
lean_object* v_a_3143_; lean_object* v___x_3145_; uint8_t v_isShared_3146_; uint8_t v_isSharedCheck_3150_; 
v_a_3143_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3150_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3150_ == 0)
{
v___x_3145_ = v___x_3142_;
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
else
{
lean_inc(v_a_3143_);
lean_dec(v___x_3142_);
v___x_3145_ = lean_box(0);
v_isShared_3146_ = v_isSharedCheck_3150_;
goto v_resetjp_3144_;
}
v_resetjp_3144_:
{
lean_object* v___x_3148_; 
if (v_isShared_3146_ == 0)
{
v___x_3148_ = v___x_3145_;
goto v_reusejp_3147_;
}
else
{
lean_object* v_reuseFailAlloc_3149_; 
v_reuseFailAlloc_3149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3149_, 0, v_a_3143_);
v___x_3148_ = v_reuseFailAlloc_3149_;
goto v_reusejp_3147_;
}
v_reusejp_3147_:
{
return v___x_3148_;
}
}
}
else
{
lean_object* v_a_3151_; lean_object* v___x_3153_; uint8_t v_isShared_3154_; uint8_t v_isSharedCheck_3158_; 
v_a_3151_ = lean_ctor_get(v___x_3142_, 0);
v_isSharedCheck_3158_ = !lean_is_exclusive(v___x_3142_);
if (v_isSharedCheck_3158_ == 0)
{
v___x_3153_ = v___x_3142_;
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
else
{
lean_inc(v_a_3151_);
lean_dec(v___x_3142_);
v___x_3153_ = lean_box(0);
v_isShared_3154_ = v_isSharedCheck_3158_;
goto v_resetjp_3152_;
}
v_resetjp_3152_:
{
lean_object* v___x_3156_; 
if (v_isShared_3154_ == 0)
{
v___x_3156_ = v___x_3153_;
goto v_reusejp_3155_;
}
else
{
lean_object* v_reuseFailAlloc_3157_; 
v_reuseFailAlloc_3157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3157_, 0, v_a_3151_);
v___x_3156_ = v_reuseFailAlloc_3157_;
goto v_reusejp_3155_;
}
v_reusejp_3155_:
{
return v___x_3156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg___boxed(lean_object* v_type_3159_, lean_object* v_k_3160_, lean_object* v_cleanupAnnotations_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_, lean_object* v___y_3164_, lean_object* v___y_3165_, lean_object* v___y_3166_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3167_; lean_object* v_res_3168_; 
v_cleanupAnnotations_boxed_3167_ = lean_unbox(v_cleanupAnnotations_3161_);
v_res_3168_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3159_, v_k_3160_, v_cleanupAnnotations_boxed_3167_, v___y_3162_, v___y_3163_, v___y_3164_, v___y_3165_);
lean_dec(v___y_3165_);
lean_dec_ref(v___y_3164_);
lean_dec(v___y_3163_);
lean_dec_ref(v___y_3162_);
return v_res_3168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(lean_object* v_00_u03b1_3169_, lean_object* v_type_3170_, lean_object* v_k_3171_, uint8_t v_cleanupAnnotations_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_, lean_object* v___y_3176_){
_start:
{
lean_object* v___x_3178_; 
v___x_3178_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3170_, v_k_3171_, v_cleanupAnnotations_3172_, v___y_3173_, v___y_3174_, v___y_3175_, v___y_3176_);
return v___x_3178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___boxed(lean_object* v_00_u03b1_3179_, lean_object* v_type_3180_, lean_object* v_k_3181_, lean_object* v_cleanupAnnotations_3182_, lean_object* v___y_3183_, lean_object* v___y_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3188_; lean_object* v_res_3189_; 
v_cleanupAnnotations_boxed_3188_ = lean_unbox(v_cleanupAnnotations_3182_);
v_res_3189_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(v_00_u03b1_3179_, v_type_3180_, v_k_3181_, v_cleanupAnnotations_boxed_3188_, v___y_3183_, v___y_3184_, v___y_3185_, v___y_3186_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v___y_3184_);
lean_dec_ref(v___y_3183_);
return v_res_3189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(lean_object* v_as_3190_, size_t v_sz_3191_, size_t v_i_3192_, lean_object* v_b_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v_a_3200_; uint8_t v___x_3204_; 
v___x_3204_ = lean_usize_dec_lt(v_i_3192_, v_sz_3191_);
if (v___x_3204_ == 0)
{
lean_object* v___x_3205_; 
v___x_3205_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3205_, 0, v_b_3193_);
return v___x_3205_;
}
else
{
lean_object* v_a_3206_; lean_object* v___x_3207_; lean_object* v___x_3208_; 
v_a_3206_ = lean_array_uget_borrowed(v_as_3190_, v_i_3192_);
v___x_3207_ = l_Lean_Expr_fvarId_x21(v_a_3206_);
lean_inc(v___x_3207_);
v___x_3208_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_3207_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3208_) == 0)
{
lean_object* v_a_3209_; lean_object* v___x_3210_; uint8_t v___x_3211_; uint8_t v___x_3212_; 
v_a_3209_ = lean_ctor_get(v___x_3208_, 0);
lean_inc(v_a_3209_);
lean_dec_ref_known(v___x_3208_, 1);
v___x_3210_ = lean_box(0);
v___x_3211_ = lean_unbox(v_a_3209_);
lean_dec(v_a_3209_);
v___x_3212_ = l_Lean_BinderInfo_isInstImplicit(v___x_3211_);
if (v___x_3212_ == 0)
{
lean_dec(v___x_3207_);
v_a_3200_ = v___x_3210_;
goto v___jp_3199_;
}
else
{
lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; 
v___x_3213_ = lean_st_ref_take(v___y_3194_);
v___x_3214_ = l_Lean_CollectFVars_State_add(v___x_3213_, v___x_3207_);
v___x_3215_ = lean_st_ref_set(v___y_3194_, v___x_3214_);
v_a_3200_ = v___x_3210_;
goto v___jp_3199_;
}
}
else
{
lean_object* v_a_3216_; lean_object* v___x_3218_; uint8_t v_isShared_3219_; uint8_t v_isSharedCheck_3223_; 
lean_dec(v___x_3207_);
v_a_3216_ = lean_ctor_get(v___x_3208_, 0);
v_isSharedCheck_3223_ = !lean_is_exclusive(v___x_3208_);
if (v_isSharedCheck_3223_ == 0)
{
v___x_3218_ = v___x_3208_;
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
else
{
lean_inc(v_a_3216_);
lean_dec(v___x_3208_);
v___x_3218_ = lean_box(0);
v_isShared_3219_ = v_isSharedCheck_3223_;
goto v_resetjp_3217_;
}
v_resetjp_3217_:
{
lean_object* v___x_3221_; 
if (v_isShared_3219_ == 0)
{
v___x_3221_ = v___x_3218_;
goto v_reusejp_3220_;
}
else
{
lean_object* v_reuseFailAlloc_3222_; 
v_reuseFailAlloc_3222_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3222_, 0, v_a_3216_);
v___x_3221_ = v_reuseFailAlloc_3222_;
goto v_reusejp_3220_;
}
v_reusejp_3220_:
{
return v___x_3221_;
}
}
}
}
v___jp_3199_:
{
size_t v___x_3201_; size_t v___x_3202_; 
v___x_3201_ = ((size_t)1ULL);
v___x_3202_ = lean_usize_add(v_i_3192_, v___x_3201_);
v_i_3192_ = v___x_3202_;
v_b_3193_ = v_a_3200_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg___boxed(lean_object* v_as_3224_, lean_object* v_sz_3225_, lean_object* v_i_3226_, lean_object* v_b_3227_, lean_object* v___y_3228_, lean_object* v___y_3229_, lean_object* v___y_3230_, lean_object* v___y_3231_, lean_object* v___y_3232_){
_start:
{
size_t v_sz_boxed_3233_; size_t v_i_boxed_3234_; lean_object* v_res_3235_; 
v_sz_boxed_3233_ = lean_unbox_usize(v_sz_3225_);
lean_dec(v_sz_3225_);
v_i_boxed_3234_ = lean_unbox_usize(v_i_3226_);
lean_dec(v_i_3226_);
v_res_3235_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_as_3224_, v_sz_boxed_3233_, v_i_boxed_3234_, v_b_3227_, v___y_3228_, v___y_3229_, v___y_3230_, v___y_3231_);
lean_dec(v___y_3231_);
lean_dec_ref(v___y_3230_);
lean_dec_ref(v___y_3229_);
lean_dec(v___y_3228_);
lean_dec_ref(v_as_3224_);
return v_res_3235_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object* v_k_3236_, lean_object* v_t_3237_){
_start:
{
if (lean_obj_tag(v_t_3237_) == 0)
{
lean_object* v_k_3238_; lean_object* v_l_3239_; lean_object* v_r_3240_; uint8_t v___x_3241_; 
v_k_3238_ = lean_ctor_get(v_t_3237_, 1);
v_l_3239_ = lean_ctor_get(v_t_3237_, 3);
v_r_3240_ = lean_ctor_get(v_t_3237_, 4);
v___x_3241_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3236_, v_k_3238_);
switch(v___x_3241_)
{
case 0:
{
v_t_3237_ = v_l_3239_;
goto _start;
}
case 1:
{
uint8_t v___x_3243_; 
v___x_3243_ = 1;
return v___x_3243_;
}
default: 
{
v_t_3237_ = v_r_3240_;
goto _start;
}
}
}
else
{
uint8_t v___x_3245_; 
v___x_3245_ = 0;
return v___x_3245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object* v_k_3246_, lean_object* v_t_3247_){
_start:
{
uint8_t v_res_3248_; lean_object* v_r_3249_; 
v_res_3248_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3246_, v_t_3247_);
lean_dec(v_t_3247_);
lean_dec(v_k_3246_);
v_r_3249_ = lean_box(v_res_3248_);
return v_r_3249_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3251_; lean_object* v___x_3252_; 
v___x_3251_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__0));
v___x_3252_ = l_Lean_stringToMessageData(v___x_3251_);
return v___x_3252_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3254_; lean_object* v___x_3255_; 
v___x_3254_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__2));
v___x_3255_ = l_Lean_stringToMessageData(v___x_3254_);
return v___x_3255_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(lean_object* v_a_3256_, lean_object* v_as_3257_, size_t v_sz_3258_, size_t v_i_3259_, lean_object* v_b_3260_, lean_object* v___y_3261_, lean_object* v___y_3262_, lean_object* v___y_3263_){
_start:
{
lean_object* v_a_3266_; uint8_t v___x_3270_; 
v___x_3270_ = lean_usize_dec_lt(v_i_3259_, v_sz_3258_);
if (v___x_3270_ == 0)
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3271_, 0, v_b_3260_);
return v___x_3271_;
}
else
{
lean_object* v_snd_3272_; 
v_snd_3272_ = lean_ctor_get(v_b_3260_, 1);
lean_inc(v_snd_3272_);
if (lean_obj_tag(v_snd_3272_) == 0)
{
lean_object* v_fst_3273_; lean_object* v___x_3275_; uint8_t v_isShared_3276_; uint8_t v_isSharedCheck_3281_; 
v_fst_3273_ = lean_ctor_get(v_b_3260_, 0);
v_isSharedCheck_3281_ = !lean_is_exclusive(v_b_3260_);
if (v_isSharedCheck_3281_ == 0)
{
lean_object* v_unused_3282_; 
v_unused_3282_ = lean_ctor_get(v_b_3260_, 1);
lean_dec(v_unused_3282_);
v___x_3275_ = v_b_3260_;
v_isShared_3276_ = v_isSharedCheck_3281_;
goto v_resetjp_3274_;
}
else
{
lean_inc(v_fst_3273_);
lean_dec(v_b_3260_);
v___x_3275_ = lean_box(0);
v_isShared_3276_ = v_isSharedCheck_3281_;
goto v_resetjp_3274_;
}
v_resetjp_3274_:
{
lean_object* v___x_3278_; 
if (v_isShared_3276_ == 0)
{
v___x_3278_ = v___x_3275_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3280_; 
v_reuseFailAlloc_3280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3280_, 0, v_fst_3273_);
lean_ctor_set(v_reuseFailAlloc_3280_, 1, v_snd_3272_);
v___x_3278_ = v_reuseFailAlloc_3280_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3279_, 0, v___x_3278_);
return v___x_3279_;
}
}
}
else
{
lean_object* v_fst_3283_; lean_object* v___x_3285_; uint8_t v_isShared_3286_; uint8_t v_isSharedCheck_3340_; 
v_fst_3283_ = lean_ctor_get(v_b_3260_, 0);
v_isSharedCheck_3340_ = !lean_is_exclusive(v_b_3260_);
if (v_isSharedCheck_3340_ == 0)
{
lean_object* v_unused_3341_; 
v_unused_3341_ = lean_ctor_get(v_b_3260_, 1);
lean_dec(v_unused_3341_);
v___x_3285_ = v_b_3260_;
v_isShared_3286_ = v_isSharedCheck_3340_;
goto v_resetjp_3284_;
}
else
{
lean_inc(v_fst_3283_);
lean_dec(v_b_3260_);
v___x_3285_ = lean_box(0);
v_isShared_3286_ = v_isSharedCheck_3340_;
goto v_resetjp_3284_;
}
v_resetjp_3284_:
{
lean_object* v_val_3287_; lean_object* v___x_3289_; uint8_t v_isShared_3290_; uint8_t v_isSharedCheck_3339_; 
v_val_3287_ = lean_ctor_get(v_snd_3272_, 0);
v_isSharedCheck_3339_ = !lean_is_exclusive(v_snd_3272_);
if (v_isSharedCheck_3339_ == 0)
{
v___x_3289_ = v_snd_3272_;
v_isShared_3290_ = v_isSharedCheck_3339_;
goto v_resetjp_3288_;
}
else
{
lean_inc(v_val_3287_);
lean_dec(v_snd_3272_);
v___x_3289_ = lean_box(0);
v_isShared_3290_ = v_isSharedCheck_3339_;
goto v_resetjp_3288_;
}
v_resetjp_3288_:
{
lean_object* v_fvarSet_3291_; lean_object* v_a_3292_; lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3296_; 
v_fvarSet_3291_ = lean_ctor_get(v_a_3256_, 1);
v_a_3292_ = lean_array_uget_borrowed(v_as_3257_, v_i_3259_);
v___x_3293_ = lean_unsigned_to_nat(1u);
v___x_3294_ = lean_nat_add(v_val_3287_, v___x_3293_);
if (v_isShared_3290_ == 0)
{
lean_ctor_set(v___x_3289_, 0, v___x_3294_);
v___x_3296_ = v___x_3289_;
goto v_reusejp_3295_;
}
else
{
lean_object* v_reuseFailAlloc_3338_; 
v_reuseFailAlloc_3338_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3338_, 0, v___x_3294_);
v___x_3296_ = v_reuseFailAlloc_3338_;
goto v_reusejp_3295_;
}
v_reusejp_3295_:
{
lean_object* v___x_3297_; uint8_t v___x_3298_; 
v___x_3297_ = l_Lean_Expr_fvarId_x21(v_a_3292_);
v___x_3298_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v___x_3297_, v_fvarSet_3291_);
if (v___x_3298_ == 0)
{
lean_object* v___x_3299_; 
v___x_3299_ = l_Lean_FVarId_getDecl___redArg(v___x_3297_, v___y_3261_, v___y_3262_, v___y_3263_);
if (lean_obj_tag(v___x_3299_) == 0)
{
lean_object* v_a_3300_; lean_object* v___x_3301_; 
v_a_3300_ = lean_ctor_get(v___x_3299_, 0);
lean_inc(v_a_3300_);
lean_dec_ref_known(v___x_3299_, 1);
v___x_3301_ = l_Lean_LocalDecl_ppAsBinder(v_a_3300_);
if (lean_obj_tag(v___x_3301_) == 1)
{
lean_object* v_val_3302_; lean_object* v___x_3304_; uint8_t v_isShared_3305_; uint8_t v_isSharedCheck_3323_; 
v_val_3302_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3323_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3323_ == 0)
{
v___x_3304_ = v___x_3301_;
v_isShared_3305_ = v_isSharedCheck_3323_;
goto v_resetjp_3303_;
}
else
{
lean_inc(v_val_3302_);
lean_dec(v___x_3301_);
v___x_3304_ = lean_box(0);
v_isShared_3305_ = v_isSharedCheck_3323_;
goto v_resetjp_3303_;
}
v_resetjp_3303_:
{
lean_object* v___x_3306_; lean_object* v___x_3307_; lean_object* v___x_3309_; 
v___x_3306_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1);
v___x_3307_ = l_Nat_reprFast(v_val_3287_);
if (v_isShared_3305_ == 0)
{
lean_ctor_set_tag(v___x_3304_, 3);
lean_ctor_set(v___x_3304_, 0, v___x_3307_);
v___x_3309_ = v___x_3304_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3322_; 
v_reuseFailAlloc_3322_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3322_, 0, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3322_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; lean_object* v___x_3313_; lean_object* v___x_3314_; lean_object* v___x_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3310_ = l_Lean_MessageData_ofFormat(v___x_3309_);
v___x_3311_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3311_, 0, v___x_3306_);
lean_ctor_set(v___x_3311_, 1, v___x_3310_);
v___x_3312_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3);
v___x_3313_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3313_, 0, v___x_3311_);
lean_ctor_set(v___x_3313_, 1, v___x_3312_);
v___x_3314_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3314_, 0, v___x_3313_);
lean_ctor_set(v___x_3314_, 1, v_val_3302_);
v___x_3315_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3316_, 0, v___x_3314_);
lean_ctor_set(v___x_3316_, 1, v___x_3315_);
v___x_3317_ = l_Lean_indentD(v___x_3316_);
v___x_3318_ = lean_array_push(v_fst_3283_, v___x_3317_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 1, v___x_3296_);
lean_ctor_set(v___x_3285_, 0, v___x_3318_);
v___x_3320_ = v___x_3285_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
lean_ctor_set(v_reuseFailAlloc_3321_, 1, v___x_3296_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
v_a_3266_ = v___x_3320_;
goto v___jp_3265_;
}
}
}
}
else
{
lean_object* v___x_3325_; 
lean_dec(v___x_3301_);
lean_dec(v_val_3287_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 1, v___x_3296_);
v___x_3325_ = v___x_3285_;
goto v_reusejp_3324_;
}
else
{
lean_object* v_reuseFailAlloc_3326_; 
v_reuseFailAlloc_3326_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3326_, 0, v_fst_3283_);
lean_ctor_set(v_reuseFailAlloc_3326_, 1, v___x_3296_);
v___x_3325_ = v_reuseFailAlloc_3326_;
goto v_reusejp_3324_;
}
v_reusejp_3324_:
{
v_a_3266_ = v___x_3325_;
goto v___jp_3265_;
}
}
}
else
{
lean_object* v_a_3327_; lean_object* v___x_3329_; uint8_t v_isShared_3330_; uint8_t v_isSharedCheck_3334_; 
lean_dec_ref(v___x_3296_);
lean_dec(v_val_3287_);
lean_del_object(v___x_3285_);
lean_dec(v_fst_3283_);
v_a_3327_ = lean_ctor_get(v___x_3299_, 0);
v_isSharedCheck_3334_ = !lean_is_exclusive(v___x_3299_);
if (v_isSharedCheck_3334_ == 0)
{
v___x_3329_ = v___x_3299_;
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
else
{
lean_inc(v_a_3327_);
lean_dec(v___x_3299_);
v___x_3329_ = lean_box(0);
v_isShared_3330_ = v_isSharedCheck_3334_;
goto v_resetjp_3328_;
}
v_resetjp_3328_:
{
lean_object* v___x_3332_; 
if (v_isShared_3330_ == 0)
{
v___x_3332_ = v___x_3329_;
goto v_reusejp_3331_;
}
else
{
lean_object* v_reuseFailAlloc_3333_; 
v_reuseFailAlloc_3333_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3333_, 0, v_a_3327_);
v___x_3332_ = v_reuseFailAlloc_3333_;
goto v_reusejp_3331_;
}
v_reusejp_3331_:
{
return v___x_3332_;
}
}
}
}
else
{
lean_object* v___x_3336_; 
lean_dec(v___x_3297_);
lean_dec(v_val_3287_);
if (v_isShared_3286_ == 0)
{
lean_ctor_set(v___x_3285_, 1, v___x_3296_);
v___x_3336_ = v___x_3285_;
goto v_reusejp_3335_;
}
else
{
lean_object* v_reuseFailAlloc_3337_; 
v_reuseFailAlloc_3337_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3337_, 0, v_fst_3283_);
lean_ctor_set(v_reuseFailAlloc_3337_, 1, v___x_3296_);
v___x_3336_ = v_reuseFailAlloc_3337_;
goto v_reusejp_3335_;
}
v_reusejp_3335_:
{
v_a_3266_ = v___x_3336_;
goto v___jp_3265_;
}
}
}
}
}
}
}
v___jp_3265_:
{
size_t v___x_3267_; size_t v___x_3268_; 
v___x_3267_ = ((size_t)1ULL);
v___x_3268_ = lean_usize_add(v_i_3259_, v___x_3267_);
v_i_3259_ = v___x_3268_;
v_b_3260_ = v_a_3266_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___boxed(lean_object* v_a_3342_, lean_object* v_as_3343_, lean_object* v_sz_3344_, lean_object* v_i_3345_, lean_object* v_b_3346_, lean_object* v___y_3347_, lean_object* v___y_3348_, lean_object* v___y_3349_, lean_object* v___y_3350_){
_start:
{
size_t v_sz_boxed_3351_; size_t v_i_boxed_3352_; lean_object* v_res_3353_; 
v_sz_boxed_3351_ = lean_unbox_usize(v_sz_3344_);
lean_dec(v_sz_3344_);
v_i_boxed_3352_ = lean_unbox_usize(v_i_3345_);
lean_dec(v_i_3345_);
v_res_3353_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3342_, v_as_3343_, v_sz_boxed_3351_, v_i_boxed_3352_, v_b_3346_, v___y_3347_, v___y_3348_, v___y_3349_);
lean_dec(v___y_3349_);
lean_dec_ref(v___y_3348_);
lean_dec_ref(v___y_3347_);
lean_dec_ref(v_as_3343_);
lean_dec_ref(v_a_3342_);
return v_res_3353_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(uint8_t v___y_3361_, uint8_t v_suppressElabErrors_3362_, lean_object* v_x_3363_){
_start:
{
if (lean_obj_tag(v_x_3363_) == 1)
{
lean_object* v_pre_3364_; 
v_pre_3364_ = lean_ctor_get(v_x_3363_, 0);
switch(lean_obj_tag(v_pre_3364_))
{
case 1:
{
lean_object* v_pre_3365_; 
v_pre_3365_ = lean_ctor_get(v_pre_3364_, 0);
switch(lean_obj_tag(v_pre_3365_))
{
case 0:
{
lean_object* v_str_3366_; lean_object* v_str_3367_; lean_object* v___x_3368_; uint8_t v___x_3369_; 
v_str_3366_ = lean_ctor_get(v_x_3363_, 1);
v_str_3367_ = lean_ctor_get(v_pre_3364_, 1);
v___x_3368_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__0));
v___x_3369_ = lean_string_dec_eq(v_str_3367_, v___x_3368_);
if (v___x_3369_ == 0)
{
lean_object* v___x_3370_; uint8_t v___x_3371_; 
v___x_3370_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__1));
v___x_3371_ = lean_string_dec_eq(v_str_3367_, v___x_3370_);
if (v___x_3371_ == 0)
{
return v___y_3361_;
}
else
{
lean_object* v___x_3372_; uint8_t v___x_3373_; 
v___x_3372_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__2));
v___x_3373_ = lean_string_dec_eq(v_str_3366_, v___x_3372_);
if (v___x_3373_ == 0)
{
return v___y_3361_;
}
else
{
return v_suppressElabErrors_3362_;
}
}
}
else
{
lean_object* v___x_3374_; uint8_t v___x_3375_; 
v___x_3374_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__3));
v___x_3375_ = lean_string_dec_eq(v_str_3366_, v___x_3374_);
if (v___x_3375_ == 0)
{
return v___y_3361_;
}
else
{
return v_suppressElabErrors_3362_;
}
}
}
case 1:
{
lean_object* v_pre_3376_; 
v_pre_3376_ = lean_ctor_get(v_pre_3365_, 0);
if (lean_obj_tag(v_pre_3376_) == 0)
{
lean_object* v_str_3377_; lean_object* v_str_3378_; lean_object* v_str_3379_; lean_object* v___x_3380_; uint8_t v___x_3381_; 
v_str_3377_ = lean_ctor_get(v_x_3363_, 1);
v_str_3378_ = lean_ctor_get(v_pre_3364_, 1);
v_str_3379_ = lean_ctor_get(v_pre_3365_, 1);
v___x_3380_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__4));
v___x_3381_ = lean_string_dec_eq(v_str_3379_, v___x_3380_);
if (v___x_3381_ == 0)
{
return v___y_3361_;
}
else
{
lean_object* v___x_3382_; uint8_t v___x_3383_; 
v___x_3382_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__5));
v___x_3383_ = lean_string_dec_eq(v_str_3378_, v___x_3382_);
if (v___x_3383_ == 0)
{
return v___y_3361_;
}
else
{
lean_object* v___x_3384_; uint8_t v___x_3385_; 
v___x_3384_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__6));
v___x_3385_ = lean_string_dec_eq(v_str_3377_, v___x_3384_);
if (v___x_3385_ == 0)
{
return v___y_3361_;
}
else
{
return v_suppressElabErrors_3362_;
}
}
}
}
else
{
return v___y_3361_;
}
}
default: 
{
return v___y_3361_;
}
}
}
case 0:
{
lean_object* v_str_3386_; lean_object* v___x_3387_; uint8_t v___x_3388_; 
v_str_3386_ = lean_ctor_get(v_x_3363_, 1);
v___x_3387_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3388_ = lean_string_dec_eq(v_str_3386_, v___x_3387_);
if (v___x_3388_ == 0)
{
return v___y_3361_;
}
else
{
return v_suppressElabErrors_3362_;
}
}
default: 
{
return v___y_3361_;
}
}
}
else
{
return v___y_3361_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed(lean_object* v___y_3389_, lean_object* v_suppressElabErrors_3390_, lean_object* v_x_3391_){
_start:
{
uint8_t v___y_11912__boxed_3392_; uint8_t v_suppressElabErrors_boxed_3393_; uint8_t v_res_3394_; lean_object* v_r_3395_; 
v___y_11912__boxed_3392_ = lean_unbox(v___y_3389_);
v_suppressElabErrors_boxed_3393_ = lean_unbox(v_suppressElabErrors_3390_);
v_res_3394_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(v___y_11912__boxed_3392_, v_suppressElabErrors_boxed_3393_, v_x_3391_);
lean_dec(v_x_3391_);
v_r_3395_ = lean_box(v_res_3394_);
return v_r_3395_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(lean_object* v_ref_3396_, lean_object* v_msgData_3397_, uint8_t v_severity_3398_, uint8_t v_isSilent_3399_, lean_object* v___y_3400_, lean_object* v___y_3401_, lean_object* v___y_3402_, lean_object* v___y_3403_){
_start:
{
lean_object* v___y_3406_; lean_object* v___y_3407_; lean_object* v___y_3408_; uint8_t v___y_3409_; lean_object* v___y_3410_; uint8_t v___y_3411_; lean_object* v___y_3412_; lean_object* v___y_3413_; lean_object* v___y_3414_; lean_object* v___y_3442_; lean_object* v___y_3443_; lean_object* v___y_3444_; uint8_t v___y_3445_; lean_object* v___y_3446_; uint8_t v___y_3447_; uint8_t v___y_3448_; lean_object* v___y_3449_; lean_object* v___y_3467_; lean_object* v___y_3468_; lean_object* v___y_3469_; lean_object* v___y_3470_; uint8_t v___y_3471_; uint8_t v___y_3472_; uint8_t v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3478_; lean_object* v___y_3479_; lean_object* v___y_3480_; uint8_t v___y_3481_; lean_object* v___y_3482_; uint8_t v___y_3483_; uint8_t v___y_3484_; uint8_t v___x_3489_; lean_object* v___y_3491_; lean_object* v___y_3492_; lean_object* v___y_3493_; uint8_t v___y_3494_; lean_object* v___y_3495_; uint8_t v___y_3496_; uint8_t v___y_3497_; uint8_t v___y_3499_; uint8_t v___x_3514_; 
v___x_3489_ = 2;
v___x_3514_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3398_, v___x_3489_);
if (v___x_3514_ == 0)
{
v___y_3499_ = v___x_3514_;
goto v___jp_3498_;
}
else
{
uint8_t v___x_3515_; 
lean_inc_ref(v_msgData_3397_);
v___x_3515_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3397_);
v___y_3499_ = v___x_3515_;
goto v___jp_3498_;
}
v___jp_3405_:
{
lean_object* v___x_3415_; lean_object* v_currNamespace_3416_; lean_object* v_openDecls_3417_; lean_object* v_env_3418_; lean_object* v_nextMacroScope_3419_; lean_object* v_ngen_3420_; lean_object* v_auxDeclNGen_3421_; lean_object* v_traceState_3422_; lean_object* v_cache_3423_; lean_object* v_messages_3424_; lean_object* v_infoState_3425_; lean_object* v_snapshotTasks_3426_; lean_object* v___x_3428_; uint8_t v_isShared_3429_; uint8_t v_isSharedCheck_3440_; 
v___x_3415_ = lean_st_ref_take(v___y_3414_);
v_currNamespace_3416_ = lean_ctor_get(v___y_3413_, 6);
v_openDecls_3417_ = lean_ctor_get(v___y_3413_, 7);
v_env_3418_ = lean_ctor_get(v___x_3415_, 0);
v_nextMacroScope_3419_ = lean_ctor_get(v___x_3415_, 1);
v_ngen_3420_ = lean_ctor_get(v___x_3415_, 2);
v_auxDeclNGen_3421_ = lean_ctor_get(v___x_3415_, 3);
v_traceState_3422_ = lean_ctor_get(v___x_3415_, 4);
v_cache_3423_ = lean_ctor_get(v___x_3415_, 5);
v_messages_3424_ = lean_ctor_get(v___x_3415_, 6);
v_infoState_3425_ = lean_ctor_get(v___x_3415_, 7);
v_snapshotTasks_3426_ = lean_ctor_get(v___x_3415_, 8);
v_isSharedCheck_3440_ = !lean_is_exclusive(v___x_3415_);
if (v_isSharedCheck_3440_ == 0)
{
v___x_3428_ = v___x_3415_;
v_isShared_3429_ = v_isSharedCheck_3440_;
goto v_resetjp_3427_;
}
else
{
lean_inc(v_snapshotTasks_3426_);
lean_inc(v_infoState_3425_);
lean_inc(v_messages_3424_);
lean_inc(v_cache_3423_);
lean_inc(v_traceState_3422_);
lean_inc(v_auxDeclNGen_3421_);
lean_inc(v_ngen_3420_);
lean_inc(v_nextMacroScope_3419_);
lean_inc(v_env_3418_);
lean_dec(v___x_3415_);
v___x_3428_ = lean_box(0);
v_isShared_3429_ = v_isSharedCheck_3440_;
goto v_resetjp_3427_;
}
v_resetjp_3427_:
{
lean_object* v___x_3430_; lean_object* v___x_3431_; lean_object* v___x_3432_; lean_object* v___x_3433_; lean_object* v___x_3435_; 
lean_inc(v_openDecls_3417_);
lean_inc(v_currNamespace_3416_);
v___x_3430_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3430_, 0, v_currNamespace_3416_);
lean_ctor_set(v___x_3430_, 1, v_openDecls_3417_);
v___x_3431_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3431_, 0, v___x_3430_);
lean_ctor_set(v___x_3431_, 1, v___y_3408_);
lean_inc_ref(v___y_3407_);
lean_inc_ref(v___y_3406_);
v___x_3432_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3432_, 0, v___y_3406_);
lean_ctor_set(v___x_3432_, 1, v___y_3410_);
lean_ctor_set(v___x_3432_, 2, v___y_3412_);
lean_ctor_set(v___x_3432_, 3, v___y_3407_);
lean_ctor_set(v___x_3432_, 4, v___x_3431_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*5, v___y_3409_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*5 + 1, v___y_3411_);
lean_ctor_set_uint8(v___x_3432_, sizeof(void*)*5 + 2, v_isSilent_3399_);
v___x_3433_ = l_Lean_MessageLog_add(v___x_3432_, v_messages_3424_);
if (v_isShared_3429_ == 0)
{
lean_ctor_set(v___x_3428_, 6, v___x_3433_);
v___x_3435_ = v___x_3428_;
goto v_reusejp_3434_;
}
else
{
lean_object* v_reuseFailAlloc_3439_; 
v_reuseFailAlloc_3439_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3439_, 0, v_env_3418_);
lean_ctor_set(v_reuseFailAlloc_3439_, 1, v_nextMacroScope_3419_);
lean_ctor_set(v_reuseFailAlloc_3439_, 2, v_ngen_3420_);
lean_ctor_set(v_reuseFailAlloc_3439_, 3, v_auxDeclNGen_3421_);
lean_ctor_set(v_reuseFailAlloc_3439_, 4, v_traceState_3422_);
lean_ctor_set(v_reuseFailAlloc_3439_, 5, v_cache_3423_);
lean_ctor_set(v_reuseFailAlloc_3439_, 6, v___x_3433_);
lean_ctor_set(v_reuseFailAlloc_3439_, 7, v_infoState_3425_);
lean_ctor_set(v_reuseFailAlloc_3439_, 8, v_snapshotTasks_3426_);
v___x_3435_ = v_reuseFailAlloc_3439_;
goto v_reusejp_3434_;
}
v_reusejp_3434_:
{
lean_object* v___x_3436_; lean_object* v___x_3437_; lean_object* v___x_3438_; 
v___x_3436_ = lean_st_ref_set(v___y_3414_, v___x_3435_);
v___x_3437_ = lean_box(0);
v___x_3438_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3438_, 0, v___x_3437_);
return v___x_3438_;
}
}
}
v___jp_3441_:
{
lean_object* v___x_3450_; lean_object* v___x_3451_; lean_object* v_a_3452_; lean_object* v___x_3454_; uint8_t v_isShared_3455_; uint8_t v_isSharedCheck_3465_; 
v___x_3450_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3397_);
v___x_3451_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3450_, v___y_3400_, v___y_3401_, v___y_3402_, v___y_3403_);
v_a_3452_ = lean_ctor_get(v___x_3451_, 0);
v_isSharedCheck_3465_ = !lean_is_exclusive(v___x_3451_);
if (v_isSharedCheck_3465_ == 0)
{
v___x_3454_ = v___x_3451_;
v_isShared_3455_ = v_isSharedCheck_3465_;
goto v_resetjp_3453_;
}
else
{
lean_inc(v_a_3452_);
lean_dec(v___x_3451_);
v___x_3454_ = lean_box(0);
v_isShared_3455_ = v_isSharedCheck_3465_;
goto v_resetjp_3453_;
}
v_resetjp_3453_:
{
lean_object* v___x_3456_; lean_object* v___x_3457_; lean_object* v___x_3458_; lean_object* v___x_3459_; 
lean_inc_ref_n(v___y_3444_, 2);
v___x_3456_ = l_Lean_FileMap_toPosition(v___y_3444_, v___y_3446_);
lean_dec(v___y_3446_);
v___x_3457_ = l_Lean_FileMap_toPosition(v___y_3444_, v___y_3449_);
lean_dec(v___y_3449_);
v___x_3458_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3458_, 0, v___x_3457_);
v___x_3459_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3445_ == 0)
{
lean_del_object(v___x_3454_);
lean_dec_ref(v___y_3442_);
v___y_3406_ = v___y_3443_;
v___y_3407_ = v___x_3459_;
v___y_3408_ = v_a_3452_;
v___y_3409_ = v___y_3447_;
v___y_3410_ = v___x_3456_;
v___y_3411_ = v___y_3448_;
v___y_3412_ = v___x_3458_;
v___y_3413_ = v___y_3402_;
v___y_3414_ = v___y_3403_;
goto v___jp_3405_;
}
else
{
uint8_t v___x_3460_; 
lean_inc(v_a_3452_);
v___x_3460_ = l_Lean_MessageData_hasTag(v___y_3442_, v_a_3452_);
if (v___x_3460_ == 0)
{
lean_object* v___x_3461_; lean_object* v___x_3463_; 
lean_dec_ref_known(v___x_3458_, 1);
lean_dec_ref(v___x_3456_);
lean_dec(v_a_3452_);
v___x_3461_ = lean_box(0);
if (v_isShared_3455_ == 0)
{
lean_ctor_set(v___x_3454_, 0, v___x_3461_);
v___x_3463_ = v___x_3454_;
goto v_reusejp_3462_;
}
else
{
lean_object* v_reuseFailAlloc_3464_; 
v_reuseFailAlloc_3464_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3464_, 0, v___x_3461_);
v___x_3463_ = v_reuseFailAlloc_3464_;
goto v_reusejp_3462_;
}
v_reusejp_3462_:
{
return v___x_3463_;
}
}
else
{
lean_del_object(v___x_3454_);
v___y_3406_ = v___y_3443_;
v___y_3407_ = v___x_3459_;
v___y_3408_ = v_a_3452_;
v___y_3409_ = v___y_3447_;
v___y_3410_ = v___x_3456_;
v___y_3411_ = v___y_3448_;
v___y_3412_ = v___x_3458_;
v___y_3413_ = v___y_3402_;
v___y_3414_ = v___y_3403_;
goto v___jp_3405_;
}
}
}
}
v___jp_3466_:
{
lean_object* v___x_3475_; 
v___x_3475_ = l_Lean_Syntax_getTailPos_x3f(v___y_3469_, v___y_3472_);
lean_dec(v___y_3469_);
if (lean_obj_tag(v___x_3475_) == 0)
{
lean_inc(v___y_3474_);
v___y_3442_ = v___y_3467_;
v___y_3443_ = v___y_3468_;
v___y_3444_ = v___y_3470_;
v___y_3445_ = v___y_3471_;
v___y_3446_ = v___y_3474_;
v___y_3447_ = v___y_3472_;
v___y_3448_ = v___y_3473_;
v___y_3449_ = v___y_3474_;
goto v___jp_3441_;
}
else
{
lean_object* v_val_3476_; 
v_val_3476_ = lean_ctor_get(v___x_3475_, 0);
lean_inc(v_val_3476_);
lean_dec_ref_known(v___x_3475_, 1);
v___y_3442_ = v___y_3467_;
v___y_3443_ = v___y_3468_;
v___y_3444_ = v___y_3470_;
v___y_3445_ = v___y_3471_;
v___y_3446_ = v___y_3474_;
v___y_3447_ = v___y_3472_;
v___y_3448_ = v___y_3473_;
v___y_3449_ = v_val_3476_;
goto v___jp_3441_;
}
}
v___jp_3477_:
{
lean_object* v_ref_3485_; lean_object* v___x_3486_; 
v_ref_3485_ = l_Lean_replaceRef(v_ref_3396_, v___y_3482_);
v___x_3486_ = l_Lean_Syntax_getPos_x3f(v_ref_3485_, v___y_3483_);
if (lean_obj_tag(v___x_3486_) == 0)
{
lean_object* v___x_3487_; 
v___x_3487_ = lean_unsigned_to_nat(0u);
v___y_3467_ = v___y_3478_;
v___y_3468_ = v___y_3479_;
v___y_3469_ = v_ref_3485_;
v___y_3470_ = v___y_3480_;
v___y_3471_ = v___y_3481_;
v___y_3472_ = v___y_3483_;
v___y_3473_ = v___y_3484_;
v___y_3474_ = v___x_3487_;
goto v___jp_3466_;
}
else
{
lean_object* v_val_3488_; 
v_val_3488_ = lean_ctor_get(v___x_3486_, 0);
lean_inc(v_val_3488_);
lean_dec_ref_known(v___x_3486_, 1);
v___y_3467_ = v___y_3478_;
v___y_3468_ = v___y_3479_;
v___y_3469_ = v_ref_3485_;
v___y_3470_ = v___y_3480_;
v___y_3471_ = v___y_3481_;
v___y_3472_ = v___y_3483_;
v___y_3473_ = v___y_3484_;
v___y_3474_ = v_val_3488_;
goto v___jp_3466_;
}
}
v___jp_3490_:
{
if (v___y_3497_ == 0)
{
v___y_3478_ = v___y_3491_;
v___y_3479_ = v___y_3492_;
v___y_3480_ = v___y_3493_;
v___y_3481_ = v___y_3494_;
v___y_3482_ = v___y_3495_;
v___y_3483_ = v___y_3496_;
v___y_3484_ = v_severity_3398_;
goto v___jp_3477_;
}
else
{
v___y_3478_ = v___y_3491_;
v___y_3479_ = v___y_3492_;
v___y_3480_ = v___y_3493_;
v___y_3481_ = v___y_3494_;
v___y_3482_ = v___y_3495_;
v___y_3483_ = v___y_3496_;
v___y_3484_ = v___x_3489_;
goto v___jp_3477_;
}
}
v___jp_3498_:
{
if (v___y_3499_ == 0)
{
lean_object* v_fileName_3500_; lean_object* v_fileMap_3501_; lean_object* v_options_3502_; lean_object* v_ref_3503_; uint8_t v_suppressElabErrors_3504_; lean_object* v___x_3505_; lean_object* v___x_3506_; lean_object* v___f_3507_; uint8_t v___x_3508_; uint8_t v___x_3509_; 
v_fileName_3500_ = lean_ctor_get(v___y_3402_, 0);
v_fileMap_3501_ = lean_ctor_get(v___y_3402_, 1);
v_options_3502_ = lean_ctor_get(v___y_3402_, 2);
v_ref_3503_ = lean_ctor_get(v___y_3402_, 5);
v_suppressElabErrors_3504_ = lean_ctor_get_uint8(v___y_3402_, sizeof(void*)*14 + 1);
v___x_3505_ = lean_box(v___y_3499_);
v___x_3506_ = lean_box(v_suppressElabErrors_3504_);
v___f_3507_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3507_, 0, v___x_3505_);
lean_closure_set(v___f_3507_, 1, v___x_3506_);
v___x_3508_ = 1;
v___x_3509_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3398_, v___x_3508_);
if (v___x_3509_ == 0)
{
v___y_3491_ = v___f_3507_;
v___y_3492_ = v_fileName_3500_;
v___y_3493_ = v_fileMap_3501_;
v___y_3494_ = v_suppressElabErrors_3504_;
v___y_3495_ = v_ref_3503_;
v___y_3496_ = v___y_3499_;
v___y_3497_ = v___x_3509_;
goto v___jp_3490_;
}
else
{
lean_object* v___x_3510_; uint8_t v___x_3511_; 
v___x_3510_ = l_Lean_warningAsError;
v___x_3511_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3502_, v___x_3510_);
v___y_3491_ = v___f_3507_;
v___y_3492_ = v_fileName_3500_;
v___y_3493_ = v_fileMap_3501_;
v___y_3494_ = v_suppressElabErrors_3504_;
v___y_3495_ = v_ref_3503_;
v___y_3496_ = v___y_3499_;
v___y_3497_ = v___x_3511_;
goto v___jp_3490_;
}
}
else
{
lean_object* v___x_3512_; lean_object* v___x_3513_; 
lean_dec_ref(v_msgData_3397_);
v___x_3512_ = lean_box(0);
v___x_3513_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3513_, 0, v___x_3512_);
return v___x_3513_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___boxed(lean_object* v_ref_3516_, lean_object* v_msgData_3517_, lean_object* v_severity_3518_, lean_object* v_isSilent_3519_, lean_object* v___y_3520_, lean_object* v___y_3521_, lean_object* v___y_3522_, lean_object* v___y_3523_, lean_object* v___y_3524_){
_start:
{
uint8_t v_severity_boxed_3525_; uint8_t v_isSilent_boxed_3526_; lean_object* v_res_3527_; 
v_severity_boxed_3525_ = lean_unbox(v_severity_3518_);
v_isSilent_boxed_3526_ = lean_unbox(v_isSilent_3519_);
v_res_3527_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3516_, v_msgData_3517_, v_severity_boxed_3525_, v_isSilent_boxed_3526_, v___y_3520_, v___y_3521_, v___y_3522_, v___y_3523_);
lean_dec(v___y_3523_);
lean_dec_ref(v___y_3522_);
lean_dec(v___y_3521_);
lean_dec_ref(v___y_3520_);
lean_dec(v_ref_3516_);
return v_res_3527_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(lean_object* v_msgData_3528_, uint8_t v_severity_3529_, uint8_t v_isSilent_3530_, lean_object* v___y_3531_, lean_object* v___y_3532_, lean_object* v___y_3533_, lean_object* v___y_3534_){
_start:
{
lean_object* v_ref_3536_; lean_object* v___x_3537_; 
v_ref_3536_ = lean_ctor_get(v___y_3533_, 5);
v___x_3537_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3536_, v_msgData_3528_, v_severity_3529_, v_isSilent_3530_, v___y_3531_, v___y_3532_, v___y_3533_, v___y_3534_);
return v___x_3537_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3___boxed(lean_object* v_msgData_3538_, lean_object* v_severity_3539_, lean_object* v_isSilent_3540_, lean_object* v___y_3541_, lean_object* v___y_3542_, lean_object* v___y_3543_, lean_object* v___y_3544_, lean_object* v___y_3545_){
_start:
{
uint8_t v_severity_boxed_3546_; uint8_t v_isSilent_boxed_3547_; lean_object* v_res_3548_; 
v_severity_boxed_3546_ = lean_unbox(v_severity_3539_);
v_isSilent_boxed_3547_ = lean_unbox(v_isSilent_3540_);
v_res_3548_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3538_, v_severity_boxed_3546_, v_isSilent_boxed_3547_, v___y_3541_, v___y_3542_, v___y_3543_, v___y_3544_);
lean_dec(v___y_3544_);
lean_dec_ref(v___y_3543_);
lean_dec(v___y_3542_);
lean_dec_ref(v___y_3541_);
return v_res_3548_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object* v_msgData_3549_, lean_object* v___y_3550_, lean_object* v___y_3551_, lean_object* v___y_3552_, lean_object* v___y_3553_){
_start:
{
uint8_t v___x_3555_; uint8_t v___x_3556_; lean_object* v___x_3557_; 
v___x_3555_ = 1;
v___x_3556_ = 0;
v___x_3557_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3549_, v___x_3555_, v___x_3556_, v___y_3550_, v___y_3551_, v___y_3552_, v___y_3553_);
return v___x_3557_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object* v_msgData_3558_, lean_object* v___y_3559_, lean_object* v___y_3560_, lean_object* v___y_3561_, lean_object* v___y_3562_, lean_object* v___y_3563_){
_start:
{
lean_object* v_res_3564_; 
v_res_3564_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v_msgData_3558_, v___y_3559_, v___y_3560_, v___y_3561_, v___y_3562_);
lean_dec(v___y_3562_);
lean_dec_ref(v___y_3561_);
lean_dec(v___y_3560_);
lean_dec_ref(v___y_3559_);
return v_res_3564_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3566_; lean_object* v___x_3567_; 
v___x_3566_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0));
v___x_3567_ = l_Lean_stringToMessageData(v___x_3566_);
return v___x_3567_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3569_; lean_object* v___x_3570_; 
v___x_3569_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2));
v___x_3570_ = l_Lean_stringToMessageData(v___x_3569_);
return v___x_3570_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3571_; lean_object* v___x_3572_; lean_object* v___x_3573_; 
v___x_3571_ = lean_box(0);
v___x_3572_ = lean_unsigned_to_nat(16u);
v___x_3573_ = lean_mk_array(v___x_3572_, v___x_3571_);
return v___x_3573_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3574_; lean_object* v___x_3575_; lean_object* v___x_3576_; 
v___x_3574_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4);
v___x_3575_ = lean_unsigned_to_nat(0u);
v___x_3576_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3576_, 0, v___x_3575_);
lean_ctor_set(v___x_3576_, 1, v___x_3574_);
return v___x_3576_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3579_; lean_object* v___x_3580_; lean_object* v___x_3581_; lean_object* v___x_3582_; 
v___x_3579_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6));
v___x_3580_ = lean_box(1);
v___x_3581_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5);
v___x_3582_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3582_, 0, v___x_3581_);
lean_ctor_set(v___x_3582_, 1, v___x_3580_);
lean_ctor_set(v___x_3582_, 2, v___x_3579_);
return v___x_3582_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3589_; lean_object* v___x_3590_; 
v___x_3589_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10));
v___x_3590_ = l_Lean_stringToMessageData(v___x_3589_);
return v___x_3590_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13(void){
_start:
{
lean_object* v___x_3592_; lean_object* v___x_3593_; 
v___x_3592_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12));
v___x_3593_ = l_Lean_stringToMessageData(v___x_3592_);
return v___x_3593_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v___x_3595_, lean_object* v_args_3596_, lean_object* v_ty_3597_, lean_object* v___y_3598_, lean_object* v___y_3599_, lean_object* v___y_3600_, lean_object* v___y_3601_){
_start:
{
lean_object* v___y_3604_; lean_object* v___y_3605_; lean_object* v___y_3606_; lean_object* v___x_3620_; lean_object* v___x_3621_; lean_object* v___x_3622_; lean_object* v___y_3678_; lean_object* v___x_3679_; 
v___x_3620_ = lean_unsigned_to_nat(0u);
v___x_3621_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7);
v___x_3622_ = lean_st_mk_ref(v___x_3621_);
v___x_3679_ = l_Lean_Expr_collectFVars(v_ty_3597_, v___x_3622_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3679_) == 0)
{
lean_object* v___x_3680_; size_t v_sz_3681_; size_t v___x_3682_; lean_object* v___x_3683_; 
lean_dec_ref_known(v___x_3679_, 1);
v___x_3680_ = lean_box(0);
v_sz_3681_ = lean_array_size(v_args_3596_);
v___x_3682_ = ((size_t)0ULL);
v___x_3683_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_args_3596_, v_sz_3681_, v___x_3682_, v___x_3680_, v___x_3622_, v___y_3598_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3683_) == 0)
{
lean_dec_ref_known(v___x_3683_, 1);
goto v___jp_3623_;
}
else
{
v___y_3678_ = v___x_3683_;
goto v___jp_3677_;
}
}
else
{
v___y_3678_ = v___x_3679_;
goto v___jp_3677_;
}
v___jp_3603_:
{
lean_object* v___x_3607_; lean_object* v___x_3608_; lean_object* v___x_3609_; lean_object* v___x_3610_; lean_object* v___x_3611_; lean_object* v___x_3612_; lean_object* v___x_3613_; lean_object* v___x_3614_; lean_object* v___x_3615_; lean_object* v___x_3616_; uint8_t v___x_3617_; 
lean_inc_ref(v___y_3606_);
v___x_3607_ = l_Lean_stringToMessageData(v___y_3606_);
v___x_3608_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3608_, 0, v___y_3604_);
lean_ctor_set(v___x_3608_, 1, v___x_3607_);
v___x_3609_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1);
v___x_3610_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3610_, 0, v___x_3608_);
lean_ctor_set(v___x_3610_, 1, v___x_3609_);
v___x_3611_ = lean_array_to_list(v___y_3605_);
v___x_3612_ = l_Lean_MessageData_nil;
v___x_3613_ = l_Lean_MessageData_joinSep(v___x_3611_, v___x_3612_);
v___x_3614_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3614_, 0, v___x_3610_);
lean_ctor_set(v___x_3614_, 1, v___x_3613_);
v___x_3615_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3);
v___x_3616_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3616_, 0, v___x_3614_);
lean_ctor_set(v___x_3616_, 1, v___x_3615_);
v___x_3617_ = l_Lean_Expr_hasSorry(v___x_3595_);
if (v___x_3617_ == 0)
{
lean_object* v___x_3618_; 
v___x_3618_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3616_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
return v___x_3618_;
}
else
{
lean_object* v___x_3619_; 
v___x_3619_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_3616_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
return v___x_3619_;
}
}
v___jp_3623_:
{
lean_object* v___x_3624_; lean_object* v___x_3625_; 
v___x_3624_ = lean_st_ref_get(v___x_3622_);
lean_dec(v___x_3622_);
v___x_3625_ = l_Lean_CollectFVars_State_addDependencies(v___x_3624_, v___y_3598_, v___y_3599_, v___y_3600_, v___y_3601_);
if (lean_obj_tag(v___x_3625_) == 0)
{
lean_object* v_a_3626_; lean_object* v___x_3627_; lean_object* v___x_3628_; size_t v_sz_3629_; size_t v___x_3630_; lean_object* v___x_3631_; 
v_a_3626_ = lean_ctor_get(v___x_3625_, 0);
lean_inc(v_a_3626_);
lean_dec_ref_known(v___x_3625_, 1);
v___x_3627_ = lean_unsigned_to_nat(1u);
v___x_3628_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9));
v_sz_3629_ = lean_array_size(v_args_3596_);
v___x_3630_ = ((size_t)0ULL);
v___x_3631_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3626_, v_args_3596_, v_sz_3629_, v___x_3630_, v___x_3628_, v___y_3598_, v___y_3600_, v___y_3601_);
lean_dec(v_a_3626_);
if (lean_obj_tag(v___x_3631_) == 0)
{
lean_object* v_a_3632_; lean_object* v___x_3634_; uint8_t v_isShared_3635_; uint8_t v_isSharedCheck_3660_; 
v_a_3632_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3660_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3660_ == 0)
{
v___x_3634_ = v___x_3631_;
v_isShared_3635_ = v_isSharedCheck_3660_;
goto v_resetjp_3633_;
}
else
{
lean_inc(v_a_3632_);
lean_dec(v___x_3631_);
v___x_3634_ = lean_box(0);
v_isShared_3635_ = v_isSharedCheck_3660_;
goto v_resetjp_3633_;
}
v_resetjp_3633_:
{
lean_object* v_fst_3636_; lean_object* v___x_3638_; uint8_t v_isShared_3639_; uint8_t v_isSharedCheck_3658_; 
v_fst_3636_ = lean_ctor_get(v_a_3632_, 0);
v_isSharedCheck_3658_ = !lean_is_exclusive(v_a_3632_);
if (v_isSharedCheck_3658_ == 0)
{
lean_object* v_unused_3659_; 
v_unused_3659_ = lean_ctor_get(v_a_3632_, 1);
lean_dec(v_unused_3659_);
v___x_3638_ = v_a_3632_;
v_isShared_3639_ = v_isSharedCheck_3658_;
goto v_resetjp_3637_;
}
else
{
lean_inc(v_fst_3636_);
lean_dec(v_a_3632_);
v___x_3638_ = lean_box(0);
v_isShared_3639_ = v_isSharedCheck_3658_;
goto v_resetjp_3637_;
}
v_resetjp_3637_:
{
lean_object* v___x_3640_; uint8_t v___x_3641_; 
v___x_3640_ = lean_array_get_size(v_fst_3636_);
v___x_3641_ = lean_nat_dec_eq(v___x_3640_, v___x_3620_);
if (v___x_3641_ == 0)
{
lean_object* v___x_3642_; lean_object* v___x_3643_; lean_object* v___x_3644_; lean_object* v___x_3645_; lean_object* v___x_3647_; 
lean_del_object(v___x_3634_);
v___x_3642_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11);
v___x_3643_ = l_Nat_reprFast(v___x_3640_);
v___x_3644_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3644_, 0, v___x_3643_);
v___x_3645_ = l_Lean_MessageData_ofFormat(v___x_3644_);
if (v_isShared_3639_ == 0)
{
lean_ctor_set_tag(v___x_3638_, 7);
lean_ctor_set(v___x_3638_, 1, v___x_3645_);
lean_ctor_set(v___x_3638_, 0, v___x_3642_);
v___x_3647_ = v___x_3638_;
goto v_reusejp_3646_;
}
else
{
lean_object* v_reuseFailAlloc_3653_; 
v_reuseFailAlloc_3653_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3653_, 0, v___x_3642_);
lean_ctor_set(v_reuseFailAlloc_3653_, 1, v___x_3645_);
v___x_3647_ = v_reuseFailAlloc_3653_;
goto v_reusejp_3646_;
}
v_reusejp_3646_:
{
lean_object* v___x_3648_; lean_object* v___x_3649_; uint8_t v___x_3650_; 
v___x_3648_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13);
v___x_3649_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3649_, 0, v___x_3647_);
lean_ctor_set(v___x_3649_, 1, v___x_3648_);
v___x_3650_ = lean_nat_dec_eq(v___x_3640_, v___x_3627_);
if (v___x_3650_ == 0)
{
lean_object* v___x_3651_; 
v___x_3651_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14));
v___y_3604_ = v___x_3649_;
v___y_3605_ = v_fst_3636_;
v___y_3606_ = v___x_3651_;
goto v___jp_3603_;
}
else
{
lean_object* v___x_3652_; 
v___x_3652_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___y_3604_ = v___x_3649_;
v___y_3605_ = v_fst_3636_;
v___y_3606_ = v___x_3652_;
goto v___jp_3603_;
}
}
}
else
{
lean_object* v___x_3654_; lean_object* v___x_3656_; 
lean_del_object(v___x_3638_);
lean_dec(v_fst_3636_);
v___x_3654_ = lean_box(0);
if (v_isShared_3635_ == 0)
{
lean_ctor_set(v___x_3634_, 0, v___x_3654_);
v___x_3656_ = v___x_3634_;
goto v_reusejp_3655_;
}
else
{
lean_object* v_reuseFailAlloc_3657_; 
v_reuseFailAlloc_3657_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3657_, 0, v___x_3654_);
v___x_3656_ = v_reuseFailAlloc_3657_;
goto v_reusejp_3655_;
}
v_reusejp_3655_:
{
return v___x_3656_;
}
}
}
}
}
else
{
lean_object* v_a_3661_; lean_object* v___x_3663_; uint8_t v_isShared_3664_; uint8_t v_isSharedCheck_3668_; 
v_a_3661_ = lean_ctor_get(v___x_3631_, 0);
v_isSharedCheck_3668_ = !lean_is_exclusive(v___x_3631_);
if (v_isSharedCheck_3668_ == 0)
{
v___x_3663_ = v___x_3631_;
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
else
{
lean_inc(v_a_3661_);
lean_dec(v___x_3631_);
v___x_3663_ = lean_box(0);
v_isShared_3664_ = v_isSharedCheck_3668_;
goto v_resetjp_3662_;
}
v_resetjp_3662_:
{
lean_object* v___x_3666_; 
if (v_isShared_3664_ == 0)
{
v___x_3666_ = v___x_3663_;
goto v_reusejp_3665_;
}
else
{
lean_object* v_reuseFailAlloc_3667_; 
v_reuseFailAlloc_3667_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3667_, 0, v_a_3661_);
v___x_3666_ = v_reuseFailAlloc_3667_;
goto v_reusejp_3665_;
}
v_reusejp_3665_:
{
return v___x_3666_;
}
}
}
}
else
{
lean_object* v_a_3669_; lean_object* v___x_3671_; uint8_t v_isShared_3672_; uint8_t v_isSharedCheck_3676_; 
v_a_3669_ = lean_ctor_get(v___x_3625_, 0);
v_isSharedCheck_3676_ = !lean_is_exclusive(v___x_3625_);
if (v_isSharedCheck_3676_ == 0)
{
v___x_3671_ = v___x_3625_;
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
else
{
lean_inc(v_a_3669_);
lean_dec(v___x_3625_);
v___x_3671_ = lean_box(0);
v_isShared_3672_ = v_isSharedCheck_3676_;
goto v_resetjp_3670_;
}
v_resetjp_3670_:
{
lean_object* v___x_3674_; 
if (v_isShared_3672_ == 0)
{
v___x_3674_ = v___x_3671_;
goto v_reusejp_3673_;
}
else
{
lean_object* v_reuseFailAlloc_3675_; 
v_reuseFailAlloc_3675_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3675_, 0, v_a_3669_);
v___x_3674_ = v_reuseFailAlloc_3675_;
goto v_reusejp_3673_;
}
v_reusejp_3673_:
{
return v___x_3674_;
}
}
}
}
v___jp_3677_:
{
if (lean_obj_tag(v___y_3678_) == 0)
{
lean_dec_ref_known(v___y_3678_, 1);
goto v___jp_3623_;
}
else
{
lean_dec(v___x_3622_);
return v___y_3678_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v___x_3684_, lean_object* v_args_3685_, lean_object* v_ty_3686_, lean_object* v___y_3687_, lean_object* v___y_3688_, lean_object* v___y_3689_, lean_object* v___y_3690_, lean_object* v___y_3691_){
_start:
{
lean_object* v_res_3692_; 
v_res_3692_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v___x_3684_, v_args_3685_, v_ty_3686_, v___y_3687_, v___y_3688_, v___y_3689_, v___y_3690_);
lean_dec(v___y_3690_);
lean_dec_ref(v___y_3689_);
lean_dec(v___y_3688_);
lean_dec_ref(v___y_3687_);
lean_dec_ref(v_args_3685_);
lean_dec_ref(v___x_3684_);
return v_res_3692_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object* v_e_3693_){
_start:
{
lean_object* v___x_3694_; 
v___x_3694_ = l_Lean_Expr_cleanupAnnotations(v_e_3693_);
switch(lean_obj_tag(v___x_3694_))
{
case 7:
{
lean_object* v_body_3695_; uint8_t v_binderInfo_3696_; uint8_t v___x_3697_; 
v_body_3695_ = lean_ctor_get(v___x_3694_, 2);
lean_inc_ref(v_body_3695_);
v_binderInfo_3696_ = lean_ctor_get_uint8(v___x_3694_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3694_, 3);
v___x_3697_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3696_);
if (v___x_3697_ == 0)
{
lean_object* v___x_3698_; uint8_t v___x_3699_; 
v___x_3698_ = lean_unsigned_to_nat(0u);
v___x_3699_ = lean_expr_has_loose_bvar(v_body_3695_, v___x_3698_);
if (v___x_3699_ == 0)
{
uint8_t v___x_3700_; 
lean_dec_ref(v_body_3695_);
v___x_3700_ = 1;
return v___x_3700_;
}
else
{
v_e_3693_ = v_body_3695_;
goto _start;
}
}
else
{
v_e_3693_ = v_body_3695_;
goto _start;
}
}
case 8:
{
lean_object* v_body_3703_; 
v_body_3703_ = lean_ctor_get(v___x_3694_, 3);
lean_inc_ref(v_body_3703_);
lean_dec_ref_known(v___x_3694_, 4);
v_e_3693_ = v_body_3703_;
goto _start;
}
default: 
{
uint8_t v___x_3705_; 
lean_dec_ref(v___x_3694_);
v___x_3705_ = 0;
return v___x_3705_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_e_3706_){
_start:
{
uint8_t v_res_3707_; lean_object* v_r_3708_; 
v_res_3707_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_e_3706_);
v_r_3708_ = lean_box(v_res_3707_);
return v_r_3708_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_cinfo_3709_, lean_object* v_a_3710_, lean_object* v_a_3711_, lean_object* v_a_3712_, lean_object* v_a_3713_){
_start:
{
lean_object* v___x_3715_; uint8_t v___x_3716_; 
v___x_3715_ = l_Lean_ConstantInfo_type(v_cinfo_3709_);
lean_inc_ref(v___x_3715_);
v___x_3716_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(v___x_3715_);
if (v___x_3716_ == 0)
{
lean_object* v___x_3717_; lean_object* v___x_3718_; 
lean_dec_ref(v___x_3715_);
v___x_3717_ = lean_box(0);
v___x_3718_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3718_, 0, v___x_3717_);
return v___x_3718_;
}
else
{
lean_object* v___f_3719_; uint8_t v___x_3720_; lean_object* v___x_3721_; 
lean_inc_ref(v___x_3715_);
v___f_3719_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3719_, 0, v___x_3715_);
v___x_3720_ = 0;
v___x_3721_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v___x_3715_, v___f_3719_, v___x_3720_, v_a_3710_, v_a_3711_, v_a_3712_, v_a_3713_);
return v___x_3721_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_cinfo_3722_, lean_object* v_a_3723_, lean_object* v_a_3724_, lean_object* v_a_3725_, lean_object* v_a_3726_, lean_object* v_a_3727_){
_start:
{
lean_object* v_res_3728_; 
v_res_3728_ = l_Lean_Meta_checkImpossibleInstance(v_cinfo_3722_, v_a_3723_, v_a_3724_, v_a_3725_, v_a_3726_);
lean_dec(v_a_3726_);
lean_dec_ref(v_a_3725_);
lean_dec(v_a_3724_);
lean_dec_ref(v_a_3723_);
lean_dec_ref(v_cinfo_3722_);
return v_res_3728_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v_00_u03b2_3729_, lean_object* v_k_3730_, lean_object* v_t_3731_){
_start:
{
uint8_t v___x_3732_; 
v___x_3732_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3730_, v_t_3731_);
return v___x_3732_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v_00_u03b2_3733_, lean_object* v_k_3734_, lean_object* v_t_3735_){
_start:
{
uint8_t v_res_3736_; lean_object* v_r_3737_; 
v_res_3736_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(v_00_u03b2_3733_, v_k_3734_, v_t_3735_);
lean_dec(v_t_3735_);
lean_dec(v_k_3734_);
v_r_3737_ = lean_box(v_res_3736_);
return v_r_3737_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_a_3738_, lean_object* v_as_3739_, size_t v_sz_3740_, size_t v_i_3741_, lean_object* v_b_3742_, lean_object* v___y_3743_, lean_object* v___y_3744_, lean_object* v___y_3745_, lean_object* v___y_3746_){
_start:
{
lean_object* v___x_3748_; 
v___x_3748_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3738_, v_as_3739_, v_sz_3740_, v_i_3741_, v_b_3742_, v___y_3743_, v___y_3745_, v___y_3746_);
return v___x_3748_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_a_3749_, lean_object* v_as_3750_, lean_object* v_sz_3751_, lean_object* v_i_3752_, lean_object* v_b_3753_, lean_object* v___y_3754_, lean_object* v___y_3755_, lean_object* v___y_3756_, lean_object* v___y_3757_, lean_object* v___y_3758_){
_start:
{
size_t v_sz_boxed_3759_; size_t v_i_boxed_3760_; lean_object* v_res_3761_; 
v_sz_boxed_3759_ = lean_unbox_usize(v_sz_3751_);
lean_dec(v_sz_3751_);
v_i_boxed_3760_ = lean_unbox_usize(v_i_3752_);
lean_dec(v_i_3752_);
v_res_3761_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_a_3749_, v_as_3750_, v_sz_boxed_3759_, v_i_boxed_3760_, v_b_3753_, v___y_3754_, v___y_3755_, v___y_3756_, v___y_3757_);
lean_dec(v___y_3757_);
lean_dec_ref(v___y_3756_);
lean_dec(v___y_3755_);
lean_dec_ref(v___y_3754_);
lean_dec_ref(v_as_3750_);
lean_dec_ref(v_a_3749_);
return v_res_3761_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object* v_as_3762_, size_t v_sz_3763_, size_t v_i_3764_, lean_object* v_b_3765_, lean_object* v___y_3766_, lean_object* v___y_3767_, lean_object* v___y_3768_, lean_object* v___y_3769_, lean_object* v___y_3770_){
_start:
{
lean_object* v___x_3772_; 
v___x_3772_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_as_3762_, v_sz_3763_, v_i_3764_, v_b_3765_, v___y_3766_, v___y_3767_, v___y_3769_, v___y_3770_);
return v___x_3772_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object* v_as_3773_, lean_object* v_sz_3774_, lean_object* v_i_3775_, lean_object* v_b_3776_, lean_object* v___y_3777_, lean_object* v___y_3778_, lean_object* v___y_3779_, lean_object* v___y_3780_, lean_object* v___y_3781_, lean_object* v___y_3782_){
_start:
{
size_t v_sz_boxed_3783_; size_t v_i_boxed_3784_; lean_object* v_res_3785_; 
v_sz_boxed_3783_ = lean_unbox_usize(v_sz_3774_);
lean_dec(v_sz_3774_);
v_i_boxed_3784_ = lean_unbox_usize(v_i_3775_);
lean_dec(v_i_3775_);
v_res_3785_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(v_as_3773_, v_sz_boxed_3783_, v_i_boxed_3784_, v_b_3776_, v___y_3777_, v___y_3778_, v___y_3779_, v___y_3780_, v___y_3781_);
lean_dec(v___y_3781_);
lean_dec_ref(v___y_3780_);
lean_dec(v___y_3779_);
lean_dec_ref(v___y_3778_);
lean_dec(v___y_3777_);
lean_dec_ref(v_as_3773_);
return v_res_3785_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3787_; lean_object* v___x_3788_; 
v___x_3787_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3788_ = l_Lean_stringToMessageData(v___x_3787_);
return v___x_3788_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3790_; lean_object* v___x_3791_; 
v___x_3790_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3791_ = l_Lean_stringToMessageData(v___x_3790_);
return v___x_3791_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3793_; lean_object* v___x_3794_; 
v___x_3793_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3794_ = l_Lean_stringToMessageData(v___x_3793_);
return v___x_3794_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_c_3795_, lean_object* v_x_3796_, lean_object* v_target_3797_, lean_object* v___y_3798_, lean_object* v___y_3799_, lean_object* v___y_3800_, lean_object* v___y_3801_){
_start:
{
lean_object* v___x_3803_; 
lean_inc_ref(v_target_3797_);
v___x_3803_ = l_Lean_Meta_isClass_x3f(v_target_3797_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
if (lean_obj_tag(v___x_3803_) == 0)
{
lean_object* v_a_3804_; lean_object* v___x_3806_; uint8_t v_isShared_3807_; uint8_t v_isSharedCheck_3822_; 
v_a_3804_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3822_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3822_ == 0)
{
v___x_3806_ = v___x_3803_;
v_isShared_3807_ = v_isSharedCheck_3822_;
goto v_resetjp_3805_;
}
else
{
lean_inc(v_a_3804_);
lean_dec(v___x_3803_);
v___x_3806_ = lean_box(0);
v_isShared_3807_ = v_isSharedCheck_3822_;
goto v_resetjp_3805_;
}
v_resetjp_3805_:
{
if (lean_obj_tag(v_a_3804_) == 0)
{
lean_object* v___x_3808_; lean_object* v___x_3809_; lean_object* v___x_3810_; lean_object* v___x_3811_; lean_object* v___x_3812_; lean_object* v___x_3813_; lean_object* v___x_3814_; lean_object* v___x_3815_; lean_object* v___x_3816_; lean_object* v___x_3817_; 
lean_del_object(v___x_3806_);
v___x_3808_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3809_ = l_Lean_MessageData_ofExpr(v_c_3795_);
v___x_3810_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3810_, 0, v___x_3808_);
lean_ctor_set(v___x_3810_, 1, v___x_3809_);
v___x_3811_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3812_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3812_, 0, v___x_3810_);
lean_ctor_set(v___x_3812_, 1, v___x_3811_);
v___x_3813_ = l_Lean_MessageData_ofExpr(v_target_3797_);
v___x_3814_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3814_, 0, v___x_3812_);
lean_ctor_set(v___x_3814_, 1, v___x_3813_);
v___x_3815_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3816_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3816_, 0, v___x_3814_);
lean_ctor_set(v___x_3816_, 1, v___x_3815_);
v___x_3817_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3816_, v___y_3798_, v___y_3799_, v___y_3800_, v___y_3801_);
return v___x_3817_;
}
else
{
lean_object* v___x_3818_; lean_object* v___x_3820_; 
lean_dec_ref_known(v_a_3804_, 1);
lean_dec_ref(v_target_3797_);
lean_dec_ref(v_c_3795_);
v___x_3818_ = lean_box(0);
if (v_isShared_3807_ == 0)
{
lean_ctor_set(v___x_3806_, 0, v___x_3818_);
v___x_3820_ = v___x_3806_;
goto v_reusejp_3819_;
}
else
{
lean_object* v_reuseFailAlloc_3821_; 
v_reuseFailAlloc_3821_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3821_, 0, v___x_3818_);
v___x_3820_ = v_reuseFailAlloc_3821_;
goto v_reusejp_3819_;
}
v_reusejp_3819_:
{
return v___x_3820_;
}
}
}
}
else
{
lean_object* v_a_3823_; lean_object* v___x_3825_; uint8_t v_isShared_3826_; uint8_t v_isSharedCheck_3830_; 
lean_dec_ref(v_target_3797_);
lean_dec_ref(v_c_3795_);
v_a_3823_ = lean_ctor_get(v___x_3803_, 0);
v_isSharedCheck_3830_ = !lean_is_exclusive(v___x_3803_);
if (v_isSharedCheck_3830_ == 0)
{
v___x_3825_ = v___x_3803_;
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
else
{
lean_inc(v_a_3823_);
lean_dec(v___x_3803_);
v___x_3825_ = lean_box(0);
v_isShared_3826_ = v_isSharedCheck_3830_;
goto v_resetjp_3824_;
}
v_resetjp_3824_:
{
lean_object* v___x_3828_; 
if (v_isShared_3826_ == 0)
{
v___x_3828_ = v___x_3825_;
goto v_reusejp_3827_;
}
else
{
lean_object* v_reuseFailAlloc_3829_; 
v_reuseFailAlloc_3829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3829_, 0, v_a_3823_);
v___x_3828_ = v_reuseFailAlloc_3829_;
goto v_reusejp_3827_;
}
v_reusejp_3827_:
{
return v___x_3828_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_c_3831_, lean_object* v_x_3832_, lean_object* v_target_3833_, lean_object* v___y_3834_, lean_object* v___y_3835_, lean_object* v___y_3836_, lean_object* v___y_3837_, lean_object* v___y_3838_){
_start:
{
lean_object* v_res_3839_; 
v_res_3839_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_c_3831_, v_x_3832_, v_target_3833_, v___y_3834_, v___y_3835_, v___y_3836_, v___y_3837_);
lean_dec(v___y_3837_);
lean_dec_ref(v___y_3836_);
lean_dec(v___y_3835_);
lean_dec_ref(v___y_3834_);
lean_dec_ref(v_x_3832_);
return v_res_3839_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_c_3840_, lean_object* v_a_3841_, lean_object* v_a_3842_, lean_object* v_a_3843_, lean_object* v_a_3844_){
_start:
{
lean_object* v___x_3846_; 
lean_inc(v_a_3844_);
lean_inc_ref(v_a_3843_);
lean_inc(v_a_3842_);
lean_inc_ref(v_a_3841_);
lean_inc_ref(v_c_3840_);
v___x_3846_ = lean_infer_type(v_c_3840_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
if (lean_obj_tag(v___x_3846_) == 0)
{
lean_object* v_a_3847_; lean_object* v___f_3848_; uint8_t v___x_3849_; lean_object* v___x_3850_; 
v_a_3847_ = lean_ctor_get(v___x_3846_, 0);
lean_inc(v_a_3847_);
lean_dec_ref_known(v___x_3846_, 1);
v___f_3848_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3848_, 0, v_c_3840_);
v___x_3849_ = 0;
v___x_3850_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3847_, v___f_3848_, v___x_3849_, v___x_3849_, v_a_3841_, v_a_3842_, v_a_3843_, v_a_3844_);
return v___x_3850_;
}
else
{
lean_object* v_a_3851_; lean_object* v___x_3853_; uint8_t v_isShared_3854_; uint8_t v_isSharedCheck_3858_; 
lean_dec_ref(v_c_3840_);
v_a_3851_ = lean_ctor_get(v___x_3846_, 0);
v_isSharedCheck_3858_ = !lean_is_exclusive(v___x_3846_);
if (v_isSharedCheck_3858_ == 0)
{
v___x_3853_ = v___x_3846_;
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
else
{
lean_inc(v_a_3851_);
lean_dec(v___x_3846_);
v___x_3853_ = lean_box(0);
v_isShared_3854_ = v_isSharedCheck_3858_;
goto v_resetjp_3852_;
}
v_resetjp_3852_:
{
lean_object* v___x_3856_; 
if (v_isShared_3854_ == 0)
{
v___x_3856_ = v___x_3853_;
goto v_reusejp_3855_;
}
else
{
lean_object* v_reuseFailAlloc_3857_; 
v_reuseFailAlloc_3857_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3857_, 0, v_a_3851_);
v___x_3856_ = v_reuseFailAlloc_3857_;
goto v_reusejp_3855_;
}
v_reusejp_3855_:
{
return v___x_3856_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_c_3859_, lean_object* v_a_3860_, lean_object* v_a_3861_, lean_object* v_a_3862_, lean_object* v_a_3863_, lean_object* v_a_3864_){
_start:
{
lean_object* v_res_3865_; 
v_res_3865_ = l_Lean_Meta_checkNonClassInstance(v_c_3859_, v_a_3860_, v_a_3861_, v_a_3862_, v_a_3863_);
lean_dec(v_a_3863_);
lean_dec_ref(v_a_3862_);
lean_dec(v_a_3861_);
lean_dec_ref(v_a_3860_);
return v_res_3865_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3876_, lean_object* v___y_3877_){
_start:
{
lean_object* v___x_3879_; lean_object* v_env_3880_; lean_object* v___x_3881_; lean_object* v___x_3882_; 
v___x_3879_ = lean_st_ref_get(v___y_3877_);
v_env_3880_ = lean_ctor_get(v___x_3879_, 0);
lean_inc_ref(v_env_3880_);
lean_dec(v___x_3879_);
v___x_3881_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3880_, v_declName_3876_);
v___x_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3882_, 0, v___x_3881_);
return v___x_3882_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3883_, lean_object* v___y_3884_, lean_object* v___y_3885_){
_start:
{
lean_object* v_res_3886_; 
v_res_3886_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3883_, v___y_3884_);
lean_dec(v___y_3884_);
return v_res_3886_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3887_, lean_object* v___y_3888_, lean_object* v___y_3889_, lean_object* v___y_3890_, lean_object* v___y_3891_){
_start:
{
lean_object* v___x_3893_; 
v___x_3893_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3887_, v___y_3891_);
return v___x_3893_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
return v_res_3900_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3901_; 
v___x_3901_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3901_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3902_; lean_object* v___x_3903_; 
v___x_3902_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3903_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3903_, 0, v___x_3902_);
return v___x_3903_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3904_; lean_object* v___x_3905_; 
v___x_3904_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3905_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3905_, 0, v___x_3904_);
lean_ctor_set(v___x_3905_, 1, v___x_3904_);
return v___x_3905_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3906_; lean_object* v___x_3907_; 
v___x_3906_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3907_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3907_, 0, v___x_3906_);
lean_ctor_set(v___x_3907_, 1, v___x_3906_);
lean_ctor_set(v___x_3907_, 2, v___x_3906_);
lean_ctor_set(v___x_3907_, 3, v___x_3906_);
lean_ctor_set(v___x_3907_, 4, v___x_3906_);
lean_ctor_set(v___x_3907_, 5, v___x_3906_);
return v___x_3907_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3908_, lean_object* v_b_3909_, uint8_t v_kind_3910_, lean_object* v___y_3911_, lean_object* v___y_3912_, lean_object* v___y_3913_){
_start:
{
lean_object* v_currNamespace_3915_; lean_object* v___x_3916_; lean_object* v_env_3917_; lean_object* v_nextMacroScope_3918_; lean_object* v_ngen_3919_; lean_object* v_auxDeclNGen_3920_; lean_object* v_traceState_3921_; lean_object* v_messages_3922_; lean_object* v_infoState_3923_; lean_object* v_snapshotTasks_3924_; lean_object* v___x_3926_; uint8_t v_isShared_3927_; uint8_t v_isSharedCheck_3951_; 
v_currNamespace_3915_ = lean_ctor_get(v___y_3912_, 6);
v___x_3916_ = lean_st_ref_take(v___y_3913_);
v_env_3917_ = lean_ctor_get(v___x_3916_, 0);
v_nextMacroScope_3918_ = lean_ctor_get(v___x_3916_, 1);
v_ngen_3919_ = lean_ctor_get(v___x_3916_, 2);
v_auxDeclNGen_3920_ = lean_ctor_get(v___x_3916_, 3);
v_traceState_3921_ = lean_ctor_get(v___x_3916_, 4);
v_messages_3922_ = lean_ctor_get(v___x_3916_, 6);
v_infoState_3923_ = lean_ctor_get(v___x_3916_, 7);
v_snapshotTasks_3924_ = lean_ctor_get(v___x_3916_, 8);
v_isSharedCheck_3951_ = !lean_is_exclusive(v___x_3916_);
if (v_isSharedCheck_3951_ == 0)
{
lean_object* v_unused_3952_; 
v_unused_3952_ = lean_ctor_get(v___x_3916_, 5);
lean_dec(v_unused_3952_);
v___x_3926_ = v___x_3916_;
v_isShared_3927_ = v_isSharedCheck_3951_;
goto v_resetjp_3925_;
}
else
{
lean_inc(v_snapshotTasks_3924_);
lean_inc(v_infoState_3923_);
lean_inc(v_messages_3922_);
lean_inc(v_traceState_3921_);
lean_inc(v_auxDeclNGen_3920_);
lean_inc(v_ngen_3919_);
lean_inc(v_nextMacroScope_3918_);
lean_inc(v_env_3917_);
lean_dec(v___x_3916_);
v___x_3926_ = lean_box(0);
v_isShared_3927_ = v_isSharedCheck_3951_;
goto v_resetjp_3925_;
}
v_resetjp_3925_:
{
lean_object* v___x_3928_; lean_object* v___x_3929_; lean_object* v___x_3931_; 
lean_inc(v_currNamespace_3915_);
v___x_3928_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3917_, v_ext_3908_, v_b_3909_, v_kind_3910_, v_currNamespace_3915_);
v___x_3929_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3927_ == 0)
{
lean_ctor_set(v___x_3926_, 5, v___x_3929_);
lean_ctor_set(v___x_3926_, 0, v___x_3928_);
v___x_3931_ = v___x_3926_;
goto v_reusejp_3930_;
}
else
{
lean_object* v_reuseFailAlloc_3950_; 
v_reuseFailAlloc_3950_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3950_, 0, v___x_3928_);
lean_ctor_set(v_reuseFailAlloc_3950_, 1, v_nextMacroScope_3918_);
lean_ctor_set(v_reuseFailAlloc_3950_, 2, v_ngen_3919_);
lean_ctor_set(v_reuseFailAlloc_3950_, 3, v_auxDeclNGen_3920_);
lean_ctor_set(v_reuseFailAlloc_3950_, 4, v_traceState_3921_);
lean_ctor_set(v_reuseFailAlloc_3950_, 5, v___x_3929_);
lean_ctor_set(v_reuseFailAlloc_3950_, 6, v_messages_3922_);
lean_ctor_set(v_reuseFailAlloc_3950_, 7, v_infoState_3923_);
lean_ctor_set(v_reuseFailAlloc_3950_, 8, v_snapshotTasks_3924_);
v___x_3931_ = v_reuseFailAlloc_3950_;
goto v_reusejp_3930_;
}
v_reusejp_3930_:
{
lean_object* v___x_3932_; lean_object* v___x_3933_; lean_object* v_mctx_3934_; lean_object* v_zetaDeltaFVarIds_3935_; lean_object* v_postponed_3936_; lean_object* v_diag_3937_; lean_object* v___x_3939_; uint8_t v_isShared_3940_; uint8_t v_isSharedCheck_3948_; 
v___x_3932_ = lean_st_ref_set(v___y_3913_, v___x_3931_);
v___x_3933_ = lean_st_ref_take(v___y_3911_);
v_mctx_3934_ = lean_ctor_get(v___x_3933_, 0);
v_zetaDeltaFVarIds_3935_ = lean_ctor_get(v___x_3933_, 2);
v_postponed_3936_ = lean_ctor_get(v___x_3933_, 3);
v_diag_3937_ = lean_ctor_get(v___x_3933_, 4);
v_isSharedCheck_3948_ = !lean_is_exclusive(v___x_3933_);
if (v_isSharedCheck_3948_ == 0)
{
lean_object* v_unused_3949_; 
v_unused_3949_ = lean_ctor_get(v___x_3933_, 1);
lean_dec(v_unused_3949_);
v___x_3939_ = v___x_3933_;
v_isShared_3940_ = v_isSharedCheck_3948_;
goto v_resetjp_3938_;
}
else
{
lean_inc(v_diag_3937_);
lean_inc(v_postponed_3936_);
lean_inc(v_zetaDeltaFVarIds_3935_);
lean_inc(v_mctx_3934_);
lean_dec(v___x_3933_);
v___x_3939_ = lean_box(0);
v_isShared_3940_ = v_isSharedCheck_3948_;
goto v_resetjp_3938_;
}
v_resetjp_3938_:
{
lean_object* v___x_3941_; lean_object* v___x_3943_; 
v___x_3941_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3940_ == 0)
{
lean_ctor_set(v___x_3939_, 1, v___x_3941_);
v___x_3943_ = v___x_3939_;
goto v_reusejp_3942_;
}
else
{
lean_object* v_reuseFailAlloc_3947_; 
v_reuseFailAlloc_3947_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3947_, 0, v_mctx_3934_);
lean_ctor_set(v_reuseFailAlloc_3947_, 1, v___x_3941_);
lean_ctor_set(v_reuseFailAlloc_3947_, 2, v_zetaDeltaFVarIds_3935_);
lean_ctor_set(v_reuseFailAlloc_3947_, 3, v_postponed_3936_);
lean_ctor_set(v_reuseFailAlloc_3947_, 4, v_diag_3937_);
v___x_3943_ = v_reuseFailAlloc_3947_;
goto v_reusejp_3942_;
}
v_reusejp_3942_:
{
lean_object* v___x_3944_; lean_object* v___x_3945_; lean_object* v___x_3946_; 
v___x_3944_ = lean_st_ref_set(v___y_3911_, v___x_3943_);
v___x_3945_ = lean_box(0);
v___x_3946_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3946_, 0, v___x_3945_);
return v___x_3946_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_3953_, lean_object* v_b_3954_, lean_object* v_kind_3955_, lean_object* v___y_3956_, lean_object* v___y_3957_, lean_object* v___y_3958_, lean_object* v___y_3959_){
_start:
{
uint8_t v_kind_boxed_3960_; lean_object* v_res_3961_; 
v_kind_boxed_3960_ = lean_unbox(v_kind_3955_);
v_res_3961_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3953_, v_b_3954_, v_kind_boxed_3960_, v___y_3956_, v___y_3957_, v___y_3958_);
lean_dec(v___y_3958_);
lean_dec_ref(v___y_3957_);
lean_dec(v___y_3956_);
return v_res_3961_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_3962_, lean_object* v_00_u03b2_3963_, lean_object* v_00_u03c3_3964_, lean_object* v_ext_3965_, lean_object* v_b_3966_, uint8_t v_kind_3967_, lean_object* v___y_3968_, lean_object* v___y_3969_, lean_object* v___y_3970_, lean_object* v___y_3971_){
_start:
{
lean_object* v___x_3973_; 
v___x_3973_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_3965_, v_b_3966_, v_kind_3967_, v___y_3969_, v___y_3970_, v___y_3971_);
return v___x_3973_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_3974_, lean_object* v_00_u03b2_3975_, lean_object* v_00_u03c3_3976_, lean_object* v_ext_3977_, lean_object* v_b_3978_, lean_object* v_kind_3979_, lean_object* v___y_3980_, lean_object* v___y_3981_, lean_object* v___y_3982_, lean_object* v___y_3983_, lean_object* v___y_3984_){
_start:
{
uint8_t v_kind_boxed_3985_; lean_object* v_res_3986_; 
v_kind_boxed_3985_ = lean_unbox(v_kind_3979_);
v_res_3986_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_3974_, v_00_u03b2_3975_, v_00_u03c3_3976_, v_ext_3977_, v_b_3978_, v_kind_boxed_3985_, v___y_3980_, v___y_3981_, v___y_3982_, v___y_3983_);
lean_dec(v___y_3983_);
lean_dec_ref(v___y_3982_);
lean_dec(v___y_3981_);
lean_dec_ref(v___y_3980_);
return v_res_3986_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_3987_, lean_object* v___y_3988_){
_start:
{
lean_object* v___x_3990_; lean_object* v_env_3991_; uint8_t v___x_3992_; lean_object* v___x_3993_; lean_object* v___x_3994_; 
v___x_3990_ = lean_st_ref_get(v___y_3988_);
v_env_3991_ = lean_ctor_get(v___x_3990_, 0);
lean_inc_ref(v_env_3991_);
lean_dec(v___x_3990_);
v___x_3992_ = l_Lean_getReducibilityStatusCore(v_env_3991_, v_declName_3987_);
v___x_3993_ = lean_box(v___x_3992_);
v___x_3994_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3994_, 0, v___x_3993_);
return v___x_3994_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_3995_, lean_object* v___y_3996_, lean_object* v___y_3997_){
_start:
{
lean_object* v_res_3998_; 
v_res_3998_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3995_, v___y_3996_);
lean_dec(v___y_3996_);
return v_res_3998_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_3999_, lean_object* v___y_4000_, lean_object* v___y_4001_, lean_object* v___y_4002_, lean_object* v___y_4003_){
_start:
{
lean_object* v___x_4005_; 
v___x_4005_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_3999_, v___y_4003_);
return v___x_4005_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_, lean_object* v___y_4011_){
_start:
{
lean_object* v_res_4012_; 
v_res_4012_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_4006_, v___y_4007_, v___y_4008_, v___y_4009_, v___y_4010_);
lean_dec(v___y_4010_);
lean_dec_ref(v___y_4009_);
lean_dec(v___y_4008_);
lean_dec_ref(v___y_4007_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_4013_, lean_object* v_msg_4014_, lean_object* v___y_4015_, lean_object* v___y_4016_, lean_object* v___y_4017_, lean_object* v___y_4018_){
_start:
{
lean_object* v_fileName_4020_; lean_object* v_fileMap_4021_; lean_object* v_options_4022_; lean_object* v_currRecDepth_4023_; lean_object* v_maxRecDepth_4024_; lean_object* v_ref_4025_; lean_object* v_currNamespace_4026_; lean_object* v_openDecls_4027_; lean_object* v_initHeartbeats_4028_; lean_object* v_maxHeartbeats_4029_; lean_object* v_quotContext_4030_; lean_object* v_currMacroScope_4031_; uint8_t v_diag_4032_; lean_object* v_cancelTk_x3f_4033_; uint8_t v_suppressElabErrors_4034_; lean_object* v_inheritedTraceOptions_4035_; lean_object* v_ref_4036_; lean_object* v___x_4037_; lean_object* v___x_4038_; 
v_fileName_4020_ = lean_ctor_get(v___y_4017_, 0);
v_fileMap_4021_ = lean_ctor_get(v___y_4017_, 1);
v_options_4022_ = lean_ctor_get(v___y_4017_, 2);
v_currRecDepth_4023_ = lean_ctor_get(v___y_4017_, 3);
v_maxRecDepth_4024_ = lean_ctor_get(v___y_4017_, 4);
v_ref_4025_ = lean_ctor_get(v___y_4017_, 5);
v_currNamespace_4026_ = lean_ctor_get(v___y_4017_, 6);
v_openDecls_4027_ = lean_ctor_get(v___y_4017_, 7);
v_initHeartbeats_4028_ = lean_ctor_get(v___y_4017_, 8);
v_maxHeartbeats_4029_ = lean_ctor_get(v___y_4017_, 9);
v_quotContext_4030_ = lean_ctor_get(v___y_4017_, 10);
v_currMacroScope_4031_ = lean_ctor_get(v___y_4017_, 11);
v_diag_4032_ = lean_ctor_get_uint8(v___y_4017_, sizeof(void*)*14);
v_cancelTk_x3f_4033_ = lean_ctor_get(v___y_4017_, 12);
v_suppressElabErrors_4034_ = lean_ctor_get_uint8(v___y_4017_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4035_ = lean_ctor_get(v___y_4017_, 13);
v_ref_4036_ = l_Lean_replaceRef(v_ref_4013_, v_ref_4025_);
lean_inc_ref(v_inheritedTraceOptions_4035_);
lean_inc(v_cancelTk_x3f_4033_);
lean_inc(v_currMacroScope_4031_);
lean_inc(v_quotContext_4030_);
lean_inc(v_maxHeartbeats_4029_);
lean_inc(v_initHeartbeats_4028_);
lean_inc(v_openDecls_4027_);
lean_inc(v_currNamespace_4026_);
lean_inc(v_maxRecDepth_4024_);
lean_inc(v_currRecDepth_4023_);
lean_inc_ref(v_options_4022_);
lean_inc_ref(v_fileMap_4021_);
lean_inc_ref(v_fileName_4020_);
v___x_4037_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4037_, 0, v_fileName_4020_);
lean_ctor_set(v___x_4037_, 1, v_fileMap_4021_);
lean_ctor_set(v___x_4037_, 2, v_options_4022_);
lean_ctor_set(v___x_4037_, 3, v_currRecDepth_4023_);
lean_ctor_set(v___x_4037_, 4, v_maxRecDepth_4024_);
lean_ctor_set(v___x_4037_, 5, v_ref_4036_);
lean_ctor_set(v___x_4037_, 6, v_currNamespace_4026_);
lean_ctor_set(v___x_4037_, 7, v_openDecls_4027_);
lean_ctor_set(v___x_4037_, 8, v_initHeartbeats_4028_);
lean_ctor_set(v___x_4037_, 9, v_maxHeartbeats_4029_);
lean_ctor_set(v___x_4037_, 10, v_quotContext_4030_);
lean_ctor_set(v___x_4037_, 11, v_currMacroScope_4031_);
lean_ctor_set(v___x_4037_, 12, v_cancelTk_x3f_4033_);
lean_ctor_set(v___x_4037_, 13, v_inheritedTraceOptions_4035_);
lean_ctor_set_uint8(v___x_4037_, sizeof(void*)*14, v_diag_4032_);
lean_ctor_set_uint8(v___x_4037_, sizeof(void*)*14 + 1, v_suppressElabErrors_4034_);
v___x_4038_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_4014_, v___y_4015_, v___y_4016_, v___x_4037_, v___y_4018_);
lean_dec_ref_known(v___x_4037_, 14);
return v___x_4038_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_4039_, lean_object* v_msg_4040_, lean_object* v___y_4041_, lean_object* v___y_4042_, lean_object* v___y_4043_, lean_object* v___y_4044_, lean_object* v___y_4045_){
_start:
{
lean_object* v_res_4046_; 
v_res_4046_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4039_, v_msg_4040_, v___y_4041_, v___y_4042_, v___y_4043_, v___y_4044_);
lean_dec(v___y_4044_);
lean_dec_ref(v___y_4043_);
lean_dec(v___y_4042_);
lean_dec_ref(v___y_4041_);
lean_dec(v_ref_4039_);
return v_res_4046_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_4047_; 
v___x_4047_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4047_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_4048_; lean_object* v___x_4049_; 
v___x_4048_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4049_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4049_, 0, v___x_4048_);
return v___x_4049_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_4050_; lean_object* v___x_4051_; lean_object* v___x_4052_; 
v___x_4050_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4051_ = lean_unsigned_to_nat(0u);
v___x_4052_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4052_, 0, v___x_4051_);
lean_ctor_set(v___x_4052_, 1, v___x_4051_);
lean_ctor_set(v___x_4052_, 2, v___x_4051_);
lean_ctor_set(v___x_4052_, 3, v___x_4051_);
lean_ctor_set(v___x_4052_, 4, v___x_4050_);
lean_ctor_set(v___x_4052_, 5, v___x_4050_);
lean_ctor_set(v___x_4052_, 6, v___x_4050_);
lean_ctor_set(v___x_4052_, 7, v___x_4050_);
lean_ctor_set(v___x_4052_, 8, v___x_4050_);
lean_ctor_set(v___x_4052_, 9, v___x_4050_);
return v___x_4052_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_4053_; lean_object* v___x_4054_; lean_object* v___x_4055_; 
v___x_4053_ = lean_unsigned_to_nat(32u);
v___x_4054_ = lean_mk_empty_array_with_capacity(v___x_4053_);
v___x_4055_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4055_, 0, v___x_4054_);
return v___x_4055_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_4056_; lean_object* v___x_4057_; lean_object* v___x_4058_; lean_object* v___x_4059_; lean_object* v___x_4060_; lean_object* v___x_4061_; 
v___x_4056_ = ((size_t)5ULL);
v___x_4057_ = lean_unsigned_to_nat(0u);
v___x_4058_ = lean_unsigned_to_nat(32u);
v___x_4059_ = lean_mk_empty_array_with_capacity(v___x_4058_);
v___x_4060_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4061_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4061_, 0, v___x_4060_);
lean_ctor_set(v___x_4061_, 1, v___x_4059_);
lean_ctor_set(v___x_4061_, 2, v___x_4057_);
lean_ctor_set(v___x_4061_, 3, v___x_4057_);
lean_ctor_set_usize(v___x_4061_, 4, v___x_4056_);
return v___x_4061_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_4062_; lean_object* v___x_4063_; lean_object* v___x_4064_; lean_object* v___x_4065_; 
v___x_4062_ = lean_box(1);
v___x_4063_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_4064_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4065_, 0, v___x_4064_);
lean_ctor_set(v___x_4065_, 1, v___x_4063_);
lean_ctor_set(v___x_4065_, 2, v___x_4062_);
return v___x_4065_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_4067_; lean_object* v___x_4068_; 
v___x_4067_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_4068_ = l_Lean_stringToMessageData(v___x_4067_);
return v___x_4068_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_4070_; lean_object* v___x_4071_; 
v___x_4070_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_4071_ = l_Lean_stringToMessageData(v___x_4070_);
return v___x_4071_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_4073_; lean_object* v___x_4074_; 
v___x_4073_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_4074_ = l_Lean_stringToMessageData(v___x_4073_);
return v___x_4074_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_4076_; lean_object* v___x_4077_; 
v___x_4076_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_4077_ = l_Lean_stringToMessageData(v___x_4076_);
return v___x_4077_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_4079_; lean_object* v___x_4080_; 
v___x_4079_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_4080_ = l_Lean_stringToMessageData(v___x_4079_);
return v___x_4080_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_4082_; lean_object* v___x_4083_; 
v___x_4082_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_4083_ = l_Lean_stringToMessageData(v___x_4082_);
return v___x_4083_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_4085_; lean_object* v___x_4086_; 
v___x_4085_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_4086_ = l_Lean_stringToMessageData(v___x_4085_);
return v___x_4086_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_4087_, lean_object* v_declHint_4088_, lean_object* v___y_4089_){
_start:
{
lean_object* v___x_4091_; lean_object* v_env_4092_; uint8_t v___x_4093_; 
v___x_4091_ = lean_st_ref_get(v___y_4089_);
v_env_4092_ = lean_ctor_get(v___x_4091_, 0);
lean_inc_ref(v_env_4092_);
lean_dec(v___x_4091_);
v___x_4093_ = l_Lean_Name_isAnonymous(v_declHint_4088_);
if (v___x_4093_ == 0)
{
uint8_t v_isExporting_4094_; 
v_isExporting_4094_ = lean_ctor_get_uint8(v_env_4092_, sizeof(void*)*8);
if (v_isExporting_4094_ == 0)
{
lean_object* v___x_4095_; 
lean_dec_ref(v_env_4092_);
lean_dec(v_declHint_4088_);
v___x_4095_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4095_, 0, v_msg_4087_);
return v___x_4095_;
}
else
{
lean_object* v___x_4096_; uint8_t v___x_4097_; 
lean_inc_ref(v_env_4092_);
v___x_4096_ = l_Lean_Environment_setExporting(v_env_4092_, v___x_4093_);
lean_inc(v_declHint_4088_);
lean_inc_ref(v___x_4096_);
v___x_4097_ = l_Lean_Environment_contains(v___x_4096_, v_declHint_4088_, v_isExporting_4094_);
if (v___x_4097_ == 0)
{
lean_object* v___x_4098_; 
lean_dec_ref(v___x_4096_);
lean_dec_ref(v_env_4092_);
lean_dec(v_declHint_4088_);
v___x_4098_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4098_, 0, v_msg_4087_);
return v___x_4098_;
}
else
{
lean_object* v___x_4099_; lean_object* v___x_4100_; lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; lean_object* v_c_4104_; lean_object* v___x_4105_; 
v___x_4099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4100_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_4101_ = l_Lean_Options_empty;
v___x_4102_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4102_, 0, v___x_4096_);
lean_ctor_set(v___x_4102_, 1, v___x_4099_);
lean_ctor_set(v___x_4102_, 2, v___x_4100_);
lean_ctor_set(v___x_4102_, 3, v___x_4101_);
lean_inc(v_declHint_4088_);
v___x_4103_ = l_Lean_MessageData_ofConstName(v_declHint_4088_, v___x_4093_);
v_c_4104_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4104_, 0, v___x_4102_);
lean_ctor_set(v_c_4104_, 1, v___x_4103_);
v___x_4105_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4092_, v_declHint_4088_);
if (lean_obj_tag(v___x_4105_) == 0)
{
lean_object* v___x_4106_; lean_object* v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
lean_dec_ref(v_env_4092_);
lean_dec(v_declHint_4088_);
v___x_4106_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4107_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4107_, 0, v___x_4106_);
lean_ctor_set(v___x_4107_, 1, v_c_4104_);
v___x_4108_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_4109_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4109_, 0, v___x_4107_);
lean_ctor_set(v___x_4109_, 1, v___x_4108_);
v___x_4110_ = l_Lean_MessageData_note(v___x_4109_);
v___x_4111_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4111_, 0, v_msg_4087_);
lean_ctor_set(v___x_4111_, 1, v___x_4110_);
v___x_4112_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4112_, 0, v___x_4111_);
return v___x_4112_;
}
else
{
lean_object* v_val_4113_; lean_object* v___x_4115_; uint8_t v_isShared_4116_; uint8_t v_isSharedCheck_4148_; 
v_val_4113_ = lean_ctor_get(v___x_4105_, 0);
v_isSharedCheck_4148_ = !lean_is_exclusive(v___x_4105_);
if (v_isSharedCheck_4148_ == 0)
{
v___x_4115_ = v___x_4105_;
v_isShared_4116_ = v_isSharedCheck_4148_;
goto v_resetjp_4114_;
}
else
{
lean_inc(v_val_4113_);
lean_dec(v___x_4105_);
v___x_4115_ = lean_box(0);
v_isShared_4116_ = v_isSharedCheck_4148_;
goto v_resetjp_4114_;
}
v_resetjp_4114_:
{
lean_object* v___x_4117_; lean_object* v___x_4118_; lean_object* v___x_4119_; lean_object* v_mod_4120_; uint8_t v___x_4121_; 
v___x_4117_ = lean_box(0);
v___x_4118_ = l_Lean_Environment_header(v_env_4092_);
lean_dec_ref(v_env_4092_);
v___x_4119_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4118_);
v_mod_4120_ = lean_array_get(v___x_4117_, v___x_4119_, v_val_4113_);
lean_dec(v_val_4113_);
lean_dec_ref(v___x_4119_);
v___x_4121_ = l_Lean_isPrivateName(v_declHint_4088_);
lean_dec(v_declHint_4088_);
if (v___x_4121_ == 0)
{
lean_object* v___x_4122_; lean_object* v___x_4123_; lean_object* v___x_4124_; lean_object* v___x_4125_; lean_object* v___x_4126_; lean_object* v___x_4127_; lean_object* v___x_4128_; lean_object* v___x_4129_; lean_object* v___x_4130_; lean_object* v___x_4131_; lean_object* v___x_4133_; 
v___x_4122_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_4123_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4123_, 0, v___x_4122_);
lean_ctor_set(v___x_4123_, 1, v_c_4104_);
v___x_4124_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_4125_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4125_, 0, v___x_4123_);
lean_ctor_set(v___x_4125_, 1, v___x_4124_);
v___x_4126_ = l_Lean_MessageData_ofName(v_mod_4120_);
v___x_4127_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4127_, 0, v___x_4125_);
lean_ctor_set(v___x_4127_, 1, v___x_4126_);
v___x_4128_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_4129_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4129_, 0, v___x_4127_);
lean_ctor_set(v___x_4129_, 1, v___x_4128_);
v___x_4130_ = l_Lean_MessageData_note(v___x_4129_);
v___x_4131_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4131_, 0, v_msg_4087_);
lean_ctor_set(v___x_4131_, 1, v___x_4130_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set_tag(v___x_4115_, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4131_);
v___x_4133_ = v___x_4115_;
goto v_reusejp_4132_;
}
else
{
lean_object* v_reuseFailAlloc_4134_; 
v_reuseFailAlloc_4134_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4134_, 0, v___x_4131_);
v___x_4133_ = v_reuseFailAlloc_4134_;
goto v_reusejp_4132_;
}
v_reusejp_4132_:
{
return v___x_4133_;
}
}
else
{
lean_object* v___x_4135_; lean_object* v___x_4136_; lean_object* v___x_4137_; lean_object* v___x_4138_; lean_object* v___x_4139_; lean_object* v___x_4140_; lean_object* v___x_4141_; lean_object* v___x_4142_; lean_object* v___x_4143_; lean_object* v___x_4144_; lean_object* v___x_4146_; 
v___x_4135_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4136_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4136_, 0, v___x_4135_);
lean_ctor_set(v___x_4136_, 1, v_c_4104_);
v___x_4137_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_4138_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4138_, 0, v___x_4136_);
lean_ctor_set(v___x_4138_, 1, v___x_4137_);
v___x_4139_ = l_Lean_MessageData_ofName(v_mod_4120_);
v___x_4140_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4140_, 0, v___x_4138_);
lean_ctor_set(v___x_4140_, 1, v___x_4139_);
v___x_4141_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_4142_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4142_, 0, v___x_4140_);
lean_ctor_set(v___x_4142_, 1, v___x_4141_);
v___x_4143_ = l_Lean_MessageData_note(v___x_4142_);
v___x_4144_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4144_, 0, v_msg_4087_);
lean_ctor_set(v___x_4144_, 1, v___x_4143_);
if (v_isShared_4116_ == 0)
{
lean_ctor_set_tag(v___x_4115_, 0);
lean_ctor_set(v___x_4115_, 0, v___x_4144_);
v___x_4146_ = v___x_4115_;
goto v_reusejp_4145_;
}
else
{
lean_object* v_reuseFailAlloc_4147_; 
v_reuseFailAlloc_4147_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4147_, 0, v___x_4144_);
v___x_4146_ = v_reuseFailAlloc_4147_;
goto v_reusejp_4145_;
}
v_reusejp_4145_:
{
return v___x_4146_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_4149_; 
lean_dec_ref(v_env_4092_);
lean_dec(v_declHint_4088_);
v___x_4149_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4149_, 0, v_msg_4087_);
return v___x_4149_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_4150_, lean_object* v_declHint_4151_, lean_object* v___y_4152_, lean_object* v___y_4153_){
_start:
{
lean_object* v_res_4154_; 
v_res_4154_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4150_, v_declHint_4151_, v___y_4152_);
lean_dec(v___y_4152_);
return v_res_4154_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(lean_object* v_msg_4155_, lean_object* v_declHint_4156_, lean_object* v___y_4157_, lean_object* v___y_4158_, lean_object* v___y_4159_, lean_object* v___y_4160_){
_start:
{
lean_object* v___x_4162_; lean_object* v_a_4163_; lean_object* v___x_4165_; uint8_t v_isShared_4166_; uint8_t v_isSharedCheck_4172_; 
v___x_4162_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4155_, v_declHint_4156_, v___y_4160_);
v_a_4163_ = lean_ctor_get(v___x_4162_, 0);
v_isSharedCheck_4172_ = !lean_is_exclusive(v___x_4162_);
if (v_isSharedCheck_4172_ == 0)
{
v___x_4165_ = v___x_4162_;
v_isShared_4166_ = v_isSharedCheck_4172_;
goto v_resetjp_4164_;
}
else
{
lean_inc(v_a_4163_);
lean_dec(v___x_4162_);
v___x_4165_ = lean_box(0);
v_isShared_4166_ = v_isSharedCheck_4172_;
goto v_resetjp_4164_;
}
v_resetjp_4164_:
{
lean_object* v___x_4167_; lean_object* v___x_4168_; lean_object* v___x_4170_; 
v___x_4167_ = l_Lean_unknownIdentifierMessageTag;
v___x_4168_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4168_, 0, v___x_4167_);
lean_ctor_set(v___x_4168_, 1, v_a_4163_);
if (v_isShared_4166_ == 0)
{
lean_ctor_set(v___x_4165_, 0, v___x_4168_);
v___x_4170_ = v___x_4165_;
goto v_reusejp_4169_;
}
else
{
lean_object* v_reuseFailAlloc_4171_; 
v_reuseFailAlloc_4171_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4171_, 0, v___x_4168_);
v___x_4170_ = v_reuseFailAlloc_4171_;
goto v_reusejp_4169_;
}
v_reusejp_4169_:
{
return v___x_4170_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_4173_, lean_object* v_declHint_4174_, lean_object* v___y_4175_, lean_object* v___y_4176_, lean_object* v___y_4177_, lean_object* v___y_4178_, lean_object* v___y_4179_){
_start:
{
lean_object* v_res_4180_; 
v_res_4180_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4173_, v_declHint_4174_, v___y_4175_, v___y_4176_, v___y_4177_, v___y_4178_);
lean_dec(v___y_4178_);
lean_dec_ref(v___y_4177_);
lean_dec(v___y_4176_);
lean_dec_ref(v___y_4175_);
return v_res_4180_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_ref_4181_, lean_object* v_msg_4182_, lean_object* v_declHint_4183_, lean_object* v___y_4184_, lean_object* v___y_4185_, lean_object* v___y_4186_, lean_object* v___y_4187_){
_start:
{
lean_object* v___x_4189_; lean_object* v_a_4190_; lean_object* v___x_4191_; 
v___x_4189_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4182_, v_declHint_4183_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
v_a_4190_ = lean_ctor_get(v___x_4189_, 0);
lean_inc(v_a_4190_);
lean_dec_ref(v___x_4189_);
v___x_4191_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4181_, v_a_4190_, v___y_4184_, v___y_4185_, v___y_4186_, v___y_4187_);
return v___x_4191_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_ref_4192_, lean_object* v_msg_4193_, lean_object* v_declHint_4194_, lean_object* v___y_4195_, lean_object* v___y_4196_, lean_object* v___y_4197_, lean_object* v___y_4198_, lean_object* v___y_4199_){
_start:
{
lean_object* v_res_4200_; 
v_res_4200_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4192_, v_msg_4193_, v_declHint_4194_, v___y_4195_, v___y_4196_, v___y_4197_, v___y_4198_);
lean_dec(v___y_4198_);
lean_dec_ref(v___y_4197_);
lean_dec(v___y_4196_);
lean_dec_ref(v___y_4195_);
lean_dec(v_ref_4192_);
return v_res_4200_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_4202_; lean_object* v___x_4203_; 
v___x_4202_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_4203_ = l_Lean_stringToMessageData(v___x_4202_);
return v___x_4203_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_4204_, lean_object* v_constName_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_, lean_object* v___y_4208_, lean_object* v___y_4209_){
_start:
{
lean_object* v___x_4211_; uint8_t v___x_4212_; lean_object* v___x_4213_; lean_object* v___x_4214_; lean_object* v___x_4215_; lean_object* v___x_4216_; lean_object* v___x_4217_; 
v___x_4211_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_4212_ = 0;
lean_inc(v_constName_4205_);
v___x_4213_ = l_Lean_MessageData_ofConstName(v_constName_4205_, v___x_4212_);
v___x_4214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4214_, 0, v___x_4211_);
lean_ctor_set(v___x_4214_, 1, v___x_4213_);
v___x_4215_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4216_, 0, v___x_4214_);
lean_ctor_set(v___x_4216_, 1, v___x_4215_);
v___x_4217_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4204_, v___x_4216_, v_constName_4205_, v___y_4206_, v___y_4207_, v___y_4208_, v___y_4209_);
return v___x_4217_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_4218_, lean_object* v_constName_4219_, lean_object* v___y_4220_, lean_object* v___y_4221_, lean_object* v___y_4222_, lean_object* v___y_4223_, lean_object* v___y_4224_){
_start:
{
lean_object* v_res_4225_; 
v_res_4225_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4218_, v_constName_4219_, v___y_4220_, v___y_4221_, v___y_4222_, v___y_4223_);
lean_dec(v___y_4223_);
lean_dec_ref(v___y_4222_);
lean_dec(v___y_4221_);
lean_dec_ref(v___y_4220_);
lean_dec(v_ref_4218_);
return v_res_4225_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_4226_, lean_object* v___y_4227_, lean_object* v___y_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_){
_start:
{
lean_object* v_ref_4232_; lean_object* v___x_4233_; 
v_ref_4232_ = lean_ctor_get(v___y_4229_, 5);
v___x_4233_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4232_, v_constName_4226_, v___y_4227_, v___y_4228_, v___y_4229_, v___y_4230_);
return v___x_4233_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_4234_, lean_object* v___y_4235_, lean_object* v___y_4236_, lean_object* v___y_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_){
_start:
{
lean_object* v_res_4240_; 
v_res_4240_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4234_, v___y_4235_, v___y_4236_, v___y_4237_, v___y_4238_);
lean_dec(v___y_4238_);
lean_dec_ref(v___y_4237_);
lean_dec(v___y_4236_);
lean_dec_ref(v___y_4235_);
return v_res_4240_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_4241_, lean_object* v___y_4242_, lean_object* v___y_4243_, lean_object* v___y_4244_, lean_object* v___y_4245_){
_start:
{
lean_object* v___x_4247_; lean_object* v_env_4248_; uint8_t v___x_4249_; lean_object* v___x_4250_; 
v___x_4247_ = lean_st_ref_get(v___y_4245_);
v_env_4248_ = lean_ctor_get(v___x_4247_, 0);
lean_inc_ref(v_env_4248_);
lean_dec(v___x_4247_);
v___x_4249_ = 0;
lean_inc(v_constName_4241_);
v___x_4250_ = l_Lean_Environment_find_x3f(v_env_4248_, v_constName_4241_, v___x_4249_);
if (lean_obj_tag(v___x_4250_) == 0)
{
lean_object* v___x_4251_; 
v___x_4251_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4241_, v___y_4242_, v___y_4243_, v___y_4244_, v___y_4245_);
return v___x_4251_;
}
else
{
lean_object* v_val_4252_; lean_object* v___x_4254_; uint8_t v_isShared_4255_; uint8_t v_isSharedCheck_4259_; 
lean_dec(v_constName_4241_);
v_val_4252_ = lean_ctor_get(v___x_4250_, 0);
v_isSharedCheck_4259_ = !lean_is_exclusive(v___x_4250_);
if (v_isSharedCheck_4259_ == 0)
{
v___x_4254_ = v___x_4250_;
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
else
{
lean_inc(v_val_4252_);
lean_dec(v___x_4250_);
v___x_4254_ = lean_box(0);
v_isShared_4255_ = v_isSharedCheck_4259_;
goto v_resetjp_4253_;
}
v_resetjp_4253_:
{
lean_object* v___x_4257_; 
if (v_isShared_4255_ == 0)
{
lean_ctor_set_tag(v___x_4254_, 0);
v___x_4257_ = v___x_4254_;
goto v_reusejp_4256_;
}
else
{
lean_object* v_reuseFailAlloc_4258_; 
v_reuseFailAlloc_4258_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4258_, 0, v_val_4252_);
v___x_4257_ = v_reuseFailAlloc_4258_;
goto v_reusejp_4256_;
}
v_reusejp_4256_:
{
return v___x_4257_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_, lean_object* v___y_4264_, lean_object* v___y_4265_){
_start:
{
lean_object* v_res_4266_; 
v_res_4266_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_4260_, v___y_4261_, v___y_4262_, v___y_4263_, v___y_4264_);
lean_dec(v___y_4264_);
lean_dec_ref(v___y_4263_);
lean_dec(v___y_4262_);
lean_dec_ref(v___y_4261_);
return v_res_4266_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4267_, lean_object* v___y_4268_, lean_object* v___y_4269_, lean_object* v___y_4270_, lean_object* v___y_4271_){
_start:
{
lean_object* v___x_4273_; lean_object* v_env_4274_; uint8_t v___x_4275_; lean_object* v___x_4276_; 
v___x_4273_ = lean_st_ref_get(v___y_4271_);
v_env_4274_ = lean_ctor_get(v___x_4273_, 0);
lean_inc_ref(v_env_4274_);
lean_dec(v___x_4273_);
v___x_4275_ = 0;
lean_inc(v_constName_4267_);
v___x_4276_ = l_Lean_Environment_findConstVal_x3f(v_env_4274_, v_constName_4267_, v___x_4275_);
if (lean_obj_tag(v___x_4276_) == 0)
{
lean_object* v___x_4277_; 
v___x_4277_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4267_, v___y_4268_, v___y_4269_, v___y_4270_, v___y_4271_);
return v___x_4277_;
}
else
{
lean_object* v_val_4278_; lean_object* v___x_4280_; uint8_t v_isShared_4281_; uint8_t v_isSharedCheck_4285_; 
lean_dec(v_constName_4267_);
v_val_4278_ = lean_ctor_get(v___x_4276_, 0);
v_isSharedCheck_4285_ = !lean_is_exclusive(v___x_4276_);
if (v_isSharedCheck_4285_ == 0)
{
v___x_4280_ = v___x_4276_;
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
else
{
lean_inc(v_val_4278_);
lean_dec(v___x_4276_);
v___x_4280_ = lean_box(0);
v_isShared_4281_ = v_isSharedCheck_4285_;
goto v_resetjp_4279_;
}
v_resetjp_4279_:
{
lean_object* v___x_4283_; 
if (v_isShared_4281_ == 0)
{
lean_ctor_set_tag(v___x_4280_, 0);
v___x_4283_ = v___x_4280_;
goto v_reusejp_4282_;
}
else
{
lean_object* v_reuseFailAlloc_4284_; 
v_reuseFailAlloc_4284_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4284_, 0, v_val_4278_);
v___x_4283_ = v_reuseFailAlloc_4284_;
goto v_reusejp_4282_;
}
v_reusejp_4282_:
{
return v___x_4283_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4286_, lean_object* v___y_4287_, lean_object* v___y_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_){
_start:
{
lean_object* v_res_4292_; 
v_res_4292_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4286_, v___y_4287_, v___y_4288_, v___y_4289_, v___y_4290_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
lean_dec(v___y_4288_);
lean_dec_ref(v___y_4287_);
return v_res_4292_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4293_, lean_object* v_a_4294_){
_start:
{
if (lean_obj_tag(v_a_4293_) == 0)
{
lean_object* v___x_4295_; 
v___x_4295_ = l_List_reverse___redArg(v_a_4294_);
return v___x_4295_;
}
else
{
lean_object* v_head_4296_; lean_object* v_tail_4297_; lean_object* v___x_4299_; uint8_t v_isShared_4300_; uint8_t v_isSharedCheck_4306_; 
v_head_4296_ = lean_ctor_get(v_a_4293_, 0);
v_tail_4297_ = lean_ctor_get(v_a_4293_, 1);
v_isSharedCheck_4306_ = !lean_is_exclusive(v_a_4293_);
if (v_isSharedCheck_4306_ == 0)
{
v___x_4299_ = v_a_4293_;
v_isShared_4300_ = v_isSharedCheck_4306_;
goto v_resetjp_4298_;
}
else
{
lean_inc(v_tail_4297_);
lean_inc(v_head_4296_);
lean_dec(v_a_4293_);
v___x_4299_ = lean_box(0);
v_isShared_4300_ = v_isSharedCheck_4306_;
goto v_resetjp_4298_;
}
v_resetjp_4298_:
{
lean_object* v___x_4301_; lean_object* v___x_4303_; 
v___x_4301_ = l_Lean_mkLevelParam(v_head_4296_);
if (v_isShared_4300_ == 0)
{
lean_ctor_set(v___x_4299_, 1, v_a_4294_);
lean_ctor_set(v___x_4299_, 0, v___x_4301_);
v___x_4303_ = v___x_4299_;
goto v_reusejp_4302_;
}
else
{
lean_object* v_reuseFailAlloc_4305_; 
v_reuseFailAlloc_4305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4305_, 0, v___x_4301_);
lean_ctor_set(v_reuseFailAlloc_4305_, 1, v_a_4294_);
v___x_4303_ = v_reuseFailAlloc_4305_;
goto v_reusejp_4302_;
}
v_reusejp_4302_:
{
v_a_4293_ = v_tail_4297_;
v_a_4294_ = v___x_4303_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4307_, lean_object* v___y_4308_, lean_object* v___y_4309_, lean_object* v___y_4310_, lean_object* v___y_4311_){
_start:
{
lean_object* v___x_4313_; 
lean_inc(v_constName_4307_);
v___x_4313_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4307_, v___y_4308_, v___y_4309_, v___y_4310_, v___y_4311_);
if (lean_obj_tag(v___x_4313_) == 0)
{
lean_object* v_a_4314_; lean_object* v___x_4316_; uint8_t v_isShared_4317_; uint8_t v_isSharedCheck_4325_; 
v_a_4314_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4325_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4325_ == 0)
{
v___x_4316_ = v___x_4313_;
v_isShared_4317_ = v_isSharedCheck_4325_;
goto v_resetjp_4315_;
}
else
{
lean_inc(v_a_4314_);
lean_dec(v___x_4313_);
v___x_4316_ = lean_box(0);
v_isShared_4317_ = v_isSharedCheck_4325_;
goto v_resetjp_4315_;
}
v_resetjp_4315_:
{
lean_object* v_levelParams_4318_; lean_object* v___x_4319_; lean_object* v___x_4320_; lean_object* v___x_4321_; lean_object* v___x_4323_; 
v_levelParams_4318_ = lean_ctor_get(v_a_4314_, 1);
lean_inc(v_levelParams_4318_);
lean_dec(v_a_4314_);
v___x_4319_ = lean_box(0);
v___x_4320_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4318_, v___x_4319_);
v___x_4321_ = l_Lean_mkConst(v_constName_4307_, v___x_4320_);
if (v_isShared_4317_ == 0)
{
lean_ctor_set(v___x_4316_, 0, v___x_4321_);
v___x_4323_ = v___x_4316_;
goto v_reusejp_4322_;
}
else
{
lean_object* v_reuseFailAlloc_4324_; 
v_reuseFailAlloc_4324_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4324_, 0, v___x_4321_);
v___x_4323_ = v_reuseFailAlloc_4324_;
goto v_reusejp_4322_;
}
v_reusejp_4322_:
{
return v___x_4323_;
}
}
}
else
{
lean_object* v_a_4326_; lean_object* v___x_4328_; uint8_t v_isShared_4329_; uint8_t v_isSharedCheck_4333_; 
lean_dec(v_constName_4307_);
v_a_4326_ = lean_ctor_get(v___x_4313_, 0);
v_isSharedCheck_4333_ = !lean_is_exclusive(v___x_4313_);
if (v_isSharedCheck_4333_ == 0)
{
v___x_4328_ = v___x_4313_;
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
else
{
lean_inc(v_a_4326_);
lean_dec(v___x_4313_);
v___x_4328_ = lean_box(0);
v_isShared_4329_ = v_isSharedCheck_4333_;
goto v_resetjp_4327_;
}
v_resetjp_4327_:
{
lean_object* v___x_4331_; 
if (v_isShared_4329_ == 0)
{
v___x_4331_ = v___x_4328_;
goto v_reusejp_4330_;
}
else
{
lean_object* v_reuseFailAlloc_4332_; 
v_reuseFailAlloc_4332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4332_, 0, v_a_4326_);
v___x_4331_ = v_reuseFailAlloc_4332_;
goto v_reusejp_4330_;
}
v_reusejp_4330_:
{
return v___x_4331_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4334_, lean_object* v___y_4335_, lean_object* v___y_4336_, lean_object* v___y_4337_, lean_object* v___y_4338_, lean_object* v___y_4339_){
_start:
{
lean_object* v_res_4340_; 
v_res_4340_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4334_, v___y_4335_, v___y_4336_, v___y_4337_, v___y_4338_);
lean_dec(v___y_4338_);
lean_dec_ref(v___y_4337_);
lean_dec(v___y_4336_);
lean_dec_ref(v___y_4335_);
return v_res_4340_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4342_; lean_object* v___x_4343_; 
v___x_4342_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4343_ = l_Lean_stringToMessageData(v___x_4342_);
return v___x_4343_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4345_; lean_object* v___x_4346_; 
v___x_4345_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4346_ = l_Lean_stringToMessageData(v___x_4345_);
return v___x_4346_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_4348_; lean_object* v___x_4349_; 
v___x_4348_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_4349_ = l_Lean_stringToMessageData(v___x_4348_);
return v___x_4349_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__7(void){
_start:
{
lean_object* v___x_4351_; lean_object* v___x_4352_; 
v___x_4351_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__6));
v___x_4352_ = l_Lean_stringToMessageData(v___x_4351_);
return v___x_4352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4353_, uint8_t v_attrKind_4354_, lean_object* v_prio_4355_, lean_object* v_a_4356_, lean_object* v_a_4357_, lean_object* v_a_4358_, lean_object* v_a_4359_){
_start:
{
lean_object* v___x_4361_; 
lean_inc(v_declName_4353_);
v___x_4361_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4353_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
if (lean_obj_tag(v___x_4361_) == 0)
{
lean_object* v_a_4362_; lean_object* v___y_4364_; lean_object* v___y_4365_; lean_object* v___y_4366_; lean_object* v___y_4367_; lean_object* v___y_4368_; lean_object* v___y_4392_; lean_object* v___y_4393_; lean_object* v___y_4394_; lean_object* v___y_4395_; lean_object* v___x_4440_; 
v_a_4362_ = lean_ctor_get(v___x_4361_, 0);
lean_inc(v_a_4362_);
lean_dec_ref_known(v___x_4361_, 1);
lean_inc(v_declName_4353_);
v___x_4440_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4353_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
if (lean_obj_tag(v___x_4440_) == 0)
{
lean_object* v_a_4441_; lean_object* v___x_4442_; uint8_t v___x_4443_; 
v_a_4441_ = lean_ctor_get(v___x_4440_, 0);
lean_inc(v_a_4441_);
lean_dec_ref_known(v___x_4440_, 1);
v___x_4442_ = l_Lean_ConstantInfo_type(v_a_4441_);
v___x_4443_ = l_Lean_Expr_hasSorry(v___x_4442_);
lean_dec_ref(v___x_4442_);
if (v___x_4443_ == 0)
{
lean_object* v___x_4444_; 
lean_inc(v_a_4362_);
v___x_4444_ = l_Lean_Meta_checkNonClassInstance(v_a_4362_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
if (lean_obj_tag(v___x_4444_) == 0)
{
lean_object* v___x_4445_; 
lean_dec_ref_known(v___x_4444_, 1);
v___x_4445_ = l_Lean_Meta_checkImpossibleInstance(v_a_4441_, v_a_4356_, v_a_4357_, v_a_4358_, v_a_4359_);
lean_dec(v_a_4441_);
if (lean_obj_tag(v___x_4445_) == 0)
{
lean_dec_ref_known(v___x_4445_, 1);
v___y_4392_ = v_a_4356_;
v___y_4393_ = v_a_4357_;
v___y_4394_ = v_a_4358_;
v___y_4395_ = v_a_4359_;
goto v___jp_4391_;
}
else
{
lean_dec(v_a_4362_);
lean_dec(v_prio_4355_);
lean_dec(v_declName_4353_);
return v___x_4445_;
}
}
else
{
lean_dec(v_a_4441_);
lean_dec(v_a_4362_);
lean_dec(v_prio_4355_);
lean_dec(v_declName_4353_);
return v___x_4444_;
}
}
else
{
lean_dec(v_a_4441_);
v___y_4392_ = v_a_4356_;
v___y_4393_ = v_a_4357_;
v___y_4394_ = v_a_4358_;
v___y_4395_ = v_a_4359_;
goto v___jp_4391_;
}
}
else
{
lean_object* v_a_4446_; lean_object* v___x_4448_; uint8_t v_isShared_4449_; uint8_t v_isSharedCheck_4453_; 
lean_dec(v_a_4362_);
lean_dec(v_prio_4355_);
lean_dec(v_declName_4353_);
v_a_4446_ = lean_ctor_get(v___x_4440_, 0);
v_isSharedCheck_4453_ = !lean_is_exclusive(v___x_4440_);
if (v_isSharedCheck_4453_ == 0)
{
v___x_4448_ = v___x_4440_;
v_isShared_4449_ = v_isSharedCheck_4453_;
goto v_resetjp_4447_;
}
else
{
lean_inc(v_a_4446_);
lean_dec(v___x_4440_);
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
v___jp_4363_:
{
lean_object* v___x_4369_; lean_object* v_a_4370_; lean_object* v___x_4372_; uint8_t v_isShared_4373_; uint8_t v_isSharedCheck_4390_; 
lean_inc(v_declName_4353_);
v___x_4369_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4353_, v___y_4368_);
v_a_4370_ = lean_ctor_get(v___x_4369_, 0);
v_isSharedCheck_4390_ = !lean_is_exclusive(v___x_4369_);
if (v_isSharedCheck_4390_ == 0)
{
v___x_4372_ = v___x_4369_;
v_isShared_4373_ = v_isSharedCheck_4390_;
goto v_resetjp_4371_;
}
else
{
lean_inc(v_a_4370_);
lean_dec(v___x_4369_);
v___x_4372_ = lean_box(0);
v_isShared_4373_ = v_isSharedCheck_4390_;
goto v_resetjp_4371_;
}
v_resetjp_4371_:
{
lean_object* v___x_4374_; 
lean_inc(v_a_4362_);
v___x_4374_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4362_, v_a_4370_, v___y_4365_, v___y_4366_, v___y_4367_, v___y_4368_);
if (lean_obj_tag(v___x_4374_) == 0)
{
lean_object* v_a_4375_; lean_object* v___x_4376_; lean_object* v___x_4378_; 
v_a_4375_ = lean_ctor_get(v___x_4374_, 0);
lean_inc(v_a_4375_);
lean_dec_ref_known(v___x_4374_, 1);
v___x_4376_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4373_ == 0)
{
lean_ctor_set_tag(v___x_4372_, 1);
lean_ctor_set(v___x_4372_, 0, v_declName_4353_);
v___x_4378_ = v___x_4372_;
goto v_reusejp_4377_;
}
else
{
lean_object* v_reuseFailAlloc_4381_; 
v_reuseFailAlloc_4381_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4381_, 0, v_declName_4353_);
v___x_4378_ = v_reuseFailAlloc_4381_;
goto v_reusejp_4377_;
}
v_reusejp_4377_:
{
lean_object* v___x_4379_; lean_object* v___x_4380_; 
v___x_4379_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4379_, 0, v___y_4364_);
lean_ctor_set(v___x_4379_, 1, v_a_4362_);
lean_ctor_set(v___x_4379_, 2, v_prio_4355_);
lean_ctor_set(v___x_4379_, 3, v___x_4378_);
lean_ctor_set(v___x_4379_, 4, v_a_4375_);
lean_ctor_set_uint8(v___x_4379_, sizeof(void*)*5, v_attrKind_4354_);
v___x_4380_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4376_, v___x_4379_, v_attrKind_4354_, v___y_4366_, v___y_4367_, v___y_4368_);
return v___x_4380_;
}
}
else
{
lean_object* v_a_4382_; lean_object* v___x_4384_; uint8_t v_isShared_4385_; uint8_t v_isSharedCheck_4389_; 
lean_del_object(v___x_4372_);
lean_dec_ref(v___y_4364_);
lean_dec(v_a_4362_);
lean_dec(v_prio_4355_);
lean_dec(v_declName_4353_);
v_a_4382_ = lean_ctor_get(v___x_4374_, 0);
v_isSharedCheck_4389_ = !lean_is_exclusive(v___x_4374_);
if (v_isSharedCheck_4389_ == 0)
{
v___x_4384_ = v___x_4374_;
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
else
{
lean_inc(v_a_4382_);
lean_dec(v___x_4374_);
v___x_4384_ = lean_box(0);
v_isShared_4385_ = v_isSharedCheck_4389_;
goto v_resetjp_4383_;
}
v_resetjp_4383_:
{
lean_object* v___x_4387_; 
if (v_isShared_4385_ == 0)
{
v___x_4387_ = v___x_4384_;
goto v_reusejp_4386_;
}
else
{
lean_object* v_reuseFailAlloc_4388_; 
v_reuseFailAlloc_4388_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4388_, 0, v_a_4382_);
v___x_4387_ = v_reuseFailAlloc_4388_;
goto v_reusejp_4386_;
}
v_reusejp_4386_:
{
return v___x_4387_;
}
}
}
}
}
v___jp_4391_:
{
lean_object* v___x_4396_; 
lean_inc(v_a_4362_);
v___x_4396_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4362_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4396_) == 0)
{
lean_object* v_a_4397_; lean_object* v___x_4398_; lean_object* v_a_4399_; uint8_t v___x_4400_; uint8_t v___x_4401_; uint8_t v___x_4402_; 
v_a_4397_ = lean_ctor_get(v___x_4396_, 0);
lean_inc(v_a_4397_);
lean_dec_ref_known(v___x_4396_, 1);
lean_inc(v_declName_4353_);
v___x_4398_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4353_, v___y_4395_);
v_a_4399_ = lean_ctor_get(v___x_4398_, 0);
lean_inc(v_a_4399_);
lean_dec_ref(v___x_4398_);
v___x_4400_ = 1;
v___x_4401_ = lean_unbox(v_a_4399_);
lean_dec(v_a_4399_);
v___x_4402_ = l_Lean_instBEqReducibilityStatus_beq(v___x_4401_, v___x_4400_);
if (v___x_4402_ == 0)
{
v___y_4364_ = v_a_4397_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
v___y_4368_ = v___y_4395_;
goto v___jp_4363_;
}
else
{
lean_object* v___x_4403_; 
lean_inc(v_declName_4353_);
v___x_4403_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4353_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4403_) == 0)
{
lean_object* v_a_4404_; uint8_t v___x_4405_; 
v_a_4404_ = lean_ctor_get(v___x_4403_, 0);
lean_inc(v_a_4404_);
lean_dec_ref_known(v___x_4403_, 1);
v___x_4405_ = l_Lean_ConstantInfo_isDefinition(v_a_4404_);
lean_dec(v_a_4404_);
if (v___x_4405_ == 0)
{
lean_object* v___x_4406_; lean_object* v_env_4407_; uint8_t v___x_4408_; 
v___x_4406_ = lean_st_ref_get(v___y_4395_);
v_env_4407_ = lean_ctor_get(v___x_4406_, 0);
lean_inc_ref(v_env_4407_);
lean_dec(v___x_4406_);
lean_inc(v_declName_4353_);
v___x_4408_ = l_Lean_wasOriginallyDefn(v_env_4407_, v_declName_4353_);
if (v___x_4408_ == 0)
{
v___y_4364_ = v_a_4397_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
v___y_4368_ = v___y_4395_;
goto v___jp_4363_;
}
else
{
lean_object* v___x_4409_; lean_object* v___x_4410_; lean_object* v___x_4411_; lean_object* v___x_4412_; lean_object* v___x_4413_; lean_object* v___x_4414_; 
v___x_4409_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4353_);
v___x_4410_ = l_Lean_MessageData_ofName(v_declName_4353_);
v___x_4411_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4411_, 0, v___x_4409_);
lean_ctor_set(v___x_4411_, 1, v___x_4410_);
v___x_4412_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4413_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4413_, 0, v___x_4411_);
lean_ctor_set(v___x_4413_, 1, v___x_4412_);
v___x_4414_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4413_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4414_) == 0)
{
lean_dec_ref_known(v___x_4414_, 1);
v___y_4364_ = v_a_4397_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
v___y_4368_ = v___y_4395_;
goto v___jp_4363_;
}
else
{
lean_dec(v_a_4397_);
lean_dec(v_a_4362_);
lean_dec(v_prio_4355_);
lean_dec(v_declName_4353_);
return v___x_4414_;
}
}
}
else
{
lean_object* v_options_4415_; lean_object* v___x_4416_; uint8_t v___x_4417_; 
v_options_4415_ = lean_ctor_get(v___y_4394_, 2);
v___x_4416_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_warnClassDefReducibility));
v___x_4417_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_4415_, v___x_4416_);
if (v___x_4417_ == 0)
{
v___y_4364_ = v_a_4397_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
v___y_4368_ = v___y_4395_;
goto v___jp_4363_;
}
else
{
lean_object* v___x_4418_; lean_object* v___x_4419_; lean_object* v___x_4420_; lean_object* v___x_4421_; lean_object* v___x_4422_; lean_object* v___x_4423_; 
v___x_4418_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
lean_inc(v_declName_4353_);
v___x_4419_ = l_Lean_MessageData_ofName(v_declName_4353_);
v___x_4420_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4420_, 0, v___x_4418_);
lean_ctor_set(v___x_4420_, 1, v___x_4419_);
v___x_4421_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__7, &l_Lean_Meta_addInstance___closed__7_once, _init_l_Lean_Meta_addInstance___closed__7);
v___x_4422_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4422_, 0, v___x_4420_);
lean_ctor_set(v___x_4422_, 1, v___x_4421_);
v___x_4423_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4422_, v___y_4392_, v___y_4393_, v___y_4394_, v___y_4395_);
if (lean_obj_tag(v___x_4423_) == 0)
{
lean_dec_ref_known(v___x_4423_, 1);
v___y_4364_ = v_a_4397_;
v___y_4365_ = v___y_4392_;
v___y_4366_ = v___y_4393_;
v___y_4367_ = v___y_4394_;
v___y_4368_ = v___y_4395_;
goto v___jp_4363_;
}
else
{
lean_dec(v_a_4397_);
lean_dec(v_a_4362_);
lean_dec(v_prio_4355_);
lean_dec(v_declName_4353_);
return v___x_4423_;
}
}
}
}
else
{
lean_object* v_a_4424_; lean_object* v___x_4426_; uint8_t v_isShared_4427_; uint8_t v_isSharedCheck_4431_; 
lean_dec(v_a_4397_);
lean_dec(v_a_4362_);
lean_dec(v_prio_4355_);
lean_dec(v_declName_4353_);
v_a_4424_ = lean_ctor_get(v___x_4403_, 0);
v_isSharedCheck_4431_ = !lean_is_exclusive(v___x_4403_);
if (v_isSharedCheck_4431_ == 0)
{
v___x_4426_ = v___x_4403_;
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
else
{
lean_inc(v_a_4424_);
lean_dec(v___x_4403_);
v___x_4426_ = lean_box(0);
v_isShared_4427_ = v_isSharedCheck_4431_;
goto v_resetjp_4425_;
}
v_resetjp_4425_:
{
lean_object* v___x_4429_; 
if (v_isShared_4427_ == 0)
{
v___x_4429_ = v___x_4426_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4430_; 
v_reuseFailAlloc_4430_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4430_, 0, v_a_4424_);
v___x_4429_ = v_reuseFailAlloc_4430_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
return v___x_4429_;
}
}
}
}
}
else
{
lean_object* v_a_4432_; lean_object* v___x_4434_; uint8_t v_isShared_4435_; uint8_t v_isSharedCheck_4439_; 
lean_dec(v_a_4362_);
lean_dec(v_prio_4355_);
lean_dec(v_declName_4353_);
v_a_4432_ = lean_ctor_get(v___x_4396_, 0);
v_isSharedCheck_4439_ = !lean_is_exclusive(v___x_4396_);
if (v_isSharedCheck_4439_ == 0)
{
v___x_4434_ = v___x_4396_;
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
else
{
lean_inc(v_a_4432_);
lean_dec(v___x_4396_);
v___x_4434_ = lean_box(0);
v_isShared_4435_ = v_isSharedCheck_4439_;
goto v_resetjp_4433_;
}
v_resetjp_4433_:
{
lean_object* v___x_4437_; 
if (v_isShared_4435_ == 0)
{
v___x_4437_ = v___x_4434_;
goto v_reusejp_4436_;
}
else
{
lean_object* v_reuseFailAlloc_4438_; 
v_reuseFailAlloc_4438_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4438_, 0, v_a_4432_);
v___x_4437_ = v_reuseFailAlloc_4438_;
goto v_reusejp_4436_;
}
v_reusejp_4436_:
{
return v___x_4437_;
}
}
}
}
}
else
{
lean_object* v_a_4454_; lean_object* v___x_4456_; uint8_t v_isShared_4457_; uint8_t v_isSharedCheck_4461_; 
lean_dec(v_prio_4355_);
lean_dec(v_declName_4353_);
v_a_4454_ = lean_ctor_get(v___x_4361_, 0);
v_isSharedCheck_4461_ = !lean_is_exclusive(v___x_4361_);
if (v_isSharedCheck_4461_ == 0)
{
v___x_4456_ = v___x_4361_;
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
else
{
lean_inc(v_a_4454_);
lean_dec(v___x_4361_);
v___x_4456_ = lean_box(0);
v_isShared_4457_ = v_isSharedCheck_4461_;
goto v_resetjp_4455_;
}
v_resetjp_4455_:
{
lean_object* v___x_4459_; 
if (v_isShared_4457_ == 0)
{
v___x_4459_ = v___x_4456_;
goto v_reusejp_4458_;
}
else
{
lean_object* v_reuseFailAlloc_4460_; 
v_reuseFailAlloc_4460_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4460_, 0, v_a_4454_);
v___x_4459_ = v_reuseFailAlloc_4460_;
goto v_reusejp_4458_;
}
v_reusejp_4458_:
{
return v___x_4459_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4462_, lean_object* v_attrKind_4463_, lean_object* v_prio_4464_, lean_object* v_a_4465_, lean_object* v_a_4466_, lean_object* v_a_4467_, lean_object* v_a_4468_, lean_object* v_a_4469_){
_start:
{
uint8_t v_attrKind_boxed_4470_; lean_object* v_res_4471_; 
v_attrKind_boxed_4470_ = lean_unbox(v_attrKind_4463_);
v_res_4471_ = l_Lean_Meta_addInstance(v_declName_4462_, v_attrKind_boxed_4470_, v_prio_4464_, v_a_4465_, v_a_4466_, v_a_4467_, v_a_4468_);
lean_dec(v_a_4468_);
lean_dec_ref(v_a_4467_);
lean_dec(v_a_4466_);
lean_dec_ref(v_a_4465_);
return v_res_4471_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_4472_, lean_object* v_constName_4473_, lean_object* v___y_4474_, lean_object* v___y_4475_, lean_object* v___y_4476_, lean_object* v___y_4477_){
_start:
{
lean_object* v___x_4479_; 
v___x_4479_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4473_, v___y_4474_, v___y_4475_, v___y_4476_, v___y_4477_);
return v___x_4479_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4480_, lean_object* v_constName_4481_, lean_object* v___y_4482_, lean_object* v___y_4483_, lean_object* v___y_4484_, lean_object* v___y_4485_, lean_object* v___y_4486_){
_start:
{
lean_object* v_res_4487_; 
v_res_4487_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_4480_, v_constName_4481_, v___y_4482_, v___y_4483_, v___y_4484_, v___y_4485_);
lean_dec(v___y_4485_);
lean_dec_ref(v___y_4484_);
lean_dec(v___y_4483_);
lean_dec_ref(v___y_4482_);
return v_res_4487_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_4488_, lean_object* v_ref_4489_, lean_object* v_constName_4490_, lean_object* v___y_4491_, lean_object* v___y_4492_, lean_object* v___y_4493_, lean_object* v___y_4494_){
_start:
{
lean_object* v___x_4496_; 
v___x_4496_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4489_, v_constName_4490_, v___y_4491_, v___y_4492_, v___y_4493_, v___y_4494_);
return v___x_4496_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4497_, lean_object* v_ref_4498_, lean_object* v_constName_4499_, lean_object* v___y_4500_, lean_object* v___y_4501_, lean_object* v___y_4502_, lean_object* v___y_4503_, lean_object* v___y_4504_){
_start:
{
lean_object* v_res_4505_; 
v_res_4505_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_4497_, v_ref_4498_, v_constName_4499_, v___y_4500_, v___y_4501_, v___y_4502_, v___y_4503_);
lean_dec(v___y_4503_);
lean_dec_ref(v___y_4502_);
lean_dec(v___y_4501_);
lean_dec_ref(v___y_4500_);
lean_dec(v_ref_4498_);
return v_res_4505_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b1_4506_, lean_object* v_ref_4507_, lean_object* v_msg_4508_, lean_object* v_declHint_4509_, lean_object* v___y_4510_, lean_object* v___y_4511_, lean_object* v___y_4512_, lean_object* v___y_4513_){
_start:
{
lean_object* v___x_4515_; 
v___x_4515_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4507_, v_msg_4508_, v_declHint_4509_, v___y_4510_, v___y_4511_, v___y_4512_, v___y_4513_);
return v___x_4515_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4516_, lean_object* v_ref_4517_, lean_object* v_msg_4518_, lean_object* v_declHint_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_, lean_object* v___y_4524_){
_start:
{
lean_object* v_res_4525_; 
v_res_4525_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(v_00_u03b1_4516_, v_ref_4517_, v_msg_4518_, v_declHint_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
lean_dec(v___y_4523_);
lean_dec_ref(v___y_4522_);
lean_dec(v___y_4521_);
lean_dec_ref(v___y_4520_);
lean_dec(v_ref_4517_);
return v_res_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_4526_, lean_object* v_declHint_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_){
_start:
{
lean_object* v___x_4533_; 
v___x_4533_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4526_, v_declHint_4527_, v___y_4531_);
return v___x_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_4534_, lean_object* v_declHint_4535_, lean_object* v___y_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v_res_4541_; 
v_res_4541_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(v_msg_4534_, v_declHint_4535_, v___y_4536_, v___y_4537_, v___y_4538_, v___y_4539_);
lean_dec(v___y_4539_);
lean_dec_ref(v___y_4538_);
lean_dec(v___y_4537_);
lean_dec_ref(v___y_4536_);
return v_res_4541_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_4542_, lean_object* v_ref_4543_, lean_object* v_msg_4544_, lean_object* v___y_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_){
_start:
{
lean_object* v___x_4550_; 
v___x_4550_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4543_, v_msg_4544_, v___y_4545_, v___y_4546_, v___y_4547_, v___y_4548_);
return v___x_4550_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4551_, lean_object* v_ref_4552_, lean_object* v_msg_4553_, lean_object* v___y_4554_, lean_object* v___y_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_){
_start:
{
lean_object* v_res_4559_; 
v_res_4559_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_4551_, v_ref_4552_, v_msg_4553_, v___y_4554_, v___y_4555_, v___y_4556_, v___y_4557_);
lean_dec(v___y_4557_);
lean_dec_ref(v___y_4556_);
lean_dec(v___y_4555_);
lean_dec_ref(v___y_4554_);
lean_dec(v_ref_4552_);
return v_res_4559_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4560_, uint8_t v_s_4561_, lean_object* v___y_4562_, lean_object* v___y_4563_){
_start:
{
lean_object* v___x_4565_; lean_object* v_env_4566_; lean_object* v_nextMacroScope_4567_; lean_object* v_ngen_4568_; lean_object* v_auxDeclNGen_4569_; lean_object* v_traceState_4570_; lean_object* v_messages_4571_; lean_object* v_infoState_4572_; lean_object* v_snapshotTasks_4573_; lean_object* v___x_4575_; uint8_t v_isShared_4576_; uint8_t v_isSharedCheck_4602_; 
v___x_4565_ = lean_st_ref_take(v___y_4563_);
v_env_4566_ = lean_ctor_get(v___x_4565_, 0);
v_nextMacroScope_4567_ = lean_ctor_get(v___x_4565_, 1);
v_ngen_4568_ = lean_ctor_get(v___x_4565_, 2);
v_auxDeclNGen_4569_ = lean_ctor_get(v___x_4565_, 3);
v_traceState_4570_ = lean_ctor_get(v___x_4565_, 4);
v_messages_4571_ = lean_ctor_get(v___x_4565_, 6);
v_infoState_4572_ = lean_ctor_get(v___x_4565_, 7);
v_snapshotTasks_4573_ = lean_ctor_get(v___x_4565_, 8);
v_isSharedCheck_4602_ = !lean_is_exclusive(v___x_4565_);
if (v_isSharedCheck_4602_ == 0)
{
lean_object* v_unused_4603_; 
v_unused_4603_ = lean_ctor_get(v___x_4565_, 5);
lean_dec(v_unused_4603_);
v___x_4575_ = v___x_4565_;
v_isShared_4576_ = v_isSharedCheck_4602_;
goto v_resetjp_4574_;
}
else
{
lean_inc(v_snapshotTasks_4573_);
lean_inc(v_infoState_4572_);
lean_inc(v_messages_4571_);
lean_inc(v_traceState_4570_);
lean_inc(v_auxDeclNGen_4569_);
lean_inc(v_ngen_4568_);
lean_inc(v_nextMacroScope_4567_);
lean_inc(v_env_4566_);
lean_dec(v___x_4565_);
v___x_4575_ = lean_box(0);
v_isShared_4576_ = v_isSharedCheck_4602_;
goto v_resetjp_4574_;
}
v_resetjp_4574_:
{
uint8_t v___x_4577_; lean_object* v___x_4578_; lean_object* v___x_4579_; lean_object* v___x_4580_; lean_object* v___x_4582_; 
v___x_4577_ = 0;
v___x_4578_ = lean_box(0);
v___x_4579_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4566_, v_declName_4560_, v_s_4561_, v___x_4577_, v___x_4578_);
v___x_4580_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4576_ == 0)
{
lean_ctor_set(v___x_4575_, 5, v___x_4580_);
lean_ctor_set(v___x_4575_, 0, v___x_4579_);
v___x_4582_ = v___x_4575_;
goto v_reusejp_4581_;
}
else
{
lean_object* v_reuseFailAlloc_4601_; 
v_reuseFailAlloc_4601_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4601_, 0, v___x_4579_);
lean_ctor_set(v_reuseFailAlloc_4601_, 1, v_nextMacroScope_4567_);
lean_ctor_set(v_reuseFailAlloc_4601_, 2, v_ngen_4568_);
lean_ctor_set(v_reuseFailAlloc_4601_, 3, v_auxDeclNGen_4569_);
lean_ctor_set(v_reuseFailAlloc_4601_, 4, v_traceState_4570_);
lean_ctor_set(v_reuseFailAlloc_4601_, 5, v___x_4580_);
lean_ctor_set(v_reuseFailAlloc_4601_, 6, v_messages_4571_);
lean_ctor_set(v_reuseFailAlloc_4601_, 7, v_infoState_4572_);
lean_ctor_set(v_reuseFailAlloc_4601_, 8, v_snapshotTasks_4573_);
v___x_4582_ = v_reuseFailAlloc_4601_;
goto v_reusejp_4581_;
}
v_reusejp_4581_:
{
lean_object* v___x_4583_; lean_object* v___x_4584_; lean_object* v_mctx_4585_; lean_object* v_zetaDeltaFVarIds_4586_; lean_object* v_postponed_4587_; lean_object* v_diag_4588_; lean_object* v___x_4590_; uint8_t v_isShared_4591_; uint8_t v_isSharedCheck_4599_; 
v___x_4583_ = lean_st_ref_set(v___y_4563_, v___x_4582_);
v___x_4584_ = lean_st_ref_take(v___y_4562_);
v_mctx_4585_ = lean_ctor_get(v___x_4584_, 0);
v_zetaDeltaFVarIds_4586_ = lean_ctor_get(v___x_4584_, 2);
v_postponed_4587_ = lean_ctor_get(v___x_4584_, 3);
v_diag_4588_ = lean_ctor_get(v___x_4584_, 4);
v_isSharedCheck_4599_ = !lean_is_exclusive(v___x_4584_);
if (v_isSharedCheck_4599_ == 0)
{
lean_object* v_unused_4600_; 
v_unused_4600_ = lean_ctor_get(v___x_4584_, 1);
lean_dec(v_unused_4600_);
v___x_4590_ = v___x_4584_;
v_isShared_4591_ = v_isSharedCheck_4599_;
goto v_resetjp_4589_;
}
else
{
lean_inc(v_diag_4588_);
lean_inc(v_postponed_4587_);
lean_inc(v_zetaDeltaFVarIds_4586_);
lean_inc(v_mctx_4585_);
lean_dec(v___x_4584_);
v___x_4590_ = lean_box(0);
v_isShared_4591_ = v_isSharedCheck_4599_;
goto v_resetjp_4589_;
}
v_resetjp_4589_:
{
lean_object* v___x_4592_; lean_object* v___x_4594_; 
v___x_4592_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_4591_ == 0)
{
lean_ctor_set(v___x_4590_, 1, v___x_4592_);
v___x_4594_ = v___x_4590_;
goto v_reusejp_4593_;
}
else
{
lean_object* v_reuseFailAlloc_4598_; 
v_reuseFailAlloc_4598_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4598_, 0, v_mctx_4585_);
lean_ctor_set(v_reuseFailAlloc_4598_, 1, v___x_4592_);
lean_ctor_set(v_reuseFailAlloc_4598_, 2, v_zetaDeltaFVarIds_4586_);
lean_ctor_set(v_reuseFailAlloc_4598_, 3, v_postponed_4587_);
lean_ctor_set(v_reuseFailAlloc_4598_, 4, v_diag_4588_);
v___x_4594_ = v_reuseFailAlloc_4598_;
goto v_reusejp_4593_;
}
v_reusejp_4593_:
{
lean_object* v___x_4595_; lean_object* v___x_4596_; lean_object* v___x_4597_; 
v___x_4595_ = lean_st_ref_set(v___y_4562_, v___x_4594_);
v___x_4596_ = lean_box(0);
v___x_4597_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4597_, 0, v___x_4596_);
return v___x_4597_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4604_, lean_object* v_s_4605_, lean_object* v___y_4606_, lean_object* v___y_4607_, lean_object* v___y_4608_){
_start:
{
uint8_t v_s_boxed_4609_; lean_object* v_res_4610_; 
v_s_boxed_4609_ = lean_unbox(v_s_4605_);
v_res_4610_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4604_, v_s_boxed_4609_, v___y_4606_, v___y_4607_);
lean_dec(v___y_4607_);
lean_dec(v___y_4606_);
return v_res_4610_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4611_, uint8_t v_s_4612_, lean_object* v___y_4613_, lean_object* v___y_4614_, lean_object* v___y_4615_, lean_object* v___y_4616_){
_start:
{
lean_object* v___x_4618_; 
v___x_4618_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4611_, v_s_4612_, v___y_4614_, v___y_4616_);
return v___x_4618_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4619_, lean_object* v_s_4620_, lean_object* v___y_4621_, lean_object* v___y_4622_, lean_object* v___y_4623_, lean_object* v___y_4624_, lean_object* v___y_4625_){
_start:
{
uint8_t v_s_boxed_4626_; lean_object* v_res_4627_; 
v_s_boxed_4626_ = lean_unbox(v_s_4620_);
v_res_4627_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4619_, v_s_boxed_4626_, v___y_4621_, v___y_4622_, v___y_4623_, v___y_4624_);
lean_dec(v___y_4624_);
lean_dec_ref(v___y_4623_);
lean_dec(v___y_4622_);
lean_dec_ref(v___y_4621_);
return v_res_4627_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4628_, uint8_t v_attrKind_4629_, lean_object* v_prio_4630_, lean_object* v_a_4631_, lean_object* v_a_4632_, lean_object* v_a_4633_, lean_object* v_a_4634_){
_start:
{
uint8_t v___x_4636_; lean_object* v___x_4637_; lean_object* v___x_4638_; 
v___x_4636_ = 4;
lean_inc(v_declName_4628_);
v___x_4637_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4628_, v___x_4636_, v_a_4632_, v_a_4634_);
lean_dec_ref(v___x_4637_);
v___x_4638_ = l_Lean_Meta_addInstance(v_declName_4628_, v_attrKind_4629_, v_prio_4630_, v_a_4631_, v_a_4632_, v_a_4633_, v_a_4634_);
return v___x_4638_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4639_, lean_object* v_attrKind_4640_, lean_object* v_prio_4641_, lean_object* v_a_4642_, lean_object* v_a_4643_, lean_object* v_a_4644_, lean_object* v_a_4645_, lean_object* v_a_4646_){
_start:
{
uint8_t v_attrKind_boxed_4647_; lean_object* v_res_4648_; 
v_attrKind_boxed_4647_ = lean_unbox(v_attrKind_4640_);
v_res_4648_ = l_Lean_Meta_registerInstance(v_declName_4639_, v_attrKind_boxed_4647_, v_prio_4641_, v_a_4642_, v_a_4643_, v_a_4644_, v_a_4645_);
lean_dec(v_a_4645_);
lean_dec_ref(v_a_4644_);
lean_dec(v_a_4643_);
lean_dec_ref(v_a_4642_);
return v_res_4648_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4649_, lean_object* v_x_4650_){
_start:
{
lean_inc_ref(v_a_4649_);
return v_a_4649_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4651_, lean_object* v_x_4652_){
_start:
{
lean_object* v_res_4653_; 
v_res_4653_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4651_, v_x_4652_);
lean_dec_ref(v_x_4652_);
lean_dec_ref(v_a_4651_);
return v_res_4653_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4654_, lean_object* v___y_4655_, lean_object* v___y_4656_){
_start:
{
lean_object* v___x_4658_; lean_object* v_env_4659_; lean_object* v_options_4660_; lean_object* v___x_4661_; lean_object* v___x_4662_; lean_object* v___x_4663_; lean_object* v___x_4664_; lean_object* v___x_4665_; lean_object* v___x_4666_; lean_object* v___x_4667_; 
v___x_4658_ = lean_st_ref_get(v___y_4656_);
v_env_4659_ = lean_ctor_get(v___x_4658_, 0);
lean_inc_ref(v_env_4659_);
lean_dec(v___x_4658_);
v_options_4660_ = lean_ctor_get(v___y_4655_, 2);
v___x_4661_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4662_ = lean_unsigned_to_nat(32u);
v___x_4663_ = lean_mk_empty_array_with_capacity(v___x_4662_);
lean_dec_ref(v___x_4663_);
v___x_4664_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_4660_);
v___x_4665_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4665_, 0, v_env_4659_);
lean_ctor_set(v___x_4665_, 1, v___x_4661_);
lean_ctor_set(v___x_4665_, 2, v___x_4664_);
lean_ctor_set(v___x_4665_, 3, v_options_4660_);
v___x_4666_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4666_, 0, v___x_4665_);
lean_ctor_set(v___x_4666_, 1, v_msgData_4654_);
v___x_4667_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4667_, 0, v___x_4666_);
return v___x_4667_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
lean_object* v_res_4672_; 
v_res_4672_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4668_, v___y_4669_, v___y_4670_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
return v_res_4672_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4673_, lean_object* v___y_4674_, lean_object* v___y_4675_){
_start:
{
lean_object* v_ref_4677_; lean_object* v___x_4678_; lean_object* v_a_4679_; lean_object* v___x_4681_; uint8_t v_isShared_4682_; uint8_t v_isSharedCheck_4687_; 
v_ref_4677_ = lean_ctor_get(v___y_4674_, 5);
v___x_4678_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4673_, v___y_4674_, v___y_4675_);
v_a_4679_ = lean_ctor_get(v___x_4678_, 0);
v_isSharedCheck_4687_ = !lean_is_exclusive(v___x_4678_);
if (v_isSharedCheck_4687_ == 0)
{
v___x_4681_ = v___x_4678_;
v_isShared_4682_ = v_isSharedCheck_4687_;
goto v_resetjp_4680_;
}
else
{
lean_inc(v_a_4679_);
lean_dec(v___x_4678_);
v___x_4681_ = lean_box(0);
v_isShared_4682_ = v_isSharedCheck_4687_;
goto v_resetjp_4680_;
}
v_resetjp_4680_:
{
lean_object* v___x_4683_; lean_object* v___x_4685_; 
lean_inc(v_ref_4677_);
v___x_4683_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4683_, 0, v_ref_4677_);
lean_ctor_set(v___x_4683_, 1, v_a_4679_);
if (v_isShared_4682_ == 0)
{
lean_ctor_set_tag(v___x_4681_, 1);
lean_ctor_set(v___x_4681_, 0, v___x_4683_);
v___x_4685_ = v___x_4681_;
goto v_reusejp_4684_;
}
else
{
lean_object* v_reuseFailAlloc_4686_; 
v_reuseFailAlloc_4686_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4686_, 0, v___x_4683_);
v___x_4685_ = v_reuseFailAlloc_4686_;
goto v_reusejp_4684_;
}
v_reusejp_4684_:
{
return v___x_4685_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4688_, lean_object* v___y_4689_, lean_object* v___y_4690_, lean_object* v___y_4691_){
_start:
{
lean_object* v_res_4692_; 
v_res_4692_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4688_, v___y_4689_, v___y_4690_);
lean_dec(v___y_4690_);
lean_dec_ref(v___y_4689_);
return v_res_4692_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4693_, lean_object* v_i_4694_, lean_object* v_k_4695_){
_start:
{
lean_object* v___x_4696_; uint8_t v___x_4697_; 
v___x_4696_ = lean_array_get_size(v_keys_4693_);
v___x_4697_ = lean_nat_dec_lt(v_i_4694_, v___x_4696_);
if (v___x_4697_ == 0)
{
lean_dec(v_i_4694_);
return v___x_4697_;
}
else
{
lean_object* v_k_x27_4698_; uint8_t v___x_4699_; 
v_k_x27_4698_ = lean_array_fget_borrowed(v_keys_4693_, v_i_4694_);
v___x_4699_ = lean_name_eq(v_k_4695_, v_k_x27_4698_);
if (v___x_4699_ == 0)
{
lean_object* v___x_4700_; lean_object* v___x_4701_; 
v___x_4700_ = lean_unsigned_to_nat(1u);
v___x_4701_ = lean_nat_add(v_i_4694_, v___x_4700_);
lean_dec(v_i_4694_);
v_i_4694_ = v___x_4701_;
goto _start;
}
else
{
lean_dec(v_i_4694_);
return v___x_4699_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4703_, lean_object* v_i_4704_, lean_object* v_k_4705_){
_start:
{
uint8_t v_res_4706_; lean_object* v_r_4707_; 
v_res_4706_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4703_, v_i_4704_, v_k_4705_);
lean_dec(v_k_4705_);
lean_dec_ref(v_keys_4703_);
v_r_4707_ = lean_box(v_res_4706_);
return v_r_4707_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4708_, size_t v_x_4709_, lean_object* v_x_4710_){
_start:
{
if (lean_obj_tag(v_x_4708_) == 0)
{
lean_object* v_es_4711_; lean_object* v___x_4712_; size_t v___x_4713_; size_t v___x_4714_; lean_object* v_j_4715_; lean_object* v___x_4716_; 
v_es_4711_ = lean_ctor_get(v_x_4708_, 0);
v___x_4712_ = lean_box(2);
v___x_4713_ = ((size_t)31ULL);
v___x_4714_ = lean_usize_land(v_x_4709_, v___x_4713_);
v_j_4715_ = lean_usize_to_nat(v___x_4714_);
v___x_4716_ = lean_array_get_borrowed(v___x_4712_, v_es_4711_, v_j_4715_);
lean_dec(v_j_4715_);
switch(lean_obj_tag(v___x_4716_))
{
case 0:
{
lean_object* v_key_4717_; uint8_t v___x_4718_; 
v_key_4717_ = lean_ctor_get(v___x_4716_, 0);
v___x_4718_ = lean_name_eq(v_x_4710_, v_key_4717_);
return v___x_4718_;
}
case 1:
{
lean_object* v_node_4719_; size_t v___x_4720_; size_t v___x_4721_; 
v_node_4719_ = lean_ctor_get(v___x_4716_, 0);
v___x_4720_ = ((size_t)5ULL);
v___x_4721_ = lean_usize_shift_right(v_x_4709_, v___x_4720_);
v_x_4708_ = v_node_4719_;
v_x_4709_ = v___x_4721_;
goto _start;
}
default: 
{
uint8_t v___x_4723_; 
v___x_4723_ = 0;
return v___x_4723_;
}
}
}
else
{
lean_object* v_ks_4724_; lean_object* v___x_4725_; uint8_t v___x_4726_; 
v_ks_4724_ = lean_ctor_get(v_x_4708_, 0);
v___x_4725_ = lean_unsigned_to_nat(0u);
v___x_4726_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4724_, v___x_4725_, v_x_4710_);
return v___x_4726_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4727_, lean_object* v_x_4728_, lean_object* v_x_4729_){
_start:
{
size_t v_x_2346__boxed_4730_; uint8_t v_res_4731_; lean_object* v_r_4732_; 
v_x_2346__boxed_4730_ = lean_unbox_usize(v_x_4728_);
lean_dec(v_x_4728_);
v_res_4731_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4727_, v_x_2346__boxed_4730_, v_x_4729_);
lean_dec(v_x_4729_);
lean_dec_ref(v_x_4727_);
v_r_4732_ = lean_box(v_res_4731_);
return v_r_4732_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4733_, lean_object* v_x_4734_){
_start:
{
uint64_t v___y_4736_; 
if (lean_obj_tag(v_x_4734_) == 0)
{
uint64_t v___x_4739_; 
v___x_4739_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0);
v___y_4736_ = v___x_4739_;
goto v___jp_4735_;
}
else
{
uint64_t v_hash_4740_; 
v_hash_4740_ = lean_ctor_get_uint64(v_x_4734_, sizeof(void*)*2);
v___y_4736_ = v_hash_4740_;
goto v___jp_4735_;
}
v___jp_4735_:
{
size_t v___x_4737_; uint8_t v___x_4738_; 
v___x_4737_ = lean_uint64_to_usize(v___y_4736_);
v___x_4738_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4733_, v___x_4737_, v_x_4734_);
return v___x_4738_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4741_, lean_object* v_x_4742_){
_start:
{
uint8_t v_res_4743_; lean_object* v_r_4744_; 
v_res_4743_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4741_, v_x_4742_);
lean_dec(v_x_4742_);
lean_dec_ref(v_x_4741_);
v_r_4744_ = lean_box(v_res_4743_);
return v_r_4744_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4745_, lean_object* v_declName_4746_, lean_object* v___y_4747_, lean_object* v___y_4748_){
_start:
{
lean_object* v_instanceNames_4753_; uint8_t v___x_4754_; 
v_instanceNames_4753_ = lean_ctor_get(v_d_4745_, 1);
v___x_4754_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4753_, v_declName_4746_);
if (v___x_4754_ == 0)
{
lean_object* v___x_4755_; lean_object* v___x_4756_; lean_object* v___x_4757_; lean_object* v___x_4758_; lean_object* v___x_4759_; lean_object* v___x_4760_; lean_object* v_a_4761_; lean_object* v___x_4763_; uint8_t v_isShared_4764_; uint8_t v_isSharedCheck_4768_; 
lean_dec_ref(v_d_4745_);
v___x_4755_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4756_ = l_Lean_MessageData_ofConstName(v_declName_4746_, v___x_4754_);
v___x_4757_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4757_, 0, v___x_4755_);
lean_ctor_set(v___x_4757_, 1, v___x_4756_);
v___x_4758_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4759_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4759_, 0, v___x_4757_);
lean_ctor_set(v___x_4759_, 1, v___x_4758_);
v___x_4760_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4759_, v___y_4747_, v___y_4748_);
v_a_4761_ = lean_ctor_get(v___x_4760_, 0);
v_isSharedCheck_4768_ = !lean_is_exclusive(v___x_4760_);
if (v_isSharedCheck_4768_ == 0)
{
v___x_4763_ = v___x_4760_;
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
else
{
lean_inc(v_a_4761_);
lean_dec(v___x_4760_);
v___x_4763_ = lean_box(0);
v_isShared_4764_ = v_isSharedCheck_4768_;
goto v_resetjp_4762_;
}
v_resetjp_4762_:
{
lean_object* v___x_4766_; 
if (v_isShared_4764_ == 0)
{
v___x_4766_ = v___x_4763_;
goto v_reusejp_4765_;
}
else
{
lean_object* v_reuseFailAlloc_4767_; 
v_reuseFailAlloc_4767_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4767_, 0, v_a_4761_);
v___x_4766_ = v_reuseFailAlloc_4767_;
goto v_reusejp_4765_;
}
v_reusejp_4765_:
{
return v___x_4766_;
}
}
}
else
{
goto v___jp_4750_;
}
v___jp_4750_:
{
lean_object* v___x_4751_; lean_object* v___x_4752_; 
v___x_4751_ = l_Lean_Meta_Instances_eraseCore(v_d_4745_, v_declName_4746_);
v___x_4752_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4752_, 0, v___x_4751_);
return v___x_4752_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4769_, lean_object* v_declName_4770_, lean_object* v___y_4771_, lean_object* v___y_4772_, lean_object* v___y_4773_){
_start:
{
lean_object* v_res_4774_; 
v_res_4774_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4769_, v_declName_4770_, v___y_4771_, v___y_4772_);
lean_dec(v___y_4772_);
lean_dec_ref(v___y_4771_);
return v_res_4774_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4775_, lean_object* v_declName_4776_, lean_object* v___y_4777_, lean_object* v___y_4778_){
_start:
{
lean_object* v___x_4780_; lean_object* v_env_4781_; lean_object* v___x_4782_; lean_object* v_ext_4783_; lean_object* v_toEnvExtension_4784_; lean_object* v_asyncMode_4785_; lean_object* v___x_4786_; lean_object* v___x_4787_; 
v___x_4780_ = lean_st_ref_get(v___y_4778_);
v_env_4781_ = lean_ctor_get(v___x_4780_, 0);
lean_inc_ref(v_env_4781_);
lean_dec(v___x_4780_);
v___x_4782_ = l_Lean_Meta_instanceExtension;
v_ext_4783_ = lean_ctor_get(v___x_4782_, 1);
v_toEnvExtension_4784_ = lean_ctor_get(v_ext_4783_, 0);
v_asyncMode_4785_ = lean_ctor_get(v_toEnvExtension_4784_, 2);
v___x_4786_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4775_, v___x_4782_, v_env_4781_, v_asyncMode_4785_);
v___x_4787_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4786_, v_declName_4776_, v___y_4777_, v___y_4778_);
if (lean_obj_tag(v___x_4787_) == 0)
{
lean_object* v_a_4788_; lean_object* v___x_4790_; uint8_t v_isShared_4791_; uint8_t v_isSharedCheck_4817_; 
v_a_4788_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4817_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4817_ == 0)
{
v___x_4790_ = v___x_4787_;
v_isShared_4791_ = v_isSharedCheck_4817_;
goto v_resetjp_4789_;
}
else
{
lean_inc(v_a_4788_);
lean_dec(v___x_4787_);
v___x_4790_ = lean_box(0);
v_isShared_4791_ = v_isSharedCheck_4817_;
goto v_resetjp_4789_;
}
v_resetjp_4789_:
{
lean_object* v___x_4792_; lean_object* v_env_4793_; lean_object* v_nextMacroScope_4794_; lean_object* v_ngen_4795_; lean_object* v_auxDeclNGen_4796_; lean_object* v_traceState_4797_; lean_object* v_messages_4798_; lean_object* v_infoState_4799_; lean_object* v_snapshotTasks_4800_; lean_object* v___x_4802_; uint8_t v_isShared_4803_; uint8_t v_isSharedCheck_4815_; 
v___x_4792_ = lean_st_ref_take(v___y_4778_);
v_env_4793_ = lean_ctor_get(v___x_4792_, 0);
v_nextMacroScope_4794_ = lean_ctor_get(v___x_4792_, 1);
v_ngen_4795_ = lean_ctor_get(v___x_4792_, 2);
v_auxDeclNGen_4796_ = lean_ctor_get(v___x_4792_, 3);
v_traceState_4797_ = lean_ctor_get(v___x_4792_, 4);
v_messages_4798_ = lean_ctor_get(v___x_4792_, 6);
v_infoState_4799_ = lean_ctor_get(v___x_4792_, 7);
v_snapshotTasks_4800_ = lean_ctor_get(v___x_4792_, 8);
v_isSharedCheck_4815_ = !lean_is_exclusive(v___x_4792_);
if (v_isSharedCheck_4815_ == 0)
{
lean_object* v_unused_4816_; 
v_unused_4816_ = lean_ctor_get(v___x_4792_, 5);
lean_dec(v_unused_4816_);
v___x_4802_ = v___x_4792_;
v_isShared_4803_ = v_isSharedCheck_4815_;
goto v_resetjp_4801_;
}
else
{
lean_inc(v_snapshotTasks_4800_);
lean_inc(v_infoState_4799_);
lean_inc(v_messages_4798_);
lean_inc(v_traceState_4797_);
lean_inc(v_auxDeclNGen_4796_);
lean_inc(v_ngen_4795_);
lean_inc(v_nextMacroScope_4794_);
lean_inc(v_env_4793_);
lean_dec(v___x_4792_);
v___x_4802_ = lean_box(0);
v_isShared_4803_ = v_isSharedCheck_4815_;
goto v_resetjp_4801_;
}
v_resetjp_4801_:
{
lean_object* v___f_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v___x_4808_; 
v___f_4804_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4804_, 0, v_a_4788_);
v___x_4805_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4782_, v_env_4793_, v___f_4804_);
v___x_4806_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4803_ == 0)
{
lean_ctor_set(v___x_4802_, 5, v___x_4806_);
lean_ctor_set(v___x_4802_, 0, v___x_4805_);
v___x_4808_ = v___x_4802_;
goto v_reusejp_4807_;
}
else
{
lean_object* v_reuseFailAlloc_4814_; 
v_reuseFailAlloc_4814_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4814_, 0, v___x_4805_);
lean_ctor_set(v_reuseFailAlloc_4814_, 1, v_nextMacroScope_4794_);
lean_ctor_set(v_reuseFailAlloc_4814_, 2, v_ngen_4795_);
lean_ctor_set(v_reuseFailAlloc_4814_, 3, v_auxDeclNGen_4796_);
lean_ctor_set(v_reuseFailAlloc_4814_, 4, v_traceState_4797_);
lean_ctor_set(v_reuseFailAlloc_4814_, 5, v___x_4806_);
lean_ctor_set(v_reuseFailAlloc_4814_, 6, v_messages_4798_);
lean_ctor_set(v_reuseFailAlloc_4814_, 7, v_infoState_4799_);
lean_ctor_set(v_reuseFailAlloc_4814_, 8, v_snapshotTasks_4800_);
v___x_4808_ = v_reuseFailAlloc_4814_;
goto v_reusejp_4807_;
}
v_reusejp_4807_:
{
lean_object* v___x_4809_; lean_object* v___x_4810_; lean_object* v___x_4812_; 
v___x_4809_ = lean_st_ref_set(v___y_4778_, v___x_4808_);
v___x_4810_ = lean_box(0);
if (v_isShared_4791_ == 0)
{
lean_ctor_set(v___x_4790_, 0, v___x_4810_);
v___x_4812_ = v___x_4790_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(0, 1, 0);
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
}
else
{
lean_object* v_a_4818_; lean_object* v___x_4820_; uint8_t v_isShared_4821_; uint8_t v_isSharedCheck_4825_; 
v_a_4818_ = lean_ctor_get(v___x_4787_, 0);
v_isSharedCheck_4825_ = !lean_is_exclusive(v___x_4787_);
if (v_isSharedCheck_4825_ == 0)
{
v___x_4820_ = v___x_4787_;
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
else
{
lean_inc(v_a_4818_);
lean_dec(v___x_4787_);
v___x_4820_ = lean_box(0);
v_isShared_4821_ = v_isSharedCheck_4825_;
goto v_resetjp_4819_;
}
v_resetjp_4819_:
{
lean_object* v___x_4823_; 
if (v_isShared_4821_ == 0)
{
v___x_4823_ = v___x_4820_;
goto v_reusejp_4822_;
}
else
{
lean_object* v_reuseFailAlloc_4824_; 
v_reuseFailAlloc_4824_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4824_, 0, v_a_4818_);
v___x_4823_ = v_reuseFailAlloc_4824_;
goto v_reusejp_4822_;
}
v_reusejp_4822_:
{
return v___x_4823_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4826_, lean_object* v_declName_4827_, lean_object* v___y_4828_, lean_object* v___y_4829_, lean_object* v___y_4830_){
_start:
{
lean_object* v_res_4831_; 
v_res_4831_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4826_, v_declName_4827_, v___y_4828_, v___y_4829_);
lean_dec(v___y_4829_);
lean_dec_ref(v___y_4828_);
lean_dec_ref(v___x_4826_);
return v_res_4831_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4838_; uint64_t v___x_4839_; 
v___x_4838_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4839_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4838_);
return v___x_4839_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4840_; lean_object* v___x_4841_; lean_object* v___x_4842_; 
v___x_4840_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4841_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4842_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4842_, 0, v___x_4841_);
lean_ctor_set_uint64(v___x_4842_, sizeof(void*)*1, v___x_4840_);
return v___x_4842_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4843_; 
v___x_4843_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4843_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4844_; lean_object* v___x_4845_; 
v___x_4844_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4845_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4845_, 0, v___x_4844_);
return v___x_4845_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4846_; lean_object* v___x_4847_; 
v___x_4846_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4847_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4847_, 0, v___x_4846_);
lean_ctor_set(v___x_4847_, 1, v___x_4846_);
lean_ctor_set(v___x_4847_, 2, v___x_4846_);
lean_ctor_set(v___x_4847_, 3, v___x_4846_);
lean_ctor_set(v___x_4847_, 4, v___x_4846_);
lean_ctor_set(v___x_4847_, 5, v___x_4846_);
return v___x_4847_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4848_; lean_object* v___x_4849_; 
v___x_4848_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4849_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4849_, 0, v___x_4848_);
lean_ctor_set(v___x_4849_, 1, v___x_4848_);
lean_ctor_set(v___x_4849_, 2, v___x_4848_);
lean_ctor_set(v___x_4849_, 3, v___x_4848_);
lean_ctor_set(v___x_4849_, 4, v___x_4848_);
return v___x_4849_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4850_, lean_object* v___x_4851_, lean_object* v_declName_4852_, lean_object* v_stx_4853_, uint8_t v_attrKind_4854_, lean_object* v___y_4855_, lean_object* v___y_4856_){
_start:
{
lean_object* v___x_4858_; lean_object* v___x_4859_; lean_object* v___x_4860_; 
v___x_4858_ = lean_unsigned_to_nat(1u);
v___x_4859_ = l_Lean_Syntax_getArg(v_stx_4853_, v___x_4858_);
v___x_4860_ = l_Lean_getAttrParamOptPrio(v___x_4859_, v___y_4855_, v___y_4856_);
if (lean_obj_tag(v___x_4860_) == 0)
{
lean_object* v_a_4861_; uint8_t v___x_4862_; uint8_t v___x_4863_; lean_object* v___x_4864_; lean_object* v___x_4865_; lean_object* v___x_4866_; lean_object* v___x_4867_; lean_object* v___x_4868_; size_t v___x_4869_; lean_object* v___x_4870_; lean_object* v___x_4871_; lean_object* v___x_4872_; lean_object* v___x_4873_; lean_object* v___x_4874_; lean_object* v___x_4875_; lean_object* v___x_4876_; lean_object* v___x_4877_; lean_object* v___x_4878_; lean_object* v___x_4879_; lean_object* v___x_4880_; lean_object* v___x_4881_; 
v_a_4861_ = lean_ctor_get(v___x_4860_, 0);
lean_inc(v_a_4861_);
lean_dec_ref_known(v___x_4860_, 1);
v___x_4862_ = 0;
v___x_4863_ = 1;
v___x_4864_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4865_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4866_ = lean_unsigned_to_nat(32u);
v___x_4867_ = lean_mk_empty_array_with_capacity(v___x_4866_);
v___x_4868_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4869_ = ((size_t)5ULL);
lean_inc_n(v___x_4850_, 6);
v___x_4870_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4870_, 0, v___x_4868_);
lean_ctor_set(v___x_4870_, 1, v___x_4867_);
lean_ctor_set(v___x_4870_, 2, v___x_4850_);
lean_ctor_set(v___x_4870_, 3, v___x_4850_);
lean_ctor_set_usize(v___x_4870_, 4, v___x_4869_);
v___x_4871_ = lean_box(1);
lean_inc_ref(v___x_4870_);
v___x_4872_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4872_, 0, v___x_4865_);
lean_ctor_set(v___x_4872_, 1, v___x_4870_);
lean_ctor_set(v___x_4872_, 2, v___x_4871_);
v___x_4873_ = lean_mk_empty_array_with_capacity(v___x_4850_);
v___x_4874_ = lean_box(0);
lean_inc(v___x_4851_);
v___x_4875_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4875_, 0, v___x_4864_);
lean_ctor_set(v___x_4875_, 1, v___x_4851_);
lean_ctor_set(v___x_4875_, 2, v___x_4872_);
lean_ctor_set(v___x_4875_, 3, v___x_4873_);
lean_ctor_set(v___x_4875_, 4, v___x_4874_);
lean_ctor_set(v___x_4875_, 5, v___x_4850_);
lean_ctor_set(v___x_4875_, 6, v___x_4874_);
lean_ctor_set_uint8(v___x_4875_, sizeof(void*)*7, v___x_4862_);
lean_ctor_set_uint8(v___x_4875_, sizeof(void*)*7 + 1, v___x_4862_);
lean_ctor_set_uint8(v___x_4875_, sizeof(void*)*7 + 2, v___x_4862_);
lean_ctor_set_uint8(v___x_4875_, sizeof(void*)*7 + 3, v___x_4863_);
v___x_4876_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4876_, 0, v___x_4850_);
lean_ctor_set(v___x_4876_, 1, v___x_4850_);
lean_ctor_set(v___x_4876_, 2, v___x_4850_);
lean_ctor_set(v___x_4876_, 3, v___x_4850_);
lean_ctor_set(v___x_4876_, 4, v___x_4865_);
lean_ctor_set(v___x_4876_, 5, v___x_4865_);
lean_ctor_set(v___x_4876_, 6, v___x_4865_);
lean_ctor_set(v___x_4876_, 7, v___x_4865_);
lean_ctor_set(v___x_4876_, 8, v___x_4865_);
lean_ctor_set(v___x_4876_, 9, v___x_4865_);
v___x_4877_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4878_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4879_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4879_, 0, v___x_4876_);
lean_ctor_set(v___x_4879_, 1, v___x_4877_);
lean_ctor_set(v___x_4879_, 2, v___x_4851_);
lean_ctor_set(v___x_4879_, 3, v___x_4870_);
lean_ctor_set(v___x_4879_, 4, v___x_4878_);
v___x_4880_ = lean_st_mk_ref(v___x_4879_);
v___x_4881_ = l_Lean_Meta_addInstance(v_declName_4852_, v_attrKind_4854_, v_a_4861_, v___x_4875_, v___x_4880_, v___y_4855_, v___y_4856_);
lean_dec_ref_known(v___x_4875_, 7);
if (lean_obj_tag(v___x_4881_) == 0)
{
lean_object* v___x_4883_; uint8_t v_isShared_4884_; uint8_t v_isSharedCheck_4890_; 
v_isSharedCheck_4890_ = !lean_is_exclusive(v___x_4881_);
if (v_isSharedCheck_4890_ == 0)
{
lean_object* v_unused_4891_; 
v_unused_4891_ = lean_ctor_get(v___x_4881_, 0);
lean_dec(v_unused_4891_);
v___x_4883_ = v___x_4881_;
v_isShared_4884_ = v_isSharedCheck_4890_;
goto v_resetjp_4882_;
}
else
{
lean_dec(v___x_4881_);
v___x_4883_ = lean_box(0);
v_isShared_4884_ = v_isSharedCheck_4890_;
goto v_resetjp_4882_;
}
v_resetjp_4882_:
{
lean_object* v___x_4885_; lean_object* v___x_4886_; lean_object* v___x_4888_; 
v___x_4885_ = lean_st_ref_get(v___x_4880_);
lean_dec(v___x_4880_);
lean_dec(v___x_4885_);
v___x_4886_ = lean_box(0);
if (v_isShared_4884_ == 0)
{
lean_ctor_set(v___x_4883_, 0, v___x_4886_);
v___x_4888_ = v___x_4883_;
goto v_reusejp_4887_;
}
else
{
lean_object* v_reuseFailAlloc_4889_; 
v_reuseFailAlloc_4889_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4889_, 0, v___x_4886_);
v___x_4888_ = v_reuseFailAlloc_4889_;
goto v_reusejp_4887_;
}
v_reusejp_4887_:
{
return v___x_4888_;
}
}
}
else
{
lean_dec(v___x_4880_);
return v___x_4881_;
}
}
else
{
lean_object* v_a_4892_; lean_object* v___x_4894_; uint8_t v_isShared_4895_; uint8_t v_isSharedCheck_4899_; 
lean_dec(v_declName_4852_);
lean_dec(v___x_4851_);
lean_dec(v___x_4850_);
v_a_4892_ = lean_ctor_get(v___x_4860_, 0);
v_isSharedCheck_4899_ = !lean_is_exclusive(v___x_4860_);
if (v_isSharedCheck_4899_ == 0)
{
v___x_4894_ = v___x_4860_;
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
else
{
lean_inc(v_a_4892_);
lean_dec(v___x_4860_);
v___x_4894_ = lean_box(0);
v_isShared_4895_ = v_isSharedCheck_4899_;
goto v_resetjp_4893_;
}
v_resetjp_4893_:
{
lean_object* v___x_4897_; 
if (v_isShared_4895_ == 0)
{
v___x_4897_ = v___x_4894_;
goto v_reusejp_4896_;
}
else
{
lean_object* v_reuseFailAlloc_4898_; 
v_reuseFailAlloc_4898_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4898_, 0, v_a_4892_);
v___x_4897_ = v_reuseFailAlloc_4898_;
goto v_reusejp_4896_;
}
v_reusejp_4896_:
{
return v___x_4897_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4900_, lean_object* v___x_4901_, lean_object* v_declName_4902_, lean_object* v_stx_4903_, lean_object* v_attrKind_4904_, lean_object* v___y_4905_, lean_object* v___y_4906_, lean_object* v___y_4907_){
_start:
{
uint8_t v_attrKind_boxed_4908_; lean_object* v_res_4909_; 
v_attrKind_boxed_4908_ = lean_unbox(v_attrKind_4904_);
v_res_4909_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4900_, v___x_4901_, v_declName_4902_, v_stx_4903_, v_attrKind_boxed_4908_, v___y_4905_, v___y_4906_);
lean_dec(v___y_4906_);
lean_dec_ref(v___y_4905_);
lean_dec(v_stx_4903_);
return v_res_4909_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4910_; lean_object* v___f_4911_; 
v___x_4910_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4911_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4911_, 0, v___x_4910_);
return v___f_4911_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_4978_; lean_object* v___f_4979_; lean_object* v___x_4980_; lean_object* v___x_4981_; 
v___f_4978_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_4979_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4980_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4981_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4981_, 0, v___x_4980_);
lean_ctor_set(v___x_4981_, 1, v___f_4979_);
lean_ctor_set(v___x_4981_, 2, v___f_4978_);
return v___x_4981_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_4983_; lean_object* v___x_4984_; 
v___x_4983_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4984_ = l_Lean_registerBuiltinAttribute(v___x_4983_);
return v___x_4984_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4985_){
_start:
{
lean_object* v_res_4986_; 
v_res_4986_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_4986_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_4987_, lean_object* v_x_4988_, lean_object* v_x_4989_){
_start:
{
uint8_t v___x_4990_; 
v___x_4990_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4988_, v_x_4989_);
return v___x_4990_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_4991_, lean_object* v_x_4992_, lean_object* v_x_4993_){
_start:
{
uint8_t v_res_4994_; lean_object* v_r_4995_; 
v_res_4994_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_4991_, v_x_4992_, v_x_4993_);
lean_dec(v_x_4993_);
lean_dec_ref(v_x_4992_);
v_r_4995_ = lean_box(v_res_4994_);
return v_r_4995_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_4996_, lean_object* v_msg_4997_, lean_object* v___y_4998_, lean_object* v___y_4999_){
_start:
{
lean_object* v___x_5001_; 
v___x_5001_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4997_, v___y_4998_, v___y_4999_);
return v___x_5001_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_5002_, lean_object* v_msg_5003_, lean_object* v___y_5004_, lean_object* v___y_5005_, lean_object* v___y_5006_){
_start:
{
lean_object* v_res_5007_; 
v_res_5007_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_5002_, v_msg_5003_, v___y_5004_, v___y_5005_);
lean_dec(v___y_5005_);
lean_dec_ref(v___y_5004_);
return v_res_5007_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5008_, lean_object* v_x_5009_, size_t v_x_5010_, lean_object* v_x_5011_){
_start:
{
uint8_t v___x_5012_; 
v___x_5012_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5009_, v_x_5010_, v_x_5011_);
return v___x_5012_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5013_, lean_object* v_x_5014_, lean_object* v_x_5015_, lean_object* v_x_5016_){
_start:
{
size_t v_x_2998__boxed_5017_; uint8_t v_res_5018_; lean_object* v_r_5019_; 
v_x_2998__boxed_5017_ = lean_unbox_usize(v_x_5015_);
lean_dec(v_x_5015_);
v_res_5018_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_5013_, v_x_5014_, v_x_2998__boxed_5017_, v_x_5016_);
lean_dec(v_x_5016_);
lean_dec_ref(v_x_5014_);
v_r_5019_ = lean_box(v_res_5018_);
return v_r_5019_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5020_, lean_object* v_keys_5021_, lean_object* v_vals_5022_, lean_object* v_heq_5023_, lean_object* v_i_5024_, lean_object* v_k_5025_){
_start:
{
uint8_t v___x_5026_; 
v___x_5026_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_5021_, v_i_5024_, v_k_5025_);
return v___x_5026_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5027_, lean_object* v_keys_5028_, lean_object* v_vals_5029_, lean_object* v_heq_5030_, lean_object* v_i_5031_, lean_object* v_k_5032_){
_start:
{
uint8_t v_res_5033_; lean_object* v_r_5034_; 
v_res_5033_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_5027_, v_keys_5028_, v_vals_5029_, v_heq_5030_, v_i_5031_, v_k_5032_);
lean_dec(v_k_5032_);
lean_dec_ref(v_vals_5029_);
lean_dec_ref(v_keys_5028_);
v_r_5034_ = lean_box(v_res_5033_);
return v_r_5034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5037_; lean_object* v___x_5038_; lean_object* v___x_5039_; 
v___x_5037_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5038_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5039_ = l_Lean_addBuiltinDocString(v___x_5037_, v___x_5038_);
return v___x_5039_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5040_){
_start:
{
lean_object* v_res_5041_; 
v_res_5041_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_5042_){
_start:
{
lean_object* v___x_5044_; lean_object* v_env_5045_; lean_object* v___x_5046_; lean_object* v_ext_5047_; lean_object* v_toEnvExtension_5048_; lean_object* v_asyncMode_5049_; lean_object* v___x_5050_; lean_object* v___x_5051_; lean_object* v_discrTree_5052_; lean_object* v___x_5053_; 
v___x_5044_ = lean_st_ref_get(v_a_5042_);
v_env_5045_ = lean_ctor_get(v___x_5044_, 0);
lean_inc_ref(v_env_5045_);
lean_dec(v___x_5044_);
v___x_5046_ = l_Lean_Meta_instanceExtension;
v_ext_5047_ = lean_ctor_get(v___x_5046_, 1);
v_toEnvExtension_5048_ = lean_ctor_get(v_ext_5047_, 0);
v_asyncMode_5049_ = lean_ctor_get(v_toEnvExtension_5048_, 2);
v___x_5050_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5051_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5050_, v___x_5046_, v_env_5045_, v_asyncMode_5049_);
v_discrTree_5052_ = lean_ctor_get(v___x_5051_, 0);
lean_inc_ref(v_discrTree_5052_);
lean_dec(v___x_5051_);
v___x_5053_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5053_, 0, v_discrTree_5052_);
return v___x_5053_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_5054_, lean_object* v_a_5055_){
_start:
{
lean_object* v_res_5056_; 
v_res_5056_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5054_);
lean_dec(v_a_5054_);
return v_res_5056_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_5057_, lean_object* v_a_5058_){
_start:
{
lean_object* v___x_5060_; 
v___x_5060_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5058_);
return v___x_5060_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_5061_, lean_object* v_a_5062_, lean_object* v_a_5063_){
_start:
{
lean_object* v_res_5064_; 
v_res_5064_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_5061_, v_a_5062_);
lean_dec(v_a_5062_);
lean_dec_ref(v_a_5061_);
return v_res_5064_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_5065_){
_start:
{
lean_object* v___x_5067_; lean_object* v_env_5068_; lean_object* v___x_5069_; lean_object* v_ext_5070_; lean_object* v_toEnvExtension_5071_; lean_object* v_asyncMode_5072_; lean_object* v___x_5073_; lean_object* v___x_5074_; lean_object* v_erased_5075_; lean_object* v___x_5076_; 
v___x_5067_ = lean_st_ref_get(v_a_5065_);
v_env_5068_ = lean_ctor_get(v___x_5067_, 0);
lean_inc_ref(v_env_5068_);
lean_dec(v___x_5067_);
v___x_5069_ = l_Lean_Meta_instanceExtension;
v_ext_5070_ = lean_ctor_get(v___x_5069_, 1);
v_toEnvExtension_5071_ = lean_ctor_get(v_ext_5070_, 0);
v_asyncMode_5072_ = lean_ctor_get(v_toEnvExtension_5071_, 2);
v___x_5073_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5074_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5073_, v___x_5069_, v_env_5068_, v_asyncMode_5072_);
v_erased_5075_ = lean_ctor_get(v___x_5074_, 2);
lean_inc_ref(v_erased_5075_);
lean_dec(v___x_5074_);
v___x_5076_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5076_, 0, v_erased_5075_);
return v___x_5076_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_5077_, lean_object* v_a_5078_){
_start:
{
lean_object* v_res_5079_; 
v_res_5079_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5077_);
lean_dec(v_a_5077_);
return v_res_5079_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_5080_, lean_object* v_a_5081_){
_start:
{
lean_object* v___x_5083_; 
v___x_5083_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5081_);
return v___x_5083_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_5084_, lean_object* v_a_5085_, lean_object* v_a_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l_Lean_Meta_getErasedInstances(v_a_5084_, v_a_5085_);
lean_dec(v_a_5085_);
lean_dec_ref(v_a_5084_);
return v_res_5087_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_5088_, lean_object* v_declName_5089_){
_start:
{
lean_object* v___x_5090_; lean_object* v_ext_5091_; lean_object* v_toEnvExtension_5092_; lean_object* v_asyncMode_5093_; lean_object* v___x_5094_; lean_object* v___x_5095_; lean_object* v_instanceNames_5096_; uint8_t v___x_5097_; 
v___x_5090_ = l_Lean_Meta_instanceExtension;
v_ext_5091_ = lean_ctor_get(v___x_5090_, 1);
v_toEnvExtension_5092_ = lean_ctor_get(v_ext_5091_, 0);
v_asyncMode_5093_ = lean_ctor_get(v_toEnvExtension_5092_, 2);
v___x_5094_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5095_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5094_, v___x_5090_, v_env_5088_, v_asyncMode_5093_);
v_instanceNames_5096_ = lean_ctor_get(v___x_5095_, 1);
lean_inc_ref(v_instanceNames_5096_);
lean_dec(v___x_5095_);
v___x_5097_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_5096_, v_declName_5089_);
lean_dec_ref(v_instanceNames_5096_);
return v___x_5097_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_5098_, lean_object* v_declName_5099_){
_start:
{
uint8_t v_res_5100_; lean_object* v_r_5101_; 
v_res_5100_ = l_Lean_Meta_isInstanceCore(v_env_5098_, v_declName_5099_);
lean_dec(v_declName_5099_);
v_r_5101_ = lean_box(v_res_5100_);
return v_r_5101_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_5102_, lean_object* v_a_5103_){
_start:
{
lean_object* v___x_5105_; lean_object* v_env_5106_; uint8_t v___x_5107_; lean_object* v___x_5108_; lean_object* v___x_5109_; 
v___x_5105_ = lean_st_ref_get(v_a_5103_);
v_env_5106_ = lean_ctor_get(v___x_5105_, 0);
lean_inc_ref(v_env_5106_);
lean_dec(v___x_5105_);
v___x_5107_ = l_Lean_Meta_isInstanceCore(v_env_5106_, v_declName_5102_);
v___x_5108_ = lean_box(v___x_5107_);
v___x_5109_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5109_, 0, v___x_5108_);
return v___x_5109_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_5110_, lean_object* v_a_5111_, lean_object* v_a_5112_){
_start:
{
lean_object* v_res_5113_; 
v_res_5113_ = l_Lean_Meta_isInstance___redArg(v_declName_5110_, v_a_5111_);
lean_dec(v_a_5111_);
lean_dec(v_declName_5110_);
return v_res_5113_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_5114_, lean_object* v_a_5115_, lean_object* v_a_5116_){
_start:
{
lean_object* v___x_5118_; 
v___x_5118_ = l_Lean_Meta_isInstance___redArg(v_declName_5114_, v_a_5116_);
return v___x_5118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_5119_, lean_object* v_a_5120_, lean_object* v_a_5121_, lean_object* v_a_5122_){
_start:
{
lean_object* v_res_5123_; 
v_res_5123_ = l_Lean_Meta_isInstance(v_declName_5119_, v_a_5120_, v_a_5121_);
lean_dec(v_a_5121_);
lean_dec_ref(v_a_5120_);
lean_dec(v_declName_5119_);
return v_res_5123_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5124_, lean_object* v_vals_5125_, lean_object* v_i_5126_, lean_object* v_k_5127_){
_start:
{
lean_object* v___x_5128_; uint8_t v___x_5129_; 
v___x_5128_ = lean_array_get_size(v_keys_5124_);
v___x_5129_ = lean_nat_dec_lt(v_i_5126_, v___x_5128_);
if (v___x_5129_ == 0)
{
lean_object* v___x_5130_; 
lean_dec(v_i_5126_);
v___x_5130_ = lean_box(0);
return v___x_5130_;
}
else
{
lean_object* v_k_x27_5131_; uint8_t v___x_5132_; 
v_k_x27_5131_ = lean_array_fget_borrowed(v_keys_5124_, v_i_5126_);
v___x_5132_ = lean_name_eq(v_k_5127_, v_k_x27_5131_);
if (v___x_5132_ == 0)
{
lean_object* v___x_5133_; lean_object* v___x_5134_; 
v___x_5133_ = lean_unsigned_to_nat(1u);
v___x_5134_ = lean_nat_add(v_i_5126_, v___x_5133_);
lean_dec(v_i_5126_);
v_i_5126_ = v___x_5134_;
goto _start;
}
else
{
lean_object* v___x_5136_; lean_object* v___x_5137_; 
v___x_5136_ = lean_array_fget_borrowed(v_vals_5125_, v_i_5126_);
lean_dec(v_i_5126_);
lean_inc(v___x_5136_);
v___x_5137_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5137_, 0, v___x_5136_);
return v___x_5137_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5138_, lean_object* v_vals_5139_, lean_object* v_i_5140_, lean_object* v_k_5141_){
_start:
{
lean_object* v_res_5142_; 
v_res_5142_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5138_, v_vals_5139_, v_i_5140_, v_k_5141_);
lean_dec(v_k_5141_);
lean_dec_ref(v_vals_5139_);
lean_dec_ref(v_keys_5138_);
return v_res_5142_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_5143_, size_t v_x_5144_, lean_object* v_x_5145_){
_start:
{
if (lean_obj_tag(v_x_5143_) == 0)
{
lean_object* v_es_5146_; lean_object* v___x_5147_; size_t v___x_5148_; size_t v___x_5149_; lean_object* v_j_5150_; lean_object* v___x_5151_; 
v_es_5146_ = lean_ctor_get(v_x_5143_, 0);
v___x_5147_ = lean_box(2);
v___x_5148_ = ((size_t)31ULL);
v___x_5149_ = lean_usize_land(v_x_5144_, v___x_5148_);
v_j_5150_ = lean_usize_to_nat(v___x_5149_);
v___x_5151_ = lean_array_get_borrowed(v___x_5147_, v_es_5146_, v_j_5150_);
lean_dec(v_j_5150_);
switch(lean_obj_tag(v___x_5151_))
{
case 0:
{
lean_object* v_key_5152_; lean_object* v_val_5153_; uint8_t v___x_5154_; 
v_key_5152_ = lean_ctor_get(v___x_5151_, 0);
v_val_5153_ = lean_ctor_get(v___x_5151_, 1);
v___x_5154_ = lean_name_eq(v_x_5145_, v_key_5152_);
if (v___x_5154_ == 0)
{
lean_object* v___x_5155_; 
v___x_5155_ = lean_box(0);
return v___x_5155_;
}
else
{
lean_object* v___x_5156_; 
lean_inc(v_val_5153_);
v___x_5156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5156_, 0, v_val_5153_);
return v___x_5156_;
}
}
case 1:
{
lean_object* v_node_5157_; size_t v___x_5158_; size_t v___x_5159_; 
v_node_5157_ = lean_ctor_get(v___x_5151_, 0);
v___x_5158_ = ((size_t)5ULL);
v___x_5159_ = lean_usize_shift_right(v_x_5144_, v___x_5158_);
v_x_5143_ = v_node_5157_;
v_x_5144_ = v___x_5159_;
goto _start;
}
default: 
{
lean_object* v___x_5161_; 
v___x_5161_ = lean_box(0);
return v___x_5161_;
}
}
}
else
{
lean_object* v_ks_5162_; lean_object* v_vs_5163_; lean_object* v___x_5164_; lean_object* v___x_5165_; 
v_ks_5162_ = lean_ctor_get(v_x_5143_, 0);
v_vs_5163_ = lean_ctor_get(v_x_5143_, 1);
v___x_5164_ = lean_unsigned_to_nat(0u);
v___x_5165_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5162_, v_vs_5163_, v___x_5164_, v_x_5145_);
return v___x_5165_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5166_, lean_object* v_x_5167_, lean_object* v_x_5168_){
_start:
{
size_t v_x_479__boxed_5169_; lean_object* v_res_5170_; 
v_x_479__boxed_5169_ = lean_unbox_usize(v_x_5167_);
lean_dec(v_x_5167_);
v_res_5170_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5166_, v_x_479__boxed_5169_, v_x_5168_);
lean_dec(v_x_5168_);
lean_dec_ref(v_x_5166_);
return v_res_5170_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_5171_, lean_object* v_x_5172_){
_start:
{
uint64_t v___y_5174_; 
if (lean_obj_tag(v_x_5172_) == 0)
{
uint64_t v___x_5177_; 
v___x_5177_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0);
v___y_5174_ = v___x_5177_;
goto v___jp_5173_;
}
else
{
uint64_t v_hash_5178_; 
v_hash_5178_ = lean_ctor_get_uint64(v_x_5172_, sizeof(void*)*2);
v___y_5174_ = v_hash_5178_;
goto v___jp_5173_;
}
v___jp_5173_:
{
size_t v___x_5175_; lean_object* v___x_5176_; 
v___x_5175_ = lean_uint64_to_usize(v___y_5174_);
v___x_5176_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5171_, v___x_5175_, v_x_5172_);
return v___x_5176_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_5179_, lean_object* v_x_5180_){
_start:
{
lean_object* v_res_5181_; 
v_res_5181_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5179_, v_x_5180_);
lean_dec(v_x_5180_);
lean_dec_ref(v_x_5179_);
return v_res_5181_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_5182_, lean_object* v_a_5183_){
_start:
{
lean_object* v___x_5185_; lean_object* v_env_5186_; lean_object* v___x_5187_; lean_object* v_ext_5188_; lean_object* v_toEnvExtension_5189_; lean_object* v_asyncMode_5190_; lean_object* v___x_5191_; lean_object* v___x_5192_; lean_object* v_instanceNames_5193_; lean_object* v___x_5194_; 
v___x_5185_ = lean_st_ref_get(v_a_5183_);
v_env_5186_ = lean_ctor_get(v___x_5185_, 0);
lean_inc_ref(v_env_5186_);
lean_dec(v___x_5185_);
v___x_5187_ = l_Lean_Meta_instanceExtension;
v_ext_5188_ = lean_ctor_get(v___x_5187_, 1);
v_toEnvExtension_5189_ = lean_ctor_get(v_ext_5188_, 0);
v_asyncMode_5190_ = lean_ctor_get(v_toEnvExtension_5189_, 2);
v___x_5191_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5192_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5191_, v___x_5187_, v_env_5186_, v_asyncMode_5190_);
v_instanceNames_5193_ = lean_ctor_get(v___x_5192_, 1);
lean_inc_ref(v_instanceNames_5193_);
lean_dec(v___x_5192_);
v___x_5194_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5193_, v_declName_5182_);
lean_dec_ref(v_instanceNames_5193_);
if (lean_obj_tag(v___x_5194_) == 1)
{
lean_object* v_val_5195_; lean_object* v___x_5197_; uint8_t v_isShared_5198_; uint8_t v_isSharedCheck_5204_; 
v_val_5195_ = lean_ctor_get(v___x_5194_, 0);
v_isSharedCheck_5204_ = !lean_is_exclusive(v___x_5194_);
if (v_isSharedCheck_5204_ == 0)
{
v___x_5197_ = v___x_5194_;
v_isShared_5198_ = v_isSharedCheck_5204_;
goto v_resetjp_5196_;
}
else
{
lean_inc(v_val_5195_);
lean_dec(v___x_5194_);
v___x_5197_ = lean_box(0);
v_isShared_5198_ = v_isSharedCheck_5204_;
goto v_resetjp_5196_;
}
v_resetjp_5196_:
{
lean_object* v_priority_5199_; lean_object* v___x_5201_; 
v_priority_5199_ = lean_ctor_get(v_val_5195_, 2);
lean_inc(v_priority_5199_);
lean_dec(v_val_5195_);
if (v_isShared_5198_ == 0)
{
lean_ctor_set(v___x_5197_, 0, v_priority_5199_);
v___x_5201_ = v___x_5197_;
goto v_reusejp_5200_;
}
else
{
lean_object* v_reuseFailAlloc_5203_; 
v_reuseFailAlloc_5203_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5203_, 0, v_priority_5199_);
v___x_5201_ = v_reuseFailAlloc_5203_;
goto v_reusejp_5200_;
}
v_reusejp_5200_:
{
lean_object* v___x_5202_; 
v___x_5202_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5202_, 0, v___x_5201_);
return v___x_5202_;
}
}
}
else
{
lean_object* v___x_5205_; lean_object* v___x_5206_; 
lean_dec(v___x_5194_);
v___x_5205_ = lean_box(0);
v___x_5206_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5206_, 0, v___x_5205_);
return v___x_5206_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_5207_, lean_object* v_a_5208_, lean_object* v_a_5209_){
_start:
{
lean_object* v_res_5210_; 
v_res_5210_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5207_, v_a_5208_);
lean_dec(v_a_5208_);
lean_dec(v_declName_5207_);
return v_res_5210_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_5211_, lean_object* v_a_5212_, lean_object* v_a_5213_){
_start:
{
lean_object* v___x_5215_; 
v___x_5215_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5211_, v_a_5213_);
return v___x_5215_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_5216_, lean_object* v_a_5217_, lean_object* v_a_5218_, lean_object* v_a_5219_){
_start:
{
lean_object* v_res_5220_; 
v_res_5220_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_5216_, v_a_5217_, v_a_5218_);
lean_dec(v_a_5218_);
lean_dec_ref(v_a_5217_);
lean_dec(v_declName_5216_);
return v_res_5220_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_5221_, lean_object* v_x_5222_, lean_object* v_x_5223_){
_start:
{
lean_object* v___x_5224_; 
v___x_5224_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5222_, v_x_5223_);
return v___x_5224_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_5225_, lean_object* v_x_5226_, lean_object* v_x_5227_){
_start:
{
lean_object* v_res_5228_; 
v_res_5228_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_5225_, v_x_5226_, v_x_5227_);
lean_dec(v_x_5227_);
lean_dec_ref(v_x_5226_);
return v_res_5228_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5229_, lean_object* v_x_5230_, size_t v_x_5231_, lean_object* v_x_5232_){
_start:
{
lean_object* v___x_5233_; 
v___x_5233_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5230_, v_x_5231_, v_x_5232_);
return v___x_5233_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5234_, lean_object* v_x_5235_, lean_object* v_x_5236_, lean_object* v_x_5237_){
_start:
{
size_t v_x_593__boxed_5238_; lean_object* v_res_5239_; 
v_x_593__boxed_5238_ = lean_unbox_usize(v_x_5236_);
lean_dec(v_x_5236_);
v_res_5239_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_5234_, v_x_5235_, v_x_593__boxed_5238_, v_x_5237_);
lean_dec(v_x_5237_);
lean_dec_ref(v_x_5235_);
return v_res_5239_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5240_, lean_object* v_keys_5241_, lean_object* v_vals_5242_, lean_object* v_heq_5243_, lean_object* v_i_5244_, lean_object* v_k_5245_){
_start:
{
lean_object* v___x_5246_; 
v___x_5246_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5241_, v_vals_5242_, v_i_5244_, v_k_5245_);
return v___x_5246_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5247_, lean_object* v_keys_5248_, lean_object* v_vals_5249_, lean_object* v_heq_5250_, lean_object* v_i_5251_, lean_object* v_k_5252_){
_start:
{
lean_object* v_res_5253_; 
v_res_5253_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5247_, v_keys_5248_, v_vals_5249_, v_heq_5250_, v_i_5251_, v_k_5252_);
lean_dec(v_k_5252_);
lean_dec_ref(v_vals_5249_);
lean_dec_ref(v_keys_5248_);
return v_res_5253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_5254_, lean_object* v_a_5255_){
_start:
{
lean_object* v___x_5257_; lean_object* v_env_5258_; lean_object* v___x_5259_; lean_object* v_ext_5260_; lean_object* v_toEnvExtension_5261_; lean_object* v_asyncMode_5262_; lean_object* v___x_5263_; lean_object* v___x_5264_; lean_object* v_instanceNames_5265_; lean_object* v___x_5266_; 
v___x_5257_ = lean_st_ref_get(v_a_5255_);
v_env_5258_ = lean_ctor_get(v___x_5257_, 0);
lean_inc_ref(v_env_5258_);
lean_dec(v___x_5257_);
v___x_5259_ = l_Lean_Meta_instanceExtension;
v_ext_5260_ = lean_ctor_get(v___x_5259_, 1);
v_toEnvExtension_5261_ = lean_ctor_get(v_ext_5260_, 0);
v_asyncMode_5262_ = lean_ctor_get(v_toEnvExtension_5261_, 2);
v___x_5263_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5264_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5263_, v___x_5259_, v_env_5258_, v_asyncMode_5262_);
v_instanceNames_5265_ = lean_ctor_get(v___x_5264_, 1);
lean_inc_ref(v_instanceNames_5265_);
lean_dec(v___x_5264_);
v___x_5266_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5265_, v_declName_5254_);
lean_dec_ref(v_instanceNames_5265_);
if (lean_obj_tag(v___x_5266_) == 1)
{
lean_object* v_val_5267_; lean_object* v___x_5269_; uint8_t v_isShared_5270_; uint8_t v_isSharedCheck_5277_; 
v_val_5267_ = lean_ctor_get(v___x_5266_, 0);
v_isSharedCheck_5277_ = !lean_is_exclusive(v___x_5266_);
if (v_isSharedCheck_5277_ == 0)
{
v___x_5269_ = v___x_5266_;
v_isShared_5270_ = v_isSharedCheck_5277_;
goto v_resetjp_5268_;
}
else
{
lean_inc(v_val_5267_);
lean_dec(v___x_5266_);
v___x_5269_ = lean_box(0);
v_isShared_5270_ = v_isSharedCheck_5277_;
goto v_resetjp_5268_;
}
v_resetjp_5268_:
{
uint8_t v_attrKind_5271_; lean_object* v___x_5272_; lean_object* v___x_5274_; 
v_attrKind_5271_ = lean_ctor_get_uint8(v_val_5267_, sizeof(void*)*5);
lean_dec(v_val_5267_);
v___x_5272_ = lean_box(v_attrKind_5271_);
if (v_isShared_5270_ == 0)
{
lean_ctor_set(v___x_5269_, 0, v___x_5272_);
v___x_5274_ = v___x_5269_;
goto v_reusejp_5273_;
}
else
{
lean_object* v_reuseFailAlloc_5276_; 
v_reuseFailAlloc_5276_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5276_, 0, v___x_5272_);
v___x_5274_ = v_reuseFailAlloc_5276_;
goto v_reusejp_5273_;
}
v_reusejp_5273_:
{
lean_object* v___x_5275_; 
v___x_5275_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5275_, 0, v___x_5274_);
return v___x_5275_;
}
}
}
else
{
lean_object* v___x_5278_; lean_object* v___x_5279_; 
lean_dec(v___x_5266_);
v___x_5278_ = lean_box(0);
v___x_5279_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5279_, 0, v___x_5278_);
return v___x_5279_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_5280_, lean_object* v_a_5281_, lean_object* v_a_5282_){
_start:
{
lean_object* v_res_5283_; 
v_res_5283_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5280_, v_a_5281_);
lean_dec(v_a_5281_);
lean_dec(v_declName_5280_);
return v_res_5283_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_5284_, lean_object* v_a_5285_, lean_object* v_a_5286_){
_start:
{
lean_object* v___x_5288_; 
v___x_5288_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5284_, v_a_5286_);
return v___x_5288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_5289_, lean_object* v_a_5290_, lean_object* v_a_5291_, lean_object* v_a_5292_){
_start:
{
lean_object* v_res_5293_; 
v_res_5293_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_5289_, v_a_5290_, v_a_5291_);
lean_dec(v_a_5291_);
lean_dec_ref(v_a_5290_);
lean_dec(v_declName_5289_);
return v_res_5293_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5298_, lean_object* v_v_5299_, lean_object* v_t_5300_){
_start:
{
if (lean_obj_tag(v_t_5300_) == 0)
{
lean_object* v_size_5301_; lean_object* v_k_5302_; lean_object* v_v_5303_; lean_object* v_l_5304_; lean_object* v_r_5305_; lean_object* v___x_5307_; uint8_t v_isShared_5308_; uint8_t v_isSharedCheck_5586_; 
v_size_5301_ = lean_ctor_get(v_t_5300_, 0);
v_k_5302_ = lean_ctor_get(v_t_5300_, 1);
v_v_5303_ = lean_ctor_get(v_t_5300_, 2);
v_l_5304_ = lean_ctor_get(v_t_5300_, 3);
v_r_5305_ = lean_ctor_get(v_t_5300_, 4);
v_isSharedCheck_5586_ = !lean_is_exclusive(v_t_5300_);
if (v_isSharedCheck_5586_ == 0)
{
v___x_5307_ = v_t_5300_;
v_isShared_5308_ = v_isSharedCheck_5586_;
goto v_resetjp_5306_;
}
else
{
lean_inc(v_r_5305_);
lean_inc(v_l_5304_);
lean_inc(v_v_5303_);
lean_inc(v_k_5302_);
lean_inc(v_size_5301_);
lean_dec(v_t_5300_);
v___x_5307_ = lean_box(0);
v_isShared_5308_ = v_isSharedCheck_5586_;
goto v_resetjp_5306_;
}
v_resetjp_5306_:
{
uint8_t v___x_5309_; 
v___x_5309_ = lean_nat_dec_lt(v_k_5302_, v_k_5298_);
if (v___x_5309_ == 0)
{
uint8_t v___x_5310_; 
v___x_5310_ = lean_nat_dec_eq(v_k_5302_, v_k_5298_);
if (v___x_5310_ == 0)
{
lean_object* v_impl_5311_; lean_object* v___x_5312_; 
lean_dec(v_size_5301_);
v_impl_5311_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5298_, v_v_5299_, v_r_5305_);
v___x_5312_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5304_) == 0)
{
lean_object* v_size_5313_; lean_object* v_size_5314_; lean_object* v_k_5315_; lean_object* v_v_5316_; lean_object* v_l_5317_; lean_object* v_r_5318_; lean_object* v___x_5319_; lean_object* v___x_5320_; uint8_t v___x_5321_; 
v_size_5313_ = lean_ctor_get(v_l_5304_, 0);
v_size_5314_ = lean_ctor_get(v_impl_5311_, 0);
lean_inc(v_size_5314_);
v_k_5315_ = lean_ctor_get(v_impl_5311_, 1);
lean_inc(v_k_5315_);
v_v_5316_ = lean_ctor_get(v_impl_5311_, 2);
lean_inc(v_v_5316_);
v_l_5317_ = lean_ctor_get(v_impl_5311_, 3);
lean_inc(v_l_5317_);
v_r_5318_ = lean_ctor_get(v_impl_5311_, 4);
lean_inc(v_r_5318_);
v___x_5319_ = lean_unsigned_to_nat(3u);
v___x_5320_ = lean_nat_mul(v___x_5319_, v_size_5313_);
v___x_5321_ = lean_nat_dec_lt(v___x_5320_, v_size_5314_);
lean_dec(v___x_5320_);
if (v___x_5321_ == 0)
{
lean_object* v___x_5322_; lean_object* v___x_5323_; lean_object* v___x_5325_; 
lean_dec(v_r_5318_);
lean_dec(v_l_5317_);
lean_dec(v_v_5316_);
lean_dec(v_k_5315_);
v___x_5322_ = lean_nat_add(v___x_5312_, v_size_5313_);
v___x_5323_ = lean_nat_add(v___x_5322_, v_size_5314_);
lean_dec(v_size_5314_);
lean_dec(v___x_5322_);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 4, v_impl_5311_);
lean_ctor_set(v___x_5307_, 0, v___x_5323_);
v___x_5325_ = v___x_5307_;
goto v_reusejp_5324_;
}
else
{
lean_object* v_reuseFailAlloc_5326_; 
v_reuseFailAlloc_5326_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5326_, 0, v___x_5323_);
lean_ctor_set(v_reuseFailAlloc_5326_, 1, v_k_5302_);
lean_ctor_set(v_reuseFailAlloc_5326_, 2, v_v_5303_);
lean_ctor_set(v_reuseFailAlloc_5326_, 3, v_l_5304_);
lean_ctor_set(v_reuseFailAlloc_5326_, 4, v_impl_5311_);
v___x_5325_ = v_reuseFailAlloc_5326_;
goto v_reusejp_5324_;
}
v_reusejp_5324_:
{
return v___x_5325_;
}
}
else
{
lean_object* v___x_5328_; uint8_t v_isShared_5329_; uint8_t v_isSharedCheck_5390_; 
v_isSharedCheck_5390_ = !lean_is_exclusive(v_impl_5311_);
if (v_isSharedCheck_5390_ == 0)
{
lean_object* v_unused_5391_; lean_object* v_unused_5392_; lean_object* v_unused_5393_; lean_object* v_unused_5394_; lean_object* v_unused_5395_; 
v_unused_5391_ = lean_ctor_get(v_impl_5311_, 4);
lean_dec(v_unused_5391_);
v_unused_5392_ = lean_ctor_get(v_impl_5311_, 3);
lean_dec(v_unused_5392_);
v_unused_5393_ = lean_ctor_get(v_impl_5311_, 2);
lean_dec(v_unused_5393_);
v_unused_5394_ = lean_ctor_get(v_impl_5311_, 1);
lean_dec(v_unused_5394_);
v_unused_5395_ = lean_ctor_get(v_impl_5311_, 0);
lean_dec(v_unused_5395_);
v___x_5328_ = v_impl_5311_;
v_isShared_5329_ = v_isSharedCheck_5390_;
goto v_resetjp_5327_;
}
else
{
lean_dec(v_impl_5311_);
v___x_5328_ = lean_box(0);
v_isShared_5329_ = v_isSharedCheck_5390_;
goto v_resetjp_5327_;
}
v_resetjp_5327_:
{
lean_object* v_size_5330_; lean_object* v_k_5331_; lean_object* v_v_5332_; lean_object* v_l_5333_; lean_object* v_r_5334_; lean_object* v_size_5335_; lean_object* v___x_5336_; lean_object* v___x_5337_; uint8_t v___x_5338_; 
v_size_5330_ = lean_ctor_get(v_l_5317_, 0);
v_k_5331_ = lean_ctor_get(v_l_5317_, 1);
v_v_5332_ = lean_ctor_get(v_l_5317_, 2);
v_l_5333_ = lean_ctor_get(v_l_5317_, 3);
v_r_5334_ = lean_ctor_get(v_l_5317_, 4);
v_size_5335_ = lean_ctor_get(v_r_5318_, 0);
v___x_5336_ = lean_unsigned_to_nat(2u);
v___x_5337_ = lean_nat_mul(v___x_5336_, v_size_5335_);
v___x_5338_ = lean_nat_dec_lt(v_size_5330_, v___x_5337_);
lean_dec(v___x_5337_);
if (v___x_5338_ == 0)
{
lean_object* v___x_5340_; uint8_t v_isShared_5341_; uint8_t v_isSharedCheck_5366_; 
lean_inc(v_r_5334_);
lean_inc(v_l_5333_);
lean_inc(v_v_5332_);
lean_inc(v_k_5331_);
v_isSharedCheck_5366_ = !lean_is_exclusive(v_l_5317_);
if (v_isSharedCheck_5366_ == 0)
{
lean_object* v_unused_5367_; lean_object* v_unused_5368_; lean_object* v_unused_5369_; lean_object* v_unused_5370_; lean_object* v_unused_5371_; 
v_unused_5367_ = lean_ctor_get(v_l_5317_, 4);
lean_dec(v_unused_5367_);
v_unused_5368_ = lean_ctor_get(v_l_5317_, 3);
lean_dec(v_unused_5368_);
v_unused_5369_ = lean_ctor_get(v_l_5317_, 2);
lean_dec(v_unused_5369_);
v_unused_5370_ = lean_ctor_get(v_l_5317_, 1);
lean_dec(v_unused_5370_);
v_unused_5371_ = lean_ctor_get(v_l_5317_, 0);
lean_dec(v_unused_5371_);
v___x_5340_ = v_l_5317_;
v_isShared_5341_ = v_isSharedCheck_5366_;
goto v_resetjp_5339_;
}
else
{
lean_dec(v_l_5317_);
v___x_5340_ = lean_box(0);
v_isShared_5341_ = v_isSharedCheck_5366_;
goto v_resetjp_5339_;
}
v_resetjp_5339_:
{
lean_object* v___x_5342_; lean_object* v___x_5343_; lean_object* v___y_5345_; lean_object* v___y_5346_; lean_object* v___y_5347_; lean_object* v___y_5356_; 
v___x_5342_ = lean_nat_add(v___x_5312_, v_size_5313_);
v___x_5343_ = lean_nat_add(v___x_5342_, v_size_5314_);
lean_dec(v_size_5314_);
if (lean_obj_tag(v_l_5333_) == 0)
{
lean_object* v_size_5364_; 
v_size_5364_ = lean_ctor_get(v_l_5333_, 0);
lean_inc(v_size_5364_);
v___y_5356_ = v_size_5364_;
goto v___jp_5355_;
}
else
{
lean_object* v___x_5365_; 
v___x_5365_ = lean_unsigned_to_nat(0u);
v___y_5356_ = v___x_5365_;
goto v___jp_5355_;
}
v___jp_5344_:
{
lean_object* v___x_5348_; lean_object* v___x_5350_; 
v___x_5348_ = lean_nat_add(v___y_5346_, v___y_5347_);
lean_dec(v___y_5347_);
lean_dec(v___y_5346_);
if (v_isShared_5341_ == 0)
{
lean_ctor_set(v___x_5340_, 4, v_r_5318_);
lean_ctor_set(v___x_5340_, 3, v_r_5334_);
lean_ctor_set(v___x_5340_, 2, v_v_5316_);
lean_ctor_set(v___x_5340_, 1, v_k_5315_);
lean_ctor_set(v___x_5340_, 0, v___x_5348_);
v___x_5350_ = v___x_5340_;
goto v_reusejp_5349_;
}
else
{
lean_object* v_reuseFailAlloc_5354_; 
v_reuseFailAlloc_5354_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5354_, 0, v___x_5348_);
lean_ctor_set(v_reuseFailAlloc_5354_, 1, v_k_5315_);
lean_ctor_set(v_reuseFailAlloc_5354_, 2, v_v_5316_);
lean_ctor_set(v_reuseFailAlloc_5354_, 3, v_r_5334_);
lean_ctor_set(v_reuseFailAlloc_5354_, 4, v_r_5318_);
v___x_5350_ = v_reuseFailAlloc_5354_;
goto v_reusejp_5349_;
}
v_reusejp_5349_:
{
lean_object* v___x_5352_; 
if (v_isShared_5329_ == 0)
{
lean_ctor_set(v___x_5328_, 4, v___x_5350_);
lean_ctor_set(v___x_5328_, 3, v___y_5345_);
lean_ctor_set(v___x_5328_, 2, v_v_5332_);
lean_ctor_set(v___x_5328_, 1, v_k_5331_);
lean_ctor_set(v___x_5328_, 0, v___x_5343_);
v___x_5352_ = v___x_5328_;
goto v_reusejp_5351_;
}
else
{
lean_object* v_reuseFailAlloc_5353_; 
v_reuseFailAlloc_5353_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5353_, 0, v___x_5343_);
lean_ctor_set(v_reuseFailAlloc_5353_, 1, v_k_5331_);
lean_ctor_set(v_reuseFailAlloc_5353_, 2, v_v_5332_);
lean_ctor_set(v_reuseFailAlloc_5353_, 3, v___y_5345_);
lean_ctor_set(v_reuseFailAlloc_5353_, 4, v___x_5350_);
v___x_5352_ = v_reuseFailAlloc_5353_;
goto v_reusejp_5351_;
}
v_reusejp_5351_:
{
return v___x_5352_;
}
}
}
v___jp_5355_:
{
lean_object* v___x_5357_; lean_object* v___x_5359_; 
v___x_5357_ = lean_nat_add(v___x_5342_, v___y_5356_);
lean_dec(v___y_5356_);
lean_dec(v___x_5342_);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 4, v_l_5333_);
lean_ctor_set(v___x_5307_, 0, v___x_5357_);
v___x_5359_ = v___x_5307_;
goto v_reusejp_5358_;
}
else
{
lean_object* v_reuseFailAlloc_5363_; 
v_reuseFailAlloc_5363_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5363_, 0, v___x_5357_);
lean_ctor_set(v_reuseFailAlloc_5363_, 1, v_k_5302_);
lean_ctor_set(v_reuseFailAlloc_5363_, 2, v_v_5303_);
lean_ctor_set(v_reuseFailAlloc_5363_, 3, v_l_5304_);
lean_ctor_set(v_reuseFailAlloc_5363_, 4, v_l_5333_);
v___x_5359_ = v_reuseFailAlloc_5363_;
goto v_reusejp_5358_;
}
v_reusejp_5358_:
{
lean_object* v___x_5360_; 
v___x_5360_ = lean_nat_add(v___x_5312_, v_size_5335_);
if (lean_obj_tag(v_r_5334_) == 0)
{
lean_object* v_size_5361_; 
v_size_5361_ = lean_ctor_get(v_r_5334_, 0);
lean_inc(v_size_5361_);
v___y_5345_ = v___x_5359_;
v___y_5346_ = v___x_5360_;
v___y_5347_ = v_size_5361_;
goto v___jp_5344_;
}
else
{
lean_object* v___x_5362_; 
v___x_5362_ = lean_unsigned_to_nat(0u);
v___y_5345_ = v___x_5359_;
v___y_5346_ = v___x_5360_;
v___y_5347_ = v___x_5362_;
goto v___jp_5344_;
}
}
}
}
}
else
{
lean_object* v___x_5372_; lean_object* v___x_5373_; lean_object* v___x_5374_; lean_object* v___x_5376_; 
lean_del_object(v___x_5307_);
v___x_5372_ = lean_nat_add(v___x_5312_, v_size_5313_);
v___x_5373_ = lean_nat_add(v___x_5372_, v_size_5314_);
lean_dec(v_size_5314_);
v___x_5374_ = lean_nat_add(v___x_5372_, v_size_5330_);
lean_dec(v___x_5372_);
lean_inc_ref(v_l_5304_);
if (v_isShared_5329_ == 0)
{
lean_ctor_set(v___x_5328_, 4, v_l_5317_);
lean_ctor_set(v___x_5328_, 3, v_l_5304_);
lean_ctor_set(v___x_5328_, 2, v_v_5303_);
lean_ctor_set(v___x_5328_, 1, v_k_5302_);
lean_ctor_set(v___x_5328_, 0, v___x_5374_);
v___x_5376_ = v___x_5328_;
goto v_reusejp_5375_;
}
else
{
lean_object* v_reuseFailAlloc_5389_; 
v_reuseFailAlloc_5389_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5389_, 0, v___x_5374_);
lean_ctor_set(v_reuseFailAlloc_5389_, 1, v_k_5302_);
lean_ctor_set(v_reuseFailAlloc_5389_, 2, v_v_5303_);
lean_ctor_set(v_reuseFailAlloc_5389_, 3, v_l_5304_);
lean_ctor_set(v_reuseFailAlloc_5389_, 4, v_l_5317_);
v___x_5376_ = v_reuseFailAlloc_5389_;
goto v_reusejp_5375_;
}
v_reusejp_5375_:
{
lean_object* v___x_5378_; uint8_t v_isShared_5379_; uint8_t v_isSharedCheck_5383_; 
v_isSharedCheck_5383_ = !lean_is_exclusive(v_l_5304_);
if (v_isSharedCheck_5383_ == 0)
{
lean_object* v_unused_5384_; lean_object* v_unused_5385_; lean_object* v_unused_5386_; lean_object* v_unused_5387_; lean_object* v_unused_5388_; 
v_unused_5384_ = lean_ctor_get(v_l_5304_, 4);
lean_dec(v_unused_5384_);
v_unused_5385_ = lean_ctor_get(v_l_5304_, 3);
lean_dec(v_unused_5385_);
v_unused_5386_ = lean_ctor_get(v_l_5304_, 2);
lean_dec(v_unused_5386_);
v_unused_5387_ = lean_ctor_get(v_l_5304_, 1);
lean_dec(v_unused_5387_);
v_unused_5388_ = lean_ctor_get(v_l_5304_, 0);
lean_dec(v_unused_5388_);
v___x_5378_ = v_l_5304_;
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
else
{
lean_dec(v_l_5304_);
v___x_5378_ = lean_box(0);
v_isShared_5379_ = v_isSharedCheck_5383_;
goto v_resetjp_5377_;
}
v_resetjp_5377_:
{
lean_object* v___x_5381_; 
if (v_isShared_5379_ == 0)
{
lean_ctor_set(v___x_5378_, 4, v_r_5318_);
lean_ctor_set(v___x_5378_, 3, v___x_5376_);
lean_ctor_set(v___x_5378_, 2, v_v_5316_);
lean_ctor_set(v___x_5378_, 1, v_k_5315_);
lean_ctor_set(v___x_5378_, 0, v___x_5373_);
v___x_5381_ = v___x_5378_;
goto v_reusejp_5380_;
}
else
{
lean_object* v_reuseFailAlloc_5382_; 
v_reuseFailAlloc_5382_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5382_, 0, v___x_5373_);
lean_ctor_set(v_reuseFailAlloc_5382_, 1, v_k_5315_);
lean_ctor_set(v_reuseFailAlloc_5382_, 2, v_v_5316_);
lean_ctor_set(v_reuseFailAlloc_5382_, 3, v___x_5376_);
lean_ctor_set(v_reuseFailAlloc_5382_, 4, v_r_5318_);
v___x_5381_ = v_reuseFailAlloc_5382_;
goto v_reusejp_5380_;
}
v_reusejp_5380_:
{
return v___x_5381_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5396_; 
v_l_5396_ = lean_ctor_get(v_impl_5311_, 3);
lean_inc(v_l_5396_);
if (lean_obj_tag(v_l_5396_) == 0)
{
lean_object* v_r_5397_; lean_object* v_k_5398_; lean_object* v_v_5399_; lean_object* v___x_5401_; uint8_t v_isShared_5402_; uint8_t v_isSharedCheck_5422_; 
v_r_5397_ = lean_ctor_get(v_impl_5311_, 4);
v_k_5398_ = lean_ctor_get(v_impl_5311_, 1);
v_v_5399_ = lean_ctor_get(v_impl_5311_, 2);
v_isSharedCheck_5422_ = !lean_is_exclusive(v_impl_5311_);
if (v_isSharedCheck_5422_ == 0)
{
lean_object* v_unused_5423_; lean_object* v_unused_5424_; 
v_unused_5423_ = lean_ctor_get(v_impl_5311_, 3);
lean_dec(v_unused_5423_);
v_unused_5424_ = lean_ctor_get(v_impl_5311_, 0);
lean_dec(v_unused_5424_);
v___x_5401_ = v_impl_5311_;
v_isShared_5402_ = v_isSharedCheck_5422_;
goto v_resetjp_5400_;
}
else
{
lean_inc(v_r_5397_);
lean_inc(v_v_5399_);
lean_inc(v_k_5398_);
lean_dec(v_impl_5311_);
v___x_5401_ = lean_box(0);
v_isShared_5402_ = v_isSharedCheck_5422_;
goto v_resetjp_5400_;
}
v_resetjp_5400_:
{
lean_object* v_k_5403_; lean_object* v_v_5404_; lean_object* v___x_5406_; uint8_t v_isShared_5407_; uint8_t v_isSharedCheck_5418_; 
v_k_5403_ = lean_ctor_get(v_l_5396_, 1);
v_v_5404_ = lean_ctor_get(v_l_5396_, 2);
v_isSharedCheck_5418_ = !lean_is_exclusive(v_l_5396_);
if (v_isSharedCheck_5418_ == 0)
{
lean_object* v_unused_5419_; lean_object* v_unused_5420_; lean_object* v_unused_5421_; 
v_unused_5419_ = lean_ctor_get(v_l_5396_, 4);
lean_dec(v_unused_5419_);
v_unused_5420_ = lean_ctor_get(v_l_5396_, 3);
lean_dec(v_unused_5420_);
v_unused_5421_ = lean_ctor_get(v_l_5396_, 0);
lean_dec(v_unused_5421_);
v___x_5406_ = v_l_5396_;
v_isShared_5407_ = v_isSharedCheck_5418_;
goto v_resetjp_5405_;
}
else
{
lean_inc(v_v_5404_);
lean_inc(v_k_5403_);
lean_dec(v_l_5396_);
v___x_5406_ = lean_box(0);
v_isShared_5407_ = v_isSharedCheck_5418_;
goto v_resetjp_5405_;
}
v_resetjp_5405_:
{
lean_object* v___x_5408_; lean_object* v___x_5410_; 
v___x_5408_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5397_, 2);
if (v_isShared_5407_ == 0)
{
lean_ctor_set(v___x_5406_, 4, v_r_5397_);
lean_ctor_set(v___x_5406_, 3, v_r_5397_);
lean_ctor_set(v___x_5406_, 2, v_v_5303_);
lean_ctor_set(v___x_5406_, 1, v_k_5302_);
lean_ctor_set(v___x_5406_, 0, v___x_5312_);
v___x_5410_ = v___x_5406_;
goto v_reusejp_5409_;
}
else
{
lean_object* v_reuseFailAlloc_5417_; 
v_reuseFailAlloc_5417_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5417_, 0, v___x_5312_);
lean_ctor_set(v_reuseFailAlloc_5417_, 1, v_k_5302_);
lean_ctor_set(v_reuseFailAlloc_5417_, 2, v_v_5303_);
lean_ctor_set(v_reuseFailAlloc_5417_, 3, v_r_5397_);
lean_ctor_set(v_reuseFailAlloc_5417_, 4, v_r_5397_);
v___x_5410_ = v_reuseFailAlloc_5417_;
goto v_reusejp_5409_;
}
v_reusejp_5409_:
{
lean_object* v___x_5412_; 
lean_inc(v_r_5397_);
if (v_isShared_5402_ == 0)
{
lean_ctor_set(v___x_5401_, 3, v_r_5397_);
lean_ctor_set(v___x_5401_, 0, v___x_5312_);
v___x_5412_ = v___x_5401_;
goto v_reusejp_5411_;
}
else
{
lean_object* v_reuseFailAlloc_5416_; 
v_reuseFailAlloc_5416_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5416_, 0, v___x_5312_);
lean_ctor_set(v_reuseFailAlloc_5416_, 1, v_k_5398_);
lean_ctor_set(v_reuseFailAlloc_5416_, 2, v_v_5399_);
lean_ctor_set(v_reuseFailAlloc_5416_, 3, v_r_5397_);
lean_ctor_set(v_reuseFailAlloc_5416_, 4, v_r_5397_);
v___x_5412_ = v_reuseFailAlloc_5416_;
goto v_reusejp_5411_;
}
v_reusejp_5411_:
{
lean_object* v___x_5414_; 
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 4, v___x_5412_);
lean_ctor_set(v___x_5307_, 3, v___x_5410_);
lean_ctor_set(v___x_5307_, 2, v_v_5404_);
lean_ctor_set(v___x_5307_, 1, v_k_5403_);
lean_ctor_set(v___x_5307_, 0, v___x_5408_);
v___x_5414_ = v___x_5307_;
goto v_reusejp_5413_;
}
else
{
lean_object* v_reuseFailAlloc_5415_; 
v_reuseFailAlloc_5415_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5415_, 0, v___x_5408_);
lean_ctor_set(v_reuseFailAlloc_5415_, 1, v_k_5403_);
lean_ctor_set(v_reuseFailAlloc_5415_, 2, v_v_5404_);
lean_ctor_set(v_reuseFailAlloc_5415_, 3, v___x_5410_);
lean_ctor_set(v_reuseFailAlloc_5415_, 4, v___x_5412_);
v___x_5414_ = v_reuseFailAlloc_5415_;
goto v_reusejp_5413_;
}
v_reusejp_5413_:
{
return v___x_5414_;
}
}
}
}
}
}
else
{
lean_object* v_r_5425_; 
v_r_5425_ = lean_ctor_get(v_impl_5311_, 4);
lean_inc(v_r_5425_);
if (lean_obj_tag(v_r_5425_) == 0)
{
lean_object* v_k_5426_; lean_object* v_v_5427_; lean_object* v___x_5429_; uint8_t v_isShared_5430_; uint8_t v_isSharedCheck_5438_; 
v_k_5426_ = lean_ctor_get(v_impl_5311_, 1);
v_v_5427_ = lean_ctor_get(v_impl_5311_, 2);
v_isSharedCheck_5438_ = !lean_is_exclusive(v_impl_5311_);
if (v_isSharedCheck_5438_ == 0)
{
lean_object* v_unused_5439_; lean_object* v_unused_5440_; lean_object* v_unused_5441_; 
v_unused_5439_ = lean_ctor_get(v_impl_5311_, 4);
lean_dec(v_unused_5439_);
v_unused_5440_ = lean_ctor_get(v_impl_5311_, 3);
lean_dec(v_unused_5440_);
v_unused_5441_ = lean_ctor_get(v_impl_5311_, 0);
lean_dec(v_unused_5441_);
v___x_5429_ = v_impl_5311_;
v_isShared_5430_ = v_isSharedCheck_5438_;
goto v_resetjp_5428_;
}
else
{
lean_inc(v_v_5427_);
lean_inc(v_k_5426_);
lean_dec(v_impl_5311_);
v___x_5429_ = lean_box(0);
v_isShared_5430_ = v_isSharedCheck_5438_;
goto v_resetjp_5428_;
}
v_resetjp_5428_:
{
lean_object* v___x_5431_; lean_object* v___x_5433_; 
v___x_5431_ = lean_unsigned_to_nat(3u);
if (v_isShared_5430_ == 0)
{
lean_ctor_set(v___x_5429_, 4, v_l_5396_);
lean_ctor_set(v___x_5429_, 2, v_v_5303_);
lean_ctor_set(v___x_5429_, 1, v_k_5302_);
lean_ctor_set(v___x_5429_, 0, v___x_5312_);
v___x_5433_ = v___x_5429_;
goto v_reusejp_5432_;
}
else
{
lean_object* v_reuseFailAlloc_5437_; 
v_reuseFailAlloc_5437_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5437_, 0, v___x_5312_);
lean_ctor_set(v_reuseFailAlloc_5437_, 1, v_k_5302_);
lean_ctor_set(v_reuseFailAlloc_5437_, 2, v_v_5303_);
lean_ctor_set(v_reuseFailAlloc_5437_, 3, v_l_5396_);
lean_ctor_set(v_reuseFailAlloc_5437_, 4, v_l_5396_);
v___x_5433_ = v_reuseFailAlloc_5437_;
goto v_reusejp_5432_;
}
v_reusejp_5432_:
{
lean_object* v___x_5435_; 
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 4, v_r_5425_);
lean_ctor_set(v___x_5307_, 3, v___x_5433_);
lean_ctor_set(v___x_5307_, 2, v_v_5427_);
lean_ctor_set(v___x_5307_, 1, v_k_5426_);
lean_ctor_set(v___x_5307_, 0, v___x_5431_);
v___x_5435_ = v___x_5307_;
goto v_reusejp_5434_;
}
else
{
lean_object* v_reuseFailAlloc_5436_; 
v_reuseFailAlloc_5436_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5436_, 0, v___x_5431_);
lean_ctor_set(v_reuseFailAlloc_5436_, 1, v_k_5426_);
lean_ctor_set(v_reuseFailAlloc_5436_, 2, v_v_5427_);
lean_ctor_set(v_reuseFailAlloc_5436_, 3, v___x_5433_);
lean_ctor_set(v_reuseFailAlloc_5436_, 4, v_r_5425_);
v___x_5435_ = v_reuseFailAlloc_5436_;
goto v_reusejp_5434_;
}
v_reusejp_5434_:
{
return v___x_5435_;
}
}
}
}
else
{
lean_object* v___x_5442_; lean_object* v___x_5444_; 
v___x_5442_ = lean_unsigned_to_nat(2u);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 4, v_impl_5311_);
lean_ctor_set(v___x_5307_, 3, v_r_5425_);
lean_ctor_set(v___x_5307_, 0, v___x_5442_);
v___x_5444_ = v___x_5307_;
goto v_reusejp_5443_;
}
else
{
lean_object* v_reuseFailAlloc_5445_; 
v_reuseFailAlloc_5445_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5445_, 0, v___x_5442_);
lean_ctor_set(v_reuseFailAlloc_5445_, 1, v_k_5302_);
lean_ctor_set(v_reuseFailAlloc_5445_, 2, v_v_5303_);
lean_ctor_set(v_reuseFailAlloc_5445_, 3, v_r_5425_);
lean_ctor_set(v_reuseFailAlloc_5445_, 4, v_impl_5311_);
v___x_5444_ = v_reuseFailAlloc_5445_;
goto v_reusejp_5443_;
}
v_reusejp_5443_:
{
return v___x_5444_;
}
}
}
}
}
else
{
lean_object* v___x_5447_; 
lean_dec(v_v_5303_);
lean_dec(v_k_5302_);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 2, v_v_5299_);
lean_ctor_set(v___x_5307_, 1, v_k_5298_);
v___x_5447_ = v___x_5307_;
goto v_reusejp_5446_;
}
else
{
lean_object* v_reuseFailAlloc_5448_; 
v_reuseFailAlloc_5448_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5448_, 0, v_size_5301_);
lean_ctor_set(v_reuseFailAlloc_5448_, 1, v_k_5298_);
lean_ctor_set(v_reuseFailAlloc_5448_, 2, v_v_5299_);
lean_ctor_set(v_reuseFailAlloc_5448_, 3, v_l_5304_);
lean_ctor_set(v_reuseFailAlloc_5448_, 4, v_r_5305_);
v___x_5447_ = v_reuseFailAlloc_5448_;
goto v_reusejp_5446_;
}
v_reusejp_5446_:
{
return v___x_5447_;
}
}
}
else
{
lean_object* v_impl_5449_; lean_object* v___x_5450_; 
lean_dec(v_size_5301_);
v_impl_5449_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5298_, v_v_5299_, v_l_5304_);
v___x_5450_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5305_) == 0)
{
lean_object* v_size_5451_; lean_object* v_size_5452_; lean_object* v_k_5453_; lean_object* v_v_5454_; lean_object* v_l_5455_; lean_object* v_r_5456_; lean_object* v___x_5457_; lean_object* v___x_5458_; uint8_t v___x_5459_; 
v_size_5451_ = lean_ctor_get(v_r_5305_, 0);
v_size_5452_ = lean_ctor_get(v_impl_5449_, 0);
lean_inc(v_size_5452_);
v_k_5453_ = lean_ctor_get(v_impl_5449_, 1);
lean_inc(v_k_5453_);
v_v_5454_ = lean_ctor_get(v_impl_5449_, 2);
lean_inc(v_v_5454_);
v_l_5455_ = lean_ctor_get(v_impl_5449_, 3);
lean_inc(v_l_5455_);
v_r_5456_ = lean_ctor_get(v_impl_5449_, 4);
lean_inc(v_r_5456_);
v___x_5457_ = lean_unsigned_to_nat(3u);
v___x_5458_ = lean_nat_mul(v___x_5457_, v_size_5451_);
v___x_5459_ = lean_nat_dec_lt(v___x_5458_, v_size_5452_);
lean_dec(v___x_5458_);
if (v___x_5459_ == 0)
{
lean_object* v___x_5460_; lean_object* v___x_5461_; lean_object* v___x_5463_; 
lean_dec(v_r_5456_);
lean_dec(v_l_5455_);
lean_dec(v_v_5454_);
lean_dec(v_k_5453_);
v___x_5460_ = lean_nat_add(v___x_5450_, v_size_5452_);
lean_dec(v_size_5452_);
v___x_5461_ = lean_nat_add(v___x_5460_, v_size_5451_);
lean_dec(v___x_5460_);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 3, v_impl_5449_);
lean_ctor_set(v___x_5307_, 0, v___x_5461_);
v___x_5463_ = v___x_5307_;
goto v_reusejp_5462_;
}
else
{
lean_object* v_reuseFailAlloc_5464_; 
v_reuseFailAlloc_5464_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5464_, 0, v___x_5461_);
lean_ctor_set(v_reuseFailAlloc_5464_, 1, v_k_5302_);
lean_ctor_set(v_reuseFailAlloc_5464_, 2, v_v_5303_);
lean_ctor_set(v_reuseFailAlloc_5464_, 3, v_impl_5449_);
lean_ctor_set(v_reuseFailAlloc_5464_, 4, v_r_5305_);
v___x_5463_ = v_reuseFailAlloc_5464_;
goto v_reusejp_5462_;
}
v_reusejp_5462_:
{
return v___x_5463_;
}
}
else
{
lean_object* v___x_5466_; uint8_t v_isShared_5467_; uint8_t v_isSharedCheck_5530_; 
v_isSharedCheck_5530_ = !lean_is_exclusive(v_impl_5449_);
if (v_isSharedCheck_5530_ == 0)
{
lean_object* v_unused_5531_; lean_object* v_unused_5532_; lean_object* v_unused_5533_; lean_object* v_unused_5534_; lean_object* v_unused_5535_; 
v_unused_5531_ = lean_ctor_get(v_impl_5449_, 4);
lean_dec(v_unused_5531_);
v_unused_5532_ = lean_ctor_get(v_impl_5449_, 3);
lean_dec(v_unused_5532_);
v_unused_5533_ = lean_ctor_get(v_impl_5449_, 2);
lean_dec(v_unused_5533_);
v_unused_5534_ = lean_ctor_get(v_impl_5449_, 1);
lean_dec(v_unused_5534_);
v_unused_5535_ = lean_ctor_get(v_impl_5449_, 0);
lean_dec(v_unused_5535_);
v___x_5466_ = v_impl_5449_;
v_isShared_5467_ = v_isSharedCheck_5530_;
goto v_resetjp_5465_;
}
else
{
lean_dec(v_impl_5449_);
v___x_5466_ = lean_box(0);
v_isShared_5467_ = v_isSharedCheck_5530_;
goto v_resetjp_5465_;
}
v_resetjp_5465_:
{
lean_object* v_size_5468_; lean_object* v_size_5469_; lean_object* v_k_5470_; lean_object* v_v_5471_; lean_object* v_l_5472_; lean_object* v_r_5473_; lean_object* v___x_5474_; lean_object* v___x_5475_; uint8_t v___x_5476_; 
v_size_5468_ = lean_ctor_get(v_l_5455_, 0);
v_size_5469_ = lean_ctor_get(v_r_5456_, 0);
v_k_5470_ = lean_ctor_get(v_r_5456_, 1);
v_v_5471_ = lean_ctor_get(v_r_5456_, 2);
v_l_5472_ = lean_ctor_get(v_r_5456_, 3);
v_r_5473_ = lean_ctor_get(v_r_5456_, 4);
v___x_5474_ = lean_unsigned_to_nat(2u);
v___x_5475_ = lean_nat_mul(v___x_5474_, v_size_5468_);
v___x_5476_ = lean_nat_dec_lt(v_size_5469_, v___x_5475_);
lean_dec(v___x_5475_);
if (v___x_5476_ == 0)
{
lean_object* v___x_5478_; uint8_t v_isShared_5479_; uint8_t v_isSharedCheck_5505_; 
lean_inc(v_r_5473_);
lean_inc(v_l_5472_);
lean_inc(v_v_5471_);
lean_inc(v_k_5470_);
v_isSharedCheck_5505_ = !lean_is_exclusive(v_r_5456_);
if (v_isSharedCheck_5505_ == 0)
{
lean_object* v_unused_5506_; lean_object* v_unused_5507_; lean_object* v_unused_5508_; lean_object* v_unused_5509_; lean_object* v_unused_5510_; 
v_unused_5506_ = lean_ctor_get(v_r_5456_, 4);
lean_dec(v_unused_5506_);
v_unused_5507_ = lean_ctor_get(v_r_5456_, 3);
lean_dec(v_unused_5507_);
v_unused_5508_ = lean_ctor_get(v_r_5456_, 2);
lean_dec(v_unused_5508_);
v_unused_5509_ = lean_ctor_get(v_r_5456_, 1);
lean_dec(v_unused_5509_);
v_unused_5510_ = lean_ctor_get(v_r_5456_, 0);
lean_dec(v_unused_5510_);
v___x_5478_ = v_r_5456_;
v_isShared_5479_ = v_isSharedCheck_5505_;
goto v_resetjp_5477_;
}
else
{
lean_dec(v_r_5456_);
v___x_5478_ = lean_box(0);
v_isShared_5479_ = v_isSharedCheck_5505_;
goto v_resetjp_5477_;
}
v_resetjp_5477_:
{
lean_object* v___x_5480_; lean_object* v___x_5481_; lean_object* v___y_5483_; lean_object* v___y_5484_; lean_object* v___y_5485_; lean_object* v___x_5493_; lean_object* v___y_5495_; 
v___x_5480_ = lean_nat_add(v___x_5450_, v_size_5452_);
lean_dec(v_size_5452_);
v___x_5481_ = lean_nat_add(v___x_5480_, v_size_5451_);
lean_dec(v___x_5480_);
v___x_5493_ = lean_nat_add(v___x_5450_, v_size_5468_);
if (lean_obj_tag(v_l_5472_) == 0)
{
lean_object* v_size_5503_; 
v_size_5503_ = lean_ctor_get(v_l_5472_, 0);
lean_inc(v_size_5503_);
v___y_5495_ = v_size_5503_;
goto v___jp_5494_;
}
else
{
lean_object* v___x_5504_; 
v___x_5504_ = lean_unsigned_to_nat(0u);
v___y_5495_ = v___x_5504_;
goto v___jp_5494_;
}
v___jp_5482_:
{
lean_object* v___x_5486_; lean_object* v___x_5488_; 
v___x_5486_ = lean_nat_add(v___y_5483_, v___y_5485_);
lean_dec(v___y_5485_);
lean_dec(v___y_5483_);
if (v_isShared_5479_ == 0)
{
lean_ctor_set(v___x_5478_, 4, v_r_5305_);
lean_ctor_set(v___x_5478_, 3, v_r_5473_);
lean_ctor_set(v___x_5478_, 2, v_v_5303_);
lean_ctor_set(v___x_5478_, 1, v_k_5302_);
lean_ctor_set(v___x_5478_, 0, v___x_5486_);
v___x_5488_ = v___x_5478_;
goto v_reusejp_5487_;
}
else
{
lean_object* v_reuseFailAlloc_5492_; 
v_reuseFailAlloc_5492_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5492_, 0, v___x_5486_);
lean_ctor_set(v_reuseFailAlloc_5492_, 1, v_k_5302_);
lean_ctor_set(v_reuseFailAlloc_5492_, 2, v_v_5303_);
lean_ctor_set(v_reuseFailAlloc_5492_, 3, v_r_5473_);
lean_ctor_set(v_reuseFailAlloc_5492_, 4, v_r_5305_);
v___x_5488_ = v_reuseFailAlloc_5492_;
goto v_reusejp_5487_;
}
v_reusejp_5487_:
{
lean_object* v___x_5490_; 
if (v_isShared_5467_ == 0)
{
lean_ctor_set(v___x_5466_, 4, v___x_5488_);
lean_ctor_set(v___x_5466_, 3, v___y_5484_);
lean_ctor_set(v___x_5466_, 2, v_v_5471_);
lean_ctor_set(v___x_5466_, 1, v_k_5470_);
lean_ctor_set(v___x_5466_, 0, v___x_5481_);
v___x_5490_ = v___x_5466_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5481_);
lean_ctor_set(v_reuseFailAlloc_5491_, 1, v_k_5470_);
lean_ctor_set(v_reuseFailAlloc_5491_, 2, v_v_5471_);
lean_ctor_set(v_reuseFailAlloc_5491_, 3, v___y_5484_);
lean_ctor_set(v_reuseFailAlloc_5491_, 4, v___x_5488_);
v___x_5490_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
return v___x_5490_;
}
}
}
v___jp_5494_:
{
lean_object* v___x_5496_; lean_object* v___x_5498_; 
v___x_5496_ = lean_nat_add(v___x_5493_, v___y_5495_);
lean_dec(v___y_5495_);
lean_dec(v___x_5493_);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 4, v_l_5472_);
lean_ctor_set(v___x_5307_, 3, v_l_5455_);
lean_ctor_set(v___x_5307_, 2, v_v_5454_);
lean_ctor_set(v___x_5307_, 1, v_k_5453_);
lean_ctor_set(v___x_5307_, 0, v___x_5496_);
v___x_5498_ = v___x_5307_;
goto v_reusejp_5497_;
}
else
{
lean_object* v_reuseFailAlloc_5502_; 
v_reuseFailAlloc_5502_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5502_, 0, v___x_5496_);
lean_ctor_set(v_reuseFailAlloc_5502_, 1, v_k_5453_);
lean_ctor_set(v_reuseFailAlloc_5502_, 2, v_v_5454_);
lean_ctor_set(v_reuseFailAlloc_5502_, 3, v_l_5455_);
lean_ctor_set(v_reuseFailAlloc_5502_, 4, v_l_5472_);
v___x_5498_ = v_reuseFailAlloc_5502_;
goto v_reusejp_5497_;
}
v_reusejp_5497_:
{
lean_object* v___x_5499_; 
v___x_5499_ = lean_nat_add(v___x_5450_, v_size_5451_);
if (lean_obj_tag(v_r_5473_) == 0)
{
lean_object* v_size_5500_; 
v_size_5500_ = lean_ctor_get(v_r_5473_, 0);
lean_inc(v_size_5500_);
v___y_5483_ = v___x_5499_;
v___y_5484_ = v___x_5498_;
v___y_5485_ = v_size_5500_;
goto v___jp_5482_;
}
else
{
lean_object* v___x_5501_; 
v___x_5501_ = lean_unsigned_to_nat(0u);
v___y_5483_ = v___x_5499_;
v___y_5484_ = v___x_5498_;
v___y_5485_ = v___x_5501_;
goto v___jp_5482_;
}
}
}
}
}
else
{
lean_object* v___x_5511_; lean_object* v___x_5512_; lean_object* v___x_5513_; lean_object* v___x_5514_; lean_object* v___x_5516_; 
lean_del_object(v___x_5307_);
v___x_5511_ = lean_nat_add(v___x_5450_, v_size_5452_);
lean_dec(v_size_5452_);
v___x_5512_ = lean_nat_add(v___x_5511_, v_size_5451_);
lean_dec(v___x_5511_);
v___x_5513_ = lean_nat_add(v___x_5450_, v_size_5451_);
v___x_5514_ = lean_nat_add(v___x_5513_, v_size_5469_);
lean_dec(v___x_5513_);
lean_inc_ref(v_r_5305_);
if (v_isShared_5467_ == 0)
{
lean_ctor_set(v___x_5466_, 4, v_r_5305_);
lean_ctor_set(v___x_5466_, 3, v_r_5456_);
lean_ctor_set(v___x_5466_, 2, v_v_5303_);
lean_ctor_set(v___x_5466_, 1, v_k_5302_);
lean_ctor_set(v___x_5466_, 0, v___x_5514_);
v___x_5516_ = v___x_5466_;
goto v_reusejp_5515_;
}
else
{
lean_object* v_reuseFailAlloc_5529_; 
v_reuseFailAlloc_5529_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5529_, 0, v___x_5514_);
lean_ctor_set(v_reuseFailAlloc_5529_, 1, v_k_5302_);
lean_ctor_set(v_reuseFailAlloc_5529_, 2, v_v_5303_);
lean_ctor_set(v_reuseFailAlloc_5529_, 3, v_r_5456_);
lean_ctor_set(v_reuseFailAlloc_5529_, 4, v_r_5305_);
v___x_5516_ = v_reuseFailAlloc_5529_;
goto v_reusejp_5515_;
}
v_reusejp_5515_:
{
lean_object* v___x_5518_; uint8_t v_isShared_5519_; uint8_t v_isSharedCheck_5523_; 
v_isSharedCheck_5523_ = !lean_is_exclusive(v_r_5305_);
if (v_isSharedCheck_5523_ == 0)
{
lean_object* v_unused_5524_; lean_object* v_unused_5525_; lean_object* v_unused_5526_; lean_object* v_unused_5527_; lean_object* v_unused_5528_; 
v_unused_5524_ = lean_ctor_get(v_r_5305_, 4);
lean_dec(v_unused_5524_);
v_unused_5525_ = lean_ctor_get(v_r_5305_, 3);
lean_dec(v_unused_5525_);
v_unused_5526_ = lean_ctor_get(v_r_5305_, 2);
lean_dec(v_unused_5526_);
v_unused_5527_ = lean_ctor_get(v_r_5305_, 1);
lean_dec(v_unused_5527_);
v_unused_5528_ = lean_ctor_get(v_r_5305_, 0);
lean_dec(v_unused_5528_);
v___x_5518_ = v_r_5305_;
v_isShared_5519_ = v_isSharedCheck_5523_;
goto v_resetjp_5517_;
}
else
{
lean_dec(v_r_5305_);
v___x_5518_ = lean_box(0);
v_isShared_5519_ = v_isSharedCheck_5523_;
goto v_resetjp_5517_;
}
v_resetjp_5517_:
{
lean_object* v___x_5521_; 
if (v_isShared_5519_ == 0)
{
lean_ctor_set(v___x_5518_, 4, v___x_5516_);
lean_ctor_set(v___x_5518_, 3, v_l_5455_);
lean_ctor_set(v___x_5518_, 2, v_v_5454_);
lean_ctor_set(v___x_5518_, 1, v_k_5453_);
lean_ctor_set(v___x_5518_, 0, v___x_5512_);
v___x_5521_ = v___x_5518_;
goto v_reusejp_5520_;
}
else
{
lean_object* v_reuseFailAlloc_5522_; 
v_reuseFailAlloc_5522_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5522_, 0, v___x_5512_);
lean_ctor_set(v_reuseFailAlloc_5522_, 1, v_k_5453_);
lean_ctor_set(v_reuseFailAlloc_5522_, 2, v_v_5454_);
lean_ctor_set(v_reuseFailAlloc_5522_, 3, v_l_5455_);
lean_ctor_set(v_reuseFailAlloc_5522_, 4, v___x_5516_);
v___x_5521_ = v_reuseFailAlloc_5522_;
goto v_reusejp_5520_;
}
v_reusejp_5520_:
{
return v___x_5521_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5536_; 
v_l_5536_ = lean_ctor_get(v_impl_5449_, 3);
lean_inc(v_l_5536_);
if (lean_obj_tag(v_l_5536_) == 0)
{
lean_object* v_r_5537_; lean_object* v_k_5538_; lean_object* v_v_5539_; lean_object* v___x_5541_; uint8_t v_isShared_5542_; uint8_t v_isSharedCheck_5550_; 
v_r_5537_ = lean_ctor_get(v_impl_5449_, 4);
v_k_5538_ = lean_ctor_get(v_impl_5449_, 1);
v_v_5539_ = lean_ctor_get(v_impl_5449_, 2);
v_isSharedCheck_5550_ = !lean_is_exclusive(v_impl_5449_);
if (v_isSharedCheck_5550_ == 0)
{
lean_object* v_unused_5551_; lean_object* v_unused_5552_; 
v_unused_5551_ = lean_ctor_get(v_impl_5449_, 3);
lean_dec(v_unused_5551_);
v_unused_5552_ = lean_ctor_get(v_impl_5449_, 0);
lean_dec(v_unused_5552_);
v___x_5541_ = v_impl_5449_;
v_isShared_5542_ = v_isSharedCheck_5550_;
goto v_resetjp_5540_;
}
else
{
lean_inc(v_r_5537_);
lean_inc(v_v_5539_);
lean_inc(v_k_5538_);
lean_dec(v_impl_5449_);
v___x_5541_ = lean_box(0);
v_isShared_5542_ = v_isSharedCheck_5550_;
goto v_resetjp_5540_;
}
v_resetjp_5540_:
{
lean_object* v___x_5543_; lean_object* v___x_5545_; 
v___x_5543_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5537_);
if (v_isShared_5542_ == 0)
{
lean_ctor_set(v___x_5541_, 3, v_r_5537_);
lean_ctor_set(v___x_5541_, 2, v_v_5303_);
lean_ctor_set(v___x_5541_, 1, v_k_5302_);
lean_ctor_set(v___x_5541_, 0, v___x_5450_);
v___x_5545_ = v___x_5541_;
goto v_reusejp_5544_;
}
else
{
lean_object* v_reuseFailAlloc_5549_; 
v_reuseFailAlloc_5549_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5549_, 0, v___x_5450_);
lean_ctor_set(v_reuseFailAlloc_5549_, 1, v_k_5302_);
lean_ctor_set(v_reuseFailAlloc_5549_, 2, v_v_5303_);
lean_ctor_set(v_reuseFailAlloc_5549_, 3, v_r_5537_);
lean_ctor_set(v_reuseFailAlloc_5549_, 4, v_r_5537_);
v___x_5545_ = v_reuseFailAlloc_5549_;
goto v_reusejp_5544_;
}
v_reusejp_5544_:
{
lean_object* v___x_5547_; 
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 4, v___x_5545_);
lean_ctor_set(v___x_5307_, 3, v_l_5536_);
lean_ctor_set(v___x_5307_, 2, v_v_5539_);
lean_ctor_set(v___x_5307_, 1, v_k_5538_);
lean_ctor_set(v___x_5307_, 0, v___x_5543_);
v___x_5547_ = v___x_5307_;
goto v_reusejp_5546_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v___x_5543_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v_k_5538_);
lean_ctor_set(v_reuseFailAlloc_5548_, 2, v_v_5539_);
lean_ctor_set(v_reuseFailAlloc_5548_, 3, v_l_5536_);
lean_ctor_set(v_reuseFailAlloc_5548_, 4, v___x_5545_);
v___x_5547_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5546_;
}
v_reusejp_5546_:
{
return v___x_5547_;
}
}
}
}
else
{
lean_object* v_r_5553_; 
v_r_5553_ = lean_ctor_get(v_impl_5449_, 4);
lean_inc(v_r_5553_);
if (lean_obj_tag(v_r_5553_) == 0)
{
lean_object* v_k_5554_; lean_object* v_v_5555_; lean_object* v___x_5557_; uint8_t v_isShared_5558_; uint8_t v_isSharedCheck_5578_; 
v_k_5554_ = lean_ctor_get(v_impl_5449_, 1);
v_v_5555_ = lean_ctor_get(v_impl_5449_, 2);
v_isSharedCheck_5578_ = !lean_is_exclusive(v_impl_5449_);
if (v_isSharedCheck_5578_ == 0)
{
lean_object* v_unused_5579_; lean_object* v_unused_5580_; lean_object* v_unused_5581_; 
v_unused_5579_ = lean_ctor_get(v_impl_5449_, 4);
lean_dec(v_unused_5579_);
v_unused_5580_ = lean_ctor_get(v_impl_5449_, 3);
lean_dec(v_unused_5580_);
v_unused_5581_ = lean_ctor_get(v_impl_5449_, 0);
lean_dec(v_unused_5581_);
v___x_5557_ = v_impl_5449_;
v_isShared_5558_ = v_isSharedCheck_5578_;
goto v_resetjp_5556_;
}
else
{
lean_inc(v_v_5555_);
lean_inc(v_k_5554_);
lean_dec(v_impl_5449_);
v___x_5557_ = lean_box(0);
v_isShared_5558_ = v_isSharedCheck_5578_;
goto v_resetjp_5556_;
}
v_resetjp_5556_:
{
lean_object* v_k_5559_; lean_object* v_v_5560_; lean_object* v___x_5562_; uint8_t v_isShared_5563_; uint8_t v_isSharedCheck_5574_; 
v_k_5559_ = lean_ctor_get(v_r_5553_, 1);
v_v_5560_ = lean_ctor_get(v_r_5553_, 2);
v_isSharedCheck_5574_ = !lean_is_exclusive(v_r_5553_);
if (v_isSharedCheck_5574_ == 0)
{
lean_object* v_unused_5575_; lean_object* v_unused_5576_; lean_object* v_unused_5577_; 
v_unused_5575_ = lean_ctor_get(v_r_5553_, 4);
lean_dec(v_unused_5575_);
v_unused_5576_ = lean_ctor_get(v_r_5553_, 3);
lean_dec(v_unused_5576_);
v_unused_5577_ = lean_ctor_get(v_r_5553_, 0);
lean_dec(v_unused_5577_);
v___x_5562_ = v_r_5553_;
v_isShared_5563_ = v_isSharedCheck_5574_;
goto v_resetjp_5561_;
}
else
{
lean_inc(v_v_5560_);
lean_inc(v_k_5559_);
lean_dec(v_r_5553_);
v___x_5562_ = lean_box(0);
v_isShared_5563_ = v_isSharedCheck_5574_;
goto v_resetjp_5561_;
}
v_resetjp_5561_:
{
lean_object* v___x_5564_; lean_object* v___x_5566_; 
v___x_5564_ = lean_unsigned_to_nat(3u);
if (v_isShared_5563_ == 0)
{
lean_ctor_set(v___x_5562_, 4, v_l_5536_);
lean_ctor_set(v___x_5562_, 3, v_l_5536_);
lean_ctor_set(v___x_5562_, 2, v_v_5555_);
lean_ctor_set(v___x_5562_, 1, v_k_5554_);
lean_ctor_set(v___x_5562_, 0, v___x_5450_);
v___x_5566_ = v___x_5562_;
goto v_reusejp_5565_;
}
else
{
lean_object* v_reuseFailAlloc_5573_; 
v_reuseFailAlloc_5573_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5573_, 0, v___x_5450_);
lean_ctor_set(v_reuseFailAlloc_5573_, 1, v_k_5554_);
lean_ctor_set(v_reuseFailAlloc_5573_, 2, v_v_5555_);
lean_ctor_set(v_reuseFailAlloc_5573_, 3, v_l_5536_);
lean_ctor_set(v_reuseFailAlloc_5573_, 4, v_l_5536_);
v___x_5566_ = v_reuseFailAlloc_5573_;
goto v_reusejp_5565_;
}
v_reusejp_5565_:
{
lean_object* v___x_5568_; 
if (v_isShared_5558_ == 0)
{
lean_ctor_set(v___x_5557_, 4, v_l_5536_);
lean_ctor_set(v___x_5557_, 2, v_v_5303_);
lean_ctor_set(v___x_5557_, 1, v_k_5302_);
lean_ctor_set(v___x_5557_, 0, v___x_5450_);
v___x_5568_ = v___x_5557_;
goto v_reusejp_5567_;
}
else
{
lean_object* v_reuseFailAlloc_5572_; 
v_reuseFailAlloc_5572_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5572_, 0, v___x_5450_);
lean_ctor_set(v_reuseFailAlloc_5572_, 1, v_k_5302_);
lean_ctor_set(v_reuseFailAlloc_5572_, 2, v_v_5303_);
lean_ctor_set(v_reuseFailAlloc_5572_, 3, v_l_5536_);
lean_ctor_set(v_reuseFailAlloc_5572_, 4, v_l_5536_);
v___x_5568_ = v_reuseFailAlloc_5572_;
goto v_reusejp_5567_;
}
v_reusejp_5567_:
{
lean_object* v___x_5570_; 
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 4, v___x_5568_);
lean_ctor_set(v___x_5307_, 3, v___x_5566_);
lean_ctor_set(v___x_5307_, 2, v_v_5560_);
lean_ctor_set(v___x_5307_, 1, v_k_5559_);
lean_ctor_set(v___x_5307_, 0, v___x_5564_);
v___x_5570_ = v___x_5307_;
goto v_reusejp_5569_;
}
else
{
lean_object* v_reuseFailAlloc_5571_; 
v_reuseFailAlloc_5571_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5571_, 0, v___x_5564_);
lean_ctor_set(v_reuseFailAlloc_5571_, 1, v_k_5559_);
lean_ctor_set(v_reuseFailAlloc_5571_, 2, v_v_5560_);
lean_ctor_set(v_reuseFailAlloc_5571_, 3, v___x_5566_);
lean_ctor_set(v_reuseFailAlloc_5571_, 4, v___x_5568_);
v___x_5570_ = v_reuseFailAlloc_5571_;
goto v_reusejp_5569_;
}
v_reusejp_5569_:
{
return v___x_5570_;
}
}
}
}
}
}
else
{
lean_object* v___x_5582_; lean_object* v___x_5584_; 
v___x_5582_ = lean_unsigned_to_nat(2u);
if (v_isShared_5308_ == 0)
{
lean_ctor_set(v___x_5307_, 4, v_r_5553_);
lean_ctor_set(v___x_5307_, 3, v_impl_5449_);
lean_ctor_set(v___x_5307_, 0, v___x_5582_);
v___x_5584_ = v___x_5307_;
goto v_reusejp_5583_;
}
else
{
lean_object* v_reuseFailAlloc_5585_; 
v_reuseFailAlloc_5585_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5585_, 0, v___x_5582_);
lean_ctor_set(v_reuseFailAlloc_5585_, 1, v_k_5302_);
lean_ctor_set(v_reuseFailAlloc_5585_, 2, v_v_5303_);
lean_ctor_set(v_reuseFailAlloc_5585_, 3, v_impl_5449_);
lean_ctor_set(v_reuseFailAlloc_5585_, 4, v_r_5553_);
v___x_5584_ = v_reuseFailAlloc_5585_;
goto v_reusejp_5583_;
}
v_reusejp_5583_:
{
return v___x_5584_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5587_; lean_object* v___x_5588_; 
v___x_5587_ = lean_unsigned_to_nat(1u);
v___x_5588_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5588_, 0, v___x_5587_);
lean_ctor_set(v___x_5588_, 1, v_k_5298_);
lean_ctor_set(v___x_5588_, 2, v_v_5299_);
lean_ctor_set(v___x_5588_, 3, v_t_5300_);
lean_ctor_set(v___x_5588_, 4, v_t_5300_);
return v___x_5588_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5589_, lean_object* v_t_5590_){
_start:
{
if (lean_obj_tag(v_t_5590_) == 0)
{
lean_object* v_k_5591_; lean_object* v_l_5592_; lean_object* v_r_5593_; uint8_t v___x_5594_; 
v_k_5591_ = lean_ctor_get(v_t_5590_, 1);
v_l_5592_ = lean_ctor_get(v_t_5590_, 3);
v_r_5593_ = lean_ctor_get(v_t_5590_, 4);
v___x_5594_ = lean_nat_dec_lt(v_k_5591_, v_k_5589_);
if (v___x_5594_ == 0)
{
uint8_t v___x_5595_; 
v___x_5595_ = lean_nat_dec_eq(v_k_5591_, v_k_5589_);
if (v___x_5595_ == 0)
{
v_t_5590_ = v_r_5593_;
goto _start;
}
else
{
return v___x_5595_;
}
}
else
{
v_t_5590_ = v_l_5592_;
goto _start;
}
}
else
{
uint8_t v___x_5598_; 
v___x_5598_ = 0;
return v___x_5598_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5599_, lean_object* v_t_5600_){
_start:
{
uint8_t v_res_5601_; lean_object* v_r_5602_; 
v_res_5601_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5599_, v_t_5600_);
lean_dec(v_t_5600_);
lean_dec(v_k_5599_);
v_r_5602_ = lean_box(v_res_5601_);
return v_r_5602_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5603_, lean_object* v_e_5604_){
_start:
{
lean_object* v_defaultInstances_5605_; lean_object* v_priorities_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5633_; 
v_defaultInstances_5605_ = lean_ctor_get(v_d_5603_, 0);
v_priorities_5606_ = lean_ctor_get(v_d_5603_, 1);
v_isSharedCheck_5633_ = !lean_is_exclusive(v_d_5603_);
if (v_isSharedCheck_5633_ == 0)
{
v___x_5608_ = v_d_5603_;
v_isShared_5609_ = v_isSharedCheck_5633_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_priorities_5606_);
lean_inc(v_defaultInstances_5605_);
lean_dec(v_d_5603_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5633_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v_className_5610_; lean_object* v_instanceName_5611_; lean_object* v_priority_5612_; lean_object* v___y_5614_; uint8_t v___x_5630_; 
v_className_5610_ = lean_ctor_get(v_e_5604_, 0);
lean_inc(v_className_5610_);
v_instanceName_5611_ = lean_ctor_get(v_e_5604_, 1);
lean_inc(v_instanceName_5611_);
v_priority_5612_ = lean_ctor_get(v_e_5604_, 2);
lean_inc(v_priority_5612_);
lean_dec_ref(v_e_5604_);
v___x_5630_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5612_, v_priorities_5606_);
if (v___x_5630_ == 0)
{
lean_object* v___x_5631_; lean_object* v___x_5632_; 
v___x_5631_ = lean_box(0);
lean_inc(v_priority_5612_);
v___x_5632_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5612_, v___x_5631_, v_priorities_5606_);
v___y_5614_ = v___x_5632_;
goto v___jp_5613_;
}
else
{
v___y_5614_ = v_priorities_5606_;
goto v___jp_5613_;
}
v___jp_5613_:
{
lean_object* v___x_5615_; 
v___x_5615_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5605_, v_className_5610_);
if (lean_obj_tag(v___x_5615_) == 0)
{
lean_object* v___x_5616_; lean_object* v___x_5617_; lean_object* v___x_5618_; lean_object* v___x_5619_; lean_object* v___x_5621_; 
v___x_5616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5616_, 0, v_instanceName_5611_);
lean_ctor_set(v___x_5616_, 1, v_priority_5612_);
v___x_5617_ = lean_box(0);
v___x_5618_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5618_, 0, v___x_5616_);
lean_ctor_set(v___x_5618_, 1, v___x_5617_);
v___x_5619_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5610_, v___x_5618_, v_defaultInstances_5605_);
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 1, v___y_5614_);
lean_ctor_set(v___x_5608_, 0, v___x_5619_);
v___x_5621_ = v___x_5608_;
goto v_reusejp_5620_;
}
else
{
lean_object* v_reuseFailAlloc_5622_; 
v_reuseFailAlloc_5622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5622_, 0, v___x_5619_);
lean_ctor_set(v_reuseFailAlloc_5622_, 1, v___y_5614_);
v___x_5621_ = v_reuseFailAlloc_5622_;
goto v_reusejp_5620_;
}
v_reusejp_5620_:
{
return v___x_5621_;
}
}
else
{
lean_object* v_val_5623_; lean_object* v___x_5624_; lean_object* v___x_5625_; lean_object* v___x_5626_; lean_object* v___x_5628_; 
v_val_5623_ = lean_ctor_get(v___x_5615_, 0);
lean_inc(v_val_5623_);
lean_dec_ref_known(v___x_5615_, 1);
v___x_5624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5624_, 0, v_instanceName_5611_);
lean_ctor_set(v___x_5624_, 1, v_priority_5612_);
v___x_5625_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5625_, 0, v___x_5624_);
lean_ctor_set(v___x_5625_, 1, v_val_5623_);
v___x_5626_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5610_, v___x_5625_, v_defaultInstances_5605_);
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 1, v___y_5614_);
lean_ctor_set(v___x_5608_, 0, v___x_5626_);
v___x_5628_ = v___x_5608_;
goto v_reusejp_5627_;
}
else
{
lean_object* v_reuseFailAlloc_5629_; 
v_reuseFailAlloc_5629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5629_, 0, v___x_5626_);
lean_ctor_set(v_reuseFailAlloc_5629_, 1, v___y_5614_);
v___x_5628_ = v_reuseFailAlloc_5629_;
goto v_reusejp_5627_;
}
v_reusejp_5627_:
{
return v___x_5628_;
}
}
}
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5634_, lean_object* v_k_5635_, lean_object* v_t_5636_){
_start:
{
uint8_t v___x_5637_; 
v___x_5637_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5635_, v_t_5636_);
return v___x_5637_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5638_, lean_object* v_k_5639_, lean_object* v_t_5640_){
_start:
{
uint8_t v_res_5641_; lean_object* v_r_5642_; 
v_res_5641_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5638_, v_k_5639_, v_t_5640_);
lean_dec(v_t_5640_);
lean_dec(v_k_5639_);
v_r_5642_ = lean_box(v_res_5641_);
return v_r_5642_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5643_, lean_object* v_k_5644_, lean_object* v_v_5645_, lean_object* v_t_5646_, lean_object* v_hl_5647_){
_start:
{
lean_object* v___x_5648_; 
v___x_5648_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5644_, v_v_5645_, v_t_5646_);
return v___x_5648_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object* v_env_5649_, lean_object* v_as_5650_, size_t v_i_5651_, size_t v_stop_5652_, lean_object* v_b_5653_){
_start:
{
lean_object* v___y_5655_; uint8_t v___x_5659_; 
v___x_5659_ = lean_usize_dec_eq(v_i_5651_, v_stop_5652_);
if (v___x_5659_ == 0)
{
lean_object* v___x_5660_; lean_object* v_instanceName_5661_; uint8_t v___x_5662_; lean_object* v___x_5663_; uint8_t v___x_5664_; 
v___x_5660_ = lean_array_uget_borrowed(v_as_5650_, v_i_5651_);
v_instanceName_5661_ = lean_ctor_get(v___x_5660_, 1);
v___x_5662_ = 1;
lean_inc_ref(v_env_5649_);
v___x_5663_ = l_Lean_Environment_setExporting(v_env_5649_, v___x_5662_);
lean_inc(v_instanceName_5661_);
v___x_5664_ = l_Lean_Environment_contains(v___x_5663_, v_instanceName_5661_, v___x_5659_);
if (v___x_5664_ == 0)
{
v___y_5655_ = v_b_5653_;
goto v___jp_5654_;
}
else
{
lean_object* v___x_5665_; 
lean_inc(v___x_5660_);
v___x_5665_ = lean_array_push(v_b_5653_, v___x_5660_);
v___y_5655_ = v___x_5665_;
goto v___jp_5654_;
}
}
else
{
lean_dec_ref(v_env_5649_);
return v_b_5653_;
}
v___jp_5654_:
{
size_t v___x_5656_; size_t v___x_5657_; 
v___x_5656_ = ((size_t)1ULL);
v___x_5657_ = lean_usize_add(v_i_5651_, v___x_5656_);
v_i_5651_ = v___x_5657_;
v_b_5653_ = v___y_5655_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_5666_, lean_object* v_as_5667_, lean_object* v_i_5668_, lean_object* v_stop_5669_, lean_object* v_b_5670_){
_start:
{
size_t v_i_boxed_5671_; size_t v_stop_boxed_5672_; lean_object* v_res_5673_; 
v_i_boxed_5671_ = lean_unbox_usize(v_i_5668_);
lean_dec(v_i_5668_);
v_stop_boxed_5672_ = lean_unbox_usize(v_stop_5669_);
lean_dec(v_stop_5669_);
v_res_5673_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5666_, v_as_5667_, v_i_boxed_5671_, v_stop_boxed_5672_, v_b_5670_);
lean_dec_ref(v_as_5667_);
return v_res_5673_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_env_5676_, lean_object* v_x_5677_, lean_object* v_entries_5678_){
_start:
{
lean_object* v_all_5679_; lean_object* v___x_5680_; lean_object* v___x_5681_; lean_object* v___x_5682_; uint8_t v___x_5683_; 
v_all_5679_ = lean_array_mk(v_entries_5678_);
v___x_5680_ = lean_unsigned_to_nat(0u);
v___x_5681_ = lean_array_get_size(v_all_5679_);
v___x_5682_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5683_ = lean_nat_dec_lt(v___x_5680_, v___x_5681_);
if (v___x_5683_ == 0)
{
lean_object* v___x_5684_; 
lean_dec_ref(v_env_5676_);
v___x_5684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5684_, 0, v___x_5682_);
lean_ctor_set(v___x_5684_, 1, v___x_5682_);
lean_ctor_set(v___x_5684_, 2, v_all_5679_);
return v___x_5684_;
}
else
{
uint8_t v___x_5685_; 
v___x_5685_ = lean_nat_dec_le(v___x_5681_, v___x_5681_);
if (v___x_5685_ == 0)
{
if (v___x_5683_ == 0)
{
lean_object* v___x_5686_; 
lean_dec_ref(v_env_5676_);
v___x_5686_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5686_, 0, v___x_5682_);
lean_ctor_set(v___x_5686_, 1, v___x_5682_);
lean_ctor_set(v___x_5686_, 2, v_all_5679_);
return v___x_5686_;
}
else
{
size_t v___x_5687_; size_t v___x_5688_; lean_object* v___x_5689_; lean_object* v___x_5690_; 
v___x_5687_ = ((size_t)0ULL);
v___x_5688_ = lean_usize_of_nat(v___x_5681_);
v___x_5689_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5676_, v_all_5679_, v___x_5687_, v___x_5688_, v___x_5682_);
lean_inc_ref(v___x_5689_);
v___x_5690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5690_, 0, v___x_5689_);
lean_ctor_set(v___x_5690_, 1, v___x_5689_);
lean_ctor_set(v___x_5690_, 2, v_all_5679_);
return v___x_5690_;
}
}
else
{
size_t v___x_5691_; size_t v___x_5692_; lean_object* v___x_5693_; lean_object* v___x_5694_; 
v___x_5691_ = ((size_t)0ULL);
v___x_5692_ = lean_usize_of_nat(v___x_5681_);
v___x_5693_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5676_, v_all_5679_, v___x_5691_, v___x_5692_, v___x_5682_);
lean_inc_ref(v___x_5693_);
v___x_5694_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5694_, 0, v___x_5693_);
lean_ctor_set(v___x_5694_, 1, v___x_5693_);
lean_ctor_set(v___x_5694_, 2, v_all_5679_);
return v___x_5694_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5695_, lean_object* v_x_5696_, lean_object* v_entries_5697_){
_start:
{
lean_object* v_res_5698_; 
v_res_5698_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5695_, v_x_5696_, v_entries_5697_);
lean_dec_ref(v_x_5696_);
return v_res_5698_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5699_){
_start:
{
lean_object* v___x_5700_; 
v___x_5700_ = lean_array_mk(v_es_5699_);
return v___x_5700_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5701_, size_t v_i_5702_, size_t v_stop_5703_, lean_object* v_b_5704_){
_start:
{
uint8_t v___x_5705_; 
v___x_5705_ = lean_usize_dec_eq(v_i_5702_, v_stop_5703_);
if (v___x_5705_ == 0)
{
lean_object* v___x_5706_; lean_object* v___x_5707_; size_t v___x_5708_; size_t v___x_5709_; 
v___x_5706_ = lean_array_uget_borrowed(v_as_5701_, v_i_5702_);
lean_inc(v___x_5706_);
v___x_5707_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5704_, v___x_5706_);
v___x_5708_ = ((size_t)1ULL);
v___x_5709_ = lean_usize_add(v_i_5702_, v___x_5708_);
v_i_5702_ = v___x_5709_;
v_b_5704_ = v___x_5707_;
goto _start;
}
else
{
return v_b_5704_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5711_, lean_object* v_i_5712_, lean_object* v_stop_5713_, lean_object* v_b_5714_){
_start:
{
size_t v_i_boxed_5715_; size_t v_stop_boxed_5716_; lean_object* v_res_5717_; 
v_i_boxed_5715_ = lean_unbox_usize(v_i_5712_);
lean_dec(v_i_5712_);
v_stop_boxed_5716_ = lean_unbox_usize(v_stop_5713_);
lean_dec(v_stop_5713_);
v_res_5717_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5711_, v_i_boxed_5715_, v_stop_boxed_5716_, v_b_5714_);
lean_dec_ref(v_as_5711_);
return v_res_5717_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5718_, size_t v_i_5719_, size_t v_stop_5720_, lean_object* v_b_5721_){
_start:
{
lean_object* v___y_5723_; uint8_t v___x_5727_; 
v___x_5727_ = lean_usize_dec_eq(v_i_5719_, v_stop_5720_);
if (v___x_5727_ == 0)
{
lean_object* v___x_5728_; lean_object* v___x_5729_; lean_object* v___x_5730_; uint8_t v___x_5731_; 
v___x_5728_ = lean_array_uget_borrowed(v_as_5718_, v_i_5719_);
v___x_5729_ = lean_unsigned_to_nat(0u);
v___x_5730_ = lean_array_get_size(v___x_5728_);
v___x_5731_ = lean_nat_dec_lt(v___x_5729_, v___x_5730_);
if (v___x_5731_ == 0)
{
v___y_5723_ = v_b_5721_;
goto v___jp_5722_;
}
else
{
uint8_t v___x_5732_; 
v___x_5732_ = lean_nat_dec_le(v___x_5730_, v___x_5730_);
if (v___x_5732_ == 0)
{
if (v___x_5731_ == 0)
{
v___y_5723_ = v_b_5721_;
goto v___jp_5722_;
}
else
{
size_t v___x_5733_; size_t v___x_5734_; lean_object* v___x_5735_; 
v___x_5733_ = ((size_t)0ULL);
v___x_5734_ = lean_usize_of_nat(v___x_5730_);
v___x_5735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5728_, v___x_5733_, v___x_5734_, v_b_5721_);
v___y_5723_ = v___x_5735_;
goto v___jp_5722_;
}
}
else
{
size_t v___x_5736_; size_t v___x_5737_; lean_object* v___x_5738_; 
v___x_5736_ = ((size_t)0ULL);
v___x_5737_ = lean_usize_of_nat(v___x_5730_);
v___x_5738_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5728_, v___x_5736_, v___x_5737_, v_b_5721_);
v___y_5723_ = v___x_5738_;
goto v___jp_5722_;
}
}
}
else
{
return v_b_5721_;
}
v___jp_5722_:
{
size_t v___x_5724_; size_t v___x_5725_; 
v___x_5724_ = ((size_t)1ULL);
v___x_5725_ = lean_usize_add(v_i_5719_, v___x_5724_);
v_i_5719_ = v___x_5725_;
v_b_5721_ = v___y_5723_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5739_, lean_object* v_i_5740_, lean_object* v_stop_5741_, lean_object* v_b_5742_){
_start:
{
size_t v_i_boxed_5743_; size_t v_stop_boxed_5744_; lean_object* v_res_5745_; 
v_i_boxed_5743_ = lean_unbox_usize(v_i_5740_);
lean_dec(v_i_5740_);
v_stop_boxed_5744_ = lean_unbox_usize(v_stop_5741_);
lean_dec(v_stop_5741_);
v_res_5745_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5739_, v_i_boxed_5743_, v_stop_boxed_5744_, v_b_5742_);
lean_dec_ref(v_as_5739_);
return v_res_5745_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_5746_, lean_object* v_as_5747_){
_start:
{
lean_object* v___x_5748_; lean_object* v___x_5749_; uint8_t v___x_5750_; 
v___x_5748_ = lean_unsigned_to_nat(0u);
v___x_5749_ = lean_array_get_size(v_as_5747_);
v___x_5750_ = lean_nat_dec_lt(v___x_5748_, v___x_5749_);
if (v___x_5750_ == 0)
{
return v_initState_5746_;
}
else
{
uint8_t v___x_5751_; 
v___x_5751_ = lean_nat_dec_le(v___x_5749_, v___x_5749_);
if (v___x_5751_ == 0)
{
if (v___x_5750_ == 0)
{
return v_initState_5746_;
}
else
{
size_t v___x_5752_; size_t v___x_5753_; lean_object* v___x_5754_; 
v___x_5752_ = ((size_t)0ULL);
v___x_5753_ = lean_usize_of_nat(v___x_5749_);
v___x_5754_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5747_, v___x_5752_, v___x_5753_, v_initState_5746_);
return v___x_5754_;
}
}
else
{
size_t v___x_5755_; size_t v___x_5756_; lean_object* v___x_5757_; 
v___x_5755_ = ((size_t)0ULL);
v___x_5756_ = lean_usize_of_nat(v___x_5749_);
v___x_5757_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5747_, v___x_5755_, v___x_5756_, v_initState_5746_);
return v___x_5757_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_5758_, lean_object* v_as_5759_){
_start:
{
lean_object* v_res_5760_; 
v_res_5760_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_5758_, v_as_5759_);
lean_dec_ref(v_as_5759_);
return v_res_5760_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5761_){
_start:
{
lean_object* v___x_5762_; lean_object* v___x_5763_; 
v___x_5762_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5763_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_5762_, v_es_5761_);
return v___x_5763_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_5764_){
_start:
{
lean_object* v_res_5765_; 
v_res_5765_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_5764_);
lean_dec_ref(v_es_5764_);
return v_res_5765_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5786_; lean_object* v___x_5787_; 
v___x_5786_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5787_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5786_);
return v___x_5787_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_5788_){
_start:
{
lean_object* v_res_5789_; 
v_res_5789_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_5789_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5790_, lean_object* v___y_5791_, lean_object* v___y_5792_){
_start:
{
lean_object* v___x_5794_; lean_object* v_nextMacroScope_5795_; lean_object* v_ngen_5796_; lean_object* v_auxDeclNGen_5797_; lean_object* v_traceState_5798_; lean_object* v_messages_5799_; lean_object* v_infoState_5800_; lean_object* v_snapshotTasks_5801_; lean_object* v___x_5803_; uint8_t v_isShared_5804_; uint8_t v_isSharedCheck_5827_; 
v___x_5794_ = lean_st_ref_take(v___y_5792_);
v_nextMacroScope_5795_ = lean_ctor_get(v___x_5794_, 1);
v_ngen_5796_ = lean_ctor_get(v___x_5794_, 2);
v_auxDeclNGen_5797_ = lean_ctor_get(v___x_5794_, 3);
v_traceState_5798_ = lean_ctor_get(v___x_5794_, 4);
v_messages_5799_ = lean_ctor_get(v___x_5794_, 6);
v_infoState_5800_ = lean_ctor_get(v___x_5794_, 7);
v_snapshotTasks_5801_ = lean_ctor_get(v___x_5794_, 8);
v_isSharedCheck_5827_ = !lean_is_exclusive(v___x_5794_);
if (v_isSharedCheck_5827_ == 0)
{
lean_object* v_unused_5828_; lean_object* v_unused_5829_; 
v_unused_5828_ = lean_ctor_get(v___x_5794_, 5);
lean_dec(v_unused_5828_);
v_unused_5829_ = lean_ctor_get(v___x_5794_, 0);
lean_dec(v_unused_5829_);
v___x_5803_ = v___x_5794_;
v_isShared_5804_ = v_isSharedCheck_5827_;
goto v_resetjp_5802_;
}
else
{
lean_inc(v_snapshotTasks_5801_);
lean_inc(v_infoState_5800_);
lean_inc(v_messages_5799_);
lean_inc(v_traceState_5798_);
lean_inc(v_auxDeclNGen_5797_);
lean_inc(v_ngen_5796_);
lean_inc(v_nextMacroScope_5795_);
lean_dec(v___x_5794_);
v___x_5803_ = lean_box(0);
v_isShared_5804_ = v_isSharedCheck_5827_;
goto v_resetjp_5802_;
}
v_resetjp_5802_:
{
lean_object* v___x_5805_; lean_object* v___x_5807_; 
v___x_5805_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5804_ == 0)
{
lean_ctor_set(v___x_5803_, 5, v___x_5805_);
lean_ctor_set(v___x_5803_, 0, v_env_5790_);
v___x_5807_ = v___x_5803_;
goto v_reusejp_5806_;
}
else
{
lean_object* v_reuseFailAlloc_5826_; 
v_reuseFailAlloc_5826_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5826_, 0, v_env_5790_);
lean_ctor_set(v_reuseFailAlloc_5826_, 1, v_nextMacroScope_5795_);
lean_ctor_set(v_reuseFailAlloc_5826_, 2, v_ngen_5796_);
lean_ctor_set(v_reuseFailAlloc_5826_, 3, v_auxDeclNGen_5797_);
lean_ctor_set(v_reuseFailAlloc_5826_, 4, v_traceState_5798_);
lean_ctor_set(v_reuseFailAlloc_5826_, 5, v___x_5805_);
lean_ctor_set(v_reuseFailAlloc_5826_, 6, v_messages_5799_);
lean_ctor_set(v_reuseFailAlloc_5826_, 7, v_infoState_5800_);
lean_ctor_set(v_reuseFailAlloc_5826_, 8, v_snapshotTasks_5801_);
v___x_5807_ = v_reuseFailAlloc_5826_;
goto v_reusejp_5806_;
}
v_reusejp_5806_:
{
lean_object* v___x_5808_; lean_object* v___x_5809_; lean_object* v_mctx_5810_; lean_object* v_zetaDeltaFVarIds_5811_; lean_object* v_postponed_5812_; lean_object* v_diag_5813_; lean_object* v___x_5815_; uint8_t v_isShared_5816_; uint8_t v_isSharedCheck_5824_; 
v___x_5808_ = lean_st_ref_set(v___y_5792_, v___x_5807_);
v___x_5809_ = lean_st_ref_take(v___y_5791_);
v_mctx_5810_ = lean_ctor_get(v___x_5809_, 0);
v_zetaDeltaFVarIds_5811_ = lean_ctor_get(v___x_5809_, 2);
v_postponed_5812_ = lean_ctor_get(v___x_5809_, 3);
v_diag_5813_ = lean_ctor_get(v___x_5809_, 4);
v_isSharedCheck_5824_ = !lean_is_exclusive(v___x_5809_);
if (v_isSharedCheck_5824_ == 0)
{
lean_object* v_unused_5825_; 
v_unused_5825_ = lean_ctor_get(v___x_5809_, 1);
lean_dec(v_unused_5825_);
v___x_5815_ = v___x_5809_;
v_isShared_5816_ = v_isSharedCheck_5824_;
goto v_resetjp_5814_;
}
else
{
lean_inc(v_diag_5813_);
lean_inc(v_postponed_5812_);
lean_inc(v_zetaDeltaFVarIds_5811_);
lean_inc(v_mctx_5810_);
lean_dec(v___x_5809_);
v___x_5815_ = lean_box(0);
v_isShared_5816_ = v_isSharedCheck_5824_;
goto v_resetjp_5814_;
}
v_resetjp_5814_:
{
lean_object* v___x_5817_; lean_object* v___x_5819_; 
v___x_5817_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5816_ == 0)
{
lean_ctor_set(v___x_5815_, 1, v___x_5817_);
v___x_5819_ = v___x_5815_;
goto v_reusejp_5818_;
}
else
{
lean_object* v_reuseFailAlloc_5823_; 
v_reuseFailAlloc_5823_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5823_, 0, v_mctx_5810_);
lean_ctor_set(v_reuseFailAlloc_5823_, 1, v___x_5817_);
lean_ctor_set(v_reuseFailAlloc_5823_, 2, v_zetaDeltaFVarIds_5811_);
lean_ctor_set(v_reuseFailAlloc_5823_, 3, v_postponed_5812_);
lean_ctor_set(v_reuseFailAlloc_5823_, 4, v_diag_5813_);
v___x_5819_ = v_reuseFailAlloc_5823_;
goto v_reusejp_5818_;
}
v_reusejp_5818_:
{
lean_object* v___x_5820_; lean_object* v___x_5821_; lean_object* v___x_5822_; 
v___x_5820_ = lean_st_ref_set(v___y_5791_, v___x_5819_);
v___x_5821_ = lean_box(0);
v___x_5822_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5822_, 0, v___x_5821_);
return v___x_5822_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5830_, lean_object* v___y_5831_, lean_object* v___y_5832_, lean_object* v___y_5833_){
_start:
{
lean_object* v_res_5834_; 
v_res_5834_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5830_, v___y_5831_, v___y_5832_);
lean_dec(v___y_5832_);
lean_dec(v___y_5831_);
return v_res_5834_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5835_, lean_object* v___y_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_, lean_object* v___y_5839_){
_start:
{
lean_object* v___x_5841_; 
v___x_5841_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5835_, v___y_5837_, v___y_5839_);
return v___x_5841_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5842_, lean_object* v___y_5843_, lean_object* v___y_5844_, lean_object* v___y_5845_, lean_object* v___y_5846_, lean_object* v___y_5847_){
_start:
{
lean_object* v_res_5848_; 
v_res_5848_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5842_, v___y_5843_, v___y_5844_, v___y_5845_, v___y_5846_);
lean_dec(v___y_5846_);
lean_dec_ref(v___y_5845_);
lean_dec(v___y_5844_);
lean_dec_ref(v___y_5843_);
return v_res_5848_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5850_; lean_object* v___x_5851_; 
v___x_5850_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5851_ = l_Lean_stringToMessageData(v___x_5850_);
return v___x_5851_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5853_; lean_object* v___x_5854_; 
v___x_5853_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5854_ = l_Lean_stringToMessageData(v___x_5853_);
return v___x_5854_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5856_; lean_object* v___x_5857_; 
v___x_5856_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5857_ = l_Lean_stringToMessageData(v___x_5856_);
return v___x_5857_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5859_; lean_object* v___x_5860_; 
v___x_5859_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5860_ = l_Lean_stringToMessageData(v___x_5859_);
return v___x_5860_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5862_; lean_object* v___x_5863_; 
v___x_5862_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5863_ = l_Lean_stringToMessageData(v___x_5862_);
return v___x_5863_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5864_, lean_object* v_prio_5865_, lean_object* v_x_5866_, lean_object* v_type_5867_, lean_object* v___y_5868_, lean_object* v___y_5869_, lean_object* v___y_5870_, lean_object* v___y_5871_){
_start:
{
lean_object* v___x_5873_; 
v___x_5873_ = l_Lean_Expr_getAppFn(v_type_5867_);
if (lean_obj_tag(v___x_5873_) == 4)
{
lean_object* v_declName_5874_; lean_object* v___y_5876_; lean_object* v___y_5877_; lean_object* v___y_5878_; lean_object* v___y_5879_; lean_object* v___x_5889_; lean_object* v_env_5890_; uint8_t v___x_5891_; 
v_declName_5874_ = lean_ctor_get(v___x_5873_, 0);
lean_inc(v_declName_5874_);
lean_dec_ref_known(v___x_5873_, 2);
v___x_5889_ = lean_st_ref_get(v___y_5871_);
v_env_5890_ = lean_ctor_get(v___x_5889_, 0);
lean_inc_ref(v_env_5890_);
lean_dec(v___x_5889_);
v___x_5891_ = l_Lean_isClass(v_env_5890_, v_declName_5874_);
if (v___x_5891_ == 0)
{
lean_object* v___x_5892_; lean_object* v___x_5893_; lean_object* v___x_5894_; lean_object* v___x_5895_; lean_object* v___x_5896_; lean_object* v___x_5897_; lean_object* v___x_5898_; lean_object* v___x_5899_; lean_object* v___x_5900_; lean_object* v___x_5901_; lean_object* v___x_5902_; lean_object* v___x_5903_; lean_object* v___x_5904_; lean_object* v___x_5905_; 
lean_dec(v_prio_5865_);
v___x_5892_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5893_ = l_Lean_MessageData_ofConstName(v_declName_5864_, v___x_5891_);
v___x_5894_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5894_, 0, v___x_5892_);
lean_ctor_set(v___x_5894_, 1, v___x_5893_);
v___x_5895_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5896_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5896_, 0, v___x_5894_);
lean_ctor_set(v___x_5896_, 1, v___x_5895_);
lean_inc(v_declName_5874_);
v___x_5897_ = l_Lean_MessageData_ofName(v_declName_5874_);
v___x_5898_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5898_, 0, v___x_5896_);
lean_ctor_set(v___x_5898_, 1, v___x_5897_);
v___x_5899_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5900_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5900_, 0, v___x_5898_);
lean_ctor_set(v___x_5900_, 1, v___x_5899_);
v___x_5901_ = l_Lean_MessageData_ofConstName(v_declName_5874_, v___x_5891_);
v___x_5902_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5902_, 0, v___x_5900_);
lean_ctor_set(v___x_5902_, 1, v___x_5901_);
v___x_5903_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5904_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5904_, 0, v___x_5902_);
lean_ctor_set(v___x_5904_, 1, v___x_5903_);
v___x_5905_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5904_, v___y_5868_, v___y_5869_, v___y_5870_, v___y_5871_);
return v___x_5905_;
}
else
{
v___y_5876_ = v___y_5868_;
v___y_5877_ = v___y_5869_;
v___y_5878_ = v___y_5870_;
v___y_5879_ = v___y_5871_;
goto v___jp_5875_;
}
v___jp_5875_:
{
lean_object* v___x_5880_; lean_object* v_env_5881_; lean_object* v___x_5882_; lean_object* v_toEnvExtension_5883_; lean_object* v_asyncMode_5884_; lean_object* v___x_5885_; lean_object* v___x_5886_; lean_object* v___x_5887_; lean_object* v___x_5888_; 
v___x_5880_ = lean_st_ref_get(v___y_5879_);
v_env_5881_ = lean_ctor_get(v___x_5880_, 0);
lean_inc_ref(v_env_5881_);
lean_dec(v___x_5880_);
v___x_5882_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5883_ = lean_ctor_get(v___x_5882_, 0);
v_asyncMode_5884_ = lean_ctor_get(v_toEnvExtension_5883_, 2);
v___x_5885_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5885_, 0, v_declName_5874_);
lean_ctor_set(v___x_5885_, 1, v_declName_5864_);
lean_ctor_set(v___x_5885_, 2, v_prio_5865_);
v___x_5886_ = lean_box(0);
v___x_5887_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5882_, v_env_5881_, v___x_5885_, v_asyncMode_5884_, v___x_5886_);
v___x_5888_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5887_, v___y_5877_, v___y_5879_);
return v___x_5888_;
}
}
else
{
lean_object* v___x_5906_; uint8_t v___x_5907_; lean_object* v___x_5908_; lean_object* v___x_5909_; lean_object* v___x_5910_; lean_object* v___x_5911_; lean_object* v___x_5912_; 
lean_dec_ref(v___x_5873_);
lean_dec(v_prio_5865_);
v___x_5906_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5907_ = 0;
v___x_5908_ = l_Lean_MessageData_ofConstName(v_declName_5864_, v___x_5907_);
v___x_5909_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5909_, 0, v___x_5906_);
lean_ctor_set(v___x_5909_, 1, v___x_5908_);
v___x_5910_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5911_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5911_, 0, v___x_5909_);
lean_ctor_set(v___x_5911_, 1, v___x_5910_);
v___x_5912_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5911_, v___y_5868_, v___y_5869_, v___y_5870_, v___y_5871_);
return v___x_5912_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5913_, lean_object* v_prio_5914_, lean_object* v_x_5915_, lean_object* v_type_5916_, lean_object* v___y_5917_, lean_object* v___y_5918_, lean_object* v___y_5919_, lean_object* v___y_5920_, lean_object* v___y_5921_){
_start:
{
lean_object* v_res_5922_; 
v_res_5922_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5913_, v_prio_5914_, v_x_5915_, v_type_5916_, v___y_5917_, v___y_5918_, v___y_5919_, v___y_5920_);
lean_dec(v___y_5920_);
lean_dec_ref(v___y_5919_);
lean_dec(v___y_5918_);
lean_dec_ref(v___y_5917_);
lean_dec_ref(v_type_5916_);
lean_dec_ref(v_x_5915_);
return v_res_5922_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5923_, lean_object* v_prio_5924_, lean_object* v_a_5925_, lean_object* v_a_5926_, lean_object* v_a_5927_, lean_object* v_a_5928_){
_start:
{
lean_object* v___x_5930_; lean_object* v_env_5931_; uint8_t v___x_5932_; lean_object* v___x_5933_; 
v___x_5930_ = lean_st_ref_get(v_a_5928_);
v_env_5931_ = lean_ctor_get(v___x_5930_, 0);
lean_inc_ref(v_env_5931_);
lean_dec(v___x_5930_);
v___x_5932_ = 0;
lean_inc(v_declName_5923_);
v___x_5933_ = l_Lean_Environment_find_x3f(v_env_5931_, v_declName_5923_, v___x_5932_);
if (lean_obj_tag(v___x_5933_) == 0)
{
lean_object* v___x_5934_; lean_object* v___x_5935_; lean_object* v___x_5936_; lean_object* v___x_5937_; lean_object* v___x_5938_; lean_object* v___x_5939_; 
lean_dec(v_prio_5924_);
v___x_5934_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5935_ = l_Lean_MessageData_ofConstName(v_declName_5923_, v___x_5932_);
v___x_5936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5936_, 0, v___x_5934_);
lean_ctor_set(v___x_5936_, 1, v___x_5935_);
v___x_5937_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5938_, 0, v___x_5936_);
lean_ctor_set(v___x_5938_, 1, v___x_5937_);
v___x_5939_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5938_, v_a_5925_, v_a_5926_, v_a_5927_, v_a_5928_);
return v___x_5939_;
}
else
{
lean_object* v_val_5940_; lean_object* v___f_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; 
v_val_5940_ = lean_ctor_get(v___x_5933_, 0);
lean_inc(v_val_5940_);
lean_dec_ref_known(v___x_5933_, 1);
v___f_5941_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5941_, 0, v_declName_5923_);
lean_closure_set(v___f_5941_, 1, v_prio_5924_);
v___x_5942_ = l_Lean_ConstantInfo_type(v_val_5940_);
lean_dec(v_val_5940_);
v___x_5943_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5942_, v___f_5941_, v___x_5932_, v___x_5932_, v_a_5925_, v_a_5926_, v_a_5927_, v_a_5928_);
return v___x_5943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5944_, lean_object* v_prio_5945_, lean_object* v_a_5946_, lean_object* v_a_5947_, lean_object* v_a_5948_, lean_object* v_a_5949_, lean_object* v_a_5950_){
_start:
{
lean_object* v_res_5951_; 
v_res_5951_ = l_Lean_Meta_addDefaultInstance(v_declName_5944_, v_prio_5945_, v_a_5946_, v_a_5947_, v_a_5948_, v_a_5949_);
lean_dec(v_a_5949_);
lean_dec_ref(v_a_5948_);
lean_dec(v_a_5947_);
lean_dec_ref(v_a_5946_);
return v_res_5951_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5953_; lean_object* v___x_5954_; 
v___x_5953_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_5954_ = l_Lean_stringToMessageData(v___x_5953_);
return v___x_5954_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_5956_; lean_object* v___x_5957_; 
v___x_5956_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_5957_ = l_Lean_stringToMessageData(v___x_5956_);
return v___x_5957_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_5961_, uint8_t v_kind_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_){
_start:
{
lean_object* v___x_5966_; lean_object* v___x_5967_; lean_object* v___x_5968_; lean_object* v___x_5969_; lean_object* v___x_5970_; lean_object* v___y_5972_; 
v___x_5966_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_5967_ = l_Lean_MessageData_ofName(v_name_5961_);
v___x_5968_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5968_, 0, v___x_5966_);
lean_ctor_set(v___x_5968_, 1, v___x_5967_);
v___x_5969_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_5970_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5970_, 0, v___x_5968_);
lean_ctor_set(v___x_5970_, 1, v___x_5969_);
switch(v_kind_5962_)
{
case 0:
{
lean_object* v___x_5979_; 
v___x_5979_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_5972_ = v___x_5979_;
goto v___jp_5971_;
}
case 1:
{
lean_object* v___x_5980_; 
v___x_5980_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_5972_ = v___x_5980_;
goto v___jp_5971_;
}
default: 
{
lean_object* v___x_5981_; 
v___x_5981_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_5972_ = v___x_5981_;
goto v___jp_5971_;
}
}
v___jp_5971_:
{
lean_object* v___x_5973_; lean_object* v___x_5974_; lean_object* v___x_5975_; lean_object* v___x_5976_; lean_object* v___x_5977_; lean_object* v___x_5978_; 
lean_inc_ref(v___y_5972_);
v___x_5973_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_5973_, 0, v___y_5972_);
v___x_5974_ = l_Lean_MessageData_ofFormat(v___x_5973_);
v___x_5975_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5975_, 0, v___x_5970_);
lean_ctor_set(v___x_5975_, 1, v___x_5974_);
v___x_5976_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5977_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5977_, 0, v___x_5975_);
lean_ctor_set(v___x_5977_, 1, v___x_5976_);
v___x_5978_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_5977_, v___y_5963_, v___y_5964_);
return v___x_5978_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_5982_, lean_object* v_kind_5983_, lean_object* v___y_5984_, lean_object* v___y_5985_, lean_object* v___y_5986_){
_start:
{
uint8_t v_kind_boxed_5987_; lean_object* v_res_5988_; 
v_kind_boxed_5987_ = lean_unbox(v_kind_5983_);
v_res_5988_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_5982_, v_kind_boxed_5987_, v___y_5984_, v___y_5985_);
lean_dec(v___y_5985_);
lean_dec_ref(v___y_5984_);
return v_res_5988_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_5989_, lean_object* v___x_5990_, lean_object* v___x_5991_, lean_object* v_declName_5992_, lean_object* v_stx_5993_, uint8_t v_kind_5994_, lean_object* v___y_5995_, lean_object* v___y_5996_){
_start:
{
lean_object* v___x_5998_; lean_object* v___x_5999_; lean_object* v___x_6000_; 
v___x_5998_ = lean_unsigned_to_nat(1u);
v___x_5999_ = l_Lean_Syntax_getArg(v_stx_5993_, v___x_5998_);
v___x_6000_ = l_Lean_getAttrParamOptPrio(v___x_5999_, v___y_5995_, v___y_5996_);
if (lean_obj_tag(v___x_6000_) == 0)
{
lean_object* v_a_6001_; lean_object* v___y_6003_; lean_object* v___y_6004_; uint8_t v___x_6035_; uint8_t v___x_6036_; 
v_a_6001_ = lean_ctor_get(v___x_6000_, 0);
lean_inc(v_a_6001_);
lean_dec_ref_known(v___x_6000_, 1);
v___x_6035_ = 0;
v___x_6036_ = l_Lean_instBEqAttributeKind_beq(v_kind_5994_, v___x_6035_);
if (v___x_6036_ == 0)
{
lean_object* v___x_6037_; 
lean_dec(v_a_6001_);
lean_dec(v_declName_5992_);
lean_dec(v___x_5990_);
lean_dec(v___x_5989_);
v___x_6037_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_5991_, v_kind_5994_, v___y_5995_, v___y_5996_);
return v___x_6037_;
}
else
{
lean_dec(v___x_5991_);
v___y_6003_ = v___y_5995_;
v___y_6004_ = v___y_5996_;
goto v___jp_6002_;
}
v___jp_6002_:
{
uint8_t v___x_6005_; uint8_t v___x_6006_; lean_object* v___x_6007_; lean_object* v___x_6008_; lean_object* v___x_6009_; lean_object* v___x_6010_; lean_object* v___x_6011_; size_t v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___x_6017_; lean_object* v___x_6018_; lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; 
v___x_6005_ = 0;
v___x_6006_ = 1;
v___x_6007_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6008_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6009_ = lean_unsigned_to_nat(32u);
v___x_6010_ = lean_mk_empty_array_with_capacity(v___x_6009_);
v___x_6011_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_6012_ = ((size_t)5ULL);
lean_inc_n(v___x_5989_, 6);
v___x_6013_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6013_, 0, v___x_6011_);
lean_ctor_set(v___x_6013_, 1, v___x_6010_);
lean_ctor_set(v___x_6013_, 2, v___x_5989_);
lean_ctor_set(v___x_6013_, 3, v___x_5989_);
lean_ctor_set_usize(v___x_6013_, 4, v___x_6012_);
v___x_6014_ = lean_box(1);
lean_inc_ref(v___x_6013_);
v___x_6015_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6015_, 0, v___x_6008_);
lean_ctor_set(v___x_6015_, 1, v___x_6013_);
lean_ctor_set(v___x_6015_, 2, v___x_6014_);
v___x_6016_ = lean_mk_empty_array_with_capacity(v___x_5989_);
v___x_6017_ = lean_box(0);
lean_inc(v___x_5990_);
v___x_6018_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6018_, 0, v___x_6007_);
lean_ctor_set(v___x_6018_, 1, v___x_5990_);
lean_ctor_set(v___x_6018_, 2, v___x_6015_);
lean_ctor_set(v___x_6018_, 3, v___x_6016_);
lean_ctor_set(v___x_6018_, 4, v___x_6017_);
lean_ctor_set(v___x_6018_, 5, v___x_5989_);
lean_ctor_set(v___x_6018_, 6, v___x_6017_);
lean_ctor_set_uint8(v___x_6018_, sizeof(void*)*7, v___x_6005_);
lean_ctor_set_uint8(v___x_6018_, sizeof(void*)*7 + 1, v___x_6005_);
lean_ctor_set_uint8(v___x_6018_, sizeof(void*)*7 + 2, v___x_6005_);
lean_ctor_set_uint8(v___x_6018_, sizeof(void*)*7 + 3, v___x_6006_);
v___x_6019_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6019_, 0, v___x_5989_);
lean_ctor_set(v___x_6019_, 1, v___x_5989_);
lean_ctor_set(v___x_6019_, 2, v___x_5989_);
lean_ctor_set(v___x_6019_, 3, v___x_5989_);
lean_ctor_set(v___x_6019_, 4, v___x_6008_);
lean_ctor_set(v___x_6019_, 5, v___x_6008_);
lean_ctor_set(v___x_6019_, 6, v___x_6008_);
lean_ctor_set(v___x_6019_, 7, v___x_6008_);
lean_ctor_set(v___x_6019_, 8, v___x_6008_);
lean_ctor_set(v___x_6019_, 9, v___x_6008_);
v___x_6020_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6021_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6022_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6022_, 0, v___x_6019_);
lean_ctor_set(v___x_6022_, 1, v___x_6020_);
lean_ctor_set(v___x_6022_, 2, v___x_5990_);
lean_ctor_set(v___x_6022_, 3, v___x_6013_);
lean_ctor_set(v___x_6022_, 4, v___x_6021_);
v___x_6023_ = lean_st_mk_ref(v___x_6022_);
v___x_6024_ = l_Lean_Meta_addDefaultInstance(v_declName_5992_, v_a_6001_, v___x_6018_, v___x_6023_, v___y_6003_, v___y_6004_);
lean_dec_ref_known(v___x_6018_, 7);
if (lean_obj_tag(v___x_6024_) == 0)
{
lean_object* v___x_6026_; uint8_t v_isShared_6027_; uint8_t v_isSharedCheck_6033_; 
v_isSharedCheck_6033_ = !lean_is_exclusive(v___x_6024_);
if (v_isSharedCheck_6033_ == 0)
{
lean_object* v_unused_6034_; 
v_unused_6034_ = lean_ctor_get(v___x_6024_, 0);
lean_dec(v_unused_6034_);
v___x_6026_ = v___x_6024_;
v_isShared_6027_ = v_isSharedCheck_6033_;
goto v_resetjp_6025_;
}
else
{
lean_dec(v___x_6024_);
v___x_6026_ = lean_box(0);
v_isShared_6027_ = v_isSharedCheck_6033_;
goto v_resetjp_6025_;
}
v_resetjp_6025_:
{
lean_object* v___x_6028_; lean_object* v___x_6029_; lean_object* v___x_6031_; 
v___x_6028_ = lean_st_ref_get(v___x_6023_);
lean_dec(v___x_6023_);
lean_dec(v___x_6028_);
v___x_6029_ = lean_box(0);
if (v_isShared_6027_ == 0)
{
lean_ctor_set(v___x_6026_, 0, v___x_6029_);
v___x_6031_ = v___x_6026_;
goto v_reusejp_6030_;
}
else
{
lean_object* v_reuseFailAlloc_6032_; 
v_reuseFailAlloc_6032_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6032_, 0, v___x_6029_);
v___x_6031_ = v_reuseFailAlloc_6032_;
goto v_reusejp_6030_;
}
v_reusejp_6030_:
{
return v___x_6031_;
}
}
}
else
{
lean_dec(v___x_6023_);
return v___x_6024_;
}
}
}
else
{
lean_object* v_a_6038_; lean_object* v___x_6040_; uint8_t v_isShared_6041_; uint8_t v_isSharedCheck_6045_; 
lean_dec(v_declName_5992_);
lean_dec(v___x_5991_);
lean_dec(v___x_5990_);
lean_dec(v___x_5989_);
v_a_6038_ = lean_ctor_get(v___x_6000_, 0);
v_isSharedCheck_6045_ = !lean_is_exclusive(v___x_6000_);
if (v_isSharedCheck_6045_ == 0)
{
v___x_6040_ = v___x_6000_;
v_isShared_6041_ = v_isSharedCheck_6045_;
goto v_resetjp_6039_;
}
else
{
lean_inc(v_a_6038_);
lean_dec(v___x_6000_);
v___x_6040_ = lean_box(0);
v_isShared_6041_ = v_isSharedCheck_6045_;
goto v_resetjp_6039_;
}
v_resetjp_6039_:
{
lean_object* v___x_6043_; 
if (v_isShared_6041_ == 0)
{
v___x_6043_ = v___x_6040_;
goto v_reusejp_6042_;
}
else
{
lean_object* v_reuseFailAlloc_6044_; 
v_reuseFailAlloc_6044_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6044_, 0, v_a_6038_);
v___x_6043_ = v_reuseFailAlloc_6044_;
goto v_reusejp_6042_;
}
v_reusejp_6042_:
{
return v___x_6043_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6046_, lean_object* v___x_6047_, lean_object* v___x_6048_, lean_object* v_declName_6049_, lean_object* v_stx_6050_, lean_object* v_kind_6051_, lean_object* v___y_6052_, lean_object* v___y_6053_, lean_object* v___y_6054_){
_start:
{
uint8_t v_kind_boxed_6055_; lean_object* v_res_6056_; 
v_kind_boxed_6055_ = lean_unbox(v_kind_6051_);
v_res_6056_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6046_, v___x_6047_, v___x_6048_, v_declName_6049_, v_stx_6050_, v_kind_boxed_6055_, v___y_6052_, v___y_6053_);
lean_dec(v___y_6053_);
lean_dec_ref(v___y_6052_);
lean_dec(v_stx_6050_);
return v_res_6056_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6058_; lean_object* v___x_6059_; 
v___x_6058_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6059_ = l_Lean_stringToMessageData(v___x_6058_);
return v___x_6059_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6061_; lean_object* v___x_6062_; 
v___x_6061_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6062_ = l_Lean_stringToMessageData(v___x_6061_);
return v___x_6062_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6063_, lean_object* v_decl_6064_, lean_object* v___y_6065_, lean_object* v___y_6066_){
_start:
{
lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; lean_object* v___x_6071_; lean_object* v___x_6072_; lean_object* v___x_6073_; 
v___x_6068_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6069_ = l_Lean_MessageData_ofName(v___x_6063_);
v___x_6070_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6070_, 0, v___x_6068_);
lean_ctor_set(v___x_6070_, 1, v___x_6069_);
v___x_6071_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6072_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6072_, 0, v___x_6070_);
lean_ctor_set(v___x_6072_, 1, v___x_6071_);
v___x_6073_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6072_, v___y_6065_, v___y_6066_);
return v___x_6073_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6074_, lean_object* v_decl_6075_, lean_object* v___y_6076_, lean_object* v___y_6077_, lean_object* v___y_6078_){
_start:
{
lean_object* v_res_6079_; 
v_res_6079_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6074_, v_decl_6075_, v___y_6076_, v___y_6077_);
lean_dec(v___y_6077_);
lean_dec_ref(v___y_6076_);
lean_dec(v_decl_6075_);
return v_res_6079_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6112_; lean_object* v___x_6113_; lean_object* v___x_6114_; 
v___x_6112_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6113_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6114_ = l_Lean_registerBuiltinAttribute(v___x_6113_);
if (lean_obj_tag(v___x_6114_) == 0)
{
lean_object* v___x_6115_; uint8_t v___x_6116_; lean_object* v___x_6117_; 
lean_dec_ref_known(v___x_6114_, 1);
v___x_6115_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_6116_ = 0;
v___x_6117_ = l_Lean_registerTraceClass(v___x_6115_, v___x_6116_, v___x_6112_);
return v___x_6117_;
}
else
{
return v___x_6114_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_6118_){
_start:
{
lean_object* v_res_6119_; 
v_res_6119_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_6119_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_6120_, lean_object* v_name_6121_, uint8_t v_kind_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_){
_start:
{
lean_object* v___x_6126_; 
v___x_6126_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6121_, v_kind_6122_, v___y_6123_, v___y_6124_);
return v___x_6126_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_6127_, lean_object* v_name_6128_, lean_object* v_kind_6129_, lean_object* v___y_6130_, lean_object* v___y_6131_, lean_object* v___y_6132_){
_start:
{
uint8_t v_kind_boxed_6133_; lean_object* v_res_6134_; 
v_kind_boxed_6133_ = lean_unbox(v_kind_6129_);
v_res_6134_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_6127_, v_name_6128_, v_kind_boxed_6133_, v___y_6130_, v___y_6131_);
lean_dec(v___y_6131_);
lean_dec_ref(v___y_6130_);
return v_res_6134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_6135_, lean_object* v_toPure_6136_, lean_object* v_____do__lift_6137_){
_start:
{
lean_object* v___x_6138_; lean_object* v_toEnvExtension_6139_; lean_object* v_asyncMode_6140_; lean_object* v___x_6141_; lean_object* v___x_6142_; lean_object* v_priorities_6143_; lean_object* v___x_6144_; 
v___x_6138_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6139_ = lean_ctor_get(v___x_6138_, 0);
v_asyncMode_6140_ = lean_ctor_get(v_toEnvExtension_6139_, 2);
v___x_6141_ = lean_box(0);
v___x_6142_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6135_, v___x_6138_, v_____do__lift_6137_, v_asyncMode_6140_, v___x_6141_);
v_priorities_6143_ = lean_ctor_get(v___x_6142_, 1);
lean_inc(v_priorities_6143_);
lean_dec(v___x_6142_);
v___x_6144_ = lean_apply_2(v_toPure_6136_, lean_box(0), v_priorities_6143_);
return v___x_6144_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_6145_, lean_object* v_inst_6146_){
_start:
{
lean_object* v_toApplicative_6147_; lean_object* v_toBind_6148_; lean_object* v_getEnv_6149_; lean_object* v_toPure_6150_; lean_object* v___x_6151_; lean_object* v___f_6152_; lean_object* v___x_6153_; 
v_toApplicative_6147_ = lean_ctor_get(v_inst_6145_, 0);
lean_inc_ref(v_toApplicative_6147_);
v_toBind_6148_ = lean_ctor_get(v_inst_6145_, 1);
lean_inc(v_toBind_6148_);
lean_dec_ref(v_inst_6145_);
v_getEnv_6149_ = lean_ctor_get(v_inst_6146_, 0);
lean_inc(v_getEnv_6149_);
lean_dec_ref(v_inst_6146_);
v_toPure_6150_ = lean_ctor_get(v_toApplicative_6147_, 1);
lean_inc(v_toPure_6150_);
lean_dec_ref(v_toApplicative_6147_);
v___x_6151_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6152_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6152_, 0, v___x_6151_);
lean_closure_set(v___f_6152_, 1, v_toPure_6150_);
v___x_6153_ = lean_apply_4(v_toBind_6148_, lean_box(0), lean_box(0), v_getEnv_6149_, v___f_6152_);
return v___x_6153_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_6154_, lean_object* v_inst_6155_, lean_object* v_inst_6156_){
_start:
{
lean_object* v___x_6157_; 
v___x_6157_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_6155_, v_inst_6156_);
return v___x_6157_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_6158_, uint8_t v_isExporting_6159_, lean_object* v_x_6160_){
_start:
{
lean_object* v_fst_6161_; uint8_t v___x_6162_; 
v_fst_6161_ = lean_ctor_get(v_x_6160_, 0);
lean_inc(v_fst_6161_);
lean_dec_ref(v_x_6160_);
v___x_6162_ = l_Lean_Environment_contains(v_env_6158_, v_fst_6161_, v_isExporting_6159_);
return v___x_6162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_6163_, lean_object* v_isExporting_6164_, lean_object* v_x_6165_){
_start:
{
uint8_t v_isExporting_boxed_6166_; uint8_t v_res_6167_; lean_object* v_r_6168_; 
v_isExporting_boxed_6166_ = lean_unbox(v_isExporting_6164_);
v_res_6167_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_6163_, v_isExporting_boxed_6166_, v_x_6165_);
v_r_6168_ = lean_box(v_res_6167_);
return v_r_6168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_6169_, lean_object* v_toApplicative_6170_, lean_object* v_className_6171_, lean_object* v_env_6172_){
_start:
{
lean_object* v___y_6174_; lean_object* v___x_6184_; lean_object* v_toEnvExtension_6185_; lean_object* v_asyncMode_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v_defaultInstances_6189_; lean_object* v___x_6190_; 
v___x_6184_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6185_ = lean_ctor_get(v___x_6184_, 0);
v_asyncMode_6186_ = lean_ctor_get(v_toEnvExtension_6185_, 2);
v___x_6187_ = lean_box(0);
lean_inc_ref(v_env_6172_);
v___x_6188_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6169_, v___x_6184_, v_env_6172_, v_asyncMode_6186_, v___x_6187_);
v_defaultInstances_6189_ = lean_ctor_get(v___x_6188_, 0);
lean_inc(v_defaultInstances_6189_);
lean_dec(v___x_6188_);
v___x_6190_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_6189_, v_className_6171_);
lean_dec(v_defaultInstances_6189_);
if (lean_obj_tag(v___x_6190_) == 0)
{
lean_object* v___x_6191_; 
v___x_6191_ = lean_box(0);
v___y_6174_ = v___x_6191_;
goto v___jp_6173_;
}
else
{
lean_object* v_val_6192_; 
v_val_6192_ = lean_ctor_get(v___x_6190_, 0);
lean_inc(v_val_6192_);
lean_dec_ref_known(v___x_6190_, 1);
v___y_6174_ = v_val_6192_;
goto v___jp_6173_;
}
v___jp_6173_:
{
uint8_t v_isExporting_6175_; 
v_isExporting_6175_ = lean_ctor_get_uint8(v_env_6172_, sizeof(void*)*8);
if (v_isExporting_6175_ == 0)
{
lean_object* v_toPure_6176_; lean_object* v___x_6177_; 
lean_dec_ref(v_env_6172_);
v_toPure_6176_ = lean_ctor_get(v_toApplicative_6170_, 1);
lean_inc(v_toPure_6176_);
lean_dec_ref(v_toApplicative_6170_);
v___x_6177_ = lean_apply_2(v_toPure_6176_, lean_box(0), v___y_6174_);
return v___x_6177_;
}
else
{
lean_object* v_toPure_6178_; lean_object* v___x_6179_; lean_object* v___f_6180_; lean_object* v___x_6181_; lean_object* v___x_6182_; lean_object* v___x_6183_; 
v_toPure_6178_ = lean_ctor_get(v_toApplicative_6170_, 1);
lean_inc(v_toPure_6178_);
lean_dec_ref(v_toApplicative_6170_);
v___x_6179_ = lean_box(v_isExporting_6175_);
v___f_6180_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6180_, 0, v_env_6172_);
lean_closure_set(v___f_6180_, 1, v___x_6179_);
v___x_6181_ = lean_box(0);
v___x_6182_ = l_List_filterTR_loop___redArg(v___f_6180_, v___y_6174_, v___x_6181_);
v___x_6183_ = lean_apply_2(v_toPure_6178_, lean_box(0), v___x_6182_);
return v___x_6183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_6193_, lean_object* v_toApplicative_6194_, lean_object* v_className_6195_, lean_object* v_env_6196_){
_start:
{
lean_object* v_res_6197_; 
v_res_6197_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_6193_, v_toApplicative_6194_, v_className_6195_, v_env_6196_);
lean_dec(v_className_6195_);
return v_res_6197_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_6198_, lean_object* v_inst_6199_, lean_object* v_className_6200_){
_start:
{
lean_object* v_toApplicative_6201_; lean_object* v_toBind_6202_; lean_object* v_getEnv_6203_; lean_object* v___x_6204_; lean_object* v___f_6205_; lean_object* v___x_6206_; 
v_toApplicative_6201_ = lean_ctor_get(v_inst_6198_, 0);
lean_inc_ref(v_toApplicative_6201_);
v_toBind_6202_ = lean_ctor_get(v_inst_6198_, 1);
lean_inc(v_toBind_6202_);
lean_dec_ref(v_inst_6198_);
v_getEnv_6203_ = lean_ctor_get(v_inst_6199_, 0);
lean_inc(v_getEnv_6203_);
lean_dec_ref(v_inst_6199_);
v___x_6204_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6205_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_6205_, 0, v___x_6204_);
lean_closure_set(v___f_6205_, 1, v_toApplicative_6201_);
lean_closure_set(v___f_6205_, 2, v_className_6200_);
v___x_6206_ = lean_apply_4(v_toBind_6202_, lean_box(0), lean_box(0), v_getEnv_6203_, v___f_6205_);
return v___x_6206_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6207_, lean_object* v_inst_6208_, lean_object* v_inst_6209_, lean_object* v_className_6210_){
_start:
{
lean_object* v___x_6211_; 
v___x_6211_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6208_, v_inst_6209_, v_className_6210_);
return v___x_6211_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Instances(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
