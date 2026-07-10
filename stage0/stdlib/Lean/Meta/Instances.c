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
uint8_t lean_bool_not(uint8_t);
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
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Lean_Options_empty;
lean_object* l_Lean_MessageData_ofConstName(lean_object*, uint8_t);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* l_Lean_EnvironmentHeader_moduleNames(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
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
uint64_t l_Lean_Meta_Context_configKey(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_shift_left(uint64_t, uint64_t);
uint64_t l_Lean_Meta_TransparencyMode_toUInt64(uint8_t);
uint64_t lean_uint64_lor(uint64_t, uint64_t);
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
static const lean_ctor_object l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___closed__0 = (const lean_object*)&l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_string_object l_Lean_Meta_addInstance___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 89, .m_capacity = 89, .m_length = 88, .m_data = "` must be marked with `@[reducible]`, `@[instance_reducible]` or `@[implicit_reducible]`"};
static const lean_object* l_Lean_Meta_addInstance___closed__4 = (const lean_object*)&l_Lean_Meta_addInstance___closed__4_value;
static lean_once_cell_t l_Lean_Meta_addInstance___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_addInstance___closed__5;
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
size_t v_x_2105__boxed_266_; size_t v_x_2106__boxed_267_; lean_object* v_res_268_; 
v_x_2105__boxed_266_ = lean_unbox_usize(v_x_262_);
lean_dec(v_x_262_);
v_x_2106__boxed_267_ = lean_unbox_usize(v_x_263_);
lean_dec(v_x_263_);
v_res_268_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_261_, v_x_2105__boxed_266_, v_x_2106__boxed_267_, v_x_264_, v_x_265_);
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
size_t v_x_2391__boxed_447_; size_t v_x_2392__boxed_448_; lean_object* v_res_449_; 
v_x_2391__boxed_447_ = lean_unbox_usize(v_x_443_);
lean_dec(v_x_443_);
v_x_2392__boxed_448_ = lean_unbox_usize(v_x_444_);
lean_dec(v_x_444_);
v_res_449_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_x_442_, v_x_2391__boxed_447_, v_x_2392__boxed_448_, v_x_445_, v_x_446_);
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
uint8_t v___x_547_; uint8_t v___x_548_; 
v___x_547_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v___x_545_, v_k_541_);
v___x_548_ = lean_bool_not(v___x_547_);
if (v___x_548_ == 0)
{
lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; uint8_t v___x_552_; 
v___x_549_ = lean_unsigned_to_nat(1u);
v___x_550_ = lean_nat_sub(v___x_542_, v___x_549_);
v___x_551_ = lean_array_fget_borrowed(v_as_540_, v___x_550_);
v___x_552_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v___x_551_, v_k_541_);
if (v___x_552_ == 0)
{
uint8_t v___x_553_; uint8_t v___x_554_; 
v___x_553_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__1(v_k_541_, v___x_551_);
v___x_554_ = lean_bool_not(v___x_553_);
if (v___x_554_ == 0)
{
lean_object* v___x_555_; 
v___x_555_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_536_, v_keys_537_, v_v_538_, v_k_539_, v_as_540_, v_k_541_, v___x_543_, v___x_550_);
return v___x_555_;
}
else
{
uint8_t v___x_556_; 
v___x_556_ = lean_nat_dec_lt(v___x_550_, v___x_542_);
if (v___x_556_ == 0)
{
lean_dec(v___x_550_);
lean_dec(v_k_539_);
lean_dec_ref(v_v_538_);
return v_as_540_;
}
else
{
lean_object* v___x_557_; lean_object* v_xs_x27_558_; lean_object* v___x_559_; lean_object* v___x_560_; 
lean_inc(v___x_551_);
v___x_557_ = lean_box(0);
v_xs_x27_558_ = lean_array_fset(v_as_540_, v___x_550_, v___x_557_);
v___x_559_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_536_, v_keys_537_, v_v_538_, v_k_539_, v___x_551_);
v___x_560_ = lean_array_fset(v_xs_x27_558_, v___x_550_, v___x_559_);
lean_dec(v___x_550_);
return v___x_560_;
}
}
}
else
{
lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; 
lean_dec(v___x_550_);
v___x_561_ = lean_box(0);
v___x_562_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_536_, v_keys_537_, v_v_538_, v_k_539_, v___x_561_);
v___x_563_ = lean_array_push(v_as_540_, v___x_562_);
return v___x_563_;
}
}
else
{
uint8_t v___x_564_; 
v___x_564_ = lean_nat_dec_lt(v___x_543_, v___x_542_);
if (v___x_564_ == 0)
{
lean_dec(v_k_539_);
lean_dec_ref(v_v_538_);
return v_as_540_;
}
else
{
lean_object* v___x_565_; lean_object* v_xs_x27_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
lean_inc(v___x_545_);
v___x_565_ = lean_box(0);
v_xs_x27_566_ = lean_array_fset(v_as_540_, v___x_543_, v___x_565_);
v___x_567_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_536_, v_keys_537_, v_v_538_, v_k_539_, v___x_545_);
v___x_568_ = lean_array_fset(v_xs_x27_566_, v___x_543_, v___x_567_);
return v___x_568_;
}
}
}
else
{
lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v_as_571_; lean_object* v___x_572_; 
v___x_569_ = lean_box(0);
v___x_570_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_536_, v_keys_537_, v_v_538_, v_k_539_, v___x_569_);
v_as_571_ = lean_array_push(v_as_540_, v___x_570_);
v___x_572_ = l___private_Init_Data_Array_Basic_0__Array_insertIdx_loop(lean_box(0), v___x_543_, v_as_571_, v___x_542_);
return v___x_572_;
}
}
else
{
lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_573_ = lean_box(0);
v___x_574_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__0(v_x_536_, v_keys_537_, v_v_538_, v_k_539_, v___x_573_);
v___x_575_ = lean_array_push(v_as_540_, v___x_574_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(lean_object* v_keys_576_, lean_object* v_v_577_, lean_object* v_x_578_, lean_object* v_x_579_){
_start:
{
lean_object* v_vs_580_; lean_object* v_children_581_; lean_object* v___x_583_; uint8_t v_isShared_584_; uint8_t v_isSharedCheck_598_; 
v_vs_580_ = lean_ctor_get(v_x_579_, 0);
v_children_581_ = lean_ctor_get(v_x_579_, 1);
v_isSharedCheck_598_ = !lean_is_exclusive(v_x_579_);
if (v_isSharedCheck_598_ == 0)
{
v___x_583_ = v_x_579_;
v_isShared_584_ = v_isSharedCheck_598_;
goto v_resetjp_582_;
}
else
{
lean_inc(v_children_581_);
lean_inc(v_vs_580_);
lean_dec(v_x_579_);
v___x_583_ = lean_box(0);
v_isShared_584_ = v_isSharedCheck_598_;
goto v_resetjp_582_;
}
v_resetjp_582_:
{
lean_object* v___x_585_; uint8_t v___x_586_; 
v___x_585_ = lean_array_get_size(v_keys_576_);
v___x_586_ = lean_nat_dec_lt(v_x_578_, v___x_585_);
if (v___x_586_ == 0)
{
lean_object* v___x_587_; lean_object* v___x_589_; 
v___x_587_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertVal___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__1(v_vs_580_, v_v_577_);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 0, v___x_587_);
v___x_589_ = v___x_583_;
goto v_reusejp_588_;
}
else
{
lean_object* v_reuseFailAlloc_590_; 
v_reuseFailAlloc_590_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_590_, 0, v___x_587_);
lean_ctor_set(v_reuseFailAlloc_590_, 1, v_children_581_);
v___x_589_ = v_reuseFailAlloc_590_;
goto v_reusejp_588_;
}
v_reusejp_588_:
{
return v___x_589_;
}
}
else
{
lean_object* v_k_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v_c_594_; lean_object* v___x_596_; 
v_k_591_ = lean_array_fget_borrowed(v_keys_576_, v_x_578_);
v___x_592_ = ((lean_object*)(l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___closed__1));
lean_inc_n(v_k_591_, 2);
v___x_593_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_593_, 0, v_k_591_);
lean_ctor_set(v___x_593_, 1, v___x_592_);
v_c_594_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(v_x_578_, v_keys_576_, v_v_577_, v_k_591_, v_children_581_, v___x_593_);
lean_dec_ref_known(v___x_593_, 2);
if (v_isShared_584_ == 0)
{
lean_ctor_set(v___x_583_, 1, v_c_594_);
v___x_596_ = v___x_583_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_vs_580_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_c_594_);
v___x_596_ = v_reuseFailAlloc_597_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
return v___x_596_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(lean_object* v_x_599_, lean_object* v_keys_600_, lean_object* v_v_601_, lean_object* v_k_602_, lean_object* v_x_603_){
_start:
{
lean_object* v_snd_604_; lean_object* v___x_606_; uint8_t v_isShared_607_; uint8_t v_isSharedCheck_614_; 
v_snd_604_ = lean_ctor_get(v_x_603_, 1);
v_isSharedCheck_614_ = !lean_is_exclusive(v_x_603_);
if (v_isSharedCheck_614_ == 0)
{
lean_object* v_unused_615_; 
v_unused_615_ = lean_ctor_get(v_x_603_, 0);
lean_dec(v_unused_615_);
v___x_606_ = v_x_603_;
v_isShared_607_ = v_isSharedCheck_614_;
goto v_resetjp_605_;
}
else
{
lean_inc(v_snd_604_);
lean_dec(v_x_603_);
v___x_606_ = lean_box(0);
v_isShared_607_ = v_isSharedCheck_614_;
goto v_resetjp_605_;
}
v_resetjp_605_:
{
lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v_c_610_; lean_object* v___x_612_; 
v___x_608_ = lean_unsigned_to_nat(1u);
v___x_609_ = lean_nat_add(v_x_599_, v___x_608_);
v_c_610_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_600_, v_v_601_, v___x_609_, v_snd_604_);
lean_dec(v___x_609_);
if (v_isShared_607_ == 0)
{
lean_ctor_set(v___x_606_, 1, v_c_610_);
lean_ctor_set(v___x_606_, 0, v_k_602_);
v___x_612_ = v___x_606_;
goto v_reusejp_611_;
}
else
{
lean_object* v_reuseFailAlloc_613_; 
v_reuseFailAlloc_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_613_, 0, v_k_602_);
lean_ctor_set(v_reuseFailAlloc_613_, 1, v_c_610_);
v___x_612_ = v_reuseFailAlloc_613_;
goto v_reusejp_611_;
}
v_reusejp_611_:
{
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2___boxed(lean_object* v_x_616_, lean_object* v_keys_617_, lean_object* v_v_618_, lean_object* v_k_619_, lean_object* v_x_620_){
_start:
{
lean_object* v_res_621_; 
v_res_621_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___lam__2(v_x_616_, v_keys_617_, v_v_618_, v_k_619_, v_x_620_);
lean_dec_ref(v_keys_617_);
lean_dec(v_x_616_);
return v_res_621_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0___boxed(lean_object* v_keys_622_, lean_object* v_v_623_, lean_object* v_x_624_, lean_object* v_x_625_){
_start:
{
lean_object* v_res_626_; 
v_res_626_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_622_, v_v_623_, v_x_624_, v_x_625_);
lean_dec(v_x_624_);
lean_dec_ref(v_keys_622_);
return v_res_626_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg___boxed(lean_object* v_x_627_, lean_object* v_keys_628_, lean_object* v_v_629_, lean_object* v_k_630_, lean_object* v_as_631_, lean_object* v_k_632_, lean_object* v_x_633_, lean_object* v_x_634_){
_start:
{
lean_object* v_res_635_; 
v_res_635_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_627_, v_keys_628_, v_v_629_, v_k_630_, v_as_631_, v_k_632_, v_x_633_, v_x_634_);
lean_dec_ref(v_k_632_);
lean_dec_ref(v_keys_628_);
lean_dec(v_x_627_);
return v_res_635_;
}
}
LEAN_EXPORT lean_object* l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2___boxed(lean_object* v_x_636_, lean_object* v_keys_637_, lean_object* v_v_638_, lean_object* v_k_639_, lean_object* v_as_640_, lean_object* v_k_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2(v_x_636_, v_keys_637_, v_v_638_, v_k_639_, v_as_640_, v_k_641_);
lean_dec_ref(v_k_641_);
lean_dec_ref(v_keys_637_);
lean_dec(v_x_636_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(lean_object* v_keys_643_, lean_object* v_v_644_, lean_object* v_x_645_){
_start:
{
if (lean_obj_tag(v_x_645_) == 0)
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; 
v___x_646_ = lean_unsigned_to_nat(1u);
v___x_647_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_createNodes(lean_box(0), v_keys_643_, v_v_644_, v___x_646_);
v___x_648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_648_, 0, v___x_647_);
return v___x_648_;
}
else
{
lean_object* v_val_649_; lean_object* v___x_651_; uint8_t v_isShared_652_; uint8_t v_isSharedCheck_658_; 
v_val_649_ = lean_ctor_get(v_x_645_, 0);
v_isSharedCheck_658_ = !lean_is_exclusive(v_x_645_);
if (v_isSharedCheck_658_ == 0)
{
v___x_651_ = v_x_645_;
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
else
{
lean_inc(v_val_649_);
lean_dec(v_x_645_);
v___x_651_ = lean_box(0);
v_isShared_652_ = v_isSharedCheck_658_;
goto v_resetjp_650_;
}
v_resetjp_650_:
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_656_; 
v___x_653_ = lean_unsigned_to_nat(1u);
v___x_654_ = l___private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0(v_keys_643_, v_v_644_, v___x_653_, v_val_649_);
if (v_isShared_652_ == 0)
{
lean_ctor_set(v___x_651_, 0, v___x_654_);
v___x_656_ = v___x_651_;
goto v_reusejp_655_;
}
else
{
lean_object* v_reuseFailAlloc_657_; 
v_reuseFailAlloc_657_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_657_, 0, v___x_654_);
v___x_656_ = v_reuseFailAlloc_657_;
goto v_reusejp_655_;
}
v_reusejp_655_:
{
return v___x_656_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0___boxed(lean_object* v_keys_659_, lean_object* v_v_660_, lean_object* v_x_661_){
_start:
{
lean_object* v_res_662_; 
v_res_662_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_659_, v_v_660_, v_x_661_);
lean_dec_ref(v_keys_659_);
return v_res_662_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(lean_object* v_keys_663_, lean_object* v_v_664_, lean_object* v_x_665_, size_t v_x_666_, size_t v_x_667_, lean_object* v_x_668_){
_start:
{
if (lean_obj_tag(v_x_665_) == 0)
{
lean_object* v_es_669_; size_t v___x_670_; size_t v___x_671_; lean_object* v_j_672_; lean_object* v___x_673_; uint8_t v___x_674_; 
v_es_669_ = lean_ctor_get(v_x_665_, 0);
v___x_670_ = ((size_t)31ULL);
v___x_671_ = lean_usize_land(v_x_666_, v___x_670_);
v_j_672_ = lean_usize_to_nat(v___x_671_);
v___x_673_ = lean_array_get_size(v_es_669_);
v___x_674_ = lean_nat_dec_lt(v_j_672_, v___x_673_);
if (v___x_674_ == 0)
{
lean_dec(v_j_672_);
lean_dec(v_x_668_);
lean_dec_ref(v_v_664_);
return v_x_665_;
}
else
{
lean_object* v___x_676_; uint8_t v_isShared_677_; uint8_t v_isSharedCheck_742_; 
lean_inc_ref(v_es_669_);
v_isSharedCheck_742_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_742_ == 0)
{
lean_object* v_unused_743_; 
v_unused_743_ = lean_ctor_get(v_x_665_, 0);
lean_dec(v_unused_743_);
v___x_676_ = v_x_665_;
v_isShared_677_ = v_isSharedCheck_742_;
goto v_resetjp_675_;
}
else
{
lean_dec(v_x_665_);
v___x_676_ = lean_box(0);
v_isShared_677_ = v_isSharedCheck_742_;
goto v_resetjp_675_;
}
v_resetjp_675_:
{
lean_object* v_v_678_; lean_object* v___x_679_; lean_object* v_xs_x27_680_; lean_object* v___y_682_; 
v_v_678_ = lean_array_fget(v_es_669_, v_j_672_);
v___x_679_ = lean_box(0);
v_xs_x27_680_ = lean_array_fset(v_es_669_, v_j_672_, v___x_679_);
switch(lean_obj_tag(v_v_678_))
{
case 0:
{
lean_object* v_key_687_; lean_object* v_val_688_; uint8_t v___x_689_; 
v_key_687_ = lean_ctor_get(v_v_678_, 0);
v_val_688_ = lean_ctor_get(v_v_678_, 1);
v___x_689_ = l_Lean_Meta_DiscrTree_instBEqKey_beq(v_x_668_, v_key_687_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; lean_object* v___x_691_; 
v___x_690_ = lean_box(0);
v___x_691_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_663_, v_v_664_, v___x_690_);
if (lean_obj_tag(v___x_691_) == 0)
{
lean_dec(v_x_668_);
v___y_682_ = v_v_678_;
goto v___jp_681_;
}
else
{
lean_object* v_val_692_; lean_object* v___x_694_; uint8_t v_isShared_695_; uint8_t v_isSharedCheck_700_; 
lean_inc(v_val_688_);
lean_inc(v_key_687_);
lean_dec_ref_known(v_v_678_, 2);
v_val_692_ = lean_ctor_get(v___x_691_, 0);
v_isSharedCheck_700_ = !lean_is_exclusive(v___x_691_);
if (v_isSharedCheck_700_ == 0)
{
v___x_694_ = v___x_691_;
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
else
{
lean_inc(v_val_692_);
lean_dec(v___x_691_);
v___x_694_ = lean_box(0);
v_isShared_695_ = v_isSharedCheck_700_;
goto v_resetjp_693_;
}
v_resetjp_693_:
{
lean_object* v___x_696_; lean_object* v___x_698_; 
v___x_696_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_687_, v_val_688_, v_x_668_, v_val_692_);
if (v_isShared_695_ == 0)
{
lean_ctor_set(v___x_694_, 0, v___x_696_);
v___x_698_ = v___x_694_;
goto v_reusejp_697_;
}
else
{
lean_object* v_reuseFailAlloc_699_; 
v_reuseFailAlloc_699_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_699_, 0, v___x_696_);
v___x_698_ = v_reuseFailAlloc_699_;
goto v_reusejp_697_;
}
v_reusejp_697_:
{
v___y_682_ = v___x_698_;
goto v___jp_681_;
}
}
}
}
else
{
lean_object* v___x_702_; uint8_t v_isShared_703_; uint8_t v_isSharedCheck_711_; 
lean_inc(v_val_688_);
v_isSharedCheck_711_ = !lean_is_exclusive(v_v_678_);
if (v_isSharedCheck_711_ == 0)
{
lean_object* v_unused_712_; lean_object* v_unused_713_; 
v_unused_712_ = lean_ctor_get(v_v_678_, 1);
lean_dec(v_unused_712_);
v_unused_713_ = lean_ctor_get(v_v_678_, 0);
lean_dec(v_unused_713_);
v___x_702_ = v_v_678_;
v_isShared_703_ = v_isSharedCheck_711_;
goto v_resetjp_701_;
}
else
{
lean_dec(v_v_678_);
v___x_702_ = lean_box(0);
v_isShared_703_ = v_isSharedCheck_711_;
goto v_resetjp_701_;
}
v_resetjp_701_:
{
lean_object* v___x_704_; lean_object* v___x_705_; 
v___x_704_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_704_, 0, v_val_688_);
v___x_705_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_663_, v_v_664_, v___x_704_);
if (lean_obj_tag(v___x_705_) == 0)
{
lean_object* v___x_706_; 
lean_del_object(v___x_702_);
lean_dec(v_x_668_);
v___x_706_ = lean_box(2);
v___y_682_ = v___x_706_;
goto v___jp_681_;
}
else
{
lean_object* v_val_707_; lean_object* v___x_709_; 
v_val_707_ = lean_ctor_get(v___x_705_, 0);
lean_inc(v_val_707_);
lean_dec_ref_known(v___x_705_, 1);
if (v_isShared_703_ == 0)
{
lean_ctor_set(v___x_702_, 1, v_val_707_);
lean_ctor_set(v___x_702_, 0, v_x_668_);
v___x_709_ = v___x_702_;
goto v_reusejp_708_;
}
else
{
lean_object* v_reuseFailAlloc_710_; 
v_reuseFailAlloc_710_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_710_, 0, v_x_668_);
lean_ctor_set(v_reuseFailAlloc_710_, 1, v_val_707_);
v___x_709_ = v_reuseFailAlloc_710_;
goto v_reusejp_708_;
}
v_reusejp_708_:
{
v___y_682_ = v___x_709_;
goto v___jp_681_;
}
}
}
}
}
case 1:
{
lean_object* v_node_714_; lean_object* v___x_716_; uint8_t v_isShared_717_; uint8_t v_isSharedCheck_737_; 
v_node_714_ = lean_ctor_get(v_v_678_, 0);
v_isSharedCheck_737_ = !lean_is_exclusive(v_v_678_);
if (v_isSharedCheck_737_ == 0)
{
v___x_716_ = v_v_678_;
v_isShared_717_ = v_isSharedCheck_737_;
goto v_resetjp_715_;
}
else
{
lean_inc(v_node_714_);
lean_dec(v_v_678_);
v___x_716_ = lean_box(0);
v_isShared_717_ = v_isSharedCheck_737_;
goto v_resetjp_715_;
}
v_resetjp_715_:
{
size_t v___x_718_; size_t v___x_719_; size_t v___x_720_; size_t v___x_721_; lean_object* v_newNode_722_; lean_object* v___x_723_; 
v___x_718_ = ((size_t)5ULL);
v___x_719_ = lean_usize_shift_right(v_x_666_, v___x_718_);
v___x_720_ = ((size_t)1ULL);
v___x_721_ = lean_usize_add(v_x_667_, v___x_720_);
v_newNode_722_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_663_, v_v_664_, v_node_714_, v___x_719_, v___x_721_, v_x_668_);
lean_inc_ref(v_newNode_722_);
v___x_723_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_722_);
if (lean_obj_tag(v___x_723_) == 0)
{
lean_object* v___x_725_; 
if (v_isShared_717_ == 0)
{
lean_ctor_set(v___x_716_, 0, v_newNode_722_);
v___x_725_ = v___x_716_;
goto v_reusejp_724_;
}
else
{
lean_object* v_reuseFailAlloc_726_; 
v_reuseFailAlloc_726_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_726_, 0, v_newNode_722_);
v___x_725_ = v_reuseFailAlloc_726_;
goto v_reusejp_724_;
}
v_reusejp_724_:
{
v___y_682_ = v___x_725_;
goto v___jp_681_;
}
}
else
{
lean_object* v_val_727_; lean_object* v_fst_728_; lean_object* v_snd_729_; lean_object* v___x_731_; uint8_t v_isShared_732_; uint8_t v_isSharedCheck_736_; 
lean_dec_ref(v_newNode_722_);
lean_del_object(v___x_716_);
v_val_727_ = lean_ctor_get(v___x_723_, 0);
lean_inc(v_val_727_);
lean_dec_ref_known(v___x_723_, 1);
v_fst_728_ = lean_ctor_get(v_val_727_, 0);
v_snd_729_ = lean_ctor_get(v_val_727_, 1);
v_isSharedCheck_736_ = !lean_is_exclusive(v_val_727_);
if (v_isSharedCheck_736_ == 0)
{
v___x_731_ = v_val_727_;
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
else
{
lean_inc(v_snd_729_);
lean_inc(v_fst_728_);
lean_dec(v_val_727_);
v___x_731_ = lean_box(0);
v_isShared_732_ = v_isSharedCheck_736_;
goto v_resetjp_730_;
}
v_resetjp_730_:
{
lean_object* v___x_734_; 
if (v_isShared_732_ == 0)
{
v___x_734_ = v___x_731_;
goto v_reusejp_733_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v_fst_728_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_snd_729_);
v___x_734_ = v_reuseFailAlloc_735_;
goto v_reusejp_733_;
}
v_reusejp_733_:
{
v___y_682_ = v___x_734_;
goto v___jp_681_;
}
}
}
}
}
default: 
{
lean_object* v___x_738_; lean_object* v___x_739_; 
v___x_738_ = lean_box(0);
v___x_739_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_663_, v_v_664_, v___x_738_);
if (lean_obj_tag(v___x_739_) == 0)
{
lean_dec(v_x_668_);
v___y_682_ = v_v_678_;
goto v___jp_681_;
}
else
{
lean_object* v_val_740_; lean_object* v___x_741_; 
v_val_740_ = lean_ctor_get(v___x_739_, 0);
lean_inc(v_val_740_);
lean_dec_ref_known(v___x_739_, 1);
v___x_741_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_741_, 0, v_x_668_);
lean_ctor_set(v___x_741_, 1, v_val_740_);
v___y_682_ = v___x_741_;
goto v___jp_681_;
}
}
}
v___jp_681_:
{
lean_object* v___x_683_; lean_object* v___x_685_; 
v___x_683_ = lean_array_fset(v_xs_x27_680_, v_j_672_, v___y_682_);
lean_dec(v_j_672_);
if (v_isShared_677_ == 0)
{
lean_ctor_set(v___x_676_, 0, v___x_683_);
v___x_685_ = v___x_676_;
goto v_reusejp_684_;
}
else
{
lean_object* v_reuseFailAlloc_686_; 
v_reuseFailAlloc_686_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_686_, 0, v___x_683_);
v___x_685_ = v_reuseFailAlloc_686_;
goto v_reusejp_684_;
}
v_reusejp_684_:
{
return v___x_685_;
}
}
}
}
}
else
{
lean_object* v_ks_744_; lean_object* v_vs_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_778_; 
v_ks_744_ = lean_ctor_get(v_x_665_, 0);
v_vs_745_ = lean_ctor_get(v_x_665_, 1);
v_isSharedCheck_778_ = !lean_is_exclusive(v_x_665_);
if (v_isSharedCheck_778_ == 0)
{
v___x_747_ = v_x_665_;
v_isShared_748_ = v_isSharedCheck_778_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_vs_745_);
lean_inc(v_ks_744_);
lean_dec(v_x_665_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_778_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v___x_749_; 
v___x_749_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__4(v_ks_744_, v_x_668_);
if (lean_obj_tag(v___x_749_) == 0)
{
lean_object* v___x_751_; 
if (v_isShared_748_ == 0)
{
v___x_751_ = v___x_747_;
goto v_reusejp_750_;
}
else
{
lean_object* v_reuseFailAlloc_756_; 
v_reuseFailAlloc_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_756_, 0, v_ks_744_);
lean_ctor_set(v_reuseFailAlloc_756_, 1, v_vs_745_);
v___x_751_ = v_reuseFailAlloc_756_;
goto v_reusejp_750_;
}
v_reusejp_750_:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = lean_box(0);
v___x_753_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_663_, v_v_664_, v___x_752_);
if (lean_obj_tag(v___x_753_) == 0)
{
lean_dec(v_x_668_);
return v___x_751_;
}
else
{
lean_object* v_val_754_; lean_object* v___x_755_; 
v_val_754_ = lean_ctor_get(v___x_753_, 0);
lean_inc(v_val_754_);
lean_dec_ref_known(v___x_753_, 1);
v___x_755_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v___x_751_, v_x_666_, v_x_667_, v_x_668_, v_val_754_);
return v___x_755_;
}
}
}
else
{
lean_object* v_val_757_; lean_object* v___x_759_; uint8_t v_isShared_760_; uint8_t v_isSharedCheck_777_; 
v_val_757_ = lean_ctor_get(v___x_749_, 0);
v_isSharedCheck_777_ = !lean_is_exclusive(v___x_749_);
if (v_isSharedCheck_777_ == 0)
{
v___x_759_ = v___x_749_;
v_isShared_760_ = v_isSharedCheck_777_;
goto v_resetjp_758_;
}
else
{
lean_inc(v_val_757_);
lean_dec(v___x_749_);
v___x_759_ = lean_box(0);
v_isShared_760_ = v_isSharedCheck_777_;
goto v_resetjp_758_;
}
v_resetjp_758_:
{
lean_object* v_v_x27_761_; lean_object* v_keys_762_; lean_object* v_vals_763_; lean_object* v___x_765_; 
v_v_x27_761_ = lean_array_fget(v_vs_745_, v_val_757_);
lean_inc(v_val_757_);
v_keys_762_ = l_Array_eraseIdx___redArg(v_ks_744_, v_val_757_);
v_vals_763_ = l_Array_eraseIdx___redArg(v_vs_745_, v_val_757_);
if (v_isShared_760_ == 0)
{
lean_ctor_set(v___x_759_, 0, v_v_x27_761_);
v___x_765_ = v___x_759_;
goto v_reusejp_764_;
}
else
{
lean_object* v_reuseFailAlloc_776_; 
v_reuseFailAlloc_776_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_776_, 0, v_v_x27_761_);
v___x_765_ = v_reuseFailAlloc_776_;
goto v_reusejp_764_;
}
v_reusejp_764_:
{
lean_object* v___x_766_; 
v___x_766_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___lam__0(v_keys_663_, v_v_664_, v___x_765_);
if (lean_obj_tag(v___x_766_) == 0)
{
lean_object* v___x_768_; 
lean_dec(v_x_668_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v_vals_763_);
lean_ctor_set(v___x_747_, 0, v_keys_762_);
v___x_768_ = v___x_747_;
goto v_reusejp_767_;
}
else
{
lean_object* v_reuseFailAlloc_769_; 
v_reuseFailAlloc_769_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_769_, 0, v_keys_762_);
lean_ctor_set(v_reuseFailAlloc_769_, 1, v_vals_763_);
v___x_768_ = v_reuseFailAlloc_769_;
goto v_reusejp_767_;
}
v_reusejp_767_:
{
return v___x_768_;
}
}
else
{
lean_object* v_val_770_; lean_object* v_keys_771_; lean_object* v_vals_772_; lean_object* v___x_774_; 
v_val_770_ = lean_ctor_get(v___x_766_, 0);
lean_inc(v_val_770_);
lean_dec_ref_known(v___x_766_, 1);
v_keys_771_ = lean_array_push(v_keys_762_, v_x_668_);
v_vals_772_ = lean_array_push(v_vals_763_, v_val_770_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 1, v_vals_772_);
lean_ctor_set(v___x_747_, 0, v_keys_771_);
v___x_774_ = v___x_747_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_775_; 
v_reuseFailAlloc_775_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_775_, 0, v_keys_771_);
lean_ctor_set(v_reuseFailAlloc_775_, 1, v_vals_772_);
v___x_774_ = v_reuseFailAlloc_775_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
return v___x_774_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1___boxed(lean_object* v_keys_779_, lean_object* v_v_780_, lean_object* v_x_781_, lean_object* v_x_782_, lean_object* v_x_783_, lean_object* v_x_784_){
_start:
{
size_t v_x_2820__boxed_785_; size_t v_x_2821__boxed_786_; lean_object* v_res_787_; 
v_x_2820__boxed_785_ = lean_unbox_usize(v_x_782_);
lean_dec(v_x_782_);
v_x_2821__boxed_786_ = lean_unbox_usize(v_x_783_);
lean_dec(v_x_783_);
v_res_787_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_779_, v_v_780_, v_x_781_, v_x_2820__boxed_785_, v_x_2821__boxed_786_, v_x_784_);
lean_dec_ref(v_keys_779_);
return v_res_787_;
}
}
static lean_object* _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3(void){
_start:
{
lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; 
v___x_791_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__2));
v___x_792_ = lean_unsigned_to_nat(23u);
v___x_793_ = lean_unsigned_to_nat(166u);
v___x_794_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__1));
v___x_795_ = ((lean_object*)(l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__0));
v___x_796_ = l_mkPanicMessageWithDecl(v___x_795_, v___x_794_, v___x_793_, v___x_792_, v___x_791_);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(lean_object* v_d_797_, lean_object* v_keys_798_, lean_object* v_v_799_){
_start:
{
lean_object* v___x_800_; lean_object* v___x_801_; uint8_t v___x_802_; 
v___x_800_ = lean_array_get_size(v_keys_798_);
v___x_801_ = lean_unsigned_to_nat(0u);
v___x_802_ = lean_nat_dec_eq(v___x_800_, v___x_801_);
if (v___x_802_ == 0)
{
lean_object* v___x_803_; lean_object* v_k_804_; uint64_t v___x_805_; size_t v_h_806_; size_t v___x_807_; lean_object* v___x_808_; 
v___x_803_ = lean_box(0);
v_k_804_ = lean_array_get_borrowed(v___x_803_, v_keys_798_, v___x_801_);
v___x_805_ = l_Lean_Meta_DiscrTree_Key_hash(v_k_804_);
v_h_806_ = lean_uint64_to_usize(v___x_805_);
v___x_807_ = ((size_t)1ULL);
lean_inc(v_k_804_);
v___x_808_ = l_Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1(v_keys_798_, v_v_799_, v_d_797_, v_h_806_, v___x_807_, v_k_804_);
return v___x_808_;
}
else
{
lean_object* v___x_809_; lean_object* v___x_810_; 
lean_dec_ref(v_v_799_);
lean_dec_ref(v_d_797_);
v___x_809_ = lean_obj_once(&l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3, &l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3_once, _init_l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___closed__3);
v___x_810_ = l_panic___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__2(v___x_809_);
return v___x_810_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0___boxed(lean_object* v_d_811_, lean_object* v_keys_812_, lean_object* v_v_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_d_811_, v_keys_812_, v_v_813_);
lean_dec_ref(v_keys_812_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(lean_object* v_xs_815_, lean_object* v_v_816_, lean_object* v_i_817_){
_start:
{
lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_818_ = lean_array_get_size(v_xs_815_);
v___x_819_ = lean_nat_dec_lt(v_i_817_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; 
lean_dec(v_i_817_);
v___x_820_ = lean_box(0);
return v___x_820_;
}
else
{
lean_object* v___x_821_; uint8_t v___x_822_; 
v___x_821_ = lean_array_fget_borrowed(v_xs_815_, v_i_817_);
v___x_822_ = lean_name_eq(v___x_821_, v_v_816_);
if (v___x_822_ == 0)
{
lean_object* v___x_823_; lean_object* v___x_824_; 
v___x_823_ = lean_unsigned_to_nat(1u);
v___x_824_ = lean_nat_add(v_i_817_, v___x_823_);
lean_dec(v_i_817_);
v_i_817_ = v___x_824_;
goto _start;
}
else
{
lean_object* v___x_826_; 
v___x_826_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_826_, 0, v_i_817_);
return v___x_826_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20___boxed(lean_object* v_xs_827_, lean_object* v_v_828_, lean_object* v_i_829_){
_start:
{
lean_object* v_res_830_; 
v_res_830_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(v_xs_827_, v_v_828_, v_i_829_);
lean_dec(v_v_828_);
lean_dec_ref(v_xs_827_);
return v_res_830_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(lean_object* v_xs_831_, lean_object* v_v_832_){
_start:
{
lean_object* v___x_833_; lean_object* v___x_834_; 
v___x_833_ = lean_unsigned_to_nat(0u);
v___x_834_ = l_Array_idxOfAux___at___00Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13_spec__20(v_xs_831_, v_v_832_, v___x_833_);
return v___x_834_;
}
}
LEAN_EXPORT lean_object* l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13___boxed(lean_object* v_xs_835_, lean_object* v_v_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(v_xs_835_, v_v_836_);
lean_dec(v_v_836_);
lean_dec_ref(v_xs_835_);
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(lean_object* v_x_838_, size_t v_x_839_, lean_object* v_x_840_){
_start:
{
if (lean_obj_tag(v_x_838_) == 0)
{
lean_object* v_es_841_; lean_object* v___x_842_; size_t v___x_843_; size_t v___x_844_; lean_object* v_j_845_; lean_object* v_entry_846_; 
v_es_841_ = lean_ctor_get(v_x_838_, 0);
v___x_842_ = lean_box(2);
v___x_843_ = ((size_t)31ULL);
v___x_844_ = lean_usize_land(v_x_839_, v___x_843_);
v_j_845_ = lean_usize_to_nat(v___x_844_);
v_entry_846_ = lean_array_get(v___x_842_, v_es_841_, v_j_845_);
switch(lean_obj_tag(v_entry_846_))
{
case 0:
{
lean_object* v_key_847_; uint8_t v___x_848_; 
v_key_847_ = lean_ctor_get(v_entry_846_, 0);
lean_inc(v_key_847_);
lean_dec_ref_known(v_entry_846_, 2);
v___x_848_ = lean_name_eq(v_x_840_, v_key_847_);
lean_dec(v_key_847_);
if (v___x_848_ == 0)
{
lean_dec(v_j_845_);
return v_x_838_;
}
else
{
lean_object* v___x_850_; uint8_t v_isShared_851_; uint8_t v_isSharedCheck_856_; 
lean_inc_ref(v_es_841_);
v_isSharedCheck_856_ = !lean_is_exclusive(v_x_838_);
if (v_isSharedCheck_856_ == 0)
{
lean_object* v_unused_857_; 
v_unused_857_ = lean_ctor_get(v_x_838_, 0);
lean_dec(v_unused_857_);
v___x_850_ = v_x_838_;
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
else
{
lean_dec(v_x_838_);
v___x_850_ = lean_box(0);
v_isShared_851_ = v_isSharedCheck_856_;
goto v_resetjp_849_;
}
v_resetjp_849_:
{
lean_object* v___x_852_; lean_object* v___x_854_; 
v___x_852_ = lean_array_set(v_es_841_, v_j_845_, v___x_842_);
lean_dec(v_j_845_);
if (v_isShared_851_ == 0)
{
lean_ctor_set(v___x_850_, 0, v___x_852_);
v___x_854_ = v___x_850_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v___x_852_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
case 1:
{
lean_object* v___x_859_; uint8_t v_isShared_860_; uint8_t v_isSharedCheck_892_; 
lean_inc_ref(v_es_841_);
v_isSharedCheck_892_ = !lean_is_exclusive(v_x_838_);
if (v_isSharedCheck_892_ == 0)
{
lean_object* v_unused_893_; 
v_unused_893_ = lean_ctor_get(v_x_838_, 0);
lean_dec(v_unused_893_);
v___x_859_ = v_x_838_;
v_isShared_860_ = v_isSharedCheck_892_;
goto v_resetjp_858_;
}
else
{
lean_dec(v_x_838_);
v___x_859_ = lean_box(0);
v_isShared_860_ = v_isSharedCheck_892_;
goto v_resetjp_858_;
}
v_resetjp_858_:
{
lean_object* v_node_861_; lean_object* v___x_863_; uint8_t v_isShared_864_; uint8_t v_isSharedCheck_891_; 
v_node_861_ = lean_ctor_get(v_entry_846_, 0);
v_isSharedCheck_891_ = !lean_is_exclusive(v_entry_846_);
if (v_isSharedCheck_891_ == 0)
{
v___x_863_ = v_entry_846_;
v_isShared_864_ = v_isSharedCheck_891_;
goto v_resetjp_862_;
}
else
{
lean_inc(v_node_861_);
lean_dec(v_entry_846_);
v___x_863_ = lean_box(0);
v_isShared_864_ = v_isSharedCheck_891_;
goto v_resetjp_862_;
}
v_resetjp_862_:
{
size_t v___x_865_; lean_object* v_entries_866_; size_t v___x_867_; lean_object* v_newNode_868_; lean_object* v___x_869_; 
v___x_865_ = ((size_t)5ULL);
v_entries_866_ = lean_array_set(v_es_841_, v_j_845_, v___x_842_);
v___x_867_ = lean_usize_shift_right(v_x_839_, v___x_865_);
v_newNode_868_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_node_861_, v___x_867_, v_x_840_);
lean_inc_ref(v_newNode_868_);
v___x_869_ = l_Lean_PersistentHashMap_isUnaryNode___redArg(v_newNode_868_);
if (lean_obj_tag(v___x_869_) == 0)
{
lean_object* v___x_871_; 
if (v_isShared_864_ == 0)
{
lean_ctor_set(v___x_863_, 0, v_newNode_868_);
v___x_871_ = v___x_863_;
goto v_reusejp_870_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v_newNode_868_);
v___x_871_ = v_reuseFailAlloc_876_;
goto v_reusejp_870_;
}
v_reusejp_870_:
{
lean_object* v___x_872_; lean_object* v___x_874_; 
v___x_872_ = lean_array_set(v_entries_866_, v_j_845_, v___x_871_);
lean_dec(v_j_845_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_872_);
v___x_874_ = v___x_859_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
else
{
lean_object* v_val_877_; lean_object* v_fst_878_; lean_object* v_snd_879_; lean_object* v___x_881_; uint8_t v_isShared_882_; uint8_t v_isSharedCheck_890_; 
lean_dec_ref(v_newNode_868_);
lean_del_object(v___x_863_);
v_val_877_ = lean_ctor_get(v___x_869_, 0);
lean_inc(v_val_877_);
lean_dec_ref_known(v___x_869_, 1);
v_fst_878_ = lean_ctor_get(v_val_877_, 0);
v_snd_879_ = lean_ctor_get(v_val_877_, 1);
v_isSharedCheck_890_ = !lean_is_exclusive(v_val_877_);
if (v_isSharedCheck_890_ == 0)
{
v___x_881_ = v_val_877_;
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
else
{
lean_inc(v_snd_879_);
lean_inc(v_fst_878_);
lean_dec(v_val_877_);
v___x_881_ = lean_box(0);
v_isShared_882_ = v_isSharedCheck_890_;
goto v_resetjp_880_;
}
v_resetjp_880_:
{
lean_object* v___x_884_; 
if (v_isShared_882_ == 0)
{
v___x_884_ = v___x_881_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_889_; 
v_reuseFailAlloc_889_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_889_, 0, v_fst_878_);
lean_ctor_set(v_reuseFailAlloc_889_, 1, v_snd_879_);
v___x_884_ = v_reuseFailAlloc_889_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_885_; lean_object* v___x_887_; 
v___x_885_ = lean_array_set(v_entries_866_, v_j_845_, v___x_884_);
lean_dec(v_j_845_);
if (v_isShared_860_ == 0)
{
lean_ctor_set(v___x_859_, 0, v___x_885_);
v___x_887_ = v___x_859_;
goto v_reusejp_886_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_885_);
v___x_887_ = v_reuseFailAlloc_888_;
goto v_reusejp_886_;
}
v_reusejp_886_:
{
return v___x_887_;
}
}
}
}
}
}
}
default: 
{
lean_dec(v_j_845_);
return v_x_838_;
}
}
}
else
{
lean_object* v_ks_894_; lean_object* v_vs_895_; lean_object* v___x_897_; uint8_t v_isShared_898_; uint8_t v_isSharedCheck_909_; 
v_ks_894_ = lean_ctor_get(v_x_838_, 0);
v_vs_895_ = lean_ctor_get(v_x_838_, 1);
v_isSharedCheck_909_ = !lean_is_exclusive(v_x_838_);
if (v_isSharedCheck_909_ == 0)
{
v___x_897_ = v_x_838_;
v_isShared_898_ = v_isSharedCheck_909_;
goto v_resetjp_896_;
}
else
{
lean_inc(v_vs_895_);
lean_inc(v_ks_894_);
lean_dec(v_x_838_);
v___x_897_ = lean_box(0);
v_isShared_898_ = v_isSharedCheck_909_;
goto v_resetjp_896_;
}
v_resetjp_896_:
{
lean_object* v___x_899_; 
v___x_899_ = l_Array_finIdxOf_x3f___at___00Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6_spec__13(v_ks_894_, v_x_840_);
if (lean_obj_tag(v___x_899_) == 0)
{
lean_object* v___x_901_; 
if (v_isShared_898_ == 0)
{
v___x_901_ = v___x_897_;
goto v_reusejp_900_;
}
else
{
lean_object* v_reuseFailAlloc_902_; 
v_reuseFailAlloc_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_902_, 0, v_ks_894_);
lean_ctor_set(v_reuseFailAlloc_902_, 1, v_vs_895_);
v___x_901_ = v_reuseFailAlloc_902_;
goto v_reusejp_900_;
}
v_reusejp_900_:
{
return v___x_901_;
}
}
else
{
lean_object* v_val_903_; lean_object* v_keys_x27_904_; lean_object* v_vals_x27_905_; lean_object* v___x_907_; 
v_val_903_ = lean_ctor_get(v___x_899_, 0);
lean_inc_n(v_val_903_, 2);
lean_dec_ref_known(v___x_899_, 1);
v_keys_x27_904_ = l_Array_eraseIdx___redArg(v_ks_894_, v_val_903_);
v_vals_x27_905_ = l_Array_eraseIdx___redArg(v_vs_895_, v_val_903_);
if (v_isShared_898_ == 0)
{
lean_ctor_set(v___x_897_, 1, v_vals_x27_905_);
lean_ctor_set(v___x_897_, 0, v_keys_x27_904_);
v___x_907_ = v___x_897_;
goto v_reusejp_906_;
}
else
{
lean_object* v_reuseFailAlloc_908_; 
v_reuseFailAlloc_908_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_908_, 0, v_keys_x27_904_);
lean_ctor_set(v_reuseFailAlloc_908_, 1, v_vals_x27_905_);
v___x_907_ = v_reuseFailAlloc_908_;
goto v_reusejp_906_;
}
v_reusejp_906_:
{
return v___x_907_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg___boxed(lean_object* v_x_910_, lean_object* v_x_911_, lean_object* v_x_912_){
_start:
{
size_t v_x_3101__boxed_913_; lean_object* v_res_914_; 
v_x_3101__boxed_913_ = lean_unbox_usize(v_x_911_);
lean_dec(v_x_911_);
v_res_914_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_910_, v_x_3101__boxed_913_, v_x_912_);
lean_dec(v_x_912_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(lean_object* v_x_915_, lean_object* v_x_916_){
_start:
{
uint64_t v___y_918_; 
if (lean_obj_tag(v_x_916_) == 0)
{
uint64_t v___x_921_; 
v___x_921_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0);
v___y_918_ = v___x_921_;
goto v___jp_917_;
}
else
{
uint64_t v_hash_922_; 
v_hash_922_ = lean_ctor_get_uint64(v_x_916_, sizeof(void*)*2);
v___y_918_ = v_hash_922_;
goto v___jp_917_;
}
v___jp_917_:
{
size_t v_h_919_; lean_object* v___x_920_; 
v_h_919_ = lean_uint64_to_usize(v___y_918_);
v___x_920_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_915_, v_h_919_, v_x_916_);
return v___x_920_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg___boxed(lean_object* v_x_923_, lean_object* v_x_924_){
_start:
{
lean_object* v_res_925_; 
v_res_925_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_923_, v_x_924_);
lean_dec(v_x_924_);
return v_res_925_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstanceEntry(lean_object* v_d_926_, lean_object* v_e_927_){
_start:
{
lean_object* v_globalName_x3f_928_; 
v_globalName_x3f_928_ = lean_ctor_get(v_e_927_, 3);
if (lean_obj_tag(v_globalName_x3f_928_) == 0)
{
lean_object* v_keys_929_; lean_object* v_discrTree_930_; lean_object* v_instanceNames_931_; lean_object* v_erased_932_; lean_object* v___x_934_; uint8_t v_isShared_935_; uint8_t v_isSharedCheck_940_; 
v_keys_929_ = lean_ctor_get(v_e_927_, 0);
lean_inc_ref(v_keys_929_);
v_discrTree_930_ = lean_ctor_get(v_d_926_, 0);
v_instanceNames_931_ = lean_ctor_get(v_d_926_, 1);
v_erased_932_ = lean_ctor_get(v_d_926_, 2);
v_isSharedCheck_940_ = !lean_is_exclusive(v_d_926_);
if (v_isSharedCheck_940_ == 0)
{
v___x_934_ = v_d_926_;
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
else
{
lean_inc(v_erased_932_);
lean_inc(v_instanceNames_931_);
lean_inc(v_discrTree_930_);
lean_dec(v_d_926_);
v___x_934_ = lean_box(0);
v_isShared_935_ = v_isSharedCheck_940_;
goto v_resetjp_933_;
}
v_resetjp_933_:
{
lean_object* v___x_936_; lean_object* v___x_938_; 
v___x_936_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_930_, v_keys_929_, v_e_927_);
lean_dec_ref(v_keys_929_);
if (v_isShared_935_ == 0)
{
lean_ctor_set(v___x_934_, 0, v___x_936_);
v___x_938_ = v___x_934_;
goto v_reusejp_937_;
}
else
{
lean_object* v_reuseFailAlloc_939_; 
v_reuseFailAlloc_939_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_939_, 0, v___x_936_);
lean_ctor_set(v_reuseFailAlloc_939_, 1, v_instanceNames_931_);
lean_ctor_set(v_reuseFailAlloc_939_, 2, v_erased_932_);
v___x_938_ = v_reuseFailAlloc_939_;
goto v_reusejp_937_;
}
v_reusejp_937_:
{
return v___x_938_;
}
}
}
else
{
lean_object* v_keys_941_; lean_object* v_val_942_; lean_object* v_discrTree_943_; lean_object* v_instanceNames_944_; lean_object* v_erased_945_; lean_object* v___x_947_; uint8_t v_isShared_948_; uint8_t v_isSharedCheck_955_; 
v_keys_941_ = lean_ctor_get(v_e_927_, 0);
v_val_942_ = lean_ctor_get(v_globalName_x3f_928_, 0);
lean_inc(v_val_942_);
v_discrTree_943_ = lean_ctor_get(v_d_926_, 0);
v_instanceNames_944_ = lean_ctor_get(v_d_926_, 1);
v_erased_945_ = lean_ctor_get(v_d_926_, 2);
v_isSharedCheck_955_ = !lean_is_exclusive(v_d_926_);
if (v_isSharedCheck_955_ == 0)
{
v___x_947_ = v_d_926_;
v_isShared_948_ = v_isSharedCheck_955_;
goto v_resetjp_946_;
}
else
{
lean_inc(v_erased_945_);
lean_inc(v_instanceNames_944_);
lean_inc(v_discrTree_943_);
lean_dec(v_d_926_);
v___x_947_ = lean_box(0);
v_isShared_948_ = v_isSharedCheck_955_;
goto v_resetjp_946_;
}
v_resetjp_946_:
{
lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_953_; 
lean_inc_ref(v_e_927_);
v___x_949_ = l_Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0(v_discrTree_943_, v_keys_941_, v_e_927_);
lean_inc(v_val_942_);
v___x_950_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_instanceNames_944_, v_val_942_, v_e_927_);
v___x_951_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_erased_945_, v_val_942_);
lean_dec(v_val_942_);
if (v_isShared_948_ == 0)
{
lean_ctor_set(v___x_947_, 2, v___x_951_);
lean_ctor_set(v___x_947_, 1, v___x_950_);
lean_ctor_set(v___x_947_, 0, v___x_949_);
v___x_953_ = v___x_947_;
goto v_reusejp_952_;
}
else
{
lean_object* v_reuseFailAlloc_954_; 
v_reuseFailAlloc_954_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_954_, 0, v___x_949_);
lean_ctor_set(v_reuseFailAlloc_954_, 1, v___x_950_);
lean_ctor_set(v_reuseFailAlloc_954_, 2, v___x_951_);
v___x_953_ = v_reuseFailAlloc_954_;
goto v_reusejp_952_;
}
v_reusejp_952_:
{
return v___x_953_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1(lean_object* v_00_u03b2_956_, lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_x_959_){
_start:
{
lean_object* v___x_960_; 
v___x_960_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_x_957_, v_x_958_, v_x_959_);
return v___x_960_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(lean_object* v_00_u03b2_961_, lean_object* v_x_962_, lean_object* v_x_963_){
_start:
{
lean_object* v___x_964_; 
v___x_964_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_x_962_, v_x_963_);
return v___x_964_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___boxed(lean_object* v_00_u03b2_965_, lean_object* v_x_966_, lean_object* v_x_967_){
_start:
{
lean_object* v_res_968_; 
v_res_968_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2(v_00_u03b2_965_, v_x_966_, v_x_967_);
lean_dec(v_x_967_);
return v_res_968_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4(lean_object* v_00_u03b2_969_, lean_object* v_x_970_, size_t v_x_971_, size_t v_x_972_, lean_object* v_x_973_, lean_object* v_x_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg(v_x_970_, v_x_971_, v_x_972_, v_x_973_, v_x_974_);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___boxed(lean_object* v_00_u03b2_976_, lean_object* v_x_977_, lean_object* v_x_978_, lean_object* v_x_979_, lean_object* v_x_980_, lean_object* v_x_981_){
_start:
{
size_t v_x_3308__boxed_982_; size_t v_x_3309__boxed_983_; lean_object* v_res_984_; 
v_x_3308__boxed_982_ = lean_unbox_usize(v_x_978_);
lean_dec(v_x_978_);
v_x_3309__boxed_983_ = lean_unbox_usize(v_x_979_);
lean_dec(v_x_979_);
v_res_984_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4(v_00_u03b2_976_, v_x_977_, v_x_3308__boxed_982_, v_x_3309__boxed_983_, v_x_980_, v_x_981_);
return v_res_984_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6(lean_object* v_00_u03b2_985_, lean_object* v_x_986_, size_t v_x_987_, lean_object* v_x_988_){
_start:
{
lean_object* v___x_989_; 
v___x_989_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___redArg(v_x_986_, v_x_987_, v_x_988_);
return v___x_989_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6___boxed(lean_object* v_00_u03b2_990_, lean_object* v_x_991_, lean_object* v_x_992_, lean_object* v_x_993_){
_start:
{
size_t v_x_3325__boxed_994_; lean_object* v_res_995_; 
v_x_3325__boxed_994_ = lean_unbox_usize(v_x_992_);
lean_dec(v_x_992_);
v_res_995_ = l_Lean_PersistentHashMap_eraseAux___at___00Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2_spec__6(v_00_u03b2_990_, v_x_991_, v_x_3325__boxed_994_, v_x_993_);
lean_dec(v_x_993_);
return v_res_995_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(lean_object* v_00_u03b2_996_, lean_object* v_x_997_, size_t v_x_998_, size_t v_x_999_, lean_object* v_x_1000_, lean_object* v_x_1001_){
_start:
{
lean_object* v___x_1002_; 
v___x_1002_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___redArg(v_x_997_, v_x_998_, v_x_999_, v_x_1000_, v_x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5___boxed(lean_object* v_00_u03b2_1003_, lean_object* v_x_1004_, lean_object* v_x_1005_, lean_object* v_x_1006_, lean_object* v_x_1007_, lean_object* v_x_1008_){
_start:
{
size_t v_x_3336__boxed_1009_; size_t v_x_3337__boxed_1010_; lean_object* v_res_1011_; 
v_x_3336__boxed_1009_ = lean_unbox_usize(v_x_1005_);
lean_dec(v_x_1005_);
v_x_3337__boxed_1010_ = lean_unbox_usize(v_x_1006_);
lean_dec(v_x_1006_);
v_res_1011_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5(v_00_u03b2_1003_, v_x_1004_, v_x_3336__boxed_1009_, v_x_3337__boxed_1010_, v_x_1007_, v_x_1008_);
return v_res_1011_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9(lean_object* v_00_u03b2_1012_, lean_object* v_n_1013_, lean_object* v_k_1014_, lean_object* v_v_1015_){
_start:
{
lean_object* v___x_1016_; 
v___x_1016_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9___redArg(v_n_1013_, v_k_1014_, v_v_1015_);
return v___x_1016_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10(lean_object* v_00_u03b2_1017_, size_t v_depth_1018_, lean_object* v_keys_1019_, lean_object* v_vals_1020_, lean_object* v_heq_1021_, lean_object* v_i_1022_, lean_object* v_entries_1023_){
_start:
{
lean_object* v___x_1024_; 
v___x_1024_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg(v_depth_1018_, v_keys_1019_, v_vals_1020_, v_i_1022_, v_entries_1023_);
return v___x_1024_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___boxed(lean_object* v_00_u03b2_1025_, lean_object* v_depth_1026_, lean_object* v_keys_1027_, lean_object* v_vals_1028_, lean_object* v_heq_1029_, lean_object* v_i_1030_, lean_object* v_entries_1031_){
_start:
{
size_t v_depth_boxed_1032_; lean_object* v_res_1033_; 
v_depth_boxed_1032_ = lean_unbox_usize(v_depth_1026_);
lean_dec(v_depth_1026_);
v_res_1033_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10(v_00_u03b2_1025_, v_depth_boxed_1032_, v_keys_1027_, v_vals_1028_, v_heq_1029_, v_i_1030_, v_entries_1031_);
lean_dec_ref(v_vals_1028_);
lean_dec_ref(v_keys_1027_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7(lean_object* v_x_1034_, lean_object* v_keys_1035_, lean_object* v_v_1036_, lean_object* v_k_1037_, lean_object* v_as_1038_, lean_object* v_k_1039_, lean_object* v_x_1040_, lean_object* v_x_1041_, lean_object* v_x_1042_, lean_object* v_x_1043_){
_start:
{
lean_object* v___x_1044_; 
v___x_1044_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___redArg(v_x_1034_, v_keys_1035_, v_v_1036_, v_k_1037_, v_as_1038_, v_k_1039_, v_x_1040_, v_x_1041_);
return v___x_1044_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7___boxed(lean_object* v_x_1045_, lean_object* v_keys_1046_, lean_object* v_v_1047_, lean_object* v_k_1048_, lean_object* v_as_1049_, lean_object* v_k_1050_, lean_object* v_x_1051_, lean_object* v_x_1052_, lean_object* v_x_1053_, lean_object* v_x_1054_){
_start:
{
lean_object* v_res_1055_; 
v_res_1055_ = l___private_Init_Data_Array_BinSearch_0__Array_binInsertAux___at___00Array_binInsertM___at___00__private_Lean_Meta_DiscrTree_Basic_0__Lean_Meta_DiscrTree_insertAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__0_spec__2_spec__7(v_x_1045_, v_keys_1046_, v_v_1047_, v_k_1048_, v_as_1049_, v_k_1050_, v_x_1051_, v_x_1052_, v_x_1053_, v_x_1054_);
lean_dec_ref(v_k_1050_);
lean_dec_ref(v_keys_1046_);
lean_dec(v_x_1045_);
return v_res_1055_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12(lean_object* v_00_u03b2_1056_, lean_object* v_n_1057_, lean_object* v_k_1058_, lean_object* v_v_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12___redArg(v_n_1057_, v_k_1058_, v_v_1059_);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13(lean_object* v_00_u03b2_1061_, size_t v_depth_1062_, lean_object* v_keys_1063_, lean_object* v_vals_1064_, lean_object* v_heq_1065_, lean_object* v_i_1066_, lean_object* v_entries_1067_){
_start:
{
lean_object* v___x_1068_; 
v___x_1068_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___redArg(v_depth_1062_, v_keys_1063_, v_vals_1064_, v_i_1066_, v_entries_1067_);
return v___x_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13___boxed(lean_object* v_00_u03b2_1069_, lean_object* v_depth_1070_, lean_object* v_keys_1071_, lean_object* v_vals_1072_, lean_object* v_heq_1073_, lean_object* v_i_1074_, lean_object* v_entries_1075_){
_start:
{
size_t v_depth_boxed_1076_; lean_object* v_res_1077_; 
v_depth_boxed_1076_ = lean_unbox_usize(v_depth_1070_);
lean_dec(v_depth_1070_);
v_res_1077_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__13(v_00_u03b2_1069_, v_depth_boxed_1076_, v_keys_1071_, v_vals_1072_, v_heq_1073_, v_i_1074_, v_entries_1075_);
lean_dec_ref(v_vals_1072_);
lean_dec_ref(v_keys_1071_);
return v_res_1077_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16(lean_object* v_00_u03b2_1078_, lean_object* v_x_1079_, lean_object* v_x_1080_, lean_object* v_x_1081_, lean_object* v_x_1082_){
_start:
{
lean_object* v___x_1083_; 
v___x_1083_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__9_spec__16___redArg(v_x_1079_, v_x_1080_, v_x_1081_, v_x_1082_);
return v___x_1083_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15(lean_object* v_00_u03b2_1084_, lean_object* v_x_1085_, lean_object* v_x_1086_, lean_object* v_x_1087_, lean_object* v_x_1088_){
_start:
{
lean_object* v___x_1089_; 
v___x_1089_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_alterAux___at___00Lean_Meta_DiscrTree_insertKeyValue___at___00Lean_Meta_addInstanceEntry_spec__0_spec__1_spec__5_spec__12_spec__15___redArg(v_x_1085_, v_x_1086_, v_x_1087_, v_x_1088_);
return v___x_1089_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_eraseCore(lean_object* v_d_1090_, lean_object* v_declName_1091_){
_start:
{
lean_object* v_discrTree_1092_; lean_object* v_instanceNames_1093_; lean_object* v_erased_1094_; lean_object* v___x_1096_; uint8_t v_isShared_1097_; uint8_t v_isSharedCheck_1104_; 
v_discrTree_1092_ = lean_ctor_get(v_d_1090_, 0);
v_instanceNames_1093_ = lean_ctor_get(v_d_1090_, 1);
v_erased_1094_ = lean_ctor_get(v_d_1090_, 2);
v_isSharedCheck_1104_ = !lean_is_exclusive(v_d_1090_);
if (v_isSharedCheck_1104_ == 0)
{
v___x_1096_ = v_d_1090_;
v_isShared_1097_ = v_isSharedCheck_1104_;
goto v_resetjp_1095_;
}
else
{
lean_inc(v_erased_1094_);
lean_inc(v_instanceNames_1093_);
lean_inc(v_discrTree_1092_);
lean_dec(v_d_1090_);
v___x_1096_ = lean_box(0);
v_isShared_1097_ = v_isSharedCheck_1104_;
goto v_resetjp_1095_;
}
v_resetjp_1095_:
{
lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1102_; 
v___x_1098_ = l_Lean_PersistentHashMap_erase___at___00Lean_Meta_addInstanceEntry_spec__2___redArg(v_instanceNames_1093_, v_declName_1091_);
v___x_1099_ = lean_box(0);
v___x_1100_ = l_Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1___redArg(v_erased_1094_, v_declName_1091_, v___x_1099_);
if (v_isShared_1097_ == 0)
{
lean_ctor_set(v___x_1096_, 2, v___x_1100_);
lean_ctor_set(v___x_1096_, 1, v___x_1098_);
v___x_1102_ = v___x_1096_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1103_; 
v_reuseFailAlloc_1103_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1103_, 0, v_discrTree_1092_);
lean_ctor_set(v_reuseFailAlloc_1103_, 1, v___x_1098_);
lean_ctor_set(v_reuseFailAlloc_1103_, 2, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1103_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
return v___x_1102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__0(lean_object* v_d_1105_, lean_object* v_declName_1106_, lean_object* v_toPure_1107_, lean_object* v_____r_1108_){
_start:
{
lean_object* v___x_1109_; lean_object* v___x_1110_; 
v___x_1109_ = l_Lean_Meta_Instances_eraseCore(v_d_1105_, v_declName_1106_);
v___x_1110_ = lean_apply_2(v_toPure_1107_, lean_box(0), v___x_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg___lam__1(lean_object* v___f_1111_, lean_object* v_____r_1112_){
_start:
{
lean_object* v___x_1113_; 
v___x_1113_ = lean_apply_1(v___f_1111_, v_____r_1112_);
return v___x_1113_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__3(void){
_start:
{
lean_object* v___x_1117_; lean_object* v___x_1118_; 
v___x_1117_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__2));
v___x_1118_ = l_Lean_stringToMessageData(v___x_1117_);
return v___x_1118_;
}
}
static lean_object* _init_l_Lean_Meta_Instances_erase___redArg___closed__5(void){
_start:
{
lean_object* v___x_1120_; lean_object* v___x_1121_; 
v___x_1120_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__4));
v___x_1121_ = l_Lean_stringToMessageData(v___x_1120_);
return v___x_1121_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___redArg(lean_object* v_inst_1122_, lean_object* v_inst_1123_, lean_object* v_d_1124_, lean_object* v_declName_1125_){
_start:
{
lean_object* v_toApplicative_1126_; lean_object* v_toBind_1127_; lean_object* v_toPure_1128_; lean_object* v_instanceNames_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___f_1132_; uint8_t v___x_1133_; 
v_toApplicative_1126_ = lean_ctor_get(v_inst_1122_, 0);
v_toBind_1127_ = lean_ctor_get(v_inst_1122_, 1);
lean_inc(v_toBind_1127_);
v_toPure_1128_ = lean_ctor_get(v_toApplicative_1126_, 1);
v_instanceNames_1129_ = lean_ctor_get(v_d_1124_, 1);
v___x_1130_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__0));
v___x_1131_ = ((lean_object*)(l_Lean_Meta_Instances_erase___redArg___closed__1));
lean_inc(v_toPure_1128_);
lean_inc_n(v_declName_1125_, 2);
lean_inc_ref(v_d_1124_);
v___f_1132_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1132_, 0, v_d_1124_);
lean_closure_set(v___f_1132_, 1, v_declName_1125_);
lean_closure_set(v___f_1132_, 2, v_toPure_1128_);
lean_inc_ref(v_instanceNames_1129_);
v___x_1133_ = l_Lean_PersistentHashMap_contains___redArg(v___x_1130_, v___x_1131_, v_instanceNames_1129_, v_declName_1125_);
if (v___x_1133_ == 0)
{
lean_object* v___f_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; 
lean_dec_ref(v_d_1124_);
v___f_1134_ = lean_alloc_closure((void*)(l_Lean_Meta_Instances_erase___redArg___lam__1), 2, 1);
lean_closure_set(v___f_1134_, 0, v___f_1132_);
v___x_1135_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_1136_ = l_Lean_MessageData_ofConstName(v_declName_1125_, v___x_1133_);
v___x_1137_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1137_, 0, v___x_1135_);
lean_ctor_set(v___x_1137_, 1, v___x_1136_);
v___x_1138_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_1139_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_1137_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
v___x_1140_ = l_Lean_throwError___redArg(v_inst_1122_, v_inst_1123_, v___x_1139_);
v___x_1141_ = lean_apply_4(v_toBind_1127_, lean_box(0), lean_box(0), v___x_1140_, v___f_1134_);
return v___x_1141_;
}
else
{
lean_object* v___x_1142_; lean_object* v___x_1143_; 
lean_inc(v_toPure_1128_);
lean_dec_ref(v___f_1132_);
lean_dec(v_toBind_1127_);
lean_dec_ref(v_inst_1123_);
lean_dec_ref(v_inst_1122_);
v___x_1142_ = lean_box(0);
v___x_1143_ = l_Lean_Meta_Instances_erase___redArg___lam__0(v_d_1124_, v_declName_1125_, v_toPure_1128_, v___x_1142_);
return v___x_1143_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase(lean_object* v_m_1144_, lean_object* v_inst_1145_, lean_object* v_inst_1146_, lean_object* v_d_1147_, lean_object* v_declName_1148_){
_start:
{
lean_object* v___x_1149_; 
v___x_1149_ = l_Lean_Meta_Instances_erase___redArg(v_inst_1145_, v_inst_1146_, v_d_1147_, v_declName_1148_);
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(lean_object* v_x_1150_, lean_object* v_e_1151_){
_start:
{
lean_object* v_globalName_x3f_1156_; 
v_globalName_x3f_1156_ = lean_ctor_get(v_e_1151_, 3);
lean_inc(v_globalName_x3f_1156_);
if (lean_obj_tag(v_globalName_x3f_1156_) == 0)
{
goto v___jp_1152_;
}
else
{
lean_object* v_val_1157_; lean_object* v___x_1159_; uint8_t v_isShared_1160_; uint8_t v_isSharedCheck_1167_; 
v_val_1157_ = lean_ctor_get(v_globalName_x3f_1156_, 0);
v_isSharedCheck_1167_ = !lean_is_exclusive(v_globalName_x3f_1156_);
if (v_isSharedCheck_1167_ == 0)
{
v___x_1159_ = v_globalName_x3f_1156_;
v_isShared_1160_ = v_isSharedCheck_1167_;
goto v_resetjp_1158_;
}
else
{
lean_inc(v_val_1157_);
lean_dec(v_globalName_x3f_1156_);
v___x_1159_ = lean_box(0);
v_isShared_1160_ = v_isSharedCheck_1167_;
goto v_resetjp_1158_;
}
v_resetjp_1158_:
{
uint8_t v___x_1161_; uint8_t v___x_1162_; 
v___x_1161_ = l_Lean_isPrivateName(v_val_1157_);
lean_dec(v_val_1157_);
v___x_1162_ = lean_bool_not(v___x_1161_);
if (v___x_1162_ == 0)
{
lean_del_object(v___x_1159_);
goto v___jp_1152_;
}
else
{
lean_object* v___x_1164_; 
if (v_isShared_1160_ == 0)
{
lean_ctor_set(v___x_1159_, 0, v_e_1151_);
v___x_1164_ = v___x_1159_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_e_1151_);
v___x_1164_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; 
lean_inc_ref_n(v___x_1164_, 2);
v___x_1165_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1165_, 0, v___x_1164_);
lean_ctor_set(v___x_1165_, 1, v___x_1164_);
lean_ctor_set(v___x_1165_, 2, v___x_1164_);
return v___x_1165_;
}
}
}
}
v___jp_1152_:
{
lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; 
v___x_1153_ = lean_box(0);
v___x_1154_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1154_, 0, v_e_1151_);
v___x_1155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1153_);
lean_ctor_set(v___x_1155_, 1, v___x_1153_);
lean_ctor_set(v___x_1155_, 2, v___x_1154_);
return v___x_1155_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v_x_1168_, lean_object* v_e_1169_){
_start:
{
lean_object* v_res_1170_; 
v_res_1170_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(v_x_1168_, v_e_1169_);
lean_dec_ref(v_x_1168_);
return v_res_1170_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(lean_object* v___y_1171_){
_start:
{
lean_inc_ref(v___y_1171_);
return v___y_1171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v___y_1172_){
_start:
{
lean_object* v_res_1173_; 
v_res_1173_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(v___y_1172_);
lean_dec_ref(v___y_1172_);
return v_res_1173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_1182_; lean_object* v___f_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; 
v___f_1182_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___f_1183_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__1_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1184_ = lean_obj_once(&l_Lean_Meta_instInhabitedInstances_default___closed__4, &l_Lean_Meta_instInhabitedInstances_default___closed__4_once, _init_l_Lean_Meta_instInhabitedInstances_default___closed__4);
v___x_1185_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__4_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1186_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_));
v___x_1187_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v___x_1185_);
lean_ctor_set(v___x_1187_, 2, v___x_1184_);
lean_ctor_set(v___x_1187_, 3, v___f_1183_);
lean_ctor_set(v___x_1187_, 4, v___f_1182_);
return v___x_1187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_1189_; lean_object* v___x_1190_; 
v___x_1189_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__5_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_);
v___x_1190_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_1189_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2____boxed(lean_object* v_a_1191_){
_start:
{
lean_object* v_res_1192_; 
v_res_1192_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_2240659058____hygCtx___hyg_2_();
return v_res_1192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(lean_object* v_k_1193_, uint8_t v_allowLevelAssignments_1194_, lean_object* v___y_1195_, lean_object* v___y_1196_, lean_object* v___y_1197_, lean_object* v___y_1198_){
_start:
{
lean_object* v___x_1200_; 
v___x_1200_ = l___private_Lean_Meta_Basic_0__Lean_Meta_withNewMCtxDepthImp(lean_box(0), v_allowLevelAssignments_1194_, v_k_1193_, v___y_1195_, v___y_1196_, v___y_1197_, v___y_1198_);
if (lean_obj_tag(v___x_1200_) == 0)
{
lean_object* v_a_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1208_; 
v_a_1201_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1208_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1208_ == 0)
{
v___x_1203_ = v___x_1200_;
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_a_1201_);
lean_dec(v___x_1200_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1208_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v___x_1206_; 
if (v_isShared_1204_ == 0)
{
v___x_1206_ = v___x_1203_;
goto v_reusejp_1205_;
}
else
{
lean_object* v_reuseFailAlloc_1207_; 
v_reuseFailAlloc_1207_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1207_, 0, v_a_1201_);
v___x_1206_ = v_reuseFailAlloc_1207_;
goto v_reusejp_1205_;
}
v_reusejp_1205_:
{
return v___x_1206_;
}
}
}
else
{
lean_object* v_a_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1216_; 
v_a_1209_ = lean_ctor_get(v___x_1200_, 0);
v_isSharedCheck_1216_ = !lean_is_exclusive(v___x_1200_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1211_ = v___x_1200_;
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_a_1209_);
lean_dec(v___x_1200_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1216_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1214_; 
if (v_isShared_1212_ == 0)
{
v___x_1214_ = v___x_1211_;
goto v_reusejp_1213_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_a_1209_);
v___x_1214_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1213_;
}
v_reusejp_1213_:
{
return v___x_1214_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg___boxed(lean_object* v_k_1217_, lean_object* v_allowLevelAssignments_1218_, lean_object* v___y_1219_, lean_object* v___y_1220_, lean_object* v___y_1221_, lean_object* v___y_1222_, lean_object* v___y_1223_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1224_; lean_object* v_res_1225_; 
v_allowLevelAssignments_boxed_1224_ = lean_unbox(v_allowLevelAssignments_1218_);
v_res_1225_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1217_, v_allowLevelAssignments_boxed_1224_, v___y_1219_, v___y_1220_, v___y_1221_, v___y_1222_);
lean_dec(v___y_1222_);
lean_dec_ref(v___y_1221_);
lean_dec(v___y_1220_);
lean_dec_ref(v___y_1219_);
return v_res_1225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(lean_object* v_00_u03b1_1226_, lean_object* v_k_1227_, uint8_t v_allowLevelAssignments_1228_, lean_object* v___y_1229_, lean_object* v___y_1230_, lean_object* v___y_1231_, lean_object* v___y_1232_){
_start:
{
lean_object* v___x_1234_; 
v___x_1234_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v_k_1227_, v_allowLevelAssignments_1228_, v___y_1229_, v___y_1230_, v___y_1231_, v___y_1232_);
return v___x_1234_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___boxed(lean_object* v_00_u03b1_1235_, lean_object* v_k_1236_, lean_object* v_allowLevelAssignments_1237_, lean_object* v___y_1238_, lean_object* v___y_1239_, lean_object* v___y_1240_, lean_object* v___y_1241_, lean_object* v___y_1242_){
_start:
{
uint8_t v_allowLevelAssignments_boxed_1243_; lean_object* v_res_1244_; 
v_allowLevelAssignments_boxed_1243_ = lean_unbox(v_allowLevelAssignments_1237_);
v_res_1244_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0(v_00_u03b1_1235_, v_k_1236_, v_allowLevelAssignments_boxed_1243_, v___y_1238_, v___y_1239_, v___y_1240_, v___y_1241_);
lean_dec(v___y_1241_);
lean_dec_ref(v___y_1240_);
lean_dec(v___y_1239_);
lean_dec_ref(v___y_1238_);
return v_res_1244_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(lean_object* v_a_1245_, lean_object* v___x_1246_, uint8_t v___x_1247_, lean_object* v___y_1248_, lean_object* v___y_1249_, lean_object* v___y_1250_, lean_object* v___y_1251_){
_start:
{
lean_object* v___x_1253_; 
v___x_1253_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_1245_, v___x_1246_, v___x_1247_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v_a_1254_; lean_object* v_snd_1255_; lean_object* v_snd_1256_; uint8_t v___x_1257_; lean_object* v___x_1258_; 
v_a_1254_ = lean_ctor_get(v___x_1253_, 0);
lean_inc(v_a_1254_);
lean_dec_ref_known(v___x_1253_, 1);
v_snd_1255_ = lean_ctor_get(v_a_1254_, 1);
lean_inc(v_snd_1255_);
lean_dec(v_a_1254_);
v_snd_1256_ = lean_ctor_get(v_snd_1255_, 1);
lean_inc(v_snd_1256_);
lean_dec(v_snd_1255_);
v___x_1257_ = 0;
v___x_1258_ = l_Lean_Meta_DiscrTree_mkPath(v_snd_1256_, v___x_1257_, v___y_1248_, v___y_1249_, v___y_1250_, v___y_1251_);
return v___x_1258_;
}
else
{
lean_object* v_a_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1266_; 
v_a_1259_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1266_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1266_ == 0)
{
v___x_1261_ = v___x_1253_;
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_a_1259_);
lean_dec(v___x_1253_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1266_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___x_1264_; 
if (v_isShared_1262_ == 0)
{
v___x_1264_ = v___x_1261_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1265_; 
v_reuseFailAlloc_1265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1265_, 0, v_a_1259_);
v___x_1264_ = v_reuseFailAlloc_1265_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
return v___x_1264_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed(lean_object* v_a_1267_, lean_object* v___x_1268_, lean_object* v___x_1269_, lean_object* v___y_1270_, lean_object* v___y_1271_, lean_object* v___y_1272_, lean_object* v___y_1273_, lean_object* v___y_1274_){
_start:
{
uint8_t v___x_497__boxed_1275_; lean_object* v_res_1276_; 
v___x_497__boxed_1275_ = lean_unbox(v___x_1269_);
v_res_1276_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0(v_a_1267_, v___x_1268_, v___x_497__boxed_1275_, v___y_1270_, v___y_1271_, v___y_1272_, v___y_1273_);
lean_dec(v___y_1273_);
lean_dec_ref(v___y_1272_);
lean_dec(v___y_1271_);
lean_dec_ref(v___y_1270_);
return v_res_1276_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(lean_object* v_e_1277_, lean_object* v_a_1278_, lean_object* v_a_1279_, lean_object* v_a_1280_, lean_object* v_a_1281_){
_start:
{
lean_object* v___x_1283_; 
lean_inc(v_a_1281_);
lean_inc_ref(v_a_1280_);
lean_inc(v_a_1279_);
lean_inc_ref(v_a_1278_);
v___x_1283_ = lean_infer_type(v_e_1277_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
if (lean_obj_tag(v___x_1283_) == 0)
{
lean_object* v_a_1284_; lean_object* v___x_1285_; uint8_t v___x_1286_; lean_object* v___x_1287_; lean_object* v___f_1288_; uint8_t v___x_1289_; lean_object* v___x_1290_; 
v_a_1284_ = lean_ctor_get(v___x_1283_, 0);
lean_inc(v_a_1284_);
lean_dec_ref_known(v___x_1283_, 1);
v___x_1285_ = lean_box(0);
v___x_1286_ = 0;
v___x_1287_ = lean_box(v___x_1286_);
v___f_1288_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___lam__0___boxed), 8, 3);
lean_closure_set(v___f_1288_, 0, v_a_1284_);
lean_closure_set(v___f_1288_, 1, v___x_1285_);
lean_closure_set(v___f_1288_, 2, v___x_1287_);
v___x_1289_ = 0;
v___x_1290_ = l_Lean_Meta_withNewMCtxDepth___at___00__private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey_spec__0___redArg(v___f_1288_, v___x_1289_, v_a_1278_, v_a_1279_, v_a_1280_, v_a_1281_);
return v___x_1290_;
}
else
{
lean_object* v_a_1291_; lean_object* v___x_1293_; uint8_t v_isShared_1294_; uint8_t v_isSharedCheck_1298_; 
v_a_1291_ = lean_ctor_get(v___x_1283_, 0);
v_isSharedCheck_1298_ = !lean_is_exclusive(v___x_1283_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1293_ = v___x_1283_;
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
else
{
lean_inc(v_a_1291_);
lean_dec(v___x_1283_);
v___x_1293_ = lean_box(0);
v_isShared_1294_ = v_isSharedCheck_1298_;
goto v_resetjp_1292_;
}
v_resetjp_1292_:
{
lean_object* v___x_1296_; 
if (v_isShared_1294_ == 0)
{
v___x_1296_ = v___x_1293_;
goto v_reusejp_1295_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_a_1291_);
v___x_1296_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1295_;
}
v_reusejp_1295_:
{
return v___x_1296_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey___boxed(lean_object* v_e_1299_, lean_object* v_a_1300_, lean_object* v_a_1301_, lean_object* v_a_1302_, lean_object* v_a_1303_, lean_object* v_a_1304_){
_start:
{
lean_object* v_res_1305_; 
v_res_1305_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_e_1299_, v_a_1300_, v_a_1301_, v_a_1302_, v_a_1303_);
lean_dec(v_a_1303_);
lean_dec_ref(v_a_1302_);
lean_dec(v_a_1301_);
lean_dec_ref(v_a_1300_);
return v_res_1305_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(lean_object* v_k_1306_, lean_object* v_b_1307_, lean_object* v_c_1308_, lean_object* v___y_1309_, lean_object* v___y_1310_, lean_object* v___y_1311_, lean_object* v___y_1312_){
_start:
{
lean_object* v___x_1314_; 
lean_inc(v___y_1312_);
lean_inc_ref(v___y_1311_);
lean_inc(v___y_1310_);
lean_inc_ref(v___y_1309_);
v___x_1314_ = lean_apply_7(v_k_1306_, v_b_1307_, v_c_1308_, v___y_1309_, v___y_1310_, v___y_1311_, v___y_1312_, lean_box(0));
return v___x_1314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed(lean_object* v_k_1315_, lean_object* v_b_1316_, lean_object* v_c_1317_, lean_object* v___y_1318_, lean_object* v___y_1319_, lean_object* v___y_1320_, lean_object* v___y_1321_, lean_object* v___y_1322_){
_start:
{
lean_object* v_res_1323_; 
v_res_1323_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0(v_k_1315_, v_b_1316_, v_c_1317_, v___y_1318_, v___y_1319_, v___y_1320_, v___y_1321_);
lean_dec(v___y_1321_);
lean_dec_ref(v___y_1320_);
lean_dec(v___y_1319_);
lean_dec_ref(v___y_1318_);
return v_res_1323_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(lean_object* v_type_1324_, lean_object* v_k_1325_, uint8_t v_cleanupAnnotations_1326_, uint8_t v_whnfType_1327_, lean_object* v___y_1328_, lean_object* v___y_1329_, lean_object* v___y_1330_, lean_object* v___y_1331_){
_start:
{
lean_object* v___f_1333_; lean_object* v___x_1334_; 
v___f_1333_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1333_, 0, v_k_1325_);
v___x_1334_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingImp(lean_box(0), v_type_1324_, v___f_1333_, v_cleanupAnnotations_1326_, v_whnfType_1327_, v___y_1328_, v___y_1329_, v___y_1330_, v___y_1331_);
if (lean_obj_tag(v___x_1334_) == 0)
{
lean_object* v_a_1335_; lean_object* v___x_1337_; uint8_t v_isShared_1338_; uint8_t v_isSharedCheck_1342_; 
v_a_1335_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1342_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1342_ == 0)
{
v___x_1337_ = v___x_1334_;
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
else
{
lean_inc(v_a_1335_);
lean_dec(v___x_1334_);
v___x_1337_ = lean_box(0);
v_isShared_1338_ = v_isSharedCheck_1342_;
goto v_resetjp_1336_;
}
v_resetjp_1336_:
{
lean_object* v___x_1340_; 
if (v_isShared_1338_ == 0)
{
v___x_1340_ = v___x_1337_;
goto v_reusejp_1339_;
}
else
{
lean_object* v_reuseFailAlloc_1341_; 
v_reuseFailAlloc_1341_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1341_, 0, v_a_1335_);
v___x_1340_ = v_reuseFailAlloc_1341_;
goto v_reusejp_1339_;
}
v_reusejp_1339_:
{
return v___x_1340_;
}
}
}
else
{
lean_object* v_a_1343_; lean_object* v___x_1345_; uint8_t v_isShared_1346_; uint8_t v_isSharedCheck_1350_; 
v_a_1343_ = lean_ctor_get(v___x_1334_, 0);
v_isSharedCheck_1350_ = !lean_is_exclusive(v___x_1334_);
if (v_isSharedCheck_1350_ == 0)
{
v___x_1345_ = v___x_1334_;
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
else
{
lean_inc(v_a_1343_);
lean_dec(v___x_1334_);
v___x_1345_ = lean_box(0);
v_isShared_1346_ = v_isSharedCheck_1350_;
goto v_resetjp_1344_;
}
v_resetjp_1344_:
{
lean_object* v___x_1348_; 
if (v_isShared_1346_ == 0)
{
v___x_1348_ = v___x_1345_;
goto v_reusejp_1347_;
}
else
{
lean_object* v_reuseFailAlloc_1349_; 
v_reuseFailAlloc_1349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1349_, 0, v_a_1343_);
v___x_1348_ = v_reuseFailAlloc_1349_;
goto v_reusejp_1347_;
}
v_reusejp_1347_:
{
return v___x_1348_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___boxed(lean_object* v_type_1351_, lean_object* v_k_1352_, lean_object* v_cleanupAnnotations_1353_, lean_object* v_whnfType_1354_, lean_object* v___y_1355_, lean_object* v___y_1356_, lean_object* v___y_1357_, lean_object* v___y_1358_, lean_object* v___y_1359_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1360_; uint8_t v_whnfType_boxed_1361_; lean_object* v_res_1362_; 
v_cleanupAnnotations_boxed_1360_ = lean_unbox(v_cleanupAnnotations_1353_);
v_whnfType_boxed_1361_ = lean_unbox(v_whnfType_1354_);
v_res_1362_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1351_, v_k_1352_, v_cleanupAnnotations_boxed_1360_, v_whnfType_boxed_1361_, v___y_1355_, v___y_1356_, v___y_1357_, v___y_1358_);
lean_dec(v___y_1358_);
lean_dec_ref(v___y_1357_);
lean_dec(v___y_1356_);
lean_dec_ref(v___y_1355_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(lean_object* v_00_u03b1_1363_, lean_object* v_type_1364_, lean_object* v_k_1365_, uint8_t v_cleanupAnnotations_1366_, uint8_t v_whnfType_1367_, lean_object* v___y_1368_, lean_object* v___y_1369_, lean_object* v___y_1370_, lean_object* v___y_1371_){
_start:
{
lean_object* v___x_1373_; 
v___x_1373_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_type_1364_, v_k_1365_, v_cleanupAnnotations_1366_, v_whnfType_1367_, v___y_1368_, v___y_1369_, v___y_1370_, v___y_1371_);
return v___x_1373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___boxed(lean_object* v_00_u03b1_1374_, lean_object* v_type_1375_, lean_object* v_k_1376_, lean_object* v_cleanupAnnotations_1377_, lean_object* v_whnfType_1378_, lean_object* v___y_1379_, lean_object* v___y_1380_, lean_object* v___y_1381_, lean_object* v___y_1382_, lean_object* v___y_1383_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_1384_; uint8_t v_whnfType_boxed_1385_; lean_object* v_res_1386_; 
v_cleanupAnnotations_boxed_1384_ = lean_unbox(v_cleanupAnnotations_1377_);
v_whnfType_boxed_1385_ = lean_unbox(v_whnfType_1378_);
v_res_1386_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1(v_00_u03b1_1374_, v_type_1375_, v_k_1376_, v_cleanupAnnotations_boxed_1384_, v_whnfType_boxed_1385_, v___y_1379_, v___y_1380_, v___y_1381_, v___y_1382_);
lean_dec(v___y_1382_);
lean_dec_ref(v___y_1381_);
lean_dec(v___y_1380_);
lean_dec_ref(v___y_1379_);
return v_res_1386_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(lean_object* v_as_1390_, size_t v_sz_1391_, size_t v_i_1392_, lean_object* v_b_1393_, lean_object* v___y_1394_, lean_object* v___y_1395_, lean_object* v___y_1396_, lean_object* v___y_1397_){
_start:
{
uint8_t v___x_1399_; 
v___x_1399_ = lean_usize_dec_lt(v_i_1392_, v_sz_1391_);
if (v___x_1399_ == 0)
{
lean_object* v___x_1400_; 
v___x_1400_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1400_, 0, v_b_1393_);
return v___x_1400_;
}
else
{
lean_object* v_fst_1401_; lean_object* v_snd_1402_; lean_object* v___x_1404_; uint8_t v_isShared_1405_; uint8_t v_isSharedCheck_1454_; 
v_fst_1401_ = lean_ctor_get(v_b_1393_, 0);
v_snd_1402_ = lean_ctor_get(v_b_1393_, 1);
v_isSharedCheck_1454_ = !lean_is_exclusive(v_b_1393_);
if (v_isSharedCheck_1454_ == 0)
{
v___x_1404_ = v_b_1393_;
v_isShared_1405_ = v_isSharedCheck_1454_;
goto v_resetjp_1403_;
}
else
{
lean_inc(v_snd_1402_);
lean_inc(v_fst_1401_);
lean_dec(v_b_1393_);
v___x_1404_ = lean_box(0);
v_isShared_1405_ = v_isSharedCheck_1454_;
goto v_resetjp_1403_;
}
v_resetjp_1403_:
{
lean_object* v_next_1411_; 
v_next_1411_ = lean_ctor_get(v_snd_1402_, 0);
lean_inc(v_next_1411_);
if (lean_obj_tag(v_next_1411_) == 0)
{
goto v___jp_1406_;
}
else
{
lean_object* v_upperBound_1412_; lean_object* v_val_1413_; lean_object* v___x_1415_; uint8_t v_isShared_1416_; uint8_t v_isSharedCheck_1453_; 
v_upperBound_1412_ = lean_ctor_get(v_snd_1402_, 1);
v_val_1413_ = lean_ctor_get(v_next_1411_, 0);
v_isSharedCheck_1453_ = !lean_is_exclusive(v_next_1411_);
if (v_isSharedCheck_1453_ == 0)
{
v___x_1415_ = v_next_1411_;
v_isShared_1416_ = v_isSharedCheck_1453_;
goto v_resetjp_1414_;
}
else
{
lean_inc(v_val_1413_);
lean_dec(v_next_1411_);
v___x_1415_ = lean_box(0);
v_isShared_1416_ = v_isSharedCheck_1453_;
goto v_resetjp_1414_;
}
v_resetjp_1414_:
{
uint8_t v___x_1417_; 
v___x_1417_ = lean_nat_dec_lt(v_val_1413_, v_upperBound_1412_);
if (v___x_1417_ == 0)
{
lean_del_object(v___x_1415_);
lean_dec(v_val_1413_);
goto v___jp_1406_;
}
else
{
lean_object* v___x_1419_; uint8_t v_isShared_1420_; uint8_t v_isSharedCheck_1450_; 
lean_inc(v_upperBound_1412_);
lean_del_object(v___x_1404_);
v_isSharedCheck_1450_ = !lean_is_exclusive(v_snd_1402_);
if (v_isSharedCheck_1450_ == 0)
{
lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1451_ = lean_ctor_get(v_snd_1402_, 1);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_snd_1402_, 0);
lean_dec(v_unused_1452_);
v___x_1419_ = v_snd_1402_;
v_isShared_1420_ = v_isSharedCheck_1450_;
goto v_resetjp_1418_;
}
else
{
lean_dec(v_snd_1402_);
v___x_1419_ = lean_box(0);
v_isShared_1420_ = v_isSharedCheck_1450_;
goto v_resetjp_1418_;
}
v_resetjp_1418_:
{
lean_object* v_a_1421_; lean_object* v___x_1422_; 
v_a_1421_ = lean_array_uget_borrowed(v_as_1390_, v_i_1392_);
lean_inc(v___y_1397_);
lean_inc_ref(v___y_1396_);
lean_inc(v___y_1395_);
lean_inc_ref(v___y_1394_);
lean_inc(v_a_1421_);
v___x_1422_ = lean_infer_type(v_a_1421_, v___y_1394_, v___y_1395_, v___y_1396_, v___y_1397_);
if (lean_obj_tag(v___x_1422_) == 0)
{
lean_object* v_a_1423_; lean_object* v_a_1425_; lean_object* v___x_1429_; lean_object* v___x_1430_; lean_object* v___x_1432_; 
v_a_1423_ = lean_ctor_get(v___x_1422_, 0);
lean_inc(v_a_1423_);
lean_dec_ref_known(v___x_1422_, 1);
v___x_1429_ = lean_unsigned_to_nat(1u);
v___x_1430_ = lean_nat_add(v_val_1413_, v___x_1429_);
if (v_isShared_1416_ == 0)
{
lean_ctor_set(v___x_1415_, 0, v___x_1430_);
v___x_1432_ = v___x_1415_;
goto v_reusejp_1431_;
}
else
{
lean_object* v_reuseFailAlloc_1441_; 
v_reuseFailAlloc_1441_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1441_, 0, v___x_1430_);
v___x_1432_ = v_reuseFailAlloc_1441_;
goto v_reusejp_1431_;
}
v___jp_1424_:
{
size_t v___x_1426_; size_t v___x_1427_; 
v___x_1426_ = ((size_t)1ULL);
v___x_1427_ = lean_usize_add(v_i_1392_, v___x_1426_);
v_i_1392_ = v___x_1427_;
v_b_1393_ = v_a_1425_;
goto _start;
}
v_reusejp_1431_:
{
lean_object* v___x_1434_; 
if (v_isShared_1420_ == 0)
{
lean_ctor_set(v___x_1419_, 0, v___x_1432_);
v___x_1434_ = v___x_1419_;
goto v_reusejp_1433_;
}
else
{
lean_object* v_reuseFailAlloc_1440_; 
v_reuseFailAlloc_1440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1440_, 0, v___x_1432_);
lean_ctor_set(v_reuseFailAlloc_1440_, 1, v_upperBound_1412_);
v___x_1434_ = v_reuseFailAlloc_1440_;
goto v_reusejp_1433_;
}
v_reusejp_1433_:
{
lean_object* v___x_1435_; uint8_t v___x_1436_; 
v___x_1435_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___closed__1));
v___x_1436_ = l_Lean_Expr_isAppOf(v_a_1423_, v___x_1435_);
lean_dec(v_a_1423_);
if (v___x_1436_ == 0)
{
lean_object* v___x_1437_; 
lean_dec(v_val_1413_);
v___x_1437_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1437_, 0, v_fst_1401_);
lean_ctor_set(v___x_1437_, 1, v___x_1434_);
v_a_1425_ = v___x_1437_;
goto v___jp_1424_;
}
else
{
lean_object* v___x_1438_; lean_object* v___x_1439_; 
v___x_1438_ = lean_array_push(v_fst_1401_, v_val_1413_);
v___x_1439_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1439_, 0, v___x_1438_);
lean_ctor_set(v___x_1439_, 1, v___x_1434_);
v_a_1425_ = v___x_1439_;
goto v___jp_1424_;
}
}
}
}
else
{
lean_object* v_a_1442_; lean_object* v___x_1444_; uint8_t v_isShared_1445_; uint8_t v_isSharedCheck_1449_; 
lean_del_object(v___x_1419_);
lean_del_object(v___x_1415_);
lean_dec(v_val_1413_);
lean_dec(v_upperBound_1412_);
lean_dec(v_fst_1401_);
v_a_1442_ = lean_ctor_get(v___x_1422_, 0);
v_isSharedCheck_1449_ = !lean_is_exclusive(v___x_1422_);
if (v_isSharedCheck_1449_ == 0)
{
v___x_1444_ = v___x_1422_;
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
else
{
lean_inc(v_a_1442_);
lean_dec(v___x_1422_);
v___x_1444_ = lean_box(0);
v_isShared_1445_ = v_isSharedCheck_1449_;
goto v_resetjp_1443_;
}
v_resetjp_1443_:
{
lean_object* v___x_1447_; 
if (v_isShared_1445_ == 0)
{
v___x_1447_ = v___x_1444_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_a_1442_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
}
}
}
v___jp_1406_:
{
lean_object* v___x_1408_; 
if (v_isShared_1405_ == 0)
{
v___x_1408_ = v___x_1404_;
goto v_reusejp_1407_;
}
else
{
lean_object* v_reuseFailAlloc_1410_; 
v_reuseFailAlloc_1410_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1410_, 0, v_fst_1401_);
lean_ctor_set(v_reuseFailAlloc_1410_, 1, v_snd_1402_);
v___x_1408_ = v_reuseFailAlloc_1410_;
goto v_reusejp_1407_;
}
v_reusejp_1407_:
{
lean_object* v___x_1409_; 
v___x_1409_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
return v___x_1409_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0___boxed(lean_object* v_as_1455_, lean_object* v_sz_1456_, lean_object* v_i_1457_, lean_object* v_b_1458_, lean_object* v___y_1459_, lean_object* v___y_1460_, lean_object* v___y_1461_, lean_object* v___y_1462_, lean_object* v___y_1463_){
_start:
{
size_t v_sz_boxed_1464_; size_t v_i_boxed_1465_; lean_object* v_res_1466_; 
v_sz_boxed_1464_ = lean_unbox_usize(v_sz_1456_);
lean_dec(v_sz_1456_);
v_i_boxed_1465_ = lean_unbox_usize(v_i_1457_);
lean_dec(v_i_1457_);
v_res_1466_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_as_1455_, v_sz_boxed_1464_, v_i_boxed_1465_, v_b_1458_, v___y_1459_, v___y_1460_, v___y_1461_, v___y_1462_);
lean_dec(v___y_1462_);
lean_dec_ref(v___y_1461_);
lean_dec(v___y_1460_);
lean_dec_ref(v___y_1459_);
lean_dec_ref(v_as_1455_);
return v_res_1466_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(lean_object* v_declName_1471_, lean_object* v_args_1472_, lean_object* v_x_1473_, lean_object* v___y_1474_, lean_object* v___y_1475_, lean_object* v___y_1476_, lean_object* v___y_1477_){
_start:
{
lean_object* v___x_1479_; lean_object* v___y_1481_; lean_object* v_env_1506_; lean_object* v___x_1507_; 
v___x_1479_ = lean_st_ref_get(v___y_1477_);
v_env_1506_ = lean_ctor_get(v___x_1479_, 0);
lean_inc_ref(v_env_1506_);
lean_dec(v___x_1479_);
v___x_1507_ = l_Lean_getOutParamPositions_x3f(v_env_1506_, v_declName_1471_);
if (lean_obj_tag(v___x_1507_) == 0)
{
lean_object* v___x_1508_; 
v___x_1508_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___y_1481_ = v___x_1508_;
goto v___jp_1480_;
}
else
{
lean_object* v_val_1509_; 
v_val_1509_ = lean_ctor_get(v___x_1507_, 0);
lean_inc(v_val_1509_);
lean_dec_ref_known(v___x_1507_, 1);
v___y_1481_ = v_val_1509_;
goto v___jp_1480_;
}
v___jp_1480_:
{
lean_object* v___x_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; size_t v_sz_1486_; size_t v___x_1487_; lean_object* v___x_1488_; 
v___x_1482_ = lean_array_get_size(v_args_1472_);
v___x_1483_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_1484_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1484_, 0, v___x_1483_);
lean_ctor_set(v___x_1484_, 1, v___x_1482_);
v___x_1485_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1485_, 0, v___y_1481_);
lean_ctor_set(v___x_1485_, 1, v___x_1484_);
v_sz_1486_ = lean_array_size(v_args_1472_);
v___x_1487_ = ((size_t)0ULL);
v___x_1488_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__0(v_args_1472_, v_sz_1486_, v___x_1487_, v___x_1485_, v___y_1474_, v___y_1475_, v___y_1476_, v___y_1477_);
if (lean_obj_tag(v___x_1488_) == 0)
{
lean_object* v_a_1489_; lean_object* v___x_1491_; uint8_t v_isShared_1492_; uint8_t v_isSharedCheck_1497_; 
v_a_1489_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1497_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1497_ == 0)
{
v___x_1491_ = v___x_1488_;
v_isShared_1492_ = v_isSharedCheck_1497_;
goto v_resetjp_1490_;
}
else
{
lean_inc(v_a_1489_);
lean_dec(v___x_1488_);
v___x_1491_ = lean_box(0);
v_isShared_1492_ = v_isSharedCheck_1497_;
goto v_resetjp_1490_;
}
v_resetjp_1490_:
{
lean_object* v_fst_1493_; lean_object* v___x_1495_; 
v_fst_1493_ = lean_ctor_get(v_a_1489_, 0);
lean_inc(v_fst_1493_);
lean_dec(v_a_1489_);
if (v_isShared_1492_ == 0)
{
lean_ctor_set(v___x_1491_, 0, v_fst_1493_);
v___x_1495_ = v___x_1491_;
goto v_reusejp_1494_;
}
else
{
lean_object* v_reuseFailAlloc_1496_; 
v_reuseFailAlloc_1496_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1496_, 0, v_fst_1493_);
v___x_1495_ = v_reuseFailAlloc_1496_;
goto v_reusejp_1494_;
}
v_reusejp_1494_:
{
return v___x_1495_;
}
}
}
else
{
lean_object* v_a_1498_; lean_object* v___x_1500_; uint8_t v_isShared_1501_; uint8_t v_isSharedCheck_1505_; 
v_a_1498_ = lean_ctor_get(v___x_1488_, 0);
v_isSharedCheck_1505_ = !lean_is_exclusive(v___x_1488_);
if (v_isSharedCheck_1505_ == 0)
{
v___x_1500_ = v___x_1488_;
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
else
{
lean_inc(v_a_1498_);
lean_dec(v___x_1488_);
v___x_1500_ = lean_box(0);
v_isShared_1501_ = v_isSharedCheck_1505_;
goto v_resetjp_1499_;
}
v_resetjp_1499_:
{
lean_object* v___x_1503_; 
if (v_isShared_1501_ == 0)
{
v___x_1503_ = v___x_1500_;
goto v_reusejp_1502_;
}
else
{
lean_object* v_reuseFailAlloc_1504_; 
v_reuseFailAlloc_1504_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1504_, 0, v_a_1498_);
v___x_1503_ = v_reuseFailAlloc_1504_;
goto v_reusejp_1502_;
}
v_reusejp_1502_:
{
return v___x_1503_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed(lean_object* v_declName_1510_, lean_object* v_args_1511_, lean_object* v_x_1512_, lean_object* v___y_1513_, lean_object* v___y_1514_, lean_object* v___y_1515_, lean_object* v___y_1516_, lean_object* v___y_1517_){
_start:
{
lean_object* v_res_1518_; 
v_res_1518_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0(v_declName_1510_, v_args_1511_, v_x_1512_, v___y_1513_, v___y_1514_, v___y_1515_, v___y_1516_);
lean_dec(v___y_1516_);
lean_dec_ref(v___y_1515_);
lean_dec(v___y_1514_);
lean_dec_ref(v___y_1513_);
lean_dec_ref(v_x_1512_);
lean_dec_ref(v_args_1511_);
lean_dec(v_declName_1510_);
return v_res_1518_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(lean_object* v_classTy_1519_, lean_object* v_a_1520_, lean_object* v_a_1521_, lean_object* v_a_1522_, lean_object* v_a_1523_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_Lean_Expr_getAppFn(v_classTy_1519_);
if (lean_obj_tag(v___x_1525_) == 4)
{
lean_object* v_declName_1526_; lean_object* v___x_1527_; 
v_declName_1526_ = lean_ctor_get(v___x_1525_, 0);
lean_inc(v_declName_1526_);
lean_inc(v_a_1523_);
lean_inc_ref(v_a_1522_);
lean_inc(v_a_1521_);
lean_inc_ref(v_a_1520_);
v___x_1527_ = lean_infer_type(v___x_1525_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
if (lean_obj_tag(v___x_1527_) == 0)
{
lean_object* v_a_1528_; lean_object* v___f_1529_; uint8_t v___x_1530_; lean_object* v___x_1531_; 
v_a_1528_ = lean_ctor_get(v___x_1527_, 0);
lean_inc(v_a_1528_);
lean_dec_ref_known(v___x_1527_, 1);
v___f_1529_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___boxed), 8, 1);
lean_closure_set(v___f_1529_, 0, v_declName_1526_);
v___x_1530_ = 0;
v___x_1531_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_1528_, v___f_1529_, v___x_1530_, v___x_1530_, v_a_1520_, v_a_1521_, v_a_1522_, v_a_1523_);
return v___x_1531_;
}
else
{
lean_object* v_a_1532_; lean_object* v___x_1534_; uint8_t v_isShared_1535_; uint8_t v_isSharedCheck_1539_; 
lean_dec(v_declName_1526_);
v_a_1532_ = lean_ctor_get(v___x_1527_, 0);
v_isSharedCheck_1539_ = !lean_is_exclusive(v___x_1527_);
if (v_isSharedCheck_1539_ == 0)
{
v___x_1534_ = v___x_1527_;
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
else
{
lean_inc(v_a_1532_);
lean_dec(v___x_1527_);
v___x_1534_ = lean_box(0);
v_isShared_1535_ = v_isSharedCheck_1539_;
goto v_resetjp_1533_;
}
v_resetjp_1533_:
{
lean_object* v___x_1537_; 
if (v_isShared_1535_ == 0)
{
v___x_1537_ = v___x_1534_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_a_1532_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
else
{
lean_object* v___x_1540_; lean_object* v___x_1541_; 
lean_dec_ref(v___x_1525_);
v___x_1540_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_1541_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1541_, 0, v___x_1540_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___boxed(lean_object* v_classTy_1542_, lean_object* v_a_1543_, lean_object* v_a_1544_, lean_object* v_a_1545_, lean_object* v_a_1546_, lean_object* v_a_1547_){
_start:
{
lean_object* v_res_1548_; 
v_res_1548_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_classTy_1542_, v_a_1543_, v_a_1544_, v_a_1545_, v_a_1546_);
lean_dec(v_a_1546_);
lean_dec_ref(v_a_1545_);
lean_dec(v_a_1544_);
lean_dec_ref(v_a_1543_);
lean_dec_ref(v_classTy_1542_);
return v_res_1548_;
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(lean_object* v_a_1549_, lean_object* v_as_1550_, lean_object* v_j_1551_){
_start:
{
lean_object* v___x_1552_; uint8_t v___x_1553_; 
v___x_1552_ = lean_array_get_size(v_as_1550_);
v___x_1553_ = lean_nat_dec_lt(v_j_1551_, v___x_1552_);
if (v___x_1553_ == 0)
{
lean_object* v___x_1554_; 
lean_dec(v_j_1551_);
v___x_1554_ = lean_box(0);
return v___x_1554_;
}
else
{
lean_object* v___x_1555_; lean_object* v___x_1556_; uint8_t v___x_1557_; 
v___x_1555_ = lean_array_fget_borrowed(v_as_1550_, v_j_1551_);
v___x_1556_ = l_Lean_Expr_mvarId_x21(v___x_1555_);
v___x_1557_ = l_Lean_instBEqMVarId_beq(v___x_1556_, v_a_1549_);
lean_dec(v___x_1556_);
if (v___x_1557_ == 0)
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_unsigned_to_nat(1u);
v___x_1559_ = lean_nat_add(v_j_1551_, v___x_1558_);
lean_dec(v_j_1551_);
v_j_1551_ = v___x_1559_;
goto _start;
}
else
{
lean_object* v___x_1561_; 
v___x_1561_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1561_, 0, v_j_1551_);
return v___x_1561_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0___boxed(lean_object* v_a_1562_, lean_object* v_as_1563_, lean_object* v_j_1564_){
_start:
{
lean_object* v_res_1565_; 
v_res_1565_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1562_, v_as_1563_, v_j_1564_);
lean_dec_ref(v_as_1563_);
lean_dec(v_a_1562_);
return v_res_1565_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(lean_object* v_x_1566_, lean_object* v_x_1567_, lean_object* v_x_1568_, lean_object* v_x_1569_){
_start:
{
lean_object* v_ks_1570_; lean_object* v_vs_1571_; lean_object* v___x_1573_; uint8_t v_isShared_1574_; uint8_t v_isSharedCheck_1595_; 
v_ks_1570_ = lean_ctor_get(v_x_1566_, 0);
v_vs_1571_ = lean_ctor_get(v_x_1566_, 1);
v_isSharedCheck_1595_ = !lean_is_exclusive(v_x_1566_);
if (v_isSharedCheck_1595_ == 0)
{
v___x_1573_ = v_x_1566_;
v_isShared_1574_ = v_isSharedCheck_1595_;
goto v_resetjp_1572_;
}
else
{
lean_inc(v_vs_1571_);
lean_inc(v_ks_1570_);
lean_dec(v_x_1566_);
v___x_1573_ = lean_box(0);
v_isShared_1574_ = v_isSharedCheck_1595_;
goto v_resetjp_1572_;
}
v_resetjp_1572_:
{
lean_object* v___x_1575_; uint8_t v___x_1576_; 
v___x_1575_ = lean_array_get_size(v_ks_1570_);
v___x_1576_ = lean_nat_dec_lt(v_x_1567_, v___x_1575_);
if (v___x_1576_ == 0)
{
lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; 
lean_dec(v_x_1567_);
v___x_1577_ = lean_array_push(v_ks_1570_, v_x_1568_);
v___x_1578_ = lean_array_push(v_vs_1571_, v_x_1569_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v___x_1578_);
lean_ctor_set(v___x_1573_, 0, v___x_1577_);
v___x_1580_ = v___x_1573_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v___x_1577_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1578_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
else
{
lean_object* v_k_x27_1582_; uint8_t v___x_1583_; 
v_k_x27_1582_ = lean_array_fget_borrowed(v_ks_1570_, v_x_1567_);
v___x_1583_ = l_Lean_instBEqMVarId_beq(v_x_1568_, v_k_x27_1582_);
if (v___x_1583_ == 0)
{
lean_object* v___x_1585_; 
if (v_isShared_1574_ == 0)
{
v___x_1585_ = v___x_1573_;
goto v_reusejp_1584_;
}
else
{
lean_object* v_reuseFailAlloc_1589_; 
v_reuseFailAlloc_1589_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1589_, 0, v_ks_1570_);
lean_ctor_set(v_reuseFailAlloc_1589_, 1, v_vs_1571_);
v___x_1585_ = v_reuseFailAlloc_1589_;
goto v_reusejp_1584_;
}
v_reusejp_1584_:
{
lean_object* v___x_1586_; lean_object* v___x_1587_; 
v___x_1586_ = lean_unsigned_to_nat(1u);
v___x_1587_ = lean_nat_add(v_x_1567_, v___x_1586_);
lean_dec(v_x_1567_);
v_x_1566_ = v___x_1585_;
v_x_1567_ = v___x_1587_;
goto _start;
}
}
else
{
lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; 
v___x_1590_ = lean_array_fset(v_ks_1570_, v_x_1567_, v_x_1568_);
v___x_1591_ = lean_array_fset(v_vs_1571_, v_x_1567_, v_x_1569_);
lean_dec(v_x_1567_);
if (v_isShared_1574_ == 0)
{
lean_ctor_set(v___x_1573_, 1, v___x_1591_);
lean_ctor_set(v___x_1573_, 0, v___x_1590_);
v___x_1593_ = v___x_1573_;
goto v_reusejp_1592_;
}
else
{
lean_object* v_reuseFailAlloc_1594_; 
v_reuseFailAlloc_1594_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1594_, 0, v___x_1590_);
lean_ctor_set(v_reuseFailAlloc_1594_, 1, v___x_1591_);
v___x_1593_ = v_reuseFailAlloc_1594_;
goto v_reusejp_1592_;
}
v_reusejp_1592_:
{
return v___x_1593_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(lean_object* v_n_1596_, lean_object* v_k_1597_, lean_object* v_v_1598_){
_start:
{
lean_object* v___x_1599_; lean_object* v___x_1600_; 
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1600_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_n_1596_, v___x_1599_, v_k_1597_, v_v_1598_);
return v___x_1600_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(lean_object* v_x_1601_, size_t v_x_1602_, size_t v_x_1603_, lean_object* v_x_1604_, lean_object* v_x_1605_){
_start:
{
if (lean_obj_tag(v_x_1601_) == 0)
{
lean_object* v_es_1606_; size_t v___x_1607_; size_t v___x_1608_; lean_object* v_j_1609_; lean_object* v___x_1610_; uint8_t v___x_1611_; 
v_es_1606_ = lean_ctor_get(v_x_1601_, 0);
v___x_1607_ = ((size_t)31ULL);
v___x_1608_ = lean_usize_land(v_x_1602_, v___x_1607_);
v_j_1609_ = lean_usize_to_nat(v___x_1608_);
v___x_1610_ = lean_array_get_size(v_es_1606_);
v___x_1611_ = lean_nat_dec_lt(v_j_1609_, v___x_1610_);
if (v___x_1611_ == 0)
{
lean_dec(v_j_1609_);
lean_dec(v_x_1605_);
lean_dec(v_x_1604_);
return v_x_1601_;
}
else
{
lean_object* v___x_1613_; uint8_t v_isShared_1614_; uint8_t v_isSharedCheck_1650_; 
lean_inc_ref(v_es_1606_);
v_isSharedCheck_1650_ = !lean_is_exclusive(v_x_1601_);
if (v_isSharedCheck_1650_ == 0)
{
lean_object* v_unused_1651_; 
v_unused_1651_ = lean_ctor_get(v_x_1601_, 0);
lean_dec(v_unused_1651_);
v___x_1613_ = v_x_1601_;
v_isShared_1614_ = v_isSharedCheck_1650_;
goto v_resetjp_1612_;
}
else
{
lean_dec(v_x_1601_);
v___x_1613_ = lean_box(0);
v_isShared_1614_ = v_isSharedCheck_1650_;
goto v_resetjp_1612_;
}
v_resetjp_1612_:
{
lean_object* v_v_1615_; lean_object* v___x_1616_; lean_object* v_xs_x27_1617_; lean_object* v___y_1619_; 
v_v_1615_ = lean_array_fget(v_es_1606_, v_j_1609_);
v___x_1616_ = lean_box(0);
v_xs_x27_1617_ = lean_array_fset(v_es_1606_, v_j_1609_, v___x_1616_);
switch(lean_obj_tag(v_v_1615_))
{
case 0:
{
lean_object* v_key_1624_; lean_object* v_val_1625_; lean_object* v___x_1627_; uint8_t v_isShared_1628_; uint8_t v_isSharedCheck_1635_; 
v_key_1624_ = lean_ctor_get(v_v_1615_, 0);
v_val_1625_ = lean_ctor_get(v_v_1615_, 1);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_v_1615_);
if (v_isSharedCheck_1635_ == 0)
{
v___x_1627_ = v_v_1615_;
v_isShared_1628_ = v_isSharedCheck_1635_;
goto v_resetjp_1626_;
}
else
{
lean_inc(v_val_1625_);
lean_inc(v_key_1624_);
lean_dec(v_v_1615_);
v___x_1627_ = lean_box(0);
v_isShared_1628_ = v_isSharedCheck_1635_;
goto v_resetjp_1626_;
}
v_resetjp_1626_:
{
uint8_t v___x_1629_; 
v___x_1629_ = l_Lean_instBEqMVarId_beq(v_x_1604_, v_key_1624_);
if (v___x_1629_ == 0)
{
lean_object* v___x_1630_; lean_object* v___x_1631_; 
lean_del_object(v___x_1627_);
v___x_1630_ = l_Lean_PersistentHashMap_mkCollisionNode___redArg(v_key_1624_, v_val_1625_, v_x_1604_, v_x_1605_);
v___x_1631_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1631_, 0, v___x_1630_);
v___y_1619_ = v___x_1631_;
goto v___jp_1618_;
}
else
{
lean_object* v___x_1633_; 
lean_dec(v_val_1625_);
lean_dec(v_key_1624_);
if (v_isShared_1628_ == 0)
{
lean_ctor_set(v___x_1627_, 1, v_x_1605_);
lean_ctor_set(v___x_1627_, 0, v_x_1604_);
v___x_1633_ = v___x_1627_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_x_1604_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_x_1605_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
v___y_1619_ = v___x_1633_;
goto v___jp_1618_;
}
}
}
}
case 1:
{
lean_object* v_node_1636_; lean_object* v___x_1638_; uint8_t v_isShared_1639_; uint8_t v_isSharedCheck_1648_; 
v_node_1636_ = lean_ctor_get(v_v_1615_, 0);
v_isSharedCheck_1648_ = !lean_is_exclusive(v_v_1615_);
if (v_isSharedCheck_1648_ == 0)
{
v___x_1638_ = v_v_1615_;
v_isShared_1639_ = v_isSharedCheck_1648_;
goto v_resetjp_1637_;
}
else
{
lean_inc(v_node_1636_);
lean_dec(v_v_1615_);
v___x_1638_ = lean_box(0);
v_isShared_1639_ = v_isSharedCheck_1648_;
goto v_resetjp_1637_;
}
v_resetjp_1637_:
{
size_t v___x_1640_; size_t v___x_1641_; size_t v___x_1642_; size_t v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; 
v___x_1640_ = ((size_t)5ULL);
v___x_1641_ = lean_usize_shift_right(v_x_1602_, v___x_1640_);
v___x_1642_ = ((size_t)1ULL);
v___x_1643_ = lean_usize_add(v_x_1603_, v___x_1642_);
v___x_1644_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_node_1636_, v___x_1641_, v___x_1643_, v_x_1604_, v_x_1605_);
if (v_isShared_1639_ == 0)
{
lean_ctor_set(v___x_1638_, 0, v___x_1644_);
v___x_1646_ = v___x_1638_;
goto v_reusejp_1645_;
}
else
{
lean_object* v_reuseFailAlloc_1647_; 
v_reuseFailAlloc_1647_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1647_, 0, v___x_1644_);
v___x_1646_ = v_reuseFailAlloc_1647_;
goto v_reusejp_1645_;
}
v_reusejp_1645_:
{
v___y_1619_ = v___x_1646_;
goto v___jp_1618_;
}
}
}
default: 
{
lean_object* v___x_1649_; 
v___x_1649_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1649_, 0, v_x_1604_);
lean_ctor_set(v___x_1649_, 1, v_x_1605_);
v___y_1619_ = v___x_1649_;
goto v___jp_1618_;
}
}
v___jp_1618_:
{
lean_object* v___x_1620_; lean_object* v___x_1622_; 
v___x_1620_ = lean_array_fset(v_xs_x27_1617_, v_j_1609_, v___y_1619_);
lean_dec(v_j_1609_);
if (v_isShared_1614_ == 0)
{
lean_ctor_set(v___x_1613_, 0, v___x_1620_);
v___x_1622_ = v___x_1613_;
goto v_reusejp_1621_;
}
else
{
lean_object* v_reuseFailAlloc_1623_; 
v_reuseFailAlloc_1623_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1623_, 0, v___x_1620_);
v___x_1622_ = v_reuseFailAlloc_1623_;
goto v_reusejp_1621_;
}
v_reusejp_1621_:
{
return v___x_1622_;
}
}
}
}
}
else
{
lean_object* v_ks_1652_; lean_object* v_vs_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1673_; 
v_ks_1652_ = lean_ctor_get(v_x_1601_, 0);
v_vs_1653_ = lean_ctor_get(v_x_1601_, 1);
v_isSharedCheck_1673_ = !lean_is_exclusive(v_x_1601_);
if (v_isSharedCheck_1673_ == 0)
{
v___x_1655_ = v_x_1601_;
v_isShared_1656_ = v_isSharedCheck_1673_;
goto v_resetjp_1654_;
}
else
{
lean_inc(v_vs_1653_);
lean_inc(v_ks_1652_);
lean_dec(v_x_1601_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1673_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1658_; 
if (v_isShared_1656_ == 0)
{
v___x_1658_ = v___x_1655_;
goto v_reusejp_1657_;
}
else
{
lean_object* v_reuseFailAlloc_1672_; 
v_reuseFailAlloc_1672_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1672_, 0, v_ks_1652_);
lean_ctor_set(v_reuseFailAlloc_1672_, 1, v_vs_1653_);
v___x_1658_ = v_reuseFailAlloc_1672_;
goto v_reusejp_1657_;
}
v_reusejp_1657_:
{
lean_object* v_newNode_1659_; uint8_t v___y_1661_; size_t v___x_1667_; uint8_t v___x_1668_; 
v_newNode_1659_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v___x_1658_, v_x_1604_, v_x_1605_);
v___x_1667_ = ((size_t)7ULL);
v___x_1668_ = lean_usize_dec_le(v___x_1667_, v_x_1603_);
if (v___x_1668_ == 0)
{
lean_object* v___x_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v___x_1669_ = l_Lean_PersistentHashMap_getCollisionNodeSize___redArg(v_newNode_1659_);
v___x_1670_ = lean_unsigned_to_nat(4u);
v___x_1671_ = lean_nat_dec_lt(v___x_1669_, v___x_1670_);
lean_dec(v___x_1669_);
v___y_1661_ = v___x_1671_;
goto v___jp_1660_;
}
else
{
v___y_1661_ = v___x_1668_;
goto v___jp_1660_;
}
v___jp_1660_:
{
if (v___y_1661_ == 0)
{
lean_object* v_ks_1662_; lean_object* v_vs_1663_; lean_object* v___x_1664_; lean_object* v___x_1665_; lean_object* v___x_1666_; 
v_ks_1662_ = lean_ctor_get(v_newNode_1659_, 0);
lean_inc_ref(v_ks_1662_);
v_vs_1663_ = lean_ctor_get(v_newNode_1659_, 1);
lean_inc_ref(v_vs_1663_);
lean_dec_ref(v_newNode_1659_);
v___x_1664_ = lean_unsigned_to_nat(0u);
v___x_1665_ = lean_obj_once(&l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0, &l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4___redArg___closed__0);
v___x_1666_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_x_1603_, v_ks_1662_, v_vs_1663_, v___x_1664_, v___x_1665_);
lean_dec_ref(v_vs_1663_);
lean_dec_ref(v_ks_1662_);
return v___x_1666_;
}
else
{
return v_newNode_1659_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(size_t v_depth_1674_, lean_object* v_keys_1675_, lean_object* v_vals_1676_, lean_object* v_i_1677_, lean_object* v_entries_1678_){
_start:
{
lean_object* v___x_1679_; uint8_t v___x_1680_; 
v___x_1679_ = lean_array_get_size(v_keys_1675_);
v___x_1680_ = lean_nat_dec_lt(v_i_1677_, v___x_1679_);
if (v___x_1680_ == 0)
{
lean_dec(v_i_1677_);
return v_entries_1678_;
}
else
{
lean_object* v_k_1681_; lean_object* v_v_1682_; uint64_t v___x_1683_; size_t v_h_1684_; size_t v___x_1685_; lean_object* v___x_1686_; size_t v___x_1687_; size_t v___x_1688_; size_t v___x_1689_; size_t v_h_1690_; lean_object* v___x_1691_; lean_object* v___x_1692_; 
v_k_1681_ = lean_array_fget_borrowed(v_keys_1675_, v_i_1677_);
v_v_1682_ = lean_array_fget_borrowed(v_vals_1676_, v_i_1677_);
v___x_1683_ = l_Lean_instHashableMVarId_hash(v_k_1681_);
v_h_1684_ = lean_uint64_to_usize(v___x_1683_);
v___x_1685_ = ((size_t)5ULL);
v___x_1686_ = lean_unsigned_to_nat(1u);
v___x_1687_ = ((size_t)1ULL);
v___x_1688_ = lean_usize_sub(v_depth_1674_, v___x_1687_);
v___x_1689_ = lean_usize_mul(v___x_1685_, v___x_1688_);
v_h_1690_ = lean_usize_shift_right(v_h_1684_, v___x_1689_);
v___x_1691_ = lean_nat_add(v_i_1677_, v___x_1686_);
lean_dec(v_i_1677_);
lean_inc(v_v_1682_);
lean_inc(v_k_1681_);
v___x_1692_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_entries_1678_, v_h_1690_, v_depth_1674_, v_k_1681_, v_v_1682_);
v_i_1677_ = v___x_1691_;
v_entries_1678_ = v___x_1692_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg___boxed(lean_object* v_depth_1694_, lean_object* v_keys_1695_, lean_object* v_vals_1696_, lean_object* v_i_1697_, lean_object* v_entries_1698_){
_start:
{
size_t v_depth_boxed_1699_; lean_object* v_res_1700_; 
v_depth_boxed_1699_ = lean_unbox_usize(v_depth_1694_);
lean_dec(v_depth_1694_);
v_res_1700_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_boxed_1699_, v_keys_1695_, v_vals_1696_, v_i_1697_, v_entries_1698_);
lean_dec_ref(v_vals_1696_);
lean_dec_ref(v_keys_1695_);
return v_res_1700_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg___boxed(lean_object* v_x_1701_, lean_object* v_x_1702_, lean_object* v_x_1703_, lean_object* v_x_1704_, lean_object* v_x_1705_){
_start:
{
size_t v_x_1620__boxed_1706_; size_t v_x_1621__boxed_1707_; lean_object* v_res_1708_; 
v_x_1620__boxed_1706_ = lean_unbox_usize(v_x_1702_);
lean_dec(v_x_1702_);
v_x_1621__boxed_1707_ = lean_unbox_usize(v_x_1703_);
lean_dec(v_x_1703_);
v_res_1708_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1701_, v_x_1620__boxed_1706_, v_x_1621__boxed_1707_, v_x_1704_, v_x_1705_);
return v_res_1708_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(lean_object* v_x_1709_, lean_object* v_x_1710_, lean_object* v_x_1711_){
_start:
{
uint64_t v___x_1712_; size_t v___x_1713_; size_t v___x_1714_; lean_object* v___x_1715_; 
v___x_1712_ = l_Lean_instHashableMVarId_hash(v_x_1710_);
v___x_1713_ = lean_uint64_to_usize(v___x_1712_);
v___x_1714_ = ((size_t)1ULL);
v___x_1715_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1709_, v___x_1713_, v___x_1714_, v_x_1710_, v_x_1711_);
return v___x_1715_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(lean_object* v_mvarId_1716_, lean_object* v_val_1717_, lean_object* v___y_1718_){
_start:
{
lean_object* v___x_1720_; lean_object* v_mctx_1721_; lean_object* v_cache_1722_; lean_object* v_zetaDeltaFVarIds_1723_; lean_object* v_postponed_1724_; lean_object* v_diag_1725_; lean_object* v___x_1727_; uint8_t v_isShared_1728_; uint8_t v_isSharedCheck_1753_; 
v___x_1720_ = lean_st_ref_take(v___y_1718_);
v_mctx_1721_ = lean_ctor_get(v___x_1720_, 0);
v_cache_1722_ = lean_ctor_get(v___x_1720_, 1);
v_zetaDeltaFVarIds_1723_ = lean_ctor_get(v___x_1720_, 2);
v_postponed_1724_ = lean_ctor_get(v___x_1720_, 3);
v_diag_1725_ = lean_ctor_get(v___x_1720_, 4);
v_isSharedCheck_1753_ = !lean_is_exclusive(v___x_1720_);
if (v_isSharedCheck_1753_ == 0)
{
v___x_1727_ = v___x_1720_;
v_isShared_1728_ = v_isSharedCheck_1753_;
goto v_resetjp_1726_;
}
else
{
lean_inc(v_diag_1725_);
lean_inc(v_postponed_1724_);
lean_inc(v_zetaDeltaFVarIds_1723_);
lean_inc(v_cache_1722_);
lean_inc(v_mctx_1721_);
lean_dec(v___x_1720_);
v___x_1727_ = lean_box(0);
v_isShared_1728_ = v_isSharedCheck_1753_;
goto v_resetjp_1726_;
}
v_resetjp_1726_:
{
lean_object* v_depth_1729_; lean_object* v_levelAssignDepth_1730_; lean_object* v_lmvarCounter_1731_; lean_object* v_mvarCounter_1732_; lean_object* v_lDecls_1733_; lean_object* v_decls_1734_; lean_object* v_userNames_1735_; lean_object* v_lAssignment_1736_; lean_object* v_eAssignment_1737_; lean_object* v_dAssignment_1738_; lean_object* v___x_1740_; uint8_t v_isShared_1741_; uint8_t v_isSharedCheck_1752_; 
v_depth_1729_ = lean_ctor_get(v_mctx_1721_, 0);
v_levelAssignDepth_1730_ = lean_ctor_get(v_mctx_1721_, 1);
v_lmvarCounter_1731_ = lean_ctor_get(v_mctx_1721_, 2);
v_mvarCounter_1732_ = lean_ctor_get(v_mctx_1721_, 3);
v_lDecls_1733_ = lean_ctor_get(v_mctx_1721_, 4);
v_decls_1734_ = lean_ctor_get(v_mctx_1721_, 5);
v_userNames_1735_ = lean_ctor_get(v_mctx_1721_, 6);
v_lAssignment_1736_ = lean_ctor_get(v_mctx_1721_, 7);
v_eAssignment_1737_ = lean_ctor_get(v_mctx_1721_, 8);
v_dAssignment_1738_ = lean_ctor_get(v_mctx_1721_, 9);
v_isSharedCheck_1752_ = !lean_is_exclusive(v_mctx_1721_);
if (v_isSharedCheck_1752_ == 0)
{
v___x_1740_ = v_mctx_1721_;
v_isShared_1741_ = v_isSharedCheck_1752_;
goto v_resetjp_1739_;
}
else
{
lean_inc(v_dAssignment_1738_);
lean_inc(v_eAssignment_1737_);
lean_inc(v_lAssignment_1736_);
lean_inc(v_userNames_1735_);
lean_inc(v_decls_1734_);
lean_inc(v_lDecls_1733_);
lean_inc(v_mvarCounter_1732_);
lean_inc(v_lmvarCounter_1731_);
lean_inc(v_levelAssignDepth_1730_);
lean_inc(v_depth_1729_);
lean_dec(v_mctx_1721_);
v___x_1740_ = lean_box(0);
v_isShared_1741_ = v_isSharedCheck_1752_;
goto v_resetjp_1739_;
}
v_resetjp_1739_:
{
lean_object* v___x_1742_; lean_object* v___x_1744_; 
v___x_1742_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_eAssignment_1737_, v_mvarId_1716_, v_val_1717_);
if (v_isShared_1741_ == 0)
{
lean_ctor_set(v___x_1740_, 8, v___x_1742_);
v___x_1744_ = v___x_1740_;
goto v_reusejp_1743_;
}
else
{
lean_object* v_reuseFailAlloc_1751_; 
v_reuseFailAlloc_1751_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v_reuseFailAlloc_1751_, 0, v_depth_1729_);
lean_ctor_set(v_reuseFailAlloc_1751_, 1, v_levelAssignDepth_1730_);
lean_ctor_set(v_reuseFailAlloc_1751_, 2, v_lmvarCounter_1731_);
lean_ctor_set(v_reuseFailAlloc_1751_, 3, v_mvarCounter_1732_);
lean_ctor_set(v_reuseFailAlloc_1751_, 4, v_lDecls_1733_);
lean_ctor_set(v_reuseFailAlloc_1751_, 5, v_decls_1734_);
lean_ctor_set(v_reuseFailAlloc_1751_, 6, v_userNames_1735_);
lean_ctor_set(v_reuseFailAlloc_1751_, 7, v_lAssignment_1736_);
lean_ctor_set(v_reuseFailAlloc_1751_, 8, v___x_1742_);
lean_ctor_set(v_reuseFailAlloc_1751_, 9, v_dAssignment_1738_);
v___x_1744_ = v_reuseFailAlloc_1751_;
goto v_reusejp_1743_;
}
v_reusejp_1743_:
{
lean_object* v___x_1746_; 
if (v_isShared_1728_ == 0)
{
lean_ctor_set(v___x_1727_, 0, v___x_1744_);
v___x_1746_ = v___x_1727_;
goto v_reusejp_1745_;
}
else
{
lean_object* v_reuseFailAlloc_1750_; 
v_reuseFailAlloc_1750_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1750_, 0, v___x_1744_);
lean_ctor_set(v_reuseFailAlloc_1750_, 1, v_cache_1722_);
lean_ctor_set(v_reuseFailAlloc_1750_, 2, v_zetaDeltaFVarIds_1723_);
lean_ctor_set(v_reuseFailAlloc_1750_, 3, v_postponed_1724_);
lean_ctor_set(v_reuseFailAlloc_1750_, 4, v_diag_1725_);
v___x_1746_ = v_reuseFailAlloc_1750_;
goto v_reusejp_1745_;
}
v_reusejp_1745_:
{
lean_object* v___x_1747_; lean_object* v___x_1748_; lean_object* v___x_1749_; 
v___x_1747_ = lean_st_ref_set(v___y_1718_, v___x_1746_);
v___x_1748_ = lean_box(0);
v___x_1749_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1749_, 0, v___x_1748_);
return v___x_1749_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg___boxed(lean_object* v_mvarId_1754_, lean_object* v_val_1755_, lean_object* v___y_1756_, lean_object* v___y_1757_){
_start:
{
lean_object* v_res_1758_; 
v_res_1758_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1754_, v_val_1755_, v___y_1756_);
lean_dec(v___y_1756_);
return v_res_1758_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(lean_object* v_argMVars_1759_, lean_object* v_argVars_1760_, lean_object* v_as_1761_, size_t v_sz_1762_, size_t v_i_1763_, lean_object* v_b_1764_, lean_object* v___y_1765_, lean_object* v___y_1766_, lean_object* v___y_1767_, lean_object* v___y_1768_){
_start:
{
uint8_t v___x_1770_; 
v___x_1770_ = lean_usize_dec_lt(v_i_1763_, v_sz_1762_);
if (v___x_1770_ == 0)
{
lean_object* v___x_1771_; 
v___x_1771_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1771_, 0, v_b_1764_);
return v___x_1771_;
}
else
{
lean_object* v___x_1772_; lean_object* v_a_1773_; lean_object* v___y_1775_; lean_object* v___y_1776_; lean_object* v___y_1777_; lean_object* v___y_1778_; lean_object* v___x_1794_; lean_object* v___x_1795_; 
v___x_1772_ = lean_box(0);
v_a_1773_ = lean_array_uget_borrowed(v_as_1761_, v_i_1763_);
v___x_1794_ = lean_unsigned_to_nat(0u);
v___x_1795_ = l_Array_findIdx_x3f_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__0(v_a_1773_, v_argMVars_1759_, v___x_1794_);
if (lean_obj_tag(v___x_1795_) == 1)
{
lean_object* v_val_1796_; lean_object* v___x_1797_; lean_object* v___x_1798_; lean_object* v___x_1799_; 
v_val_1796_ = lean_ctor_get(v___x_1795_, 0);
lean_inc(v_val_1796_);
lean_dec_ref_known(v___x_1795_, 1);
v___x_1797_ = l_Lean_instInhabitedExpr;
v___x_1798_ = lean_array_get_borrowed(v___x_1797_, v_argVars_1760_, v_val_1796_);
lean_dec(v_val_1796_);
lean_inc(v___x_1798_);
lean_inc(v_a_1773_);
v___x_1799_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_a_1773_, v___x_1798_, v___y_1766_);
if (lean_obj_tag(v___x_1799_) == 0)
{
lean_dec_ref_known(v___x_1799_, 1);
v___y_1775_ = v___y_1765_;
v___y_1776_ = v___y_1766_;
v___y_1777_ = v___y_1767_;
v___y_1778_ = v___y_1768_;
goto v___jp_1774_;
}
else
{
return v___x_1799_;
}
}
else
{
lean_dec(v___x_1795_);
v___y_1775_ = v___y_1765_;
v___y_1776_ = v___y_1766_;
v___y_1777_ = v___y_1767_;
v___y_1778_ = v___y_1768_;
goto v___jp_1774_;
}
v___jp_1774_:
{
lean_object* v___x_1779_; lean_object* v___x_1780_; 
lean_inc(v_a_1773_);
v___x_1779_ = l_Lean_Expr_mvar___override(v_a_1773_);
lean_inc(v___y_1778_);
lean_inc_ref(v___y_1777_);
lean_inc(v___y_1776_);
lean_inc_ref(v___y_1775_);
v___x_1780_ = lean_infer_type(v___x_1779_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1780_) == 0)
{
lean_object* v_a_1781_; lean_object* v___x_1782_; 
v_a_1781_ = lean_ctor_get(v___x_1780_, 0);
lean_inc(v_a_1781_);
lean_dec_ref_known(v___x_1780_, 1);
v___x_1782_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1759_, v_argVars_1760_, v_a_1781_, v___y_1775_, v___y_1776_, v___y_1777_, v___y_1778_);
if (lean_obj_tag(v___x_1782_) == 0)
{
size_t v___x_1783_; size_t v___x_1784_; 
lean_dec_ref_known(v___x_1782_, 1);
v___x_1783_ = ((size_t)1ULL);
v___x_1784_ = lean_usize_add(v_i_1763_, v___x_1783_);
v_i_1763_ = v___x_1784_;
v_b_1764_ = v___x_1772_;
goto _start;
}
else
{
return v___x_1782_;
}
}
else
{
lean_object* v_a_1786_; lean_object* v___x_1788_; uint8_t v_isShared_1789_; uint8_t v_isSharedCheck_1793_; 
v_a_1786_ = lean_ctor_get(v___x_1780_, 0);
v_isSharedCheck_1793_ = !lean_is_exclusive(v___x_1780_);
if (v_isSharedCheck_1793_ == 0)
{
v___x_1788_ = v___x_1780_;
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
else
{
lean_inc(v_a_1786_);
lean_dec(v___x_1780_);
v___x_1788_ = lean_box(0);
v_isShared_1789_ = v_isSharedCheck_1793_;
goto v_resetjp_1787_;
}
v_resetjp_1787_:
{
lean_object* v___x_1791_; 
if (v_isShared_1789_ == 0)
{
v___x_1791_ = v___x_1788_;
goto v_reusejp_1790_;
}
else
{
lean_object* v_reuseFailAlloc_1792_; 
v_reuseFailAlloc_1792_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1792_, 0, v_a_1786_);
v___x_1791_ = v_reuseFailAlloc_1792_;
goto v_reusejp_1790_;
}
v_reusejp_1790_:
{
return v___x_1791_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(lean_object* v_argMVars_1800_, lean_object* v_argVars_1801_, lean_object* v_e_1802_, lean_object* v_a_1803_, lean_object* v_a_1804_, lean_object* v_a_1805_, lean_object* v_a_1806_){
_start:
{
lean_object* v___x_1808_; 
v___x_1808_ = l_Lean_Meta_getMVars(v_e_1802_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
if (lean_obj_tag(v___x_1808_) == 0)
{
lean_object* v_a_1809_; lean_object* v___x_1810_; size_t v_sz_1811_; size_t v___x_1812_; lean_object* v___x_1813_; 
v_a_1809_ = lean_ctor_get(v___x_1808_, 0);
lean_inc(v_a_1809_);
lean_dec_ref_known(v___x_1808_, 1);
v___x_1810_ = lean_box(0);
v_sz_1811_ = lean_array_size(v_a_1809_);
v___x_1812_ = ((size_t)0ULL);
v___x_1813_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1800_, v_argVars_1801_, v_a_1809_, v_sz_1811_, v___x_1812_, v___x_1810_, v_a_1803_, v_a_1804_, v_a_1805_, v_a_1806_);
lean_dec(v_a_1809_);
if (lean_obj_tag(v___x_1813_) == 0)
{
lean_object* v___x_1815_; uint8_t v_isShared_1816_; uint8_t v_isSharedCheck_1820_; 
v_isSharedCheck_1820_ = !lean_is_exclusive(v___x_1813_);
if (v_isSharedCheck_1820_ == 0)
{
lean_object* v_unused_1821_; 
v_unused_1821_ = lean_ctor_get(v___x_1813_, 0);
lean_dec(v_unused_1821_);
v___x_1815_ = v___x_1813_;
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
else
{
lean_dec(v___x_1813_);
v___x_1815_ = lean_box(0);
v_isShared_1816_ = v_isSharedCheck_1820_;
goto v_resetjp_1814_;
}
v_resetjp_1814_:
{
lean_object* v___x_1818_; 
if (v_isShared_1816_ == 0)
{
lean_ctor_set(v___x_1815_, 0, v___x_1810_);
v___x_1818_ = v___x_1815_;
goto v_reusejp_1817_;
}
else
{
lean_object* v_reuseFailAlloc_1819_; 
v_reuseFailAlloc_1819_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1819_, 0, v___x_1810_);
v___x_1818_ = v_reuseFailAlloc_1819_;
goto v_reusejp_1817_;
}
v_reusejp_1817_:
{
return v___x_1818_;
}
}
}
else
{
return v___x_1813_;
}
}
else
{
lean_object* v_a_1822_; lean_object* v___x_1824_; uint8_t v_isShared_1825_; uint8_t v_isSharedCheck_1829_; 
v_a_1822_ = lean_ctor_get(v___x_1808_, 0);
v_isSharedCheck_1829_ = !lean_is_exclusive(v___x_1808_);
if (v_isSharedCheck_1829_ == 0)
{
v___x_1824_ = v___x_1808_;
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
else
{
lean_inc(v_a_1822_);
lean_dec(v___x_1808_);
v___x_1824_ = lean_box(0);
v_isShared_1825_ = v_isSharedCheck_1829_;
goto v_resetjp_1823_;
}
v_resetjp_1823_:
{
lean_object* v___x_1827_; 
if (v_isShared_1825_ == 0)
{
v___x_1827_ = v___x_1824_;
goto v_reusejp_1826_;
}
else
{
lean_object* v_reuseFailAlloc_1828_; 
v_reuseFailAlloc_1828_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1828_, 0, v_a_1822_);
v___x_1827_ = v_reuseFailAlloc_1828_;
goto v_reusejp_1826_;
}
v_reusejp_1826_:
{
return v___x_1827_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn___boxed(lean_object* v_argMVars_1830_, lean_object* v_argVars_1831_, lean_object* v_e_1832_, lean_object* v_a_1833_, lean_object* v_a_1834_, lean_object* v_a_1835_, lean_object* v_a_1836_, lean_object* v_a_1837_){
_start:
{
lean_object* v_res_1838_; 
v_res_1838_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_argMVars_1830_, v_argVars_1831_, v_e_1832_, v_a_1833_, v_a_1834_, v_a_1835_, v_a_1836_);
lean_dec(v_a_1836_);
lean_dec_ref(v_a_1835_);
lean_dec(v_a_1834_);
lean_dec_ref(v_a_1833_);
lean_dec_ref(v_argVars_1831_);
lean_dec_ref(v_argMVars_1830_);
return v_res_1838_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2___boxed(lean_object* v_argMVars_1839_, lean_object* v_argVars_1840_, lean_object* v_as_1841_, lean_object* v_sz_1842_, lean_object* v_i_1843_, lean_object* v_b_1844_, lean_object* v___y_1845_, lean_object* v___y_1846_, lean_object* v___y_1847_, lean_object* v___y_1848_, lean_object* v___y_1849_){
_start:
{
size_t v_sz_boxed_1850_; size_t v_i_boxed_1851_; lean_object* v_res_1852_; 
v_sz_boxed_1850_ = lean_unbox_usize(v_sz_1842_);
lean_dec(v_sz_1842_);
v_i_boxed_1851_ = lean_unbox_usize(v_i_1843_);
lean_dec(v_i_1843_);
v_res_1852_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__2(v_argMVars_1839_, v_argVars_1840_, v_as_1841_, v_sz_boxed_1850_, v_i_boxed_1851_, v_b_1844_, v___y_1845_, v___y_1846_, v___y_1847_, v___y_1848_);
lean_dec(v___y_1848_);
lean_dec_ref(v___y_1847_);
lean_dec(v___y_1846_);
lean_dec_ref(v___y_1845_);
lean_dec_ref(v_as_1841_);
lean_dec_ref(v_argVars_1840_);
lean_dec_ref(v_argMVars_1839_);
return v_res_1852_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(lean_object* v_mvarId_1853_, lean_object* v_val_1854_, lean_object* v___y_1855_, lean_object* v___y_1856_, lean_object* v___y_1857_, lean_object* v___y_1858_){
_start:
{
lean_object* v___x_1860_; 
v___x_1860_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___redArg(v_mvarId_1853_, v_val_1854_, v___y_1856_);
return v___x_1860_;
}
}
LEAN_EXPORT lean_object* l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1___boxed(lean_object* v_mvarId_1861_, lean_object* v_val_1862_, lean_object* v___y_1863_, lean_object* v___y_1864_, lean_object* v___y_1865_, lean_object* v___y_1866_, lean_object* v___y_1867_){
_start:
{
lean_object* v_res_1868_; 
v_res_1868_ = l_Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1(v_mvarId_1861_, v_val_1862_, v___y_1863_, v___y_1864_, v___y_1865_, v___y_1866_);
lean_dec(v___y_1866_);
lean_dec_ref(v___y_1865_);
lean_dec(v___y_1864_);
lean_dec_ref(v___y_1863_);
return v_res_1868_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1(lean_object* v_00_u03b2_1869_, lean_object* v_x_1870_, lean_object* v_x_1871_, lean_object* v_x_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1___redArg(v_x_1870_, v_x_1871_, v_x_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(lean_object* v_00_u03b2_1874_, lean_object* v_x_1875_, size_t v_x_1876_, size_t v_x_1877_, lean_object* v_x_1878_, lean_object* v_x_1879_){
_start:
{
lean_object* v___x_1880_; 
v___x_1880_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___redArg(v_x_1875_, v_x_1876_, v_x_1877_, v_x_1878_, v_x_1879_);
return v___x_1880_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2___boxed(lean_object* v_00_u03b2_1881_, lean_object* v_x_1882_, lean_object* v_x_1883_, lean_object* v_x_1884_, lean_object* v_x_1885_, lean_object* v_x_1886_){
_start:
{
size_t v_x_1982__boxed_1887_; size_t v_x_1983__boxed_1888_; lean_object* v_res_1889_; 
v_x_1982__boxed_1887_ = lean_unbox_usize(v_x_1883_);
lean_dec(v_x_1883_);
v_x_1983__boxed_1888_ = lean_unbox_usize(v_x_1884_);
lean_dec(v_x_1884_);
v_res_1889_ = l_Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2(v_00_u03b2_1881_, v_x_1882_, v_x_1982__boxed_1887_, v_x_1983__boxed_1888_, v_x_1885_, v_x_1886_);
return v_res_1889_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4(lean_object* v_00_u03b2_1890_, lean_object* v_n_1891_, lean_object* v_k_1892_, lean_object* v_v_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l_Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4___redArg(v_n_1891_, v_k_1892_, v_v_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(lean_object* v_00_u03b2_1895_, size_t v_depth_1896_, lean_object* v_keys_1897_, lean_object* v_vals_1898_, lean_object* v_heq_1899_, lean_object* v_i_1900_, lean_object* v_entries_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___redArg(v_depth_1896_, v_keys_1897_, v_vals_1898_, v_i_1900_, v_entries_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5___boxed(lean_object* v_00_u03b2_1903_, lean_object* v_depth_1904_, lean_object* v_keys_1905_, lean_object* v_vals_1906_, lean_object* v_heq_1907_, lean_object* v_i_1908_, lean_object* v_entries_1909_){
_start:
{
size_t v_depth_boxed_1910_; lean_object* v_res_1911_; 
v_depth_boxed_1910_ = lean_unbox_usize(v_depth_1904_);
lean_dec(v_depth_1904_);
v_res_1911_ = l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__5(v_00_u03b2_1903_, v_depth_boxed_1910_, v_keys_1905_, v_vals_1906_, v_heq_1907_, v_i_1908_, v_entries_1909_);
lean_dec_ref(v_vals_1906_);
lean_dec_ref(v_keys_1905_);
return v_res_1911_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5(lean_object* v_00_u03b2_1912_, lean_object* v_x_1913_, lean_object* v_x_1914_, lean_object* v_x_1915_, lean_object* v_x_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_Lean_PersistentHashMap_insertAtCollisionNodeAux___at___00Lean_PersistentHashMap_insertAtCollisionNode___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_MVarId_assign___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn_spec__1_spec__1_spec__2_spec__4_spec__5___redArg(v_x_1913_, v_x_1914_, v_x_1915_, v_x_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(lean_object* v_e_1918_, lean_object* v___y_1919_){
_start:
{
uint8_t v___x_1921_; uint8_t v___x_1922_; 
v___x_1921_ = l_Lean_Expr_hasMVar(v_e_1918_);
v___x_1922_ = lean_bool_not(v___x_1921_);
if (v___x_1922_ == 0)
{
lean_object* v___x_1923_; lean_object* v_mctx_1924_; lean_object* v___x_1925_; lean_object* v_fst_1926_; lean_object* v_snd_1927_; lean_object* v___x_1928_; lean_object* v_cache_1929_; lean_object* v_zetaDeltaFVarIds_1930_; lean_object* v_postponed_1931_; lean_object* v_diag_1932_; lean_object* v___x_1934_; uint8_t v_isShared_1935_; uint8_t v_isSharedCheck_1941_; 
v___x_1923_ = lean_st_ref_get(v___y_1919_);
v_mctx_1924_ = lean_ctor_get(v___x_1923_, 0);
lean_inc_ref(v_mctx_1924_);
lean_dec(v___x_1923_);
v___x_1925_ = l_Lean_instantiateMVarsCore(v_mctx_1924_, v_e_1918_);
v_fst_1926_ = lean_ctor_get(v___x_1925_, 0);
lean_inc(v_fst_1926_);
v_snd_1927_ = lean_ctor_get(v___x_1925_, 1);
lean_inc(v_snd_1927_);
lean_dec_ref(v___x_1925_);
v___x_1928_ = lean_st_ref_take(v___y_1919_);
v_cache_1929_ = lean_ctor_get(v___x_1928_, 1);
v_zetaDeltaFVarIds_1930_ = lean_ctor_get(v___x_1928_, 2);
v_postponed_1931_ = lean_ctor_get(v___x_1928_, 3);
v_diag_1932_ = lean_ctor_get(v___x_1928_, 4);
v_isSharedCheck_1941_ = !lean_is_exclusive(v___x_1928_);
if (v_isSharedCheck_1941_ == 0)
{
lean_object* v_unused_1942_; 
v_unused_1942_ = lean_ctor_get(v___x_1928_, 0);
lean_dec(v_unused_1942_);
v___x_1934_ = v___x_1928_;
v_isShared_1935_ = v_isSharedCheck_1941_;
goto v_resetjp_1933_;
}
else
{
lean_inc(v_diag_1932_);
lean_inc(v_postponed_1931_);
lean_inc(v_zetaDeltaFVarIds_1930_);
lean_inc(v_cache_1929_);
lean_dec(v___x_1928_);
v___x_1934_ = lean_box(0);
v_isShared_1935_ = v_isSharedCheck_1941_;
goto v_resetjp_1933_;
}
v_resetjp_1933_:
{
lean_object* v___x_1937_; 
if (v_isShared_1935_ == 0)
{
lean_ctor_set(v___x_1934_, 0, v_snd_1927_);
v___x_1937_ = v___x_1934_;
goto v_reusejp_1936_;
}
else
{
lean_object* v_reuseFailAlloc_1940_; 
v_reuseFailAlloc_1940_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_1940_, 0, v_snd_1927_);
lean_ctor_set(v_reuseFailAlloc_1940_, 1, v_cache_1929_);
lean_ctor_set(v_reuseFailAlloc_1940_, 2, v_zetaDeltaFVarIds_1930_);
lean_ctor_set(v_reuseFailAlloc_1940_, 3, v_postponed_1931_);
lean_ctor_set(v_reuseFailAlloc_1940_, 4, v_diag_1932_);
v___x_1937_ = v_reuseFailAlloc_1940_;
goto v_reusejp_1936_;
}
v_reusejp_1936_:
{
lean_object* v___x_1938_; lean_object* v___x_1939_; 
v___x_1938_ = lean_st_ref_set(v___y_1919_, v___x_1937_);
v___x_1939_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1939_, 0, v_fst_1926_);
return v___x_1939_;
}
}
}
else
{
lean_object* v___x_1943_; 
v___x_1943_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1943_, 0, v_e_1918_);
return v___x_1943_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg___boxed(lean_object* v_e_1944_, lean_object* v___y_1945_, lean_object* v___y_1946_){
_start:
{
lean_object* v_res_1947_; 
v_res_1947_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1944_, v___y_1945_);
lean_dec(v___y_1945_);
return v_res_1947_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(lean_object* v_e_1948_, lean_object* v___y_1949_, lean_object* v___y_1950_, lean_object* v___y_1951_, lean_object* v___y_1952_){
_start:
{
lean_object* v___x_1954_; 
v___x_1954_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_e_1948_, v___y_1950_);
return v___x_1954_;
}
}
LEAN_EXPORT lean_object* l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___boxed(lean_object* v_e_1955_, lean_object* v___y_1956_, lean_object* v___y_1957_, lean_object* v___y_1958_, lean_object* v___y_1959_, lean_object* v___y_1960_){
_start:
{
lean_object* v_res_1961_; 
v_res_1961_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3(v_e_1955_, v___y_1956_, v___y_1957_, v___y_1958_, v___y_1959_);
lean_dec(v___y_1959_);
lean_dec_ref(v___y_1958_);
lean_dec(v___y_1957_);
lean_dec_ref(v___y_1956_);
return v_res_1961_;
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(lean_object* v_opts_1962_, lean_object* v_opt_1963_){
_start:
{
lean_object* v_name_1964_; lean_object* v_defValue_1965_; lean_object* v_map_1966_; lean_object* v___x_1967_; 
v_name_1964_ = lean_ctor_get(v_opt_1963_, 0);
v_defValue_1965_ = lean_ctor_get(v_opt_1963_, 1);
v_map_1966_ = lean_ctor_get(v_opts_1962_, 0);
v___x_1967_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_1966_, v_name_1964_);
if (lean_obj_tag(v___x_1967_) == 0)
{
uint8_t v___x_1968_; 
v___x_1968_ = lean_unbox(v_defValue_1965_);
return v___x_1968_;
}
else
{
lean_object* v_val_1969_; 
v_val_1969_ = lean_ctor_get(v___x_1967_, 0);
lean_inc(v_val_1969_);
lean_dec_ref_known(v___x_1967_, 1);
if (lean_obj_tag(v_val_1969_) == 1)
{
uint8_t v_v_1970_; 
v_v_1970_ = lean_ctor_get_uint8(v_val_1969_, 0);
lean_dec_ref_known(v_val_1969_, 0);
return v_v_1970_;
}
else
{
uint8_t v___x_1971_; 
lean_dec(v_val_1969_);
v___x_1971_ = lean_unbox(v_defValue_1965_);
return v___x_1971_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4___boxed(lean_object* v_opts_1972_, lean_object* v_opt_1973_){
_start:
{
uint8_t v_res_1974_; lean_object* v_r_1975_; 
v_res_1974_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_opts_1972_, v_opt_1973_);
lean_dec_ref(v_opt_1973_);
lean_dec_ref(v_opts_1972_);
v_r_1975_ = lean_box(v_res_1974_);
return v_r_1975_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(lean_object* v_a_1976_, lean_object* v_as_1977_, size_t v_i_1978_, size_t v_stop_1979_){
_start:
{
uint8_t v___x_1980_; 
v___x_1980_ = lean_usize_dec_eq(v_i_1978_, v_stop_1979_);
if (v___x_1980_ == 0)
{
lean_object* v___x_1981_; uint8_t v___x_1982_; 
v___x_1981_ = lean_array_uget_borrowed(v_as_1977_, v_i_1978_);
v___x_1982_ = lean_nat_dec_eq(v_a_1976_, v___x_1981_);
if (v___x_1982_ == 0)
{
size_t v___x_1983_; size_t v___x_1984_; 
v___x_1983_ = ((size_t)1ULL);
v___x_1984_ = lean_usize_add(v_i_1978_, v___x_1983_);
v_i_1978_ = v___x_1984_;
goto _start;
}
else
{
return v___x_1982_;
}
}
else
{
uint8_t v___x_1986_; 
v___x_1986_ = 0;
return v___x_1986_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1___boxed(lean_object* v_a_1987_, lean_object* v_as_1988_, lean_object* v_i_1989_, lean_object* v_stop_1990_){
_start:
{
size_t v_i_boxed_1991_; size_t v_stop_boxed_1992_; uint8_t v_res_1993_; lean_object* v_r_1994_; 
v_i_boxed_1991_ = lean_unbox_usize(v_i_1989_);
lean_dec(v_i_1989_);
v_stop_boxed_1992_ = lean_unbox_usize(v_stop_1990_);
lean_dec(v_stop_1990_);
v_res_1993_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1987_, v_as_1988_, v_i_boxed_1991_, v_stop_boxed_1992_);
lean_dec_ref(v_as_1988_);
lean_dec(v_a_1987_);
v_r_1994_ = lean_box(v_res_1993_);
return v_r_1994_;
}
}
LEAN_EXPORT uint8_t l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(lean_object* v_as_1995_, lean_object* v_a_1996_){
_start:
{
lean_object* v___x_1997_; lean_object* v___x_1998_; uint8_t v___x_1999_; 
v___x_1997_ = lean_unsigned_to_nat(0u);
v___x_1998_ = lean_array_get_size(v_as_1995_);
v___x_1999_ = lean_nat_dec_lt(v___x_1997_, v___x_1998_);
if (v___x_1999_ == 0)
{
return v___x_1999_;
}
else
{
if (v___x_1999_ == 0)
{
return v___x_1999_;
}
else
{
size_t v___x_2000_; size_t v___x_2001_; uint8_t v___x_2002_; 
v___x_2000_ = ((size_t)0ULL);
v___x_2001_ = lean_usize_of_nat(v___x_1998_);
v___x_2002_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1_spec__1(v_a_1996_, v_as_1995_, v___x_2000_, v___x_2001_);
return v___x_2002_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1___boxed(lean_object* v_as_2003_, lean_object* v_a_2004_){
_start:
{
uint8_t v_res_2005_; lean_object* v_r_2006_; 
v_res_2005_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_as_2003_, v_a_2004_);
lean_dec(v_a_2004_);
lean_dec_ref(v_as_2003_);
v_r_2006_ = lean_box(v_res_2005_);
return v_r_2006_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(lean_object* v_a_2007_, lean_object* v_fst_2008_, lean_object* v_argVars_2009_, lean_object* v_as_2010_, size_t v_sz_2011_, size_t v_i_2012_, lean_object* v_b_2013_, lean_object* v___y_2014_, lean_object* v___y_2015_, lean_object* v___y_2016_, lean_object* v___y_2017_){
_start:
{
lean_object* v_a_2020_; uint8_t v___x_2024_; 
v___x_2024_ = lean_usize_dec_lt(v_i_2012_, v_sz_2011_);
if (v___x_2024_ == 0)
{
lean_object* v___x_2025_; 
v___x_2025_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2025_, 0, v_b_2013_);
return v___x_2025_;
}
else
{
lean_object* v_next_2026_; 
v_next_2026_ = lean_ctor_get(v_b_2013_, 0);
lean_inc(v_next_2026_);
if (lean_obj_tag(v_next_2026_) == 0)
{
lean_object* v___x_2027_; 
v___x_2027_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2027_, 0, v_b_2013_);
return v___x_2027_;
}
else
{
lean_object* v_upperBound_2028_; lean_object* v_val_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2060_; 
v_upperBound_2028_ = lean_ctor_get(v_b_2013_, 1);
v_val_2029_ = lean_ctor_get(v_next_2026_, 0);
v_isSharedCheck_2060_ = !lean_is_exclusive(v_next_2026_);
if (v_isSharedCheck_2060_ == 0)
{
v___x_2031_ = v_next_2026_;
v_isShared_2032_ = v_isSharedCheck_2060_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_val_2029_);
lean_dec(v_next_2026_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2060_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
uint8_t v___x_2033_; 
v___x_2033_ = lean_nat_dec_lt(v_val_2029_, v_upperBound_2028_);
if (v___x_2033_ == 0)
{
lean_object* v___x_2034_; 
lean_del_object(v___x_2031_);
lean_dec(v_val_2029_);
v___x_2034_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2034_, 0, v_b_2013_);
return v___x_2034_;
}
else
{
lean_object* v___x_2036_; uint8_t v_isShared_2037_; uint8_t v_isSharedCheck_2057_; 
lean_inc(v_upperBound_2028_);
v_isSharedCheck_2057_ = !lean_is_exclusive(v_b_2013_);
if (v_isSharedCheck_2057_ == 0)
{
lean_object* v_unused_2058_; lean_object* v_unused_2059_; 
v_unused_2058_ = lean_ctor_get(v_b_2013_, 1);
lean_dec(v_unused_2058_);
v_unused_2059_ = lean_ctor_get(v_b_2013_, 0);
lean_dec(v_unused_2059_);
v___x_2036_ = v_b_2013_;
v_isShared_2037_ = v_isSharedCheck_2057_;
goto v_resetjp_2035_;
}
else
{
lean_dec(v_b_2013_);
v___x_2036_ = lean_box(0);
v_isShared_2037_ = v_isSharedCheck_2057_;
goto v_resetjp_2035_;
}
v_resetjp_2035_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; lean_object* v___x_2041_; 
v___x_2038_ = lean_unsigned_to_nat(1u);
v___x_2039_ = lean_nat_add(v_val_2029_, v___x_2038_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 0, v___x_2039_);
v___x_2041_ = v___x_2031_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2056_; 
v_reuseFailAlloc_2056_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2056_, 0, v___x_2039_);
v___x_2041_ = v_reuseFailAlloc_2056_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2043_; 
if (v_isShared_2037_ == 0)
{
lean_ctor_set(v___x_2036_, 0, v___x_2041_);
v___x_2043_ = v___x_2036_;
goto v_reusejp_2042_;
}
else
{
lean_object* v_reuseFailAlloc_2055_; 
v_reuseFailAlloc_2055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2055_, 0, v___x_2041_);
lean_ctor_set(v_reuseFailAlloc_2055_, 1, v_upperBound_2028_);
v___x_2043_ = v_reuseFailAlloc_2055_;
goto v_reusejp_2042_;
}
v_reusejp_2042_:
{
uint8_t v___x_2044_; 
v___x_2044_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2007_, v_val_2029_);
lean_dec(v_val_2029_);
if (v___x_2044_ == 0)
{
lean_object* v_a_2045_; lean_object* v___x_2046_; 
v_a_2045_ = lean_array_uget_borrowed(v_as_2010_, v_i_2012_);
lean_inc(v_a_2045_);
v___x_2046_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2008_, v_argVars_2009_, v_a_2045_, v___y_2014_, v___y_2015_, v___y_2016_, v___y_2017_);
if (lean_obj_tag(v___x_2046_) == 0)
{
lean_dec_ref_known(v___x_2046_, 1);
v_a_2020_ = v___x_2043_;
goto v___jp_2019_;
}
else
{
lean_object* v_a_2047_; lean_object* v___x_2049_; uint8_t v_isShared_2050_; uint8_t v_isSharedCheck_2054_; 
lean_dec_ref(v___x_2043_);
v_a_2047_ = lean_ctor_get(v___x_2046_, 0);
v_isSharedCheck_2054_ = !lean_is_exclusive(v___x_2046_);
if (v_isSharedCheck_2054_ == 0)
{
v___x_2049_ = v___x_2046_;
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
else
{
lean_inc(v_a_2047_);
lean_dec(v___x_2046_);
v___x_2049_ = lean_box(0);
v_isShared_2050_ = v_isSharedCheck_2054_;
goto v_resetjp_2048_;
}
v_resetjp_2048_:
{
lean_object* v___x_2052_; 
if (v_isShared_2050_ == 0)
{
v___x_2052_ = v___x_2049_;
goto v_reusejp_2051_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_a_2047_);
v___x_2052_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2051_;
}
v_reusejp_2051_:
{
return v___x_2052_;
}
}
}
}
else
{
v_a_2020_ = v___x_2043_;
goto v___jp_2019_;
}
}
}
}
}
}
}
}
v___jp_2019_:
{
size_t v___x_2021_; size_t v___x_2022_; 
v___x_2021_ = ((size_t)1ULL);
v___x_2022_ = lean_usize_add(v_i_2012_, v___x_2021_);
v_i_2012_ = v___x_2022_;
v_b_2013_ = v_a_2020_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8___boxed(lean_object* v_a_2061_, lean_object* v_fst_2062_, lean_object* v_argVars_2063_, lean_object* v_as_2064_, lean_object* v_sz_2065_, lean_object* v_i_2066_, lean_object* v_b_2067_, lean_object* v___y_2068_, lean_object* v___y_2069_, lean_object* v___y_2070_, lean_object* v___y_2071_, lean_object* v___y_2072_){
_start:
{
size_t v_sz_boxed_2073_; size_t v_i_boxed_2074_; lean_object* v_res_2075_; 
v_sz_boxed_2073_ = lean_unbox_usize(v_sz_2065_);
lean_dec(v_sz_2065_);
v_i_boxed_2074_ = lean_unbox_usize(v_i_2066_);
lean_dec(v_i_2066_);
v_res_2075_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2061_, v_fst_2062_, v_argVars_2063_, v_as_2064_, v_sz_boxed_2073_, v_i_boxed_2074_, v_b_2067_, v___y_2068_, v___y_2069_, v___y_2070_, v___y_2071_);
lean_dec(v___y_2071_);
lean_dec_ref(v___y_2070_);
lean_dec(v___y_2069_);
lean_dec_ref(v___y_2068_);
lean_dec_ref(v_as_2064_);
lean_dec_ref(v_argVars_2063_);
lean_dec_ref(v_fst_2062_);
lean_dec_ref(v_a_2061_);
return v_res_2075_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(lean_object* v_next_2076_, lean_object* v_as_2077_, size_t v_i_2078_, size_t v_stop_2079_, lean_object* v_b_2080_){
_start:
{
lean_object* v___y_2082_; uint8_t v___x_2086_; 
v___x_2086_ = lean_usize_dec_eq(v_i_2078_, v_stop_2079_);
if (v___x_2086_ == 0)
{
lean_object* v___x_2087_; uint8_t v___x_2088_; uint8_t v___x_2089_; 
v___x_2087_ = lean_array_uget_borrowed(v_as_2077_, v_i_2078_);
v___x_2088_ = lean_nat_dec_eq(v___x_2087_, v_next_2076_);
v___x_2089_ = lean_bool_not(v___x_2088_);
if (v___x_2089_ == 0)
{
v___y_2082_ = v_b_2080_;
goto v___jp_2081_;
}
else
{
lean_object* v___x_2090_; 
lean_inc(v___x_2087_);
v___x_2090_ = lean_array_push(v_b_2080_, v___x_2087_);
v___y_2082_ = v___x_2090_;
goto v___jp_2081_;
}
}
else
{
return v_b_2080_;
}
v___jp_2081_:
{
size_t v___x_2083_; size_t v___x_2084_; 
v___x_2083_ = ((size_t)1ULL);
v___x_2084_ = lean_usize_add(v_i_2078_, v___x_2083_);
v_i_2078_ = v___x_2084_;
v_b_2080_ = v___y_2082_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0___boxed(lean_object* v_next_2091_, lean_object* v_as_2092_, lean_object* v_i_2093_, lean_object* v_stop_2094_, lean_object* v_b_2095_){
_start:
{
size_t v_i_boxed_2096_; size_t v_stop_boxed_2097_; lean_object* v_res_2098_; 
v_i_boxed_2096_ = lean_unbox_usize(v_i_2093_);
lean_dec(v_i_2093_);
v_stop_boxed_2097_ = lean_unbox_usize(v_stop_2094_);
lean_dec(v_stop_2094_);
v_res_2098_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2091_, v_as_2092_, v_i_boxed_2096_, v_stop_boxed_2097_, v_b_2095_);
lean_dec_ref(v_as_2092_);
lean_dec(v_next_2091_);
return v_res_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(lean_object* v_fst_2099_, lean_object* v_fst_2100_, lean_object* v_argVars_2101_, lean_object* v_snd_2102_, lean_object* v_next_2103_, lean_object* v___y_2104_, lean_object* v___y_2105_, lean_object* v___y_2106_, lean_object* v___y_2107_){
_start:
{
lean_object* v___x_2109_; lean_object* v___y_2111_; lean_object* v___x_2152_; lean_object* v___x_2153_; lean_object* v___x_2154_; uint8_t v___x_2155_; 
lean_inc(v_next_2103_);
v___x_2109_ = lean_array_push(v_fst_2099_, v_next_2103_);
v___x_2152_ = lean_unsigned_to_nat(0u);
v___x_2153_ = lean_array_get_size(v_snd_2102_);
v___x_2154_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2155_ = lean_nat_dec_lt(v___x_2152_, v___x_2153_);
if (v___x_2155_ == 0)
{
v___y_2111_ = v___x_2154_;
goto v___jp_2110_;
}
else
{
uint8_t v___x_2156_; 
v___x_2156_ = lean_nat_dec_le(v___x_2153_, v___x_2153_);
if (v___x_2156_ == 0)
{
if (v___x_2155_ == 0)
{
v___y_2111_ = v___x_2154_;
goto v___jp_2110_;
}
else
{
size_t v___x_2157_; size_t v___x_2158_; lean_object* v___x_2159_; 
v___x_2157_ = ((size_t)0ULL);
v___x_2158_ = lean_usize_of_nat(v___x_2153_);
v___x_2159_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2103_, v_snd_2102_, v___x_2157_, v___x_2158_, v___x_2154_);
v___y_2111_ = v___x_2159_;
goto v___jp_2110_;
}
}
else
{
size_t v___x_2160_; size_t v___x_2161_; lean_object* v___x_2162_; 
v___x_2160_ = ((size_t)0ULL);
v___x_2161_ = lean_usize_of_nat(v___x_2153_);
v___x_2162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__0(v_next_2103_, v_snd_2102_, v___x_2160_, v___x_2161_, v___x_2154_);
v___y_2111_ = v___x_2162_;
goto v___jp_2110_;
}
}
v___jp_2110_:
{
lean_object* v___x_2112_; lean_object* v___x_2113_; lean_object* v___x_2114_; 
v___x_2112_ = l_Lean_instInhabitedExpr;
v___x_2113_ = lean_array_get_borrowed(v___x_2112_, v_fst_2100_, v_next_2103_);
lean_dec(v_next_2103_);
lean_inc(v___y_2107_);
lean_inc_ref(v___y_2106_);
lean_inc(v___y_2105_);
lean_inc_ref(v___y_2104_);
lean_inc(v___x_2113_);
v___x_2114_ = lean_infer_type(v___x_2113_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2114_) == 0)
{
lean_object* v_a_2115_; lean_object* v___x_2116_; 
v_a_2115_ = lean_ctor_get(v___x_2114_, 0);
lean_inc(v_a_2115_);
lean_dec_ref_known(v___x_2114_, 1);
v___x_2116_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2100_, v_argVars_2101_, v_a_2115_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2116_) == 0)
{
lean_object* v___x_2117_; 
lean_dec_ref_known(v___x_2116_, 1);
lean_inc(v___x_2113_);
v___x_2117_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2100_, v_argVars_2101_, v___x_2113_, v___y_2104_, v___y_2105_, v___y_2106_, v___y_2107_);
if (lean_obj_tag(v___x_2117_) == 0)
{
lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2126_; 
v_isSharedCheck_2126_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2126_ == 0)
{
lean_object* v_unused_2127_; 
v_unused_2127_ = lean_ctor_get(v___x_2117_, 0);
lean_dec(v_unused_2127_);
v___x_2119_ = v___x_2117_;
v_isShared_2120_ = v_isSharedCheck_2126_;
goto v_resetjp_2118_;
}
else
{
lean_dec(v___x_2117_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2126_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2121_; lean_object* v___x_2122_; lean_object* v___x_2124_; 
v___x_2121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2121_, 0, v___x_2109_);
lean_ctor_set(v___x_2121_, 1, v___y_2111_);
v___x_2122_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2122_, 0, v___x_2121_);
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2122_);
v___x_2124_ = v___x_2119_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2125_; 
v_reuseFailAlloc_2125_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2125_, 0, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2125_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
return v___x_2124_;
}
}
}
else
{
lean_object* v_a_2128_; lean_object* v___x_2130_; uint8_t v_isShared_2131_; uint8_t v_isSharedCheck_2135_; 
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___x_2109_);
v_a_2128_ = lean_ctor_get(v___x_2117_, 0);
v_isSharedCheck_2135_ = !lean_is_exclusive(v___x_2117_);
if (v_isSharedCheck_2135_ == 0)
{
v___x_2130_ = v___x_2117_;
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
else
{
lean_inc(v_a_2128_);
lean_dec(v___x_2117_);
v___x_2130_ = lean_box(0);
v_isShared_2131_ = v_isSharedCheck_2135_;
goto v_resetjp_2129_;
}
v_resetjp_2129_:
{
lean_object* v___x_2133_; 
if (v_isShared_2131_ == 0)
{
v___x_2133_ = v___x_2130_;
goto v_reusejp_2132_;
}
else
{
lean_object* v_reuseFailAlloc_2134_; 
v_reuseFailAlloc_2134_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2134_, 0, v_a_2128_);
v___x_2133_ = v_reuseFailAlloc_2134_;
goto v_reusejp_2132_;
}
v_reusejp_2132_:
{
return v___x_2133_;
}
}
}
}
else
{
lean_object* v_a_2136_; lean_object* v___x_2138_; uint8_t v_isShared_2139_; uint8_t v_isSharedCheck_2143_; 
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___x_2109_);
v_a_2136_ = lean_ctor_get(v___x_2116_, 0);
v_isSharedCheck_2143_ = !lean_is_exclusive(v___x_2116_);
if (v_isSharedCheck_2143_ == 0)
{
v___x_2138_ = v___x_2116_;
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
else
{
lean_inc(v_a_2136_);
lean_dec(v___x_2116_);
v___x_2138_ = lean_box(0);
v_isShared_2139_ = v_isSharedCheck_2143_;
goto v_resetjp_2137_;
}
v_resetjp_2137_:
{
lean_object* v___x_2141_; 
if (v_isShared_2139_ == 0)
{
v___x_2141_ = v___x_2138_;
goto v_reusejp_2140_;
}
else
{
lean_object* v_reuseFailAlloc_2142_; 
v_reuseFailAlloc_2142_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2142_, 0, v_a_2136_);
v___x_2141_ = v_reuseFailAlloc_2142_;
goto v_reusejp_2140_;
}
v_reusejp_2140_:
{
return v___x_2141_;
}
}
}
}
else
{
lean_object* v_a_2144_; lean_object* v___x_2146_; uint8_t v_isShared_2147_; uint8_t v_isSharedCheck_2151_; 
lean_dec_ref(v___y_2111_);
lean_dec_ref(v___x_2109_);
v_a_2144_ = lean_ctor_get(v___x_2114_, 0);
v_isSharedCheck_2151_ = !lean_is_exclusive(v___x_2114_);
if (v_isSharedCheck_2151_ == 0)
{
v___x_2146_ = v___x_2114_;
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
else
{
lean_inc(v_a_2144_);
lean_dec(v___x_2114_);
v___x_2146_ = lean_box(0);
v_isShared_2147_ = v_isSharedCheck_2151_;
goto v_resetjp_2145_;
}
v_resetjp_2145_:
{
lean_object* v___x_2149_; 
if (v_isShared_2147_ == 0)
{
v___x_2149_ = v___x_2146_;
goto v_reusejp_2148_;
}
else
{
lean_object* v_reuseFailAlloc_2150_; 
v_reuseFailAlloc_2150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2150_, 0, v_a_2144_);
v___x_2149_ = v_reuseFailAlloc_2150_;
goto v_reusejp_2148_;
}
v_reusejp_2148_:
{
return v___x_2149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed(lean_object* v_fst_2163_, lean_object* v_fst_2164_, lean_object* v_argVars_2165_, lean_object* v_snd_2166_, lean_object* v_next_2167_, lean_object* v___y_2168_, lean_object* v___y_2169_, lean_object* v___y_2170_, lean_object* v___y_2171_, lean_object* v___y_2172_){
_start:
{
lean_object* v_res_2173_; 
v_res_2173_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2163_, v_fst_2164_, v_argVars_2165_, v_snd_2166_, v_next_2167_, v___y_2168_, v___y_2169_, v___y_2170_, v___y_2171_);
lean_dec(v___y_2171_);
lean_dec_ref(v___y_2170_);
lean_dec(v___y_2169_);
lean_dec_ref(v___y_2168_);
lean_dec(v_snd_2166_);
lean_dec_ref(v_argVars_2165_);
lean_dec_ref(v_fst_2164_);
return v_res_2173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(lean_object* v_upperBound_2177_, lean_object* v_a_2178_, lean_object* v_a_2179_, lean_object* v_b_2180_){
_start:
{
uint8_t v___x_2182_; 
v___x_2182_ = lean_nat_dec_lt(v_a_2179_, v_upperBound_2177_);
if (v___x_2182_ == 0)
{
lean_object* v___x_2183_; 
lean_dec(v_a_2179_);
v___x_2183_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2183_, 0, v_b_2180_);
return v___x_2183_;
}
else
{
lean_object* v_snd_2184_; lean_object* v___x_2186_; uint8_t v_isShared_2187_; uint8_t v_isSharedCheck_2225_; 
v_snd_2184_ = lean_ctor_get(v_b_2180_, 1);
v_isSharedCheck_2225_ = !lean_is_exclusive(v_b_2180_);
if (v_isSharedCheck_2225_ == 0)
{
lean_object* v_unused_2226_; 
v_unused_2226_ = lean_ctor_get(v_b_2180_, 0);
lean_dec(v_unused_2226_);
v___x_2186_ = v_b_2180_;
v_isShared_2187_ = v_isSharedCheck_2225_;
goto v_resetjp_2185_;
}
else
{
lean_inc(v_snd_2184_);
lean_dec(v_b_2180_);
v___x_2186_ = lean_box(0);
v_isShared_2187_ = v_isSharedCheck_2225_;
goto v_resetjp_2185_;
}
v_resetjp_2185_:
{
lean_object* v_array_2188_; lean_object* v_start_2189_; lean_object* v_stop_2190_; lean_object* v___x_2191_; uint8_t v___x_2192_; 
v_array_2188_ = lean_ctor_get(v_snd_2184_, 0);
v_start_2189_ = lean_ctor_get(v_snd_2184_, 1);
v_stop_2190_ = lean_ctor_get(v_snd_2184_, 2);
v___x_2191_ = lean_box(0);
v___x_2192_ = lean_nat_dec_lt(v_start_2189_, v_stop_2190_);
if (v___x_2192_ == 0)
{
lean_object* v___x_2194_; 
lean_dec(v_a_2179_);
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 0, v___x_2191_);
v___x_2194_ = v___x_2186_;
goto v_reusejp_2193_;
}
else
{
lean_object* v_reuseFailAlloc_2196_; 
v_reuseFailAlloc_2196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2196_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2196_, 1, v_snd_2184_);
v___x_2194_ = v_reuseFailAlloc_2196_;
goto v_reusejp_2193_;
}
v_reusejp_2193_:
{
lean_object* v___x_2195_; 
v___x_2195_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2195_, 0, v___x_2194_);
return v___x_2195_;
}
}
else
{
lean_object* v___x_2198_; uint8_t v_isShared_2199_; uint8_t v_isSharedCheck_2221_; 
lean_inc(v_stop_2190_);
lean_inc(v_start_2189_);
lean_inc_ref(v_array_2188_);
v_isSharedCheck_2221_ = !lean_is_exclusive(v_snd_2184_);
if (v_isSharedCheck_2221_ == 0)
{
lean_object* v_unused_2222_; lean_object* v_unused_2223_; lean_object* v_unused_2224_; 
v_unused_2222_ = lean_ctor_get(v_snd_2184_, 2);
lean_dec(v_unused_2222_);
v_unused_2223_ = lean_ctor_get(v_snd_2184_, 1);
lean_dec(v_unused_2223_);
v_unused_2224_ = lean_ctor_get(v_snd_2184_, 0);
lean_dec(v_unused_2224_);
v___x_2198_ = v_snd_2184_;
v_isShared_2199_ = v_isSharedCheck_2221_;
goto v_resetjp_2197_;
}
else
{
lean_dec(v_snd_2184_);
v___x_2198_ = lean_box(0);
v_isShared_2199_ = v_isSharedCheck_2221_;
goto v_resetjp_2197_;
}
v_resetjp_2197_:
{
lean_object* v___x_2200_; lean_object* v___x_2201_; lean_object* v___x_2202_; lean_object* v___x_2204_; 
v___x_2200_ = lean_array_fget(v_array_2188_, v_start_2189_);
v___x_2201_ = lean_unsigned_to_nat(1u);
v___x_2202_ = lean_nat_add(v_start_2189_, v___x_2201_);
lean_dec(v_start_2189_);
if (v_isShared_2199_ == 0)
{
lean_ctor_set(v___x_2198_, 1, v___x_2202_);
v___x_2204_ = v___x_2198_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2220_; 
v_reuseFailAlloc_2220_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2220_, 0, v_array_2188_);
lean_ctor_set(v_reuseFailAlloc_2220_, 1, v___x_2202_);
lean_ctor_set(v_reuseFailAlloc_2220_, 2, v_stop_2190_);
v___x_2204_ = v_reuseFailAlloc_2220_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
uint8_t v___y_2206_; uint8_t v___x_2217_; uint8_t v___x_2218_; 
v___x_2217_ = l_Array_contains___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__1(v_a_2178_, v_a_2179_);
v___x_2218_ = lean_bool_not(v___x_2217_);
if (v___x_2218_ == 0)
{
lean_dec(v___x_2200_);
v___y_2206_ = v___x_2218_;
goto v___jp_2205_;
}
else
{
uint8_t v___x_2219_; 
v___x_2219_ = l_Lean_Expr_hasExprMVar(v___x_2200_);
lean_dec(v___x_2200_);
v___y_2206_ = v___x_2219_;
goto v___jp_2205_;
}
v___jp_2205_:
{
if (v___y_2206_ == 0)
{
lean_object* v___x_2208_; 
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v___x_2204_);
lean_ctor_set(v___x_2186_, 0, v___x_2191_);
v___x_2208_ = v___x_2186_;
goto v_reusejp_2207_;
}
else
{
lean_object* v_reuseFailAlloc_2211_; 
v_reuseFailAlloc_2211_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2211_, 0, v___x_2191_);
lean_ctor_set(v_reuseFailAlloc_2211_, 1, v___x_2204_);
v___x_2208_ = v_reuseFailAlloc_2211_;
goto v_reusejp_2207_;
}
v_reusejp_2207_:
{
lean_object* v___x_2209_; 
v___x_2209_ = lean_nat_add(v_a_2179_, v___x_2201_);
lean_dec(v_a_2179_);
v_a_2179_ = v___x_2209_;
v_b_2180_ = v___x_2208_;
goto _start;
}
}
else
{
lean_object* v___x_2212_; lean_object* v___x_2214_; 
lean_dec(v_a_2179_);
v___x_2212_ = ((lean_object*)(l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___closed__0));
if (v_isShared_2187_ == 0)
{
lean_ctor_set(v___x_2186_, 1, v___x_2204_);
lean_ctor_set(v___x_2186_, 0, v___x_2212_);
v___x_2214_ = v___x_2186_;
goto v_reusejp_2213_;
}
else
{
lean_object* v_reuseFailAlloc_2216_; 
v_reuseFailAlloc_2216_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2216_, 0, v___x_2212_);
lean_ctor_set(v_reuseFailAlloc_2216_, 1, v___x_2204_);
v___x_2214_ = v_reuseFailAlloc_2216_;
goto v_reusejp_2213_;
}
v_reusejp_2213_:
{
lean_object* v___x_2215_; 
v___x_2215_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2215_, 0, v___x_2214_);
return v___x_2215_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg___boxed(lean_object* v_upperBound_2227_, lean_object* v_a_2228_, lean_object* v_a_2229_, lean_object* v_b_2230_, lean_object* v___y_2231_){
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_2227_, v_a_2228_, v_a_2229_, v_b_2230_);
lean_dec_ref(v_a_2228_);
lean_dec(v_upperBound_2227_);
return v_res_2232_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0(void){
_start:
{
lean_object* v___x_2233_; lean_object* v_dummy_2234_; 
v___x_2233_ = lean_box(0);
v_dummy_2234_ = l_Lean_Expr_sort___override(v___x_2233_);
return v_dummy_2234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(lean_object* v___x_2235_, uint8_t v___x_2236_, lean_object* v_x_2237_, lean_object* v_argTy_2238_, lean_object* v___y_2239_, lean_object* v___y_2240_, lean_object* v___y_2241_, lean_object* v___y_2242_){
_start:
{
lean_object* v___x_2244_; 
lean_inc(v___y_2242_);
lean_inc_ref(v___y_2241_);
lean_inc(v___y_2240_);
lean_inc_ref(v___y_2239_);
v___x_2244_ = lean_whnf(v_argTy_2238_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
if (lean_obj_tag(v___x_2244_) == 0)
{
lean_object* v_a_2245_; lean_object* v___x_2246_; 
v_a_2245_ = lean_ctor_get(v___x_2244_, 0);
lean_inc(v_a_2245_);
lean_dec_ref_known(v___x_2244_, 1);
v___x_2246_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2245_, v___y_2239_, v___y_2240_, v___y_2241_, v___y_2242_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v_a_2247_; lean_object* v_dummy_2248_; lean_object* v_nargs_2249_; lean_object* v___x_2250_; lean_object* v___x_2251_; lean_object* v___x_2252_; lean_object* v___x_2253_; lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; lean_object* v___x_2258_; 
v_a_2247_ = lean_ctor_get(v___x_2246_, 0);
lean_inc(v_a_2247_);
lean_dec_ref_known(v___x_2246_, 1);
v_dummy_2248_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2249_ = l_Lean_Expr_getAppNumArgs(v_a_2245_);
lean_inc(v_nargs_2249_);
v___x_2250_ = lean_mk_array(v_nargs_2249_, v_dummy_2248_);
v___x_2251_ = lean_unsigned_to_nat(1u);
v___x_2252_ = lean_nat_sub(v_nargs_2249_, v___x_2251_);
lean_dec(v_nargs_2249_);
v___x_2253_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2245_, v___x_2250_, v___x_2252_);
v___x_2254_ = lean_array_get_size(v___x_2253_);
lean_inc(v___x_2235_);
v___x_2255_ = l_Array_toSubarray___redArg(v___x_2253_, v___x_2235_, v___x_2254_);
v___x_2256_ = lean_box(0);
v___x_2257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
lean_ctor_set(v___x_2257_, 1, v___x_2255_);
v___x_2258_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v___x_2254_, v_a_2247_, v___x_2235_, v___x_2257_);
lean_dec(v_a_2247_);
if (lean_obj_tag(v___x_2258_) == 0)
{
lean_object* v_a_2259_; lean_object* v___x_2261_; uint8_t v_isShared_2262_; uint8_t v_isSharedCheck_2272_; 
v_a_2259_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2272_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2272_ == 0)
{
v___x_2261_ = v___x_2258_;
v_isShared_2262_ = v_isSharedCheck_2272_;
goto v_resetjp_2260_;
}
else
{
lean_inc(v_a_2259_);
lean_dec(v___x_2258_);
v___x_2261_ = lean_box(0);
v_isShared_2262_ = v_isSharedCheck_2272_;
goto v_resetjp_2260_;
}
v_resetjp_2260_:
{
lean_object* v_fst_2263_; 
v_fst_2263_ = lean_ctor_get(v_a_2259_, 0);
lean_inc(v_fst_2263_);
lean_dec(v_a_2259_);
if (lean_obj_tag(v_fst_2263_) == 0)
{
lean_object* v___x_2264_; lean_object* v___x_2266_; 
v___x_2264_ = lean_box(v___x_2236_);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v___x_2264_);
v___x_2266_ = v___x_2261_;
goto v_reusejp_2265_;
}
else
{
lean_object* v_reuseFailAlloc_2267_; 
v_reuseFailAlloc_2267_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2267_, 0, v___x_2264_);
v___x_2266_ = v_reuseFailAlloc_2267_;
goto v_reusejp_2265_;
}
v_reusejp_2265_:
{
return v___x_2266_;
}
}
else
{
lean_object* v_val_2268_; lean_object* v___x_2270_; 
v_val_2268_ = lean_ctor_get(v_fst_2263_, 0);
lean_inc(v_val_2268_);
lean_dec_ref_known(v_fst_2263_, 1);
if (v_isShared_2262_ == 0)
{
lean_ctor_set(v___x_2261_, 0, v_val_2268_);
v___x_2270_ = v___x_2261_;
goto v_reusejp_2269_;
}
else
{
lean_object* v_reuseFailAlloc_2271_; 
v_reuseFailAlloc_2271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2271_, 0, v_val_2268_);
v___x_2270_ = v_reuseFailAlloc_2271_;
goto v_reusejp_2269_;
}
v_reusejp_2269_:
{
return v___x_2270_;
}
}
}
}
else
{
lean_object* v_a_2273_; lean_object* v___x_2275_; uint8_t v_isShared_2276_; uint8_t v_isSharedCheck_2280_; 
v_a_2273_ = lean_ctor_get(v___x_2258_, 0);
v_isSharedCheck_2280_ = !lean_is_exclusive(v___x_2258_);
if (v_isSharedCheck_2280_ == 0)
{
v___x_2275_ = v___x_2258_;
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
else
{
lean_inc(v_a_2273_);
lean_dec(v___x_2258_);
v___x_2275_ = lean_box(0);
v_isShared_2276_ = v_isSharedCheck_2280_;
goto v_resetjp_2274_;
}
v_resetjp_2274_:
{
lean_object* v___x_2278_; 
if (v_isShared_2276_ == 0)
{
v___x_2278_ = v___x_2275_;
goto v_reusejp_2277_;
}
else
{
lean_object* v_reuseFailAlloc_2279_; 
v_reuseFailAlloc_2279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2279_, 0, v_a_2273_);
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
lean_dec(v_a_2245_);
lean_dec(v___x_2235_);
v_a_2281_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2288_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2288_ == 0)
{
v___x_2283_ = v___x_2246_;
v_isShared_2284_ = v_isSharedCheck_2288_;
goto v_resetjp_2282_;
}
else
{
lean_inc(v_a_2281_);
lean_dec(v___x_2246_);
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
lean_dec(v___x_2235_);
v_a_2289_ = lean_ctor_get(v___x_2244_, 0);
v_isSharedCheck_2296_ = !lean_is_exclusive(v___x_2244_);
if (v_isSharedCheck_2296_ == 0)
{
v___x_2291_ = v___x_2244_;
v_isShared_2292_ = v_isSharedCheck_2296_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_a_2289_);
lean_dec(v___x_2244_);
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
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed(lean_object* v___x_2297_, lean_object* v___x_2298_, lean_object* v_x_2299_, lean_object* v_argTy_2300_, lean_object* v___y_2301_, lean_object* v___y_2302_, lean_object* v___y_2303_, lean_object* v___y_2304_, lean_object* v___y_2305_){
_start:
{
uint8_t v___x_25397__boxed_2306_; lean_object* v_res_2307_; 
v___x_25397__boxed_2306_ = lean_unbox(v___x_2298_);
v_res_2307_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0(v___x_2297_, v___x_25397__boxed_2306_, v_x_2299_, v_argTy_2300_, v___y_2301_, v___y_2302_, v___y_2303_, v___y_2304_);
lean_dec(v___y_2304_);
lean_dec_ref(v___y_2303_);
lean_dec(v___y_2302_);
lean_dec_ref(v___y_2301_);
lean_dec_ref(v_x_2299_);
return v_res_2307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__1(lean_object* v_a_2308_, lean_object* v___f_2309_, lean_object* v_____r_2310_, lean_object* v___y_2311_, lean_object* v___y_2312_, lean_object* v___y_2313_, lean_object* v___y_2314_){
_start:
{
uint8_t v___x_2316_; lean_object* v___x_2317_; 
v___x_2316_ = 0;
v___x_2317_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_2308_, v___f_2309_, v___x_2316_, v___x_2316_, v___y_2311_, v___y_2312_, v___y_2313_, v___y_2314_);
return v___x_2317_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__1___boxed(lean_object* v_a_2318_, lean_object* v___f_2319_, lean_object* v_____r_2320_, lean_object* v___y_2321_, lean_object* v___y_2322_, lean_object* v___y_2323_, lean_object* v___y_2324_, lean_object* v___y_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__1(v_a_2318_, v___f_2319_, v_____r_2320_, v___y_2321_, v___y_2322_, v___y_2323_, v___y_2324_);
lean_dec(v___y_2324_);
lean_dec_ref(v___y_2323_);
lean_dec(v___y_2322_);
lean_dec_ref(v___y_2321_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(lean_object* v_fst_2330_, lean_object* v___x_2331_, lean_object* v_projInfo_x3f_2332_, lean_object* v_argVars_2333_, lean_object* v_as_2334_, size_t v_sz_2335_, size_t v_i_2336_, lean_object* v_b_2337_, lean_object* v___y_2338_, lean_object* v___y_2339_, lean_object* v___y_2340_, lean_object* v___y_2341_){
_start:
{
uint8_t v___x_2343_; 
v___x_2343_ = lean_usize_dec_lt(v_i_2336_, v_sz_2335_);
if (v___x_2343_ == 0)
{
lean_object* v___x_2344_; 
v___x_2344_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2344_, 0, v_b_2337_);
return v___x_2344_;
}
else
{
lean_object* v_a_2345_; lean_object* v___x_2346_; lean_object* v___x_2347_; lean_object* v___x_2348_; 
lean_dec_ref(v_b_2337_);
v_a_2345_ = lean_array_uget_borrowed(v_as_2334_, v_i_2336_);
v___x_2346_ = l_Lean_instInhabitedExpr;
v___x_2347_ = lean_array_get_borrowed(v___x_2346_, v_fst_2330_, v_a_2345_);
lean_inc(v___y_2341_);
lean_inc_ref(v___y_2340_);
lean_inc(v___y_2339_);
lean_inc_ref(v___y_2338_);
lean_inc(v___x_2347_);
v___x_2348_ = lean_infer_type(v___x_2347_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
if (lean_obj_tag(v___x_2348_) == 0)
{
lean_object* v_a_2349_; lean_object* v___x_2350_; 
v_a_2349_ = lean_ctor_get(v___x_2348_, 0);
lean_inc(v_a_2349_);
lean_dec_ref_known(v___x_2348_, 1);
v___x_2350_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2349_, v___y_2339_);
if (lean_obj_tag(v___x_2350_) == 0)
{
lean_object* v_a_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2398_; 
v_a_2351_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2398_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2398_ == 0)
{
v___x_2353_ = v___x_2350_;
v_isShared_2354_ = v_isSharedCheck_2398_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_a_2351_);
lean_dec(v___x_2350_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2398_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v___x_2355_; lean_object* v___x_2363_; lean_object* v___y_2365_; lean_object* v___x_2379_; uint8_t v___x_2380_; uint8_t v___x_2381_; lean_object* v___x_2382_; lean_object* v___f_2383_; 
v___x_2355_ = lean_box(0);
v___x_2363_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v___x_2379_ = lean_unsigned_to_nat(0u);
v___x_2380_ = lean_nat_dec_eq(v___x_2331_, v___x_2379_);
v___x_2381_ = lean_bool_not(v___x_2380_);
v___x_2382_ = lean_box(v___x_2381_);
v___f_2383_ = lean_alloc_closure((void*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___boxed), 9, 2);
lean_closure_set(v___f_2383_, 0, v___x_2379_);
lean_closure_set(v___f_2383_, 1, v___x_2382_);
if (lean_obj_tag(v_projInfo_x3f_2332_) == 1)
{
lean_object* v_val_2384_; lean_object* v_numParams_2385_; uint8_t v___x_2386_; 
v_val_2384_ = lean_ctor_get(v_projInfo_x3f_2332_, 0);
v_numParams_2385_ = lean_ctor_get(v_val_2384_, 1);
v___x_2386_ = lean_nat_dec_eq(v_numParams_2385_, v_a_2345_);
if (v___x_2386_ == 0)
{
lean_object* v___x_2387_; 
v___x_2387_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__1(v_a_2351_, v___f_2383_, v___x_2355_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
v___y_2365_ = v___x_2387_;
goto v___jp_2364_;
}
else
{
lean_object* v___x_2388_; 
lean_dec_ref(v___f_2383_);
v___x_2388_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_assignMVarsIn(v_fst_2330_, v_argVars_2333_, v_a_2351_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
if (lean_obj_tag(v___x_2388_) == 0)
{
lean_dec_ref_known(v___x_2388_, 1);
goto v___jp_2356_;
}
else
{
lean_object* v_a_2389_; lean_object* v___x_2391_; uint8_t v_isShared_2392_; uint8_t v_isSharedCheck_2396_; 
lean_del_object(v___x_2353_);
v_a_2389_ = lean_ctor_get(v___x_2388_, 0);
v_isSharedCheck_2396_ = !lean_is_exclusive(v___x_2388_);
if (v_isSharedCheck_2396_ == 0)
{
v___x_2391_ = v___x_2388_;
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
else
{
lean_inc(v_a_2389_);
lean_dec(v___x_2388_);
v___x_2391_ = lean_box(0);
v_isShared_2392_ = v_isSharedCheck_2396_;
goto v_resetjp_2390_;
}
v_resetjp_2390_:
{
lean_object* v___x_2394_; 
if (v_isShared_2392_ == 0)
{
v___x_2394_ = v___x_2391_;
goto v_reusejp_2393_;
}
else
{
lean_object* v_reuseFailAlloc_2395_; 
v_reuseFailAlloc_2395_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2395_, 0, v_a_2389_);
v___x_2394_ = v_reuseFailAlloc_2395_;
goto v_reusejp_2393_;
}
v_reusejp_2393_:
{
return v___x_2394_;
}
}
}
}
}
else
{
lean_object* v___x_2397_; 
v___x_2397_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__1(v_a_2351_, v___f_2383_, v___x_2355_, v___y_2338_, v___y_2339_, v___y_2340_, v___y_2341_);
v___y_2365_ = v___x_2397_;
goto v___jp_2364_;
}
v___jp_2356_:
{
lean_object* v___x_2357_; lean_object* v___x_2358_; lean_object* v___x_2359_; lean_object* v___x_2361_; 
lean_inc(v_a_2345_);
v___x_2357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2357_, 0, v_a_2345_);
v___x_2358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2358_, 0, v___x_2357_);
v___x_2359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2359_, 0, v___x_2358_);
lean_ctor_set(v___x_2359_, 1, v___x_2355_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 0, v___x_2359_);
v___x_2361_ = v___x_2353_;
goto v_reusejp_2360_;
}
else
{
lean_object* v_reuseFailAlloc_2362_; 
v_reuseFailAlloc_2362_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2362_, 0, v___x_2359_);
v___x_2361_ = v_reuseFailAlloc_2362_;
goto v_reusejp_2360_;
}
v_reusejp_2360_:
{
return v___x_2361_;
}
}
v___jp_2364_:
{
if (lean_obj_tag(v___y_2365_) == 0)
{
lean_object* v_a_2366_; uint8_t v___x_2367_; 
v_a_2366_ = lean_ctor_get(v___y_2365_, 0);
lean_inc(v_a_2366_);
lean_dec_ref_known(v___y_2365_, 1);
v___x_2367_ = lean_unbox(v_a_2366_);
lean_dec(v_a_2366_);
if (v___x_2367_ == 0)
{
size_t v___x_2368_; size_t v___x_2369_; 
lean_del_object(v___x_2353_);
v___x_2368_ = ((size_t)1ULL);
v___x_2369_ = lean_usize_add(v_i_2336_, v___x_2368_);
v_i_2336_ = v___x_2369_;
v_b_2337_ = v___x_2363_;
goto _start;
}
else
{
goto v___jp_2356_;
}
}
else
{
lean_object* v_a_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2378_; 
lean_del_object(v___x_2353_);
v_a_2371_ = lean_ctor_get(v___y_2365_, 0);
v_isSharedCheck_2378_ = !lean_is_exclusive(v___y_2365_);
if (v_isSharedCheck_2378_ == 0)
{
v___x_2373_ = v___y_2365_;
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_a_2371_);
lean_dec(v___y_2365_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2378_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v___x_2376_; 
if (v_isShared_2374_ == 0)
{
v___x_2376_ = v___x_2373_;
goto v_reusejp_2375_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_a_2371_);
v___x_2376_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2375_;
}
v_reusejp_2375_:
{
return v___x_2376_;
}
}
}
}
}
}
else
{
lean_object* v_a_2399_; lean_object* v___x_2401_; uint8_t v_isShared_2402_; uint8_t v_isSharedCheck_2406_; 
v_a_2399_ = lean_ctor_get(v___x_2350_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2350_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2401_ = v___x_2350_;
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
else
{
lean_inc(v_a_2399_);
lean_dec(v___x_2350_);
v___x_2401_ = lean_box(0);
v_isShared_2402_ = v_isSharedCheck_2406_;
goto v_resetjp_2400_;
}
v_resetjp_2400_:
{
lean_object* v___x_2404_; 
if (v_isShared_2402_ == 0)
{
v___x_2404_ = v___x_2401_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2405_; 
v_reuseFailAlloc_2405_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2405_, 0, v_a_2399_);
v___x_2404_ = v_reuseFailAlloc_2405_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
return v___x_2404_;
}
}
}
}
else
{
lean_object* v_a_2407_; lean_object* v___x_2409_; uint8_t v_isShared_2410_; uint8_t v_isSharedCheck_2414_; 
v_a_2407_ = lean_ctor_get(v___x_2348_, 0);
v_isSharedCheck_2414_ = !lean_is_exclusive(v___x_2348_);
if (v_isSharedCheck_2414_ == 0)
{
v___x_2409_ = v___x_2348_;
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
else
{
lean_inc(v_a_2407_);
lean_dec(v___x_2348_);
v___x_2409_ = lean_box(0);
v_isShared_2410_ = v_isSharedCheck_2414_;
goto v_resetjp_2408_;
}
v_resetjp_2408_:
{
lean_object* v___x_2412_; 
if (v_isShared_2410_ == 0)
{
v___x_2412_ = v___x_2409_;
goto v_reusejp_2411_;
}
else
{
lean_object* v_reuseFailAlloc_2413_; 
v_reuseFailAlloc_2413_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2413_, 0, v_a_2407_);
v___x_2412_ = v_reuseFailAlloc_2413_;
goto v_reusejp_2411_;
}
v_reusejp_2411_:
{
return v___x_2412_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___boxed(lean_object* v_fst_2415_, lean_object* v___x_2416_, lean_object* v_projInfo_x3f_2417_, lean_object* v_argVars_2418_, lean_object* v_as_2419_, lean_object* v_sz_2420_, lean_object* v_i_2421_, lean_object* v_b_2422_, lean_object* v___y_2423_, lean_object* v___y_2424_, lean_object* v___y_2425_, lean_object* v___y_2426_, lean_object* v___y_2427_){
_start:
{
size_t v_sz_boxed_2428_; size_t v_i_boxed_2429_; lean_object* v_res_2430_; 
v_sz_boxed_2428_ = lean_unbox_usize(v_sz_2420_);
lean_dec(v_sz_2420_);
v_i_boxed_2429_ = lean_unbox_usize(v_i_2421_);
lean_dec(v_i_2421_);
v_res_2430_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2415_, v___x_2416_, v_projInfo_x3f_2417_, v_argVars_2418_, v_as_2419_, v_sz_boxed_2428_, v_i_boxed_2429_, v_b_2422_, v___y_2423_, v___y_2424_, v___y_2425_, v___y_2426_);
lean_dec(v___y_2426_);
lean_dec_ref(v___y_2425_);
lean_dec(v___y_2424_);
lean_dec_ref(v___y_2423_);
lean_dec_ref(v_as_2419_);
lean_dec_ref(v_argVars_2418_);
lean_dec(v_projInfo_x3f_2417_);
lean_dec(v___x_2416_);
lean_dec_ref(v_fst_2415_);
return v_res_2430_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(lean_object* v_msgData_2431_, lean_object* v___y_2432_, lean_object* v___y_2433_, lean_object* v___y_2434_, lean_object* v___y_2435_){
_start:
{
lean_object* v___x_2437_; lean_object* v_env_2438_; lean_object* v___x_2439_; lean_object* v_mctx_2440_; lean_object* v_lctx_2441_; lean_object* v_options_2442_; lean_object* v___x_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; 
v___x_2437_ = lean_st_ref_get(v___y_2435_);
v_env_2438_ = lean_ctor_get(v___x_2437_, 0);
lean_inc_ref(v_env_2438_);
lean_dec(v___x_2437_);
v___x_2439_ = lean_st_ref_get(v___y_2433_);
v_mctx_2440_ = lean_ctor_get(v___x_2439_, 0);
lean_inc_ref(v_mctx_2440_);
lean_dec(v___x_2439_);
v_lctx_2441_ = lean_ctor_get(v___y_2432_, 2);
v_options_2442_ = lean_ctor_get(v___y_2434_, 2);
lean_inc_ref(v_options_2442_);
lean_inc_ref(v_lctx_2441_);
v___x_2443_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_2443_, 0, v_env_2438_);
lean_ctor_set(v___x_2443_, 1, v_mctx_2440_);
lean_ctor_set(v___x_2443_, 2, v_lctx_2441_);
lean_ctor_set(v___x_2443_, 3, v_options_2442_);
v___x_2444_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_2444_, 0, v___x_2443_);
lean_ctor_set(v___x_2444_, 1, v_msgData_2431_);
v___x_2445_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2445_, 0, v___x_2444_);
return v___x_2445_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7___boxed(lean_object* v_msgData_2446_, lean_object* v___y_2447_, lean_object* v___y_2448_, lean_object* v___y_2449_, lean_object* v___y_2450_, lean_object* v___y_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msgData_2446_, v___y_2447_, v___y_2448_, v___y_2449_, v___y_2450_);
lean_dec(v___y_2450_);
lean_dec_ref(v___y_2449_);
lean_dec(v___y_2448_);
lean_dec_ref(v___y_2447_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(lean_object* v_msg_2453_, lean_object* v___y_2454_, lean_object* v___y_2455_, lean_object* v___y_2456_, lean_object* v___y_2457_){
_start:
{
lean_object* v_ref_2459_; lean_object* v___x_2460_; lean_object* v_a_2461_; lean_object* v___x_2463_; uint8_t v_isShared_2464_; uint8_t v_isSharedCheck_2469_; 
v_ref_2459_ = lean_ctor_get(v___y_2456_, 5);
v___x_2460_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2453_, v___y_2454_, v___y_2455_, v___y_2456_, v___y_2457_);
v_a_2461_ = lean_ctor_get(v___x_2460_, 0);
v_isSharedCheck_2469_ = !lean_is_exclusive(v___x_2460_);
if (v_isSharedCheck_2469_ == 0)
{
v___x_2463_ = v___x_2460_;
v_isShared_2464_ = v_isSharedCheck_2469_;
goto v_resetjp_2462_;
}
else
{
lean_inc(v_a_2461_);
lean_dec(v___x_2460_);
v___x_2463_ = lean_box(0);
v_isShared_2464_ = v_isSharedCheck_2469_;
goto v_resetjp_2462_;
}
v_resetjp_2462_:
{
lean_object* v___x_2465_; lean_object* v___x_2467_; 
lean_inc(v_ref_2459_);
v___x_2465_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2465_, 0, v_ref_2459_);
lean_ctor_set(v___x_2465_, 1, v_a_2461_);
if (v_isShared_2464_ == 0)
{
lean_ctor_set_tag(v___x_2463_, 1);
lean_ctor_set(v___x_2463_, 0, v___x_2465_);
v___x_2467_ = v___x_2463_;
goto v_reusejp_2466_;
}
else
{
lean_object* v_reuseFailAlloc_2468_; 
v_reuseFailAlloc_2468_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2468_, 0, v___x_2465_);
v___x_2467_ = v_reuseFailAlloc_2468_;
goto v_reusejp_2466_;
}
v_reusejp_2466_:
{
return v___x_2467_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg___boxed(lean_object* v_msg_2470_, lean_object* v___y_2471_, lean_object* v___y_2472_, lean_object* v___y_2473_, lean_object* v___y_2474_, lean_object* v___y_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_2470_, v___y_2471_, v___y_2472_, v___y_2473_, v___y_2474_);
lean_dec(v___y_2474_);
lean_dec_ref(v___y_2473_);
lean_dec(v___y_2472_);
lean_dec_ref(v___y_2471_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(lean_object* v_fst_2477_, lean_object* v___x_2478_, size_t v_sz_2479_, size_t v_i_2480_, lean_object* v_bs_2481_, lean_object* v___y_2482_, lean_object* v___y_2483_, lean_object* v___y_2484_, lean_object* v___y_2485_){
_start:
{
uint8_t v___x_2487_; 
v___x_2487_ = lean_usize_dec_lt(v_i_2480_, v_sz_2479_);
if (v___x_2487_ == 0)
{
lean_object* v___x_2488_; 
v___x_2488_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2488_, 0, v_bs_2481_);
return v___x_2488_;
}
else
{
lean_object* v_v_2489_; lean_object* v___x_2490_; lean_object* v___x_2491_; lean_object* v___x_2492_; 
v_v_2489_ = lean_array_uget_borrowed(v_bs_2481_, v_i_2480_);
v___x_2490_ = l_Lean_instInhabitedExpr;
v___x_2491_ = lean_array_get_borrowed(v___x_2490_, v_fst_2477_, v_v_2489_);
lean_inc(v___y_2485_);
lean_inc_ref(v___y_2484_);
lean_inc(v___y_2483_);
lean_inc_ref(v___y_2482_);
lean_inc(v___x_2491_);
v___x_2492_ = lean_infer_type(v___x_2491_, v___y_2482_, v___y_2483_, v___y_2484_, v___y_2485_);
if (lean_obj_tag(v___x_2492_) == 0)
{
lean_object* v_a_2493_; lean_object* v___x_2494_; 
v_a_2493_ = lean_ctor_get(v___x_2492_, 0);
lean_inc(v_a_2493_);
lean_dec_ref_known(v___x_2492_, 1);
v___x_2494_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2493_, v___y_2483_);
if (lean_obj_tag(v___x_2494_) == 0)
{
lean_object* v_a_2495_; lean_object* v___x_2496_; uint8_t v___x_2497_; uint8_t v___x_2498_; lean_object* v_bs_x27_2499_; lean_object* v___x_2500_; lean_object* v___x_2501_; size_t v___x_2502_; size_t v___x_2503_; lean_object* v___x_2504_; 
v_a_2495_ = lean_ctor_get(v___x_2494_, 0);
lean_inc(v_a_2495_);
lean_dec_ref_known(v___x_2494_, 1);
v___x_2496_ = lean_unsigned_to_nat(0u);
v___x_2497_ = lean_nat_dec_eq(v___x_2478_, v___x_2496_);
v___x_2498_ = lean_bool_not(v___x_2497_);
v_bs_x27_2499_ = lean_array_uset(v_bs_2481_, v_i_2480_, v___x_2496_);
v___x_2500_ = l_Lean_Expr_setPPExplicit(v_a_2495_, v___x_2498_);
v___x_2501_ = l_Lean_indentExpr(v___x_2500_);
v___x_2502_ = ((size_t)1ULL);
v___x_2503_ = lean_usize_add(v_i_2480_, v___x_2502_);
v___x_2504_ = lean_array_uset(v_bs_x27_2499_, v_i_2480_, v___x_2501_);
v_i_2480_ = v___x_2503_;
v_bs_2481_ = v___x_2504_;
goto _start;
}
else
{
lean_object* v_a_2506_; lean_object* v___x_2508_; uint8_t v_isShared_2509_; uint8_t v_isSharedCheck_2513_; 
lean_dec_ref(v_bs_2481_);
v_a_2506_ = lean_ctor_get(v___x_2494_, 0);
v_isSharedCheck_2513_ = !lean_is_exclusive(v___x_2494_);
if (v_isSharedCheck_2513_ == 0)
{
v___x_2508_ = v___x_2494_;
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
else
{
lean_inc(v_a_2506_);
lean_dec(v___x_2494_);
v___x_2508_ = lean_box(0);
v_isShared_2509_ = v_isSharedCheck_2513_;
goto v_resetjp_2507_;
}
v_resetjp_2507_:
{
lean_object* v___x_2511_; 
if (v_isShared_2509_ == 0)
{
v___x_2511_ = v___x_2508_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2512_; 
v_reuseFailAlloc_2512_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2512_, 0, v_a_2506_);
v___x_2511_ = v_reuseFailAlloc_2512_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
return v___x_2511_;
}
}
}
}
else
{
lean_object* v_a_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2521_; 
lean_dec_ref(v_bs_2481_);
v_a_2514_ = lean_ctor_get(v___x_2492_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2492_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2516_ = v___x_2492_;
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_a_2514_);
lean_dec(v___x_2492_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2521_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2519_; 
if (v_isShared_2517_ == 0)
{
v___x_2519_ = v___x_2516_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v_a_2514_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5___boxed(lean_object* v_fst_2522_, lean_object* v___x_2523_, lean_object* v_sz_2524_, lean_object* v_i_2525_, lean_object* v_bs_2526_, lean_object* v___y_2527_, lean_object* v___y_2528_, lean_object* v___y_2529_, lean_object* v___y_2530_, lean_object* v___y_2531_){
_start:
{
size_t v_sz_boxed_2532_; size_t v_i_boxed_2533_; lean_object* v_res_2534_; 
v_sz_boxed_2532_ = lean_unbox_usize(v_sz_2524_);
lean_dec(v_sz_2524_);
v_i_boxed_2533_ = lean_unbox_usize(v_i_2525_);
lean_dec(v_i_2525_);
v_res_2534_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2522_, v___x_2523_, v_sz_boxed_2532_, v_i_boxed_2533_, v_bs_2526_, v___y_2527_, v___y_2528_, v___y_2529_, v___y_2530_);
lean_dec(v___y_2530_);
lean_dec_ref(v___y_2529_);
lean_dec(v___y_2528_);
lean_dec_ref(v___y_2527_);
lean_dec(v___x_2523_);
lean_dec_ref(v_fst_2522_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(lean_object* v_snd_2535_, lean_object* v___f_2536_, lean_object* v_____r_2537_, lean_object* v___y_2538_, lean_object* v___y_2539_, lean_object* v___y_2540_, lean_object* v___y_2541_){
_start:
{
lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; 
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = lean_array_get_borrowed(v___x_2543_, v_snd_2535_, v___x_2543_);
lean_inc(v___y_2541_);
lean_inc_ref(v___y_2540_);
lean_inc(v___y_2539_);
lean_inc_ref(v___y_2538_);
lean_inc(v___x_2544_);
v___x_2545_ = lean_apply_6(v___f_2536_, v___x_2544_, v___y_2538_, v___y_2539_, v___y_2540_, v___y_2541_, lean_box(0));
return v___x_2545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1___boxed(lean_object* v_snd_2546_, lean_object* v___f_2547_, lean_object* v_____r_2548_, lean_object* v___y_2549_, lean_object* v___y_2550_, lean_object* v___y_2551_, lean_object* v___y_2552_, lean_object* v___y_2553_){
_start:
{
lean_object* v_res_2554_; 
v_res_2554_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2546_, v___f_2547_, v_____r_2548_, v___y_2549_, v___y_2550_, v___y_2551_, v___y_2552_);
lean_dec(v___y_2552_);
lean_dec_ref(v___y_2551_);
lean_dec(v___y_2550_);
lean_dec_ref(v___y_2549_);
lean_dec(v_snd_2546_);
return v_res_2554_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_2558_; lean_object* v___x_2559_; 
v___x_2558_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__1));
v___x_2559_ = l_Lean_MessageData_ofFormat(v___x_2558_);
return v___x_2559_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__3));
v___x_2562_ = l_Lean_stringToMessageData(v___x_2561_);
return v___x_2562_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6(void){
_start:
{
lean_object* v___x_2564_; lean_object* v___x_2565_; 
v___x_2564_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__5));
v___x_2565_ = l_Lean_stringToMessageData(v___x_2564_);
return v___x_2565_;
}
}
static lean_object* _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8(void){
_start:
{
lean_object* v___x_2567_; lean_object* v___x_2568_; 
v___x_2567_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__7));
v___x_2568_ = l_Lean_stringToMessageData(v___x_2567_);
return v___x_2568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(lean_object* v_fst_2569_, lean_object* v_argVars_2570_, lean_object* v_inst_2571_, lean_object* v_a_2572_, lean_object* v_projInfo_x3f_2573_, lean_object* v_a_2574_, lean_object* v___y_2575_, lean_object* v___y_2576_, lean_object* v___y_2577_, lean_object* v___y_2578_){
_start:
{
lean_object* v___y_2581_; lean_object* v_fst_2601_; lean_object* v_snd_2602_; lean_object* v___x_2604_; uint8_t v_isShared_2605_; uint8_t v_isSharedCheck_2679_; 
v_fst_2601_ = lean_ctor_get(v_a_2574_, 0);
v_snd_2602_ = lean_ctor_get(v_a_2574_, 1);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_a_2574_);
if (v_isSharedCheck_2679_ == 0)
{
v___x_2604_ = v_a_2574_;
v_isShared_2605_ = v_isSharedCheck_2679_;
goto v_resetjp_2603_;
}
else
{
lean_inc(v_snd_2602_);
lean_inc(v_fst_2601_);
lean_dec(v_a_2574_);
v___x_2604_ = lean_box(0);
v_isShared_2605_ = v_isSharedCheck_2679_;
goto v_resetjp_2603_;
}
v___jp_2580_:
{
if (lean_obj_tag(v___y_2581_) == 0)
{
lean_object* v_a_2582_; lean_object* v___x_2584_; uint8_t v_isShared_2585_; uint8_t v_isSharedCheck_2592_; 
v_a_2582_ = lean_ctor_get(v___y_2581_, 0);
v_isSharedCheck_2592_ = !lean_is_exclusive(v___y_2581_);
if (v_isSharedCheck_2592_ == 0)
{
v___x_2584_ = v___y_2581_;
v_isShared_2585_ = v_isSharedCheck_2592_;
goto v_resetjp_2583_;
}
else
{
lean_inc(v_a_2582_);
lean_dec(v___y_2581_);
v___x_2584_ = lean_box(0);
v_isShared_2585_ = v_isSharedCheck_2592_;
goto v_resetjp_2583_;
}
v_resetjp_2583_:
{
if (lean_obj_tag(v_a_2582_) == 0)
{
lean_object* v_a_2586_; lean_object* v___x_2588_; 
lean_dec_ref(v_a_2572_);
lean_dec_ref(v_inst_2571_);
lean_dec_ref(v_argVars_2570_);
lean_dec_ref(v_fst_2569_);
v_a_2586_ = lean_ctor_get(v_a_2582_, 0);
lean_inc(v_a_2586_);
lean_dec_ref_known(v_a_2582_, 1);
if (v_isShared_2585_ == 0)
{
lean_ctor_set(v___x_2584_, 0, v_a_2586_);
v___x_2588_ = v___x_2584_;
goto v_reusejp_2587_;
}
else
{
lean_object* v_reuseFailAlloc_2589_; 
v_reuseFailAlloc_2589_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2589_, 0, v_a_2586_);
v___x_2588_ = v_reuseFailAlloc_2589_;
goto v_reusejp_2587_;
}
v_reusejp_2587_:
{
return v___x_2588_;
}
}
else
{
lean_object* v_a_2590_; 
lean_del_object(v___x_2584_);
v_a_2590_ = lean_ctor_get(v_a_2582_, 0);
lean_inc(v_a_2590_);
lean_dec_ref_known(v_a_2582_, 1);
v_a_2574_ = v_a_2590_;
goto _start;
}
}
}
else
{
lean_object* v_a_2593_; lean_object* v___x_2595_; uint8_t v_isShared_2596_; uint8_t v_isSharedCheck_2600_; 
lean_dec_ref(v_a_2572_);
lean_dec_ref(v_inst_2571_);
lean_dec_ref(v_argVars_2570_);
lean_dec_ref(v_fst_2569_);
v_a_2593_ = lean_ctor_get(v___y_2581_, 0);
v_isSharedCheck_2600_ = !lean_is_exclusive(v___y_2581_);
if (v_isSharedCheck_2600_ == 0)
{
v___x_2595_ = v___y_2581_;
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
else
{
lean_inc(v_a_2593_);
lean_dec(v___y_2581_);
v___x_2595_ = lean_box(0);
v_isShared_2596_ = v_isSharedCheck_2600_;
goto v_resetjp_2594_;
}
v_resetjp_2594_:
{
lean_object* v___x_2598_; 
if (v_isShared_2596_ == 0)
{
v___x_2598_ = v___x_2595_;
goto v_reusejp_2597_;
}
else
{
lean_object* v_reuseFailAlloc_2599_; 
v_reuseFailAlloc_2599_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2599_, 0, v_a_2593_);
v___x_2598_ = v_reuseFailAlloc_2599_;
goto v_reusejp_2597_;
}
v_reusejp_2597_:
{
return v___x_2598_;
}
}
}
}
v_resetjp_2603_:
{
lean_object* v___x_2606_; lean_object* v___x_2607_; uint8_t v___x_2608_; uint8_t v___x_2609_; 
v___x_2606_ = lean_array_get_size(v_snd_2602_);
v___x_2607_ = lean_unsigned_to_nat(0u);
v___x_2608_ = lean_nat_dec_eq(v___x_2606_, v___x_2607_);
v___x_2609_ = lean_bool_not(v___x_2608_);
if (v___x_2609_ == 0)
{
lean_object* v___x_2611_; 
lean_dec_ref(v_a_2572_);
lean_dec_ref(v_inst_2571_);
lean_dec_ref(v_argVars_2570_);
lean_dec_ref(v_fst_2569_);
if (v_isShared_2605_ == 0)
{
v___x_2611_ = v___x_2604_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_fst_2601_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_snd_2602_);
v___x_2611_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
lean_object* v___x_2612_; 
v___x_2612_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2612_, 0, v___x_2611_);
return v___x_2612_;
}
}
else
{
lean_object* v___x_2614_; lean_object* v___x_2615_; size_t v_sz_2616_; size_t v___x_2617_; lean_object* v___x_2618_; 
lean_del_object(v___x_2604_);
v___x_2614_ = lean_box(0);
v___x_2615_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___closed__0));
v_sz_2616_ = lean_array_size(v_snd_2602_);
v___x_2617_ = ((size_t)0ULL);
v___x_2618_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7(v_fst_2569_, v___x_2606_, v_projInfo_x3f_2573_, v_argVars_2570_, v_snd_2602_, v_sz_2616_, v___x_2617_, v___x_2615_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2618_) == 0)
{
lean_object* v_a_2619_; lean_object* v_fst_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2669_; 
v_a_2619_ = lean_ctor_get(v___x_2618_, 0);
lean_inc(v_a_2619_);
lean_dec_ref_known(v___x_2618_, 1);
v_fst_2620_ = lean_ctor_get(v_a_2619_, 0);
v_isSharedCheck_2669_ = !lean_is_exclusive(v_a_2619_);
if (v_isSharedCheck_2669_ == 0)
{
lean_object* v_unused_2670_; 
v_unused_2670_ = lean_ctor_get(v_a_2619_, 1);
lean_dec(v_unused_2670_);
v___x_2622_ = v_a_2619_;
v_isShared_2623_ = v_isSharedCheck_2669_;
goto v_resetjp_2621_;
}
else
{
lean_inc(v_fst_2620_);
lean_dec(v_a_2619_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2669_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___f_2624_; 
lean_inc(v_snd_2602_);
lean_inc_ref(v_argVars_2570_);
lean_inc_ref(v_fst_2569_);
lean_inc(v_fst_2601_);
v___f_2624_ = lean_alloc_closure((void*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_2624_, 0, v_fst_2601_);
lean_closure_set(v___f_2624_, 1, v_fst_2569_);
lean_closure_set(v___f_2624_, 2, v_argVars_2570_);
lean_closure_set(v___f_2624_, 3, v_snd_2602_);
if (lean_obj_tag(v_fst_2620_) == 0)
{
lean_dec(v_fst_2601_);
goto v___jp_2625_;
}
else
{
lean_object* v_val_2666_; 
v_val_2666_ = lean_ctor_get(v_fst_2620_, 0);
lean_inc(v_val_2666_);
lean_dec_ref_known(v_fst_2620_, 1);
if (lean_obj_tag(v_val_2666_) == 0)
{
lean_dec(v_fst_2601_);
goto v___jp_2625_;
}
else
{
lean_object* v_val_2667_; lean_object* v___x_2668_; 
lean_dec_ref(v___f_2624_);
lean_del_object(v___x_2622_);
v_val_2667_ = lean_ctor_get(v_val_2666_, 0);
lean_inc(v_val_2667_);
lean_dec_ref_known(v_val_2666_, 1);
v___x_2668_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__0(v_fst_2601_, v_fst_2569_, v_argVars_2570_, v_snd_2602_, v_val_2667_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
lean_dec(v_snd_2602_);
v___y_2581_ = v___x_2668_;
goto v___jp_2580_;
}
}
v___jp_2625_:
{
lean_object* v_options_2626_; lean_object* v___x_2627_; uint8_t v___x_2628_; 
v_options_2626_ = lean_ctor_get(v___y_2577_, 2);
v___x_2627_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2628_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2626_, v___x_2627_);
if (v___x_2628_ == 0)
{
lean_object* v___x_2629_; 
lean_del_object(v___x_2622_);
v___x_2629_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2602_, v___f_2624_, v___x_2614_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
lean_dec(v_snd_2602_);
v___y_2581_ = v___x_2629_;
goto v___jp_2580_;
}
else
{
lean_object* v___x_2630_; 
lean_inc(v_snd_2602_);
v___x_2630_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__5(v_fst_2569_, v___x_2606_, v_sz_2616_, v___x_2617_, v_snd_2602_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2630_) == 0)
{
lean_object* v_a_2631_; lean_object* v___x_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2638_; 
v_a_2631_ = lean_ctor_get(v___x_2630_, 0);
lean_inc(v_a_2631_);
lean_dec_ref_known(v___x_2630_, 1);
v___x_2632_ = lean_array_to_list(v_a_2631_);
v___x_2633_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2634_ = l_Lean_MessageData_joinSep(v___x_2632_, v___x_2633_);
v___x_2635_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__4);
lean_inc_ref(v_inst_2571_);
v___x_2636_ = l_Lean_MessageData_ofExpr(v_inst_2571_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set_tag(v___x_2622_, 7);
lean_ctor_set(v___x_2622_, 1, v___x_2636_);
lean_ctor_set(v___x_2622_, 0, v___x_2635_);
v___x_2638_ = v___x_2622_;
goto v_reusejp_2637_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v___x_2635_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v___x_2636_);
v___x_2638_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2637_;
}
v_reusejp_2637_:
{
lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; lean_object* v___x_2643_; lean_object* v___x_2644_; lean_object* v___x_2645_; lean_object* v___x_2646_; 
v___x_2639_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__6);
v___x_2640_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2640_, 0, v___x_2638_);
lean_ctor_set(v___x_2640_, 1, v___x_2639_);
lean_inc_ref(v_a_2572_);
v___x_2641_ = l_Lean_indentExpr(v_a_2572_);
v___x_2642_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2642_, 0, v___x_2640_);
lean_ctor_set(v___x_2642_, 1, v___x_2641_);
v___x_2643_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__8);
v___x_2644_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2644_, 0, v___x_2642_);
lean_ctor_set(v___x_2644_, 1, v___x_2643_);
v___x_2645_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2645_, 0, v___x_2644_);
lean_ctor_set(v___x_2645_, 1, v___x_2634_);
v___x_2646_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2645_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
if (lean_obj_tag(v___x_2646_) == 0)
{
lean_object* v_a_2647_; lean_object* v___x_2648_; 
v_a_2647_ = lean_ctor_get(v___x_2646_, 0);
lean_inc(v_a_2647_);
lean_dec_ref_known(v___x_2646_, 1);
v___x_2648_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___lam__1(v_snd_2602_, v___f_2624_, v_a_2647_, v___y_2575_, v___y_2576_, v___y_2577_, v___y_2578_);
lean_dec(v_snd_2602_);
v___y_2581_ = v___x_2648_;
goto v___jp_2580_;
}
else
{
lean_object* v_a_2649_; lean_object* v___x_2651_; uint8_t v_isShared_2652_; uint8_t v_isSharedCheck_2656_; 
lean_dec_ref(v___f_2624_);
lean_dec(v_snd_2602_);
lean_dec_ref(v_a_2572_);
lean_dec_ref(v_inst_2571_);
lean_dec_ref(v_argVars_2570_);
lean_dec_ref(v_fst_2569_);
v_a_2649_ = lean_ctor_get(v___x_2646_, 0);
v_isSharedCheck_2656_ = !lean_is_exclusive(v___x_2646_);
if (v_isSharedCheck_2656_ == 0)
{
v___x_2651_ = v___x_2646_;
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
else
{
lean_inc(v_a_2649_);
lean_dec(v___x_2646_);
v___x_2651_ = lean_box(0);
v_isShared_2652_ = v_isSharedCheck_2656_;
goto v_resetjp_2650_;
}
v_resetjp_2650_:
{
lean_object* v___x_2654_; 
if (v_isShared_2652_ == 0)
{
v___x_2654_ = v___x_2651_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_a_2649_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
}
else
{
lean_object* v_a_2658_; lean_object* v___x_2660_; uint8_t v_isShared_2661_; uint8_t v_isSharedCheck_2665_; 
lean_dec_ref(v___f_2624_);
lean_del_object(v___x_2622_);
lean_dec(v_snd_2602_);
lean_dec_ref(v_a_2572_);
lean_dec_ref(v_inst_2571_);
lean_dec_ref(v_argVars_2570_);
lean_dec_ref(v_fst_2569_);
v_a_2658_ = lean_ctor_get(v___x_2630_, 0);
v_isSharedCheck_2665_ = !lean_is_exclusive(v___x_2630_);
if (v_isSharedCheck_2665_ == 0)
{
v___x_2660_ = v___x_2630_;
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
else
{
lean_inc(v_a_2658_);
lean_dec(v___x_2630_);
v___x_2660_ = lean_box(0);
v_isShared_2661_ = v_isSharedCheck_2665_;
goto v_resetjp_2659_;
}
v_resetjp_2659_:
{
lean_object* v___x_2663_; 
if (v_isShared_2661_ == 0)
{
v___x_2663_ = v___x_2660_;
goto v_reusejp_2662_;
}
else
{
lean_object* v_reuseFailAlloc_2664_; 
v_reuseFailAlloc_2664_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2664_, 0, v_a_2658_);
v___x_2663_ = v_reuseFailAlloc_2664_;
goto v_reusejp_2662_;
}
v_reusejp_2662_:
{
return v___x_2663_;
}
}
}
}
}
}
}
else
{
lean_object* v_a_2671_; lean_object* v___x_2673_; uint8_t v_isShared_2674_; uint8_t v_isSharedCheck_2678_; 
lean_dec(v_snd_2602_);
lean_dec(v_fst_2601_);
lean_dec_ref(v_a_2572_);
lean_dec_ref(v_inst_2571_);
lean_dec_ref(v_argVars_2570_);
lean_dec_ref(v_fst_2569_);
v_a_2671_ = lean_ctor_get(v___x_2618_, 0);
v_isSharedCheck_2678_ = !lean_is_exclusive(v___x_2618_);
if (v_isSharedCheck_2678_ == 0)
{
v___x_2673_ = v___x_2618_;
v_isShared_2674_ = v_isSharedCheck_2678_;
goto v_resetjp_2672_;
}
else
{
lean_inc(v_a_2671_);
lean_dec(v___x_2618_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___boxed(lean_object* v_fst_2680_, lean_object* v_argVars_2681_, lean_object* v_inst_2682_, lean_object* v_a_2683_, lean_object* v_projInfo_x3f_2684_, lean_object* v_a_2685_, lean_object* v___y_2686_, lean_object* v___y_2687_, lean_object* v___y_2688_, lean_object* v___y_2689_, lean_object* v___y_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2680_, v_argVars_2681_, v_inst_2682_, v_a_2683_, v_projInfo_x3f_2684_, v_a_2685_, v___y_2686_, v___y_2687_, v___y_2688_, v___y_2689_);
lean_dec(v___y_2689_);
lean_dec_ref(v___y_2688_);
lean_dec(v___y_2687_);
lean_dec_ref(v___y_2686_);
lean_dec(v_projInfo_x3f_2684_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(lean_object* v_fst_2692_, lean_object* v_a_2693_, lean_object* v_a_2694_){
_start:
{
if (lean_obj_tag(v_a_2693_) == 0)
{
lean_object* v___x_2695_; 
v___x_2695_ = l_List_reverse___redArg(v_a_2694_);
return v___x_2695_;
}
else
{
lean_object* v_head_2696_; lean_object* v_tail_2697_; lean_object* v___x_2699_; uint8_t v_isShared_2700_; uint8_t v_isSharedCheck_2712_; 
v_head_2696_ = lean_ctor_get(v_a_2693_, 0);
v_tail_2697_ = lean_ctor_get(v_a_2693_, 1);
v_isSharedCheck_2712_ = !lean_is_exclusive(v_a_2693_);
if (v_isSharedCheck_2712_ == 0)
{
v___x_2699_ = v_a_2693_;
v_isShared_2700_ = v_isSharedCheck_2712_;
goto v_resetjp_2698_;
}
else
{
lean_inc(v_tail_2697_);
lean_inc(v_head_2696_);
lean_dec(v_a_2693_);
v___x_2699_ = lean_box(0);
v_isShared_2700_ = v_isSharedCheck_2712_;
goto v_resetjp_2698_;
}
v_resetjp_2698_:
{
uint8_t v___x_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; uint8_t v___x_2704_; uint8_t v___x_2705_; uint8_t v___x_2706_; 
v___x_2701_ = 0;
v___x_2702_ = lean_box(v___x_2701_);
v___x_2703_ = lean_array_get(v___x_2702_, v_fst_2692_, v_head_2696_);
lean_dec(v___x_2702_);
v___x_2704_ = 3;
v___x_2705_ = lean_unbox(v___x_2703_);
lean_dec(v___x_2703_);
v___x_2706_ = l_Lean_instBEqBinderInfo_beq(v___x_2705_, v___x_2704_);
if (v___x_2706_ == 0)
{
lean_del_object(v___x_2699_);
lean_dec(v_head_2696_);
v_a_2693_ = v_tail_2697_;
goto _start;
}
else
{
lean_object* v___x_2709_; 
if (v_isShared_2700_ == 0)
{
lean_ctor_set(v___x_2699_, 1, v_a_2694_);
v___x_2709_ = v___x_2699_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2711_; 
v_reuseFailAlloc_2711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2711_, 0, v_head_2696_);
lean_ctor_set(v_reuseFailAlloc_2711_, 1, v_a_2694_);
v___x_2709_ = v_reuseFailAlloc_2711_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
v_a_2693_ = v_tail_2697_;
v_a_2694_ = v___x_2709_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9___boxed(lean_object* v_fst_2713_, lean_object* v_a_2714_, lean_object* v_a_2715_){
_start:
{
lean_object* v_res_2716_; 
v_res_2716_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2713_, v_a_2714_, v_a_2715_);
lean_dec_ref(v_fst_2713_);
return v_res_2716_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(lean_object* v_argVars_2717_, size_t v_sz_2718_, size_t v_i_2719_, lean_object* v_bs_2720_, lean_object* v___y_2721_, lean_object* v___y_2722_, lean_object* v___y_2723_, lean_object* v___y_2724_){
_start:
{
uint8_t v___x_2726_; 
v___x_2726_ = lean_usize_dec_lt(v_i_2719_, v_sz_2718_);
if (v___x_2726_ == 0)
{
lean_object* v___x_2727_; 
v___x_2727_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_2727_, 0, v_bs_2720_);
return v___x_2727_;
}
else
{
lean_object* v_v_2728_; lean_object* v___x_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; 
v_v_2728_ = lean_array_uget_borrowed(v_bs_2720_, v_i_2719_);
v___x_2729_ = l_Lean_instInhabitedExpr;
v___x_2730_ = lean_array_get_borrowed(v___x_2729_, v_argVars_2717_, v_v_2728_);
lean_inc(v___y_2724_);
lean_inc_ref(v___y_2723_);
lean_inc(v___y_2722_);
lean_inc_ref(v___y_2721_);
lean_inc(v___x_2730_);
v___x_2731_ = lean_infer_type(v___x_2730_, v___y_2721_, v___y_2722_, v___y_2723_, v___y_2724_);
if (lean_obj_tag(v___x_2731_) == 0)
{
lean_object* v_a_2732_; lean_object* v___x_2733_; lean_object* v_bs_x27_2734_; lean_object* v___x_2735_; size_t v___x_2736_; size_t v___x_2737_; lean_object* v___x_2738_; 
v_a_2732_ = lean_ctor_get(v___x_2731_, 0);
lean_inc(v_a_2732_);
lean_dec_ref_known(v___x_2731_, 1);
v___x_2733_ = lean_unsigned_to_nat(0u);
v_bs_x27_2734_ = lean_array_uset(v_bs_2720_, v_i_2719_, v___x_2733_);
v___x_2735_ = l_Lean_indentExpr(v_a_2732_);
v___x_2736_ = ((size_t)1ULL);
v___x_2737_ = lean_usize_add(v_i_2719_, v___x_2736_);
v___x_2738_ = lean_array_uset(v_bs_x27_2734_, v_i_2719_, v___x_2735_);
v_i_2719_ = v___x_2737_;
v_bs_2720_ = v___x_2738_;
goto _start;
}
else
{
lean_object* v_a_2740_; lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2747_; 
lean_dec_ref(v_bs_2720_);
v_a_2740_ = lean_ctor_get(v___x_2731_, 0);
v_isSharedCheck_2747_ = !lean_is_exclusive(v___x_2731_);
if (v_isSharedCheck_2747_ == 0)
{
v___x_2742_ = v___x_2731_;
v_isShared_2743_ = v_isSharedCheck_2747_;
goto v_resetjp_2741_;
}
else
{
lean_inc(v_a_2740_);
lean_dec(v___x_2731_);
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
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11___boxed(lean_object* v_argVars_2748_, lean_object* v_sz_2749_, lean_object* v_i_2750_, lean_object* v_bs_2751_, lean_object* v___y_2752_, lean_object* v___y_2753_, lean_object* v___y_2754_, lean_object* v___y_2755_, lean_object* v___y_2756_){
_start:
{
size_t v_sz_boxed_2757_; size_t v_i_boxed_2758_; lean_object* v_res_2759_; 
v_sz_boxed_2757_ = lean_unbox_usize(v_sz_2749_);
lean_dec(v_sz_2749_);
v_i_boxed_2758_ = lean_unbox_usize(v_i_2750_);
lean_dec(v_i_2750_);
v_res_2759_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2748_, v_sz_boxed_2757_, v_i_boxed_2758_, v_bs_2751_, v___y_2752_, v___y_2753_, v___y_2754_, v___y_2755_);
lean_dec(v___y_2755_);
lean_dec_ref(v___y_2754_);
lean_dec(v___y_2753_);
lean_dec_ref(v___y_2752_);
lean_dec_ref(v_argVars_2748_);
return v_res_2759_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(lean_object* v_a_2760_, lean_object* v_a_2761_){
_start:
{
if (lean_obj_tag(v_a_2760_) == 0)
{
lean_object* v___x_2762_; 
v___x_2762_ = l_List_reverse___redArg(v_a_2761_);
return v___x_2762_;
}
else
{
lean_object* v_head_2763_; lean_object* v_tail_2764_; lean_object* v___x_2766_; uint8_t v_isShared_2767_; uint8_t v_isSharedCheck_2775_; 
v_head_2763_ = lean_ctor_get(v_a_2760_, 0);
v_tail_2764_ = lean_ctor_get(v_a_2760_, 1);
v_isSharedCheck_2775_ = !lean_is_exclusive(v_a_2760_);
if (v_isSharedCheck_2775_ == 0)
{
v___x_2766_ = v_a_2760_;
v_isShared_2767_ = v_isSharedCheck_2775_;
goto v_resetjp_2765_;
}
else
{
lean_inc(v_tail_2764_);
lean_inc(v_head_2763_);
lean_dec(v_a_2760_);
v___x_2766_ = lean_box(0);
v_isShared_2767_ = v_isSharedCheck_2775_;
goto v_resetjp_2765_;
}
v_resetjp_2765_:
{
lean_object* v___x_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; 
v___x_2768_ = l_Nat_reprFast(v_head_2763_);
v___x_2769_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_2769_, 0, v___x_2768_);
v___x_2770_ = l_Lean_MessageData_ofFormat(v___x_2769_);
if (v_isShared_2767_ == 0)
{
lean_ctor_set(v___x_2766_, 1, v_a_2761_);
lean_ctor_set(v___x_2766_, 0, v___x_2770_);
v___x_2772_ = v___x_2766_;
goto v_reusejp_2771_;
}
else
{
lean_object* v_reuseFailAlloc_2774_; 
v_reuseFailAlloc_2774_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2774_, 0, v___x_2770_);
lean_ctor_set(v_reuseFailAlloc_2774_, 1, v_a_2761_);
v___x_2772_ = v_reuseFailAlloc_2774_;
goto v_reusejp_2771_;
}
v_reusejp_2771_:
{
v_a_2760_ = v_tail_2764_;
v_a_2761_ = v___x_2772_;
goto _start;
}
}
}
}
}
static double _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0(void){
_start:
{
lean_object* v___x_2776_; double v___x_2777_; 
v___x_2776_ = lean_unsigned_to_nat(0u);
v___x_2777_ = lean_float_of_nat(v___x_2776_);
return v___x_2777_;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(lean_object* v_cls_2780_, lean_object* v_msg_2781_, lean_object* v___y_2782_, lean_object* v___y_2783_, lean_object* v___y_2784_, lean_object* v___y_2785_){
_start:
{
lean_object* v_ref_2787_; lean_object* v___x_2788_; lean_object* v_a_2789_; lean_object* v___x_2791_; uint8_t v_isShared_2792_; uint8_t v_isSharedCheck_2833_; 
v_ref_2787_ = lean_ctor_get(v___y_2784_, 5);
v___x_2788_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v_msg_2781_, v___y_2782_, v___y_2783_, v___y_2784_, v___y_2785_);
v_a_2789_ = lean_ctor_get(v___x_2788_, 0);
v_isSharedCheck_2833_ = !lean_is_exclusive(v___x_2788_);
if (v_isSharedCheck_2833_ == 0)
{
v___x_2791_ = v___x_2788_;
v_isShared_2792_ = v_isSharedCheck_2833_;
goto v_resetjp_2790_;
}
else
{
lean_inc(v_a_2789_);
lean_dec(v___x_2788_);
v___x_2791_ = lean_box(0);
v_isShared_2792_ = v_isSharedCheck_2833_;
goto v_resetjp_2790_;
}
v_resetjp_2790_:
{
lean_object* v___x_2793_; lean_object* v_traceState_2794_; lean_object* v_env_2795_; lean_object* v_nextMacroScope_2796_; lean_object* v_ngen_2797_; lean_object* v_auxDeclNGen_2798_; lean_object* v_cache_2799_; lean_object* v_messages_2800_; lean_object* v_infoState_2801_; lean_object* v_snapshotTasks_2802_; lean_object* v___x_2804_; uint8_t v_isShared_2805_; uint8_t v_isSharedCheck_2832_; 
v___x_2793_ = lean_st_ref_take(v___y_2785_);
v_traceState_2794_ = lean_ctor_get(v___x_2793_, 4);
v_env_2795_ = lean_ctor_get(v___x_2793_, 0);
v_nextMacroScope_2796_ = lean_ctor_get(v___x_2793_, 1);
v_ngen_2797_ = lean_ctor_get(v___x_2793_, 2);
v_auxDeclNGen_2798_ = lean_ctor_get(v___x_2793_, 3);
v_cache_2799_ = lean_ctor_get(v___x_2793_, 5);
v_messages_2800_ = lean_ctor_get(v___x_2793_, 6);
v_infoState_2801_ = lean_ctor_get(v___x_2793_, 7);
v_snapshotTasks_2802_ = lean_ctor_get(v___x_2793_, 8);
v_isSharedCheck_2832_ = !lean_is_exclusive(v___x_2793_);
if (v_isSharedCheck_2832_ == 0)
{
v___x_2804_ = v___x_2793_;
v_isShared_2805_ = v_isSharedCheck_2832_;
goto v_resetjp_2803_;
}
else
{
lean_inc(v_snapshotTasks_2802_);
lean_inc(v_infoState_2801_);
lean_inc(v_messages_2800_);
lean_inc(v_cache_2799_);
lean_inc(v_traceState_2794_);
lean_inc(v_auxDeclNGen_2798_);
lean_inc(v_ngen_2797_);
lean_inc(v_nextMacroScope_2796_);
lean_inc(v_env_2795_);
lean_dec(v___x_2793_);
v___x_2804_ = lean_box(0);
v_isShared_2805_ = v_isSharedCheck_2832_;
goto v_resetjp_2803_;
}
v_resetjp_2803_:
{
uint64_t v_tid_2806_; lean_object* v_traces_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2831_; 
v_tid_2806_ = lean_ctor_get_uint64(v_traceState_2794_, sizeof(void*)*1);
v_traces_2807_ = lean_ctor_get(v_traceState_2794_, 0);
v_isSharedCheck_2831_ = !lean_is_exclusive(v_traceState_2794_);
if (v_isSharedCheck_2831_ == 0)
{
v___x_2809_ = v_traceState_2794_;
v_isShared_2810_ = v_isSharedCheck_2831_;
goto v_resetjp_2808_;
}
else
{
lean_inc(v_traces_2807_);
lean_dec(v_traceState_2794_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2831_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; double v___x_2812_; uint8_t v___x_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; lean_object* v___x_2818_; lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2811_ = lean_box(0);
v___x_2812_ = lean_float_once(&l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0, &l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0_once, _init_l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__0);
v___x_2813_ = 0;
v___x_2814_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___x_2815_ = lean_alloc_ctor(0, 3, 17);
lean_ctor_set(v___x_2815_, 0, v_cls_2780_);
lean_ctor_set(v___x_2815_, 1, v___x_2811_);
lean_ctor_set(v___x_2815_, 2, v___x_2814_);
lean_ctor_set_float(v___x_2815_, sizeof(void*)*3, v___x_2812_);
lean_ctor_set_float(v___x_2815_, sizeof(void*)*3 + 8, v___x_2812_);
lean_ctor_set_uint8(v___x_2815_, sizeof(void*)*3 + 16, v___x_2813_);
v___x_2816_ = ((lean_object*)(l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___closed__1));
v___x_2817_ = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(v___x_2817_, 0, v___x_2815_);
lean_ctor_set(v___x_2817_, 1, v_a_2789_);
lean_ctor_set(v___x_2817_, 2, v___x_2816_);
lean_inc(v_ref_2787_);
v___x_2818_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2818_, 0, v_ref_2787_);
lean_ctor_set(v___x_2818_, 1, v___x_2817_);
v___x_2819_ = l_Lean_PersistentArray_push___redArg(v_traces_2807_, v___x_2818_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 0, v___x_2819_);
v___x_2821_ = v___x_2809_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2830_; 
v_reuseFailAlloc_2830_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v_reuseFailAlloc_2830_, 0, v___x_2819_);
lean_ctor_set_uint64(v_reuseFailAlloc_2830_, sizeof(void*)*1, v_tid_2806_);
v___x_2821_ = v_reuseFailAlloc_2830_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
lean_object* v___x_2823_; 
if (v_isShared_2805_ == 0)
{
lean_ctor_set(v___x_2804_, 4, v___x_2821_);
v___x_2823_ = v___x_2804_;
goto v_reusejp_2822_;
}
else
{
lean_object* v_reuseFailAlloc_2829_; 
v_reuseFailAlloc_2829_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_2829_, 0, v_env_2795_);
lean_ctor_set(v_reuseFailAlloc_2829_, 1, v_nextMacroScope_2796_);
lean_ctor_set(v_reuseFailAlloc_2829_, 2, v_ngen_2797_);
lean_ctor_set(v_reuseFailAlloc_2829_, 3, v_auxDeclNGen_2798_);
lean_ctor_set(v_reuseFailAlloc_2829_, 4, v___x_2821_);
lean_ctor_set(v_reuseFailAlloc_2829_, 5, v_cache_2799_);
lean_ctor_set(v_reuseFailAlloc_2829_, 6, v_messages_2800_);
lean_ctor_set(v_reuseFailAlloc_2829_, 7, v_infoState_2801_);
lean_ctor_set(v_reuseFailAlloc_2829_, 8, v_snapshotTasks_2802_);
v___x_2823_ = v_reuseFailAlloc_2829_;
goto v_reusejp_2822_;
}
v_reusejp_2822_:
{
lean_object* v___x_2824_; lean_object* v___x_2825_; lean_object* v___x_2827_; 
v___x_2824_ = lean_st_ref_set(v___y_2785_, v___x_2823_);
v___x_2825_ = lean_box(0);
if (v_isShared_2792_ == 0)
{
lean_ctor_set(v___x_2791_, 0, v___x_2825_);
v___x_2827_ = v___x_2791_;
goto v_reusejp_2826_;
}
else
{
lean_object* v_reuseFailAlloc_2828_; 
v_reuseFailAlloc_2828_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2828_, 0, v___x_2825_);
v___x_2827_ = v_reuseFailAlloc_2828_;
goto v_reusejp_2826_;
}
v_reusejp_2826_:
{
return v___x_2827_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13___boxed(lean_object* v_cls_2834_, lean_object* v_msg_2835_, lean_object* v___y_2836_, lean_object* v___y_2837_, lean_object* v___y_2838_, lean_object* v___y_2839_, lean_object* v___y_2840_){
_start:
{
lean_object* v_res_2841_; 
v_res_2841_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v_cls_2834_, v_msg_2835_, v___y_2836_, v___y_2837_, v___y_2838_, v___y_2839_);
lean_dec(v___y_2839_);
lean_dec_ref(v___y_2838_);
lean_dec(v___y_2837_);
lean_dec_ref(v___y_2836_);
return v_res_2841_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4(void){
_start:
{
lean_object* v___x_2849_; lean_object* v___x_2850_; lean_object* v___x_2851_; 
v___x_2849_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2850_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__3));
v___x_2851_ = l_Lean_Name_append(v___x_2850_, v___x_2849_);
return v___x_2851_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6(void){
_start:
{
lean_object* v___x_2853_; lean_object* v___x_2854_; 
v___x_2853_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__5));
v___x_2854_ = l_Lean_stringToMessageData(v___x_2853_);
return v___x_2854_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8(void){
_start:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; 
v___x_2856_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__7));
v___x_2857_ = l_Lean_stringToMessageData(v___x_2856_);
return v___x_2857_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10(void){
_start:
{
lean_object* v___x_2859_; lean_object* v___x_2860_; 
v___x_2859_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__9));
v___x_2860_ = l_Lean_stringToMessageData(v___x_2859_);
return v___x_2860_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12(void){
_start:
{
lean_object* v___x_2862_; lean_object* v___x_2863_; 
v___x_2862_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__11));
v___x_2863_ = l_Lean_stringToMessageData(v___x_2862_);
return v___x_2863_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(lean_object* v_a_2864_, lean_object* v_fst_2865_, lean_object* v_fst_2866_, lean_object* v_inst_2867_, lean_object* v_a_2868_, lean_object* v_projInfo_x3f_2869_, lean_object* v_argVars_2870_, lean_object* v_x_2871_, lean_object* v___y_2872_, lean_object* v___y_2873_, lean_object* v___y_2874_, lean_object* v___y_2875_){
_start:
{
lean_object* v___x_2877_; 
v___x_2877_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf(v_a_2864_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
if (lean_obj_tag(v___x_2877_) == 0)
{
lean_object* v_a_2878_; lean_object* v_dummy_2879_; lean_object* v_nargs_2880_; lean_object* v___x_2881_; lean_object* v___x_2882_; lean_object* v___x_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2887_; size_t v_sz_2888_; size_t v___x_2889_; lean_object* v___x_2890_; 
v_a_2878_ = lean_ctor_get(v___x_2877_, 0);
lean_inc(v_a_2878_);
lean_dec_ref_known(v___x_2877_, 1);
v_dummy_2879_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__7___lam__0___closed__0);
v_nargs_2880_ = l_Lean_Expr_getAppNumArgs(v_a_2864_);
lean_inc(v_nargs_2880_);
v___x_2881_ = lean_mk_array(v_nargs_2880_, v_dummy_2879_);
v___x_2882_ = lean_unsigned_to_nat(1u);
v___x_2883_ = lean_nat_sub(v_nargs_2880_, v___x_2882_);
lean_dec(v_nargs_2880_);
lean_inc_ref(v_a_2864_);
v___x_2884_ = l___private_Lean_Expr_0__Lean_Expr_getAppArgsAux(v_a_2864_, v___x_2881_, v___x_2883_);
v___x_2885_ = lean_array_get_size(v___x_2884_);
v___x_2886_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__0));
v___x_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2887_, 0, v___x_2886_);
lean_ctor_set(v___x_2887_, 1, v___x_2885_);
v_sz_2888_ = lean_array_size(v___x_2884_);
v___x_2889_ = ((size_t)0ULL);
v___x_2890_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__8(v_a_2878_, v_fst_2865_, v_argVars_2870_, v___x_2884_, v_sz_2888_, v___x_2889_, v___x_2887_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
lean_dec_ref(v___x_2884_);
lean_dec(v_a_2878_);
if (lean_obj_tag(v___x_2890_) == 0)
{
lean_object* v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; lean_object* v___x_2897_; lean_object* v___x_2898_; 
lean_dec_ref_known(v___x_2890_, 1);
v___x_2891_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf___lam__0___closed__1));
v___x_2892_ = lean_array_get_size(v_fst_2865_);
v___x_2893_ = l_List_range(v___x_2892_);
v___x_2894_ = lean_box(0);
v___x_2895_ = l_List_filterTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__9(v_fst_2866_, v___x_2893_, v___x_2894_);
v___x_2896_ = lean_array_mk(v___x_2895_);
v___x_2897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2897_, 0, v___x_2891_);
lean_ctor_set(v___x_2897_, 1, v___x_2896_);
lean_inc_ref(v_inst_2867_);
lean_inc_ref(v_argVars_2870_);
v___x_2898_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_2865_, v_argVars_2870_, v_inst_2867_, v_a_2868_, v_projInfo_x3f_2869_, v___x_2897_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
if (lean_obj_tag(v___x_2898_) == 0)
{
lean_object* v_a_2899_; lean_object* v___x_2901_; uint8_t v_isShared_2902_; uint8_t v_isSharedCheck_2991_; 
v_a_2899_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2991_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2991_ == 0)
{
v___x_2901_ = v___x_2898_;
v_isShared_2902_ = v_isSharedCheck_2991_;
goto v_resetjp_2900_;
}
else
{
lean_inc(v_a_2899_);
lean_dec(v___x_2898_);
v___x_2901_ = lean_box(0);
v_isShared_2902_ = v_isSharedCheck_2991_;
goto v_resetjp_2900_;
}
v_resetjp_2900_:
{
lean_object* v_fst_2903_; lean_object* v___x_2905_; uint8_t v_isShared_2906_; uint8_t v_isSharedCheck_2989_; 
v_fst_2903_ = lean_ctor_get(v_a_2899_, 0);
v_isSharedCheck_2989_ = !lean_is_exclusive(v_a_2899_);
if (v_isSharedCheck_2989_ == 0)
{
lean_object* v_unused_2990_; 
v_unused_2990_ = lean_ctor_get(v_a_2899_, 1);
lean_dec(v_unused_2990_);
v___x_2905_ = v_a_2899_;
v_isShared_2906_ = v_isSharedCheck_2989_;
goto v_resetjp_2904_;
}
else
{
lean_inc(v_fst_2903_);
lean_dec(v_a_2899_);
v___x_2905_ = lean_box(0);
v_isShared_2906_ = v_isSharedCheck_2989_;
goto v_resetjp_2904_;
}
v_resetjp_2904_:
{
lean_object* v___y_2908_; lean_object* v___y_2909_; lean_object* v___y_2910_; lean_object* v_options_2911_; lean_object* v_inheritedTraceOptions_2912_; lean_object* v___y_2913_; lean_object* v_options_2969_; lean_object* v_inheritedTraceOptions_2970_; lean_object* v___x_2971_; uint8_t v___x_2972_; 
v_options_2969_ = lean_ctor_get(v___y_2874_, 2);
v_inheritedTraceOptions_2970_ = lean_ctor_get(v___y_2874_, 13);
v___x_2971_ = l_Lean_Meta_synthInstance_checkSynthOrder;
v___x_2972_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_2969_, v___x_2971_);
if (v___x_2972_ == 0)
{
lean_dec_ref(v_a_2864_);
v___y_2908_ = v___y_2872_;
v___y_2909_ = v___y_2873_;
v___y_2910_ = v___y_2874_;
v_options_2911_ = v_options_2969_;
v_inheritedTraceOptions_2912_ = v_inheritedTraceOptions_2970_;
v___y_2913_ = v___y_2875_;
goto v___jp_2907_;
}
else
{
lean_object* v___x_2973_; lean_object* v_a_2974_; uint8_t v___x_2975_; 
v___x_2973_ = l_Lean_instantiateMVars___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__3___redArg(v_a_2864_, v___y_2873_);
v_a_2974_ = lean_ctor_get(v___x_2973_, 0);
lean_inc(v_a_2974_);
lean_dec_ref(v___x_2973_);
v___x_2975_ = l_Lean_Expr_hasExprMVar(v_a_2974_);
if (v___x_2975_ == 0)
{
lean_dec(v_a_2974_);
v___y_2908_ = v___y_2872_;
v___y_2909_ = v___y_2873_;
v___y_2910_ = v___y_2874_;
v_options_2911_ = v_options_2969_;
v_inheritedTraceOptions_2912_ = v_inheritedTraceOptions_2970_;
v___y_2913_ = v___y_2875_;
goto v___jp_2907_;
}
else
{
lean_object* v___x_2976_; lean_object* v___x_2977_; lean_object* v___x_2978_; lean_object* v___x_2979_; lean_object* v___x_2980_; lean_object* v_a_2981_; lean_object* v___x_2983_; uint8_t v_isShared_2984_; uint8_t v_isSharedCheck_2988_; 
lean_del_object(v___x_2905_);
lean_dec(v_fst_2903_);
lean_del_object(v___x_2901_);
lean_dec_ref(v_argVars_2870_);
lean_dec_ref(v_inst_2867_);
v___x_2976_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__12);
v___x_2977_ = l_Lean_Expr_setPPExplicit(v_a_2974_, v___x_2975_);
v___x_2978_ = l_Lean_indentExpr(v___x_2977_);
v___x_2979_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2979_, 0, v___x_2976_);
lean_ctor_set(v___x_2979_, 1, v___x_2978_);
v___x_2980_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_2979_, v___y_2872_, v___y_2873_, v___y_2874_, v___y_2875_);
v_a_2981_ = lean_ctor_get(v___x_2980_, 0);
v_isSharedCheck_2988_ = !lean_is_exclusive(v___x_2980_);
if (v_isSharedCheck_2988_ == 0)
{
v___x_2983_ = v___x_2980_;
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
else
{
lean_inc(v_a_2981_);
lean_dec(v___x_2980_);
v___x_2983_ = lean_box(0);
v_isShared_2984_ = v_isSharedCheck_2988_;
goto v_resetjp_2982_;
}
v_resetjp_2982_:
{
lean_object* v___x_2986_; 
if (v_isShared_2984_ == 0)
{
v___x_2986_ = v___x_2983_;
goto v_reusejp_2985_;
}
else
{
lean_object* v_reuseFailAlloc_2987_; 
v_reuseFailAlloc_2987_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2987_, 0, v_a_2981_);
v___x_2986_ = v_reuseFailAlloc_2987_;
goto v_reusejp_2985_;
}
v_reusejp_2985_:
{
return v___x_2986_;
}
}
}
}
v___jp_2907_:
{
uint8_t v_hasTrace_2914_; 
v_hasTrace_2914_ = lean_ctor_get_uint8(v_options_2911_, sizeof(void*)*1);
if (v_hasTrace_2914_ == 0)
{
lean_object* v___x_2916_; 
lean_del_object(v___x_2905_);
lean_dec_ref(v_argVars_2870_);
lean_dec_ref(v_inst_2867_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v_fst_2903_);
v___x_2916_ = v___x_2901_;
goto v_reusejp_2915_;
}
else
{
lean_object* v_reuseFailAlloc_2917_; 
v_reuseFailAlloc_2917_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2917_, 0, v_fst_2903_);
v___x_2916_ = v_reuseFailAlloc_2917_;
goto v_reusejp_2915_;
}
v_reusejp_2915_:
{
return v___x_2916_;
}
}
else
{
lean_object* v___x_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; 
v___x_2918_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_2919_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__4);
v___x_2920_ = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(v_inheritedTraceOptions_2912_, v_options_2911_, v___x_2919_);
if (v___x_2920_ == 0)
{
lean_object* v___x_2922_; 
lean_del_object(v___x_2905_);
lean_dec_ref(v_argVars_2870_);
lean_dec_ref(v_inst_2867_);
if (v_isShared_2902_ == 0)
{
lean_ctor_set(v___x_2901_, 0, v_fst_2903_);
v___x_2922_ = v___x_2901_;
goto v_reusejp_2921_;
}
else
{
lean_object* v_reuseFailAlloc_2923_; 
v_reuseFailAlloc_2923_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2923_, 0, v_fst_2903_);
v___x_2922_ = v_reuseFailAlloc_2923_;
goto v_reusejp_2921_;
}
v_reusejp_2921_:
{
return v___x_2922_;
}
}
else
{
size_t v_sz_2924_; lean_object* v___x_2925_; 
lean_del_object(v___x_2901_);
v_sz_2924_ = lean_array_size(v_fst_2903_);
lean_inc(v_fst_2903_);
v___x_2925_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__11(v_argVars_2870_, v_sz_2924_, v___x_2889_, v_fst_2903_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2913_);
lean_dec_ref(v_argVars_2870_);
if (lean_obj_tag(v___x_2925_) == 0)
{
lean_object* v_a_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2930_; 
v_a_2926_ = lean_ctor_get(v___x_2925_, 0);
lean_inc(v_a_2926_);
lean_dec_ref_known(v___x_2925_, 1);
v___x_2927_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__6);
v___x_2928_ = l_Lean_MessageData_ofExpr(v_inst_2867_);
if (v_isShared_2906_ == 0)
{
lean_ctor_set_tag(v___x_2905_, 7);
lean_ctor_set(v___x_2905_, 1, v___x_2928_);
lean_ctor_set(v___x_2905_, 0, v___x_2927_);
v___x_2930_ = v___x_2905_;
goto v_reusejp_2929_;
}
else
{
lean_object* v_reuseFailAlloc_2960_; 
v_reuseFailAlloc_2960_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2960_, 0, v___x_2927_);
lean_ctor_set(v_reuseFailAlloc_2960_, 1, v___x_2928_);
v___x_2930_ = v_reuseFailAlloc_2960_;
goto v_reusejp_2929_;
}
v_reusejp_2929_:
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2931_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__8);
v___x_2932_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2932_, 0, v___x_2930_);
lean_ctor_set(v___x_2932_, 1, v___x_2931_);
lean_inc(v_fst_2903_);
v___x_2933_ = lean_array_to_list(v_fst_2903_);
v___x_2934_ = l_List_mapTR_loop___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__12(v___x_2933_, v___x_2894_);
v___x_2935_ = l_Lean_MessageData_ofList(v___x_2934_);
v___x_2936_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2936_, 0, v___x_2932_);
lean_ctor_set(v___x_2936_, 1, v___x_2935_);
v___x_2937_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__10);
v___x_2938_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = lean_array_to_list(v_a_2926_);
v___x_2940_ = lean_obj_once(&l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2, &l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2_once, _init_l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__2);
v___x_2941_ = l_Lean_MessageData_joinSep(v___x_2939_, v___x_2940_);
v___x_2942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2938_);
lean_ctor_set(v___x_2942_, 1, v___x_2941_);
v___x_2943_ = l_Lean_addTrace___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__13(v___x_2918_, v___x_2942_, v___y_2908_, v___y_2909_, v___y_2910_, v___y_2913_);
if (lean_obj_tag(v___x_2943_) == 0)
{
lean_object* v___x_2945_; uint8_t v_isShared_2946_; uint8_t v_isSharedCheck_2950_; 
v_isSharedCheck_2950_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2950_ == 0)
{
lean_object* v_unused_2951_; 
v_unused_2951_ = lean_ctor_get(v___x_2943_, 0);
lean_dec(v_unused_2951_);
v___x_2945_ = v___x_2943_;
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
else
{
lean_dec(v___x_2943_);
v___x_2945_ = lean_box(0);
v_isShared_2946_ = v_isSharedCheck_2950_;
goto v_resetjp_2944_;
}
v_resetjp_2944_:
{
lean_object* v___x_2948_; 
if (v_isShared_2946_ == 0)
{
lean_ctor_set(v___x_2945_, 0, v_fst_2903_);
v___x_2948_ = v___x_2945_;
goto v_reusejp_2947_;
}
else
{
lean_object* v_reuseFailAlloc_2949_; 
v_reuseFailAlloc_2949_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2949_, 0, v_fst_2903_);
v___x_2948_ = v_reuseFailAlloc_2949_;
goto v_reusejp_2947_;
}
v_reusejp_2947_:
{
return v___x_2948_;
}
}
}
else
{
lean_object* v_a_2952_; lean_object* v___x_2954_; uint8_t v_isShared_2955_; uint8_t v_isSharedCheck_2959_; 
lean_dec(v_fst_2903_);
v_a_2952_ = lean_ctor_get(v___x_2943_, 0);
v_isSharedCheck_2959_ = !lean_is_exclusive(v___x_2943_);
if (v_isSharedCheck_2959_ == 0)
{
v___x_2954_ = v___x_2943_;
v_isShared_2955_ = v_isSharedCheck_2959_;
goto v_resetjp_2953_;
}
else
{
lean_inc(v_a_2952_);
lean_dec(v___x_2943_);
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
}
else
{
lean_object* v_a_2961_; lean_object* v___x_2963_; uint8_t v_isShared_2964_; uint8_t v_isSharedCheck_2968_; 
lean_del_object(v___x_2905_);
lean_dec(v_fst_2903_);
lean_dec_ref(v_inst_2867_);
v_a_2961_ = lean_ctor_get(v___x_2925_, 0);
v_isSharedCheck_2968_ = !lean_is_exclusive(v___x_2925_);
if (v_isSharedCheck_2968_ == 0)
{
v___x_2963_ = v___x_2925_;
v_isShared_2964_ = v_isSharedCheck_2968_;
goto v_resetjp_2962_;
}
else
{
lean_inc(v_a_2961_);
lean_dec(v___x_2925_);
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
}
}
}
}
}
else
{
lean_object* v_a_2992_; lean_object* v___x_2994_; uint8_t v_isShared_2995_; uint8_t v_isSharedCheck_2999_; 
lean_dec_ref(v_argVars_2870_);
lean_dec_ref(v_inst_2867_);
lean_dec_ref(v_a_2864_);
v_a_2992_ = lean_ctor_get(v___x_2898_, 0);
v_isSharedCheck_2999_ = !lean_is_exclusive(v___x_2898_);
if (v_isSharedCheck_2999_ == 0)
{
v___x_2994_ = v___x_2898_;
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
else
{
lean_inc(v_a_2992_);
lean_dec(v___x_2898_);
v___x_2994_ = lean_box(0);
v_isShared_2995_ = v_isSharedCheck_2999_;
goto v_resetjp_2993_;
}
v_resetjp_2993_:
{
lean_object* v___x_2997_; 
if (v_isShared_2995_ == 0)
{
v___x_2997_ = v___x_2994_;
goto v_reusejp_2996_;
}
else
{
lean_object* v_reuseFailAlloc_2998_; 
v_reuseFailAlloc_2998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2998_, 0, v_a_2992_);
v___x_2997_ = v_reuseFailAlloc_2998_;
goto v_reusejp_2996_;
}
v_reusejp_2996_:
{
return v___x_2997_;
}
}
}
}
else
{
lean_object* v_a_3000_; lean_object* v___x_3002_; uint8_t v_isShared_3003_; uint8_t v_isSharedCheck_3007_; 
lean_dec_ref(v_argVars_2870_);
lean_dec_ref(v_a_2868_);
lean_dec_ref(v_inst_2867_);
lean_dec_ref(v_fst_2865_);
lean_dec_ref(v_a_2864_);
v_a_3000_ = lean_ctor_get(v___x_2890_, 0);
v_isSharedCheck_3007_ = !lean_is_exclusive(v___x_2890_);
if (v_isSharedCheck_3007_ == 0)
{
v___x_3002_ = v___x_2890_;
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
else
{
lean_inc(v_a_3000_);
lean_dec(v___x_2890_);
v___x_3002_ = lean_box(0);
v_isShared_3003_ = v_isSharedCheck_3007_;
goto v_resetjp_3001_;
}
v_resetjp_3001_:
{
lean_object* v___x_3005_; 
if (v_isShared_3003_ == 0)
{
v___x_3005_ = v___x_3002_;
goto v_reusejp_3004_;
}
else
{
lean_object* v_reuseFailAlloc_3006_; 
v_reuseFailAlloc_3006_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3006_, 0, v_a_3000_);
v___x_3005_ = v_reuseFailAlloc_3006_;
goto v_reusejp_3004_;
}
v_reusejp_3004_:
{
return v___x_3005_;
}
}
}
}
else
{
lean_dec_ref(v_argVars_2870_);
lean_dec_ref(v_a_2868_);
lean_dec_ref(v_inst_2867_);
lean_dec_ref(v_fst_2865_);
lean_dec_ref(v_a_2864_);
return v___x_2877_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed(lean_object* v_a_3008_, lean_object* v_fst_3009_, lean_object* v_fst_3010_, lean_object* v_inst_3011_, lean_object* v_a_3012_, lean_object* v_projInfo_x3f_3013_, lean_object* v_argVars_3014_, lean_object* v_x_3015_, lean_object* v___y_3016_, lean_object* v___y_3017_, lean_object* v___y_3018_, lean_object* v___y_3019_, lean_object* v___y_3020_){
_start:
{
lean_object* v_res_3021_; 
v_res_3021_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0(v_a_3008_, v_fst_3009_, v_fst_3010_, v_inst_3011_, v_a_3012_, v_projInfo_x3f_3013_, v_argVars_3014_, v_x_3015_, v___y_3016_, v___y_3017_, v___y_3018_, v___y_3019_);
lean_dec(v___y_3019_);
lean_dec_ref(v___y_3018_);
lean_dec(v___y_3017_);
lean_dec_ref(v___y_3016_);
lean_dec_ref(v_x_3015_);
lean_dec(v_projInfo_x3f_3013_);
lean_dec_ref(v_fst_3010_);
return v_res_3021_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0(void){
_start:
{
uint8_t v___x_3022_; uint64_t v___x_3023_; 
v___x_3022_ = 2;
v___x_3023_ = l_Lean_Meta_TransparencyMode_toUInt64(v___x_3022_);
return v___x_3023_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(lean_object* v_inst_3024_, lean_object* v_projInfo_x3f_3025_, lean_object* v_a_3026_, lean_object* v_a_3027_, lean_object* v_a_3028_, lean_object* v_a_3029_){
_start:
{
lean_object* v___x_3031_; uint8_t v_foApprox_3032_; uint8_t v_ctxApprox_3033_; uint8_t v_quasiPatternApprox_3034_; uint8_t v_constApprox_3035_; uint8_t v_isDefEqStuckEx_3036_; uint8_t v_unificationHints_3037_; uint8_t v_proofIrrelevance_3038_; uint8_t v_assignSyntheticOpaque_3039_; uint8_t v_offsetCnstrs_3040_; uint8_t v_etaStruct_3041_; uint8_t v_univApprox_3042_; uint8_t v_iota_3043_; uint8_t v_beta_3044_; uint8_t v_proj_3045_; uint8_t v_zeta_3046_; uint8_t v_zetaDelta_3047_; uint8_t v_zetaUnused_3048_; uint8_t v_zetaHave_3049_; lean_object* v___x_3051_; uint8_t v_isShared_3052_; uint8_t v_isSharedCheck_3114_; 
v___x_3031_ = l_Lean_Meta_Context_config(v_a_3026_);
v_foApprox_3032_ = lean_ctor_get_uint8(v___x_3031_, 0);
v_ctxApprox_3033_ = lean_ctor_get_uint8(v___x_3031_, 1);
v_quasiPatternApprox_3034_ = lean_ctor_get_uint8(v___x_3031_, 2);
v_constApprox_3035_ = lean_ctor_get_uint8(v___x_3031_, 3);
v_isDefEqStuckEx_3036_ = lean_ctor_get_uint8(v___x_3031_, 4);
v_unificationHints_3037_ = lean_ctor_get_uint8(v___x_3031_, 5);
v_proofIrrelevance_3038_ = lean_ctor_get_uint8(v___x_3031_, 6);
v_assignSyntheticOpaque_3039_ = lean_ctor_get_uint8(v___x_3031_, 7);
v_offsetCnstrs_3040_ = lean_ctor_get_uint8(v___x_3031_, 8);
v_etaStruct_3041_ = lean_ctor_get_uint8(v___x_3031_, 10);
v_univApprox_3042_ = lean_ctor_get_uint8(v___x_3031_, 11);
v_iota_3043_ = lean_ctor_get_uint8(v___x_3031_, 12);
v_beta_3044_ = lean_ctor_get_uint8(v___x_3031_, 13);
v_proj_3045_ = lean_ctor_get_uint8(v___x_3031_, 14);
v_zeta_3046_ = lean_ctor_get_uint8(v___x_3031_, 15);
v_zetaDelta_3047_ = lean_ctor_get_uint8(v___x_3031_, 16);
v_zetaUnused_3048_ = lean_ctor_get_uint8(v___x_3031_, 17);
v_zetaHave_3049_ = lean_ctor_get_uint8(v___x_3031_, 18);
v_isSharedCheck_3114_ = !lean_is_exclusive(v___x_3031_);
if (v_isSharedCheck_3114_ == 0)
{
v___x_3051_ = v___x_3031_;
v_isShared_3052_ = v_isSharedCheck_3114_;
goto v_resetjp_3050_;
}
else
{
lean_dec(v___x_3031_);
v___x_3051_ = lean_box(0);
v_isShared_3052_ = v_isSharedCheck_3114_;
goto v_resetjp_3050_;
}
v_resetjp_3050_:
{
uint8_t v_trackZetaDelta_3053_; lean_object* v_zetaDeltaSet_3054_; lean_object* v_lctx_3055_; lean_object* v_localInstances_3056_; lean_object* v_defEqCtx_x3f_3057_; lean_object* v_synthPendingDepth_3058_; lean_object* v_canUnfold_x3f_3059_; uint8_t v_univApprox_3060_; uint8_t v_inTypeClassResolution_3061_; uint8_t v_cacheInferType_3062_; uint8_t v___x_3063_; lean_object* v_config_3065_; 
v_trackZetaDelta_3053_ = lean_ctor_get_uint8(v_a_3026_, sizeof(void*)*7);
v_zetaDeltaSet_3054_ = lean_ctor_get(v_a_3026_, 1);
v_lctx_3055_ = lean_ctor_get(v_a_3026_, 2);
v_localInstances_3056_ = lean_ctor_get(v_a_3026_, 3);
v_defEqCtx_x3f_3057_ = lean_ctor_get(v_a_3026_, 4);
v_synthPendingDepth_3058_ = lean_ctor_get(v_a_3026_, 5);
v_canUnfold_x3f_3059_ = lean_ctor_get(v_a_3026_, 6);
v_univApprox_3060_ = lean_ctor_get_uint8(v_a_3026_, sizeof(void*)*7 + 1);
v_inTypeClassResolution_3061_ = lean_ctor_get_uint8(v_a_3026_, sizeof(void*)*7 + 2);
v_cacheInferType_3062_ = lean_ctor_get_uint8(v_a_3026_, sizeof(void*)*7 + 3);
v___x_3063_ = 2;
if (v_isShared_3052_ == 0)
{
v_config_3065_ = v___x_3051_;
goto v_reusejp_3064_;
}
else
{
lean_object* v_reuseFailAlloc_3113_; 
v_reuseFailAlloc_3113_ = lean_alloc_ctor(0, 0, 19);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 0, v_foApprox_3032_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 1, v_ctxApprox_3033_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 2, v_quasiPatternApprox_3034_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 3, v_constApprox_3035_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 4, v_isDefEqStuckEx_3036_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 5, v_unificationHints_3037_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 6, v_proofIrrelevance_3038_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 7, v_assignSyntheticOpaque_3039_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 8, v_offsetCnstrs_3040_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 10, v_etaStruct_3041_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 11, v_univApprox_3042_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 12, v_iota_3043_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 13, v_beta_3044_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 14, v_proj_3045_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 15, v_zeta_3046_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 16, v_zetaDelta_3047_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 17, v_zetaUnused_3048_);
lean_ctor_set_uint8(v_reuseFailAlloc_3113_, 18, v_zetaHave_3049_);
v_config_3065_ = v_reuseFailAlloc_3113_;
goto v_reusejp_3064_;
}
v_reusejp_3064_:
{
uint64_t v___x_3066_; uint64_t v___x_3067_; uint64_t v___x_3068_; uint64_t v___x_3069_; uint64_t v___x_3070_; uint64_t v_key_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v___x_3074_; 
lean_ctor_set_uint8(v_config_3065_, 9, v___x_3063_);
v___x_3066_ = l_Lean_Meta_Context_configKey(v_a_3026_);
v___x_3067_ = 3ULL;
v___x_3068_ = lean_uint64_shift_right(v___x_3066_, v___x_3067_);
v___x_3069_ = lean_uint64_shift_left(v___x_3068_, v___x_3067_);
v___x_3070_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0, &l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0_once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___closed__0);
v_key_3071_ = lean_uint64_lor(v___x_3069_, v___x_3070_);
v___x_3072_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_3072_, 0, v_config_3065_);
lean_ctor_set_uint64(v___x_3072_, sizeof(void*)*1, v_key_3071_);
lean_inc(v_canUnfold_x3f_3059_);
lean_inc(v_synthPendingDepth_3058_);
lean_inc(v_defEqCtx_x3f_3057_);
lean_inc_ref(v_localInstances_3056_);
lean_inc_ref(v_lctx_3055_);
lean_inc(v_zetaDeltaSet_3054_);
v___x_3073_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_3073_, 0, v___x_3072_);
lean_ctor_set(v___x_3073_, 1, v_zetaDeltaSet_3054_);
lean_ctor_set(v___x_3073_, 2, v_lctx_3055_);
lean_ctor_set(v___x_3073_, 3, v_localInstances_3056_);
lean_ctor_set(v___x_3073_, 4, v_defEqCtx_x3f_3057_);
lean_ctor_set(v___x_3073_, 5, v_synthPendingDepth_3058_);
lean_ctor_set(v___x_3073_, 6, v_canUnfold_x3f_3059_);
lean_ctor_set_uint8(v___x_3073_, sizeof(void*)*7, v_trackZetaDelta_3053_);
lean_ctor_set_uint8(v___x_3073_, sizeof(void*)*7 + 1, v_univApprox_3060_);
lean_ctor_set_uint8(v___x_3073_, sizeof(void*)*7 + 2, v_inTypeClassResolution_3061_);
lean_ctor_set_uint8(v___x_3073_, sizeof(void*)*7 + 3, v_cacheInferType_3062_);
lean_inc(v_a_3029_);
lean_inc_ref(v_a_3028_);
lean_inc(v_a_3027_);
lean_inc_ref(v___x_3073_);
lean_inc_ref(v_inst_3024_);
v___x_3074_ = lean_infer_type(v_inst_3024_, v___x_3073_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3074_) == 0)
{
lean_object* v_a_3075_; lean_object* v___x_3076_; uint8_t v___x_3077_; lean_object* v___x_3078_; 
v_a_3075_ = lean_ctor_get(v___x_3074_, 0);
lean_inc_n(v_a_3075_, 2);
lean_dec_ref_known(v___x_3074_, 1);
v___x_3076_ = lean_box(0);
v___x_3077_ = 0;
v___x_3078_ = l_Lean_Meta_forallMetaTelescopeReducing(v_a_3075_, v___x_3076_, v___x_3077_, v___x_3073_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3078_) == 0)
{
lean_object* v_a_3079_; lean_object* v_snd_3080_; lean_object* v_fst_3081_; lean_object* v_fst_3082_; lean_object* v_snd_3083_; lean_object* v___x_3084_; 
v_a_3079_ = lean_ctor_get(v___x_3078_, 0);
lean_inc(v_a_3079_);
lean_dec_ref_known(v___x_3078_, 1);
v_snd_3080_ = lean_ctor_get(v_a_3079_, 1);
lean_inc(v_snd_3080_);
v_fst_3081_ = lean_ctor_get(v_a_3079_, 0);
lean_inc(v_fst_3081_);
lean_dec(v_a_3079_);
v_fst_3082_ = lean_ctor_get(v_snd_3080_, 0);
lean_inc(v_fst_3082_);
v_snd_3083_ = lean_ctor_get(v_snd_3080_, 1);
lean_inc(v_snd_3083_);
lean_dec(v_snd_3080_);
lean_inc(v_a_3029_);
lean_inc_ref(v_a_3028_);
lean_inc(v_a_3027_);
lean_inc_ref(v___x_3073_);
v___x_3084_ = lean_whnf(v_snd_3083_, v___x_3073_, v_a_3027_, v_a_3028_, v_a_3029_);
if (lean_obj_tag(v___x_3084_) == 0)
{
lean_object* v_a_3085_; lean_object* v___f_3086_; uint8_t v___x_3087_; lean_object* v___x_3088_; 
v_a_3085_ = lean_ctor_get(v___x_3084_, 0);
lean_inc(v_a_3085_);
lean_dec_ref_known(v___x_3084_, 1);
lean_inc(v_a_3075_);
v___f_3086_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___boxed), 13, 6);
lean_closure_set(v___f_3086_, 0, v_a_3085_);
lean_closure_set(v___f_3086_, 1, v_fst_3081_);
lean_closure_set(v___f_3086_, 2, v_fst_3082_);
lean_closure_set(v___f_3086_, 3, v_inst_3024_);
lean_closure_set(v___f_3086_, 4, v_a_3075_);
lean_closure_set(v___f_3086_, 5, v_projInfo_x3f_3025_);
v___x_3087_ = 0;
v___x_3088_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3075_, v___f_3086_, v___x_3087_, v___x_3087_, v___x_3073_, v_a_3027_, v_a_3028_, v_a_3029_);
lean_dec_ref_known(v___x_3073_, 7);
return v___x_3088_;
}
else
{
lean_object* v_a_3089_; lean_object* v___x_3091_; uint8_t v_isShared_3092_; uint8_t v_isSharedCheck_3096_; 
lean_dec(v_fst_3082_);
lean_dec(v_fst_3081_);
lean_dec(v_a_3075_);
lean_dec_ref_known(v___x_3073_, 7);
lean_dec(v_projInfo_x3f_3025_);
lean_dec_ref(v_inst_3024_);
v_a_3089_ = lean_ctor_get(v___x_3084_, 0);
v_isSharedCheck_3096_ = !lean_is_exclusive(v___x_3084_);
if (v_isSharedCheck_3096_ == 0)
{
v___x_3091_ = v___x_3084_;
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
else
{
lean_inc(v_a_3089_);
lean_dec(v___x_3084_);
v___x_3091_ = lean_box(0);
v_isShared_3092_ = v_isSharedCheck_3096_;
goto v_resetjp_3090_;
}
v_resetjp_3090_:
{
lean_object* v___x_3094_; 
if (v_isShared_3092_ == 0)
{
v___x_3094_ = v___x_3091_;
goto v_reusejp_3093_;
}
else
{
lean_object* v_reuseFailAlloc_3095_; 
v_reuseFailAlloc_3095_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3095_, 0, v_a_3089_);
v___x_3094_ = v_reuseFailAlloc_3095_;
goto v_reusejp_3093_;
}
v_reusejp_3093_:
{
return v___x_3094_;
}
}
}
}
else
{
lean_object* v_a_3097_; lean_object* v___x_3099_; uint8_t v_isShared_3100_; uint8_t v_isSharedCheck_3104_; 
lean_dec(v_a_3075_);
lean_dec_ref_known(v___x_3073_, 7);
lean_dec(v_projInfo_x3f_3025_);
lean_dec_ref(v_inst_3024_);
v_a_3097_ = lean_ctor_get(v___x_3078_, 0);
v_isSharedCheck_3104_ = !lean_is_exclusive(v___x_3078_);
if (v_isSharedCheck_3104_ == 0)
{
v___x_3099_ = v___x_3078_;
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
else
{
lean_inc(v_a_3097_);
lean_dec(v___x_3078_);
v___x_3099_ = lean_box(0);
v_isShared_3100_ = v_isSharedCheck_3104_;
goto v_resetjp_3098_;
}
v_resetjp_3098_:
{
lean_object* v___x_3102_; 
if (v_isShared_3100_ == 0)
{
v___x_3102_ = v___x_3099_;
goto v_reusejp_3101_;
}
else
{
lean_object* v_reuseFailAlloc_3103_; 
v_reuseFailAlloc_3103_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3103_, 0, v_a_3097_);
v___x_3102_ = v_reuseFailAlloc_3103_;
goto v_reusejp_3101_;
}
v_reusejp_3101_:
{
return v___x_3102_;
}
}
}
}
else
{
lean_object* v_a_3105_; lean_object* v___x_3107_; uint8_t v_isShared_3108_; uint8_t v_isSharedCheck_3112_; 
lean_dec_ref_known(v___x_3073_, 7);
lean_dec(v_projInfo_x3f_3025_);
lean_dec_ref(v_inst_3024_);
v_a_3105_ = lean_ctor_get(v___x_3074_, 0);
v_isSharedCheck_3112_ = !lean_is_exclusive(v___x_3074_);
if (v_isSharedCheck_3112_ == 0)
{
v___x_3107_ = v___x_3074_;
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
else
{
lean_inc(v_a_3105_);
lean_dec(v___x_3074_);
v___x_3107_ = lean_box(0);
v_isShared_3108_ = v_isSharedCheck_3112_;
goto v_resetjp_3106_;
}
v_resetjp_3106_:
{
lean_object* v___x_3110_; 
if (v_isShared_3108_ == 0)
{
v___x_3110_ = v___x_3107_;
goto v_reusejp_3109_;
}
else
{
lean_object* v_reuseFailAlloc_3111_; 
v_reuseFailAlloc_3111_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3111_, 0, v_a_3105_);
v___x_3110_ = v_reuseFailAlloc_3111_;
goto v_reusejp_3109_;
}
v_reusejp_3109_:
{
return v___x_3110_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___boxed(lean_object* v_inst_3115_, lean_object* v_projInfo_x3f_3116_, lean_object* v_a_3117_, lean_object* v_a_3118_, lean_object* v_a_3119_, lean_object* v_a_3120_, lean_object* v_a_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_inst_3115_, v_projInfo_x3f_3116_, v_a_3117_, v_a_3118_, v_a_3119_, v_a_3120_);
lean_dec(v_a_3120_);
lean_dec_ref(v_a_3119_);
lean_dec(v_a_3118_);
lean_dec_ref(v_a_3117_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(lean_object* v_upperBound_3123_, lean_object* v_a_3124_, lean_object* v_inst_3125_, lean_object* v_R_3126_, lean_object* v_a_3127_, lean_object* v_b_3128_, lean_object* v_c_3129_, lean_object* v___y_3130_, lean_object* v___y_3131_, lean_object* v___y_3132_, lean_object* v___y_3133_){
_start:
{
lean_object* v___x_3135_; 
v___x_3135_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___redArg(v_upperBound_3123_, v_a_3124_, v_a_3127_, v_b_3128_);
return v___x_3135_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2___boxed(lean_object* v_upperBound_3136_, lean_object* v_a_3137_, lean_object* v_inst_3138_, lean_object* v_R_3139_, lean_object* v_a_3140_, lean_object* v_b_3141_, lean_object* v_c_3142_, lean_object* v___y_3143_, lean_object* v___y_3144_, lean_object* v___y_3145_, lean_object* v___y_3146_, lean_object* v___y_3147_){
_start:
{
lean_object* v_res_3148_; 
v_res_3148_ = l_WellFounded_opaqueFix_u2083___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__2(v_upperBound_3136_, v_a_3137_, v_inst_3138_, v_R_3139_, v_a_3140_, v_b_3141_, v_c_3142_, v___y_3143_, v___y_3144_, v___y_3145_, v___y_3146_);
lean_dec(v___y_3146_);
lean_dec_ref(v___y_3145_);
lean_dec(v___y_3144_);
lean_dec_ref(v___y_3143_);
lean_dec_ref(v_a_3137_);
lean_dec(v_upperBound_3136_);
return v_res_3148_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(lean_object* v_00_u03b1_3149_, lean_object* v_msg_3150_, lean_object* v___y_3151_, lean_object* v___y_3152_, lean_object* v___y_3153_, lean_object* v___y_3154_){
_start:
{
lean_object* v___x_3156_; 
v___x_3156_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_3150_, v___y_3151_, v___y_3152_, v___y_3153_, v___y_3154_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___boxed(lean_object* v_00_u03b1_3157_, lean_object* v_msg_3158_, lean_object* v___y_3159_, lean_object* v___y_3160_, lean_object* v___y_3161_, lean_object* v___y_3162_, lean_object* v___y_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6(v_00_u03b1_3157_, v_msg_3158_, v___y_3159_, v___y_3160_, v___y_3161_, v___y_3162_);
lean_dec(v___y_3162_);
lean_dec_ref(v___y_3161_);
lean_dec(v___y_3160_);
lean_dec_ref(v___y_3159_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(lean_object* v_fst_3165_, lean_object* v_argVars_3166_, lean_object* v_inst_3167_, lean_object* v_a_3168_, lean_object* v_projInfo_x3f_3169_, lean_object* v_inst_3170_, lean_object* v_a_3171_, lean_object* v___y_3172_, lean_object* v___y_3173_, lean_object* v___y_3174_, lean_object* v___y_3175_){
_start:
{
lean_object* v___x_3177_; 
v___x_3177_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg(v_fst_3165_, v_argVars_3166_, v_inst_3167_, v_a_3168_, v_projInfo_x3f_3169_, v_a_3171_, v___y_3172_, v___y_3173_, v___y_3174_, v___y_3175_);
return v___x_3177_;
}
}
LEAN_EXPORT lean_object* l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___boxed(lean_object* v_fst_3178_, lean_object* v_argVars_3179_, lean_object* v_inst_3180_, lean_object* v_a_3181_, lean_object* v_projInfo_x3f_3182_, lean_object* v_inst_3183_, lean_object* v_a_3184_, lean_object* v___y_3185_, lean_object* v___y_3186_, lean_object* v___y_3187_, lean_object* v___y_3188_, lean_object* v___y_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10(v_fst_3178_, v_argVars_3179_, v_inst_3180_, v_a_3181_, v_projInfo_x3f_3182_, v_inst_3183_, v_a_3184_, v___y_3185_, v___y_3186_, v___y_3187_, v___y_3188_);
lean_dec(v___y_3188_);
lean_dec_ref(v___y_3187_);
lean_dec(v___y_3186_);
lean_dec_ref(v___y_3185_);
lean_dec(v_projInfo_x3f_3182_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(lean_object* v_type_3191_, lean_object* v_k_3192_, uint8_t v_cleanupAnnotations_3193_, lean_object* v___y_3194_, lean_object* v___y_3195_, lean_object* v___y_3196_, lean_object* v___y_3197_){
_start:
{
lean_object* v___f_3199_; uint8_t v___x_3200_; lean_object* v___x_3201_; lean_object* v___x_3202_; 
v___f_3199_ = lean_alloc_closure((void*)(l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3199_, 0, v_k_3192_);
v___x_3200_ = 0;
v___x_3201_ = lean_box(0);
v___x_3202_ = l___private_Lean_Meta_Basic_0__Lean_Meta_forallTelescopeReducingAuxAux(lean_box(0), v___x_3200_, v___x_3201_, v_type_3191_, v___f_3199_, v_cleanupAnnotations_3193_, v___x_3200_, v___y_3194_, v___y_3195_, v___y_3196_, v___y_3197_);
if (lean_obj_tag(v___x_3202_) == 0)
{
lean_object* v_a_3203_; lean_object* v___x_3205_; uint8_t v_isShared_3206_; uint8_t v_isSharedCheck_3210_; 
v_a_3203_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3210_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3210_ == 0)
{
v___x_3205_ = v___x_3202_;
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
else
{
lean_inc(v_a_3203_);
lean_dec(v___x_3202_);
v___x_3205_ = lean_box(0);
v_isShared_3206_ = v_isSharedCheck_3210_;
goto v_resetjp_3204_;
}
v_resetjp_3204_:
{
lean_object* v___x_3208_; 
if (v_isShared_3206_ == 0)
{
v___x_3208_ = v___x_3205_;
goto v_reusejp_3207_;
}
else
{
lean_object* v_reuseFailAlloc_3209_; 
v_reuseFailAlloc_3209_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3209_, 0, v_a_3203_);
v___x_3208_ = v_reuseFailAlloc_3209_;
goto v_reusejp_3207_;
}
v_reusejp_3207_:
{
return v___x_3208_;
}
}
}
else
{
lean_object* v_a_3211_; lean_object* v___x_3213_; uint8_t v_isShared_3214_; uint8_t v_isSharedCheck_3218_; 
v_a_3211_ = lean_ctor_get(v___x_3202_, 0);
v_isSharedCheck_3218_ = !lean_is_exclusive(v___x_3202_);
if (v_isSharedCheck_3218_ == 0)
{
v___x_3213_ = v___x_3202_;
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
else
{
lean_inc(v_a_3211_);
lean_dec(v___x_3202_);
v___x_3213_ = lean_box(0);
v_isShared_3214_ = v_isSharedCheck_3218_;
goto v_resetjp_3212_;
}
v_resetjp_3212_:
{
lean_object* v___x_3216_; 
if (v_isShared_3214_ == 0)
{
v___x_3216_ = v___x_3213_;
goto v_reusejp_3215_;
}
else
{
lean_object* v_reuseFailAlloc_3217_; 
v_reuseFailAlloc_3217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3217_, 0, v_a_3211_);
v___x_3216_ = v_reuseFailAlloc_3217_;
goto v_reusejp_3215_;
}
v_reusejp_3215_:
{
return v___x_3216_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg___boxed(lean_object* v_type_3219_, lean_object* v_k_3220_, lean_object* v_cleanupAnnotations_3221_, lean_object* v___y_3222_, lean_object* v___y_3223_, lean_object* v___y_3224_, lean_object* v___y_3225_, lean_object* v___y_3226_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3227_; lean_object* v_res_3228_; 
v_cleanupAnnotations_boxed_3227_ = lean_unbox(v_cleanupAnnotations_3221_);
v_res_3228_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3219_, v_k_3220_, v_cleanupAnnotations_boxed_3227_, v___y_3222_, v___y_3223_, v___y_3224_, v___y_3225_);
lean_dec(v___y_3225_);
lean_dec_ref(v___y_3224_);
lean_dec(v___y_3223_);
lean_dec_ref(v___y_3222_);
return v_res_3228_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(lean_object* v_00_u03b1_3229_, lean_object* v_type_3230_, lean_object* v_k_3231_, uint8_t v_cleanupAnnotations_3232_, lean_object* v___y_3233_, lean_object* v___y_3234_, lean_object* v___y_3235_, lean_object* v___y_3236_){
_start:
{
lean_object* v___x_3238_; 
v___x_3238_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v_type_3230_, v_k_3231_, v_cleanupAnnotations_3232_, v___y_3233_, v___y_3234_, v___y_3235_, v___y_3236_);
return v___x_3238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___boxed(lean_object* v_00_u03b1_3239_, lean_object* v_type_3240_, lean_object* v_k_3241_, lean_object* v_cleanupAnnotations_3242_, lean_object* v___y_3243_, lean_object* v___y_3244_, lean_object* v___y_3245_, lean_object* v___y_3246_, lean_object* v___y_3247_){
_start:
{
uint8_t v_cleanupAnnotations_boxed_3248_; lean_object* v_res_3249_; 
v_cleanupAnnotations_boxed_3248_ = lean_unbox(v_cleanupAnnotations_3242_);
v_res_3249_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5(v_00_u03b1_3239_, v_type_3240_, v_k_3241_, v_cleanupAnnotations_boxed_3248_, v___y_3243_, v___y_3244_, v___y_3245_, v___y_3246_);
lean_dec(v___y_3246_);
lean_dec_ref(v___y_3245_);
lean_dec(v___y_3244_);
lean_dec_ref(v___y_3243_);
return v_res_3249_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(lean_object* v_as_3250_, size_t v_sz_3251_, size_t v_i_3252_, lean_object* v_b_3253_, lean_object* v___y_3254_, lean_object* v___y_3255_, lean_object* v___y_3256_, lean_object* v___y_3257_){
_start:
{
lean_object* v_a_3260_; uint8_t v___x_3264_; 
v___x_3264_ = lean_usize_dec_lt(v_i_3252_, v_sz_3251_);
if (v___x_3264_ == 0)
{
lean_object* v___x_3265_; 
v___x_3265_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3265_, 0, v_b_3253_);
return v___x_3265_;
}
else
{
lean_object* v_a_3266_; lean_object* v___x_3267_; lean_object* v___x_3268_; 
v_a_3266_ = lean_array_uget_borrowed(v_as_3250_, v_i_3252_);
v___x_3267_ = l_Lean_Expr_fvarId_x21(v_a_3266_);
lean_inc(v___x_3267_);
v___x_3268_ = l_Lean_FVarId_getBinderInfo___redArg(v___x_3267_, v___y_3255_, v___y_3256_, v___y_3257_);
if (lean_obj_tag(v___x_3268_) == 0)
{
lean_object* v_a_3269_; lean_object* v___x_3270_; uint8_t v___x_3271_; uint8_t v___x_3272_; 
v_a_3269_ = lean_ctor_get(v___x_3268_, 0);
lean_inc(v_a_3269_);
lean_dec_ref_known(v___x_3268_, 1);
v___x_3270_ = lean_box(0);
v___x_3271_ = lean_unbox(v_a_3269_);
lean_dec(v_a_3269_);
v___x_3272_ = l_Lean_BinderInfo_isInstImplicit(v___x_3271_);
if (v___x_3272_ == 0)
{
lean_dec(v___x_3267_);
v_a_3260_ = v___x_3270_;
goto v___jp_3259_;
}
else
{
lean_object* v___x_3273_; lean_object* v___x_3274_; lean_object* v___x_3275_; 
v___x_3273_ = lean_st_ref_take(v___y_3254_);
v___x_3274_ = l_Lean_CollectFVars_State_add(v___x_3273_, v___x_3267_);
v___x_3275_ = lean_st_ref_set(v___y_3254_, v___x_3274_);
v_a_3260_ = v___x_3270_;
goto v___jp_3259_;
}
}
else
{
lean_object* v_a_3276_; lean_object* v___x_3278_; uint8_t v_isShared_3279_; uint8_t v_isSharedCheck_3283_; 
lean_dec(v___x_3267_);
v_a_3276_ = lean_ctor_get(v___x_3268_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3268_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3278_ = v___x_3268_;
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
else
{
lean_inc(v_a_3276_);
lean_dec(v___x_3268_);
v___x_3278_ = lean_box(0);
v_isShared_3279_ = v_isSharedCheck_3283_;
goto v_resetjp_3277_;
}
v_resetjp_3277_:
{
lean_object* v___x_3281_; 
if (v_isShared_3279_ == 0)
{
v___x_3281_ = v___x_3278_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v_a_3276_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
v___jp_3259_:
{
size_t v___x_3261_; size_t v___x_3262_; 
v___x_3261_ = ((size_t)1ULL);
v___x_3262_ = lean_usize_add(v_i_3252_, v___x_3261_);
v_i_3252_ = v___x_3262_;
v_b_3253_ = v_a_3260_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg___boxed(lean_object* v_as_3284_, lean_object* v_sz_3285_, lean_object* v_i_3286_, lean_object* v_b_3287_, lean_object* v___y_3288_, lean_object* v___y_3289_, lean_object* v___y_3290_, lean_object* v___y_3291_, lean_object* v___y_3292_){
_start:
{
size_t v_sz_boxed_3293_; size_t v_i_boxed_3294_; lean_object* v_res_3295_; 
v_sz_boxed_3293_ = lean_unbox_usize(v_sz_3285_);
lean_dec(v_sz_3285_);
v_i_boxed_3294_ = lean_unbox_usize(v_i_3286_);
lean_dec(v_i_3286_);
v_res_3295_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_as_3284_, v_sz_boxed_3293_, v_i_boxed_3294_, v_b_3287_, v___y_3288_, v___y_3289_, v___y_3290_, v___y_3291_);
lean_dec(v___y_3291_);
lean_dec_ref(v___y_3290_);
lean_dec_ref(v___y_3289_);
lean_dec(v___y_3288_);
lean_dec_ref(v_as_3284_);
return v_res_3295_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(lean_object* v_k_3296_, lean_object* v_t_3297_){
_start:
{
if (lean_obj_tag(v_t_3297_) == 0)
{
lean_object* v_k_3298_; lean_object* v_l_3299_; lean_object* v_r_3300_; uint8_t v___x_3301_; 
v_k_3298_ = lean_ctor_get(v_t_3297_, 1);
v_l_3299_ = lean_ctor_get(v_t_3297_, 3);
v_r_3300_ = lean_ctor_get(v_t_3297_, 4);
v___x_3301_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_3296_, v_k_3298_);
switch(v___x_3301_)
{
case 0:
{
v_t_3297_ = v_l_3299_;
goto _start;
}
case 1:
{
uint8_t v___x_3303_; 
v___x_3303_ = 1;
return v___x_3303_;
}
default: 
{
v_t_3297_ = v_r_3300_;
goto _start;
}
}
}
else
{
uint8_t v___x_3305_; 
v___x_3305_ = 0;
return v___x_3305_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg___boxed(lean_object* v_k_3306_, lean_object* v_t_3307_){
_start:
{
uint8_t v_res_3308_; lean_object* v_r_3309_; 
v_res_3308_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3306_, v_t_3307_);
lean_dec(v_t_3307_);
lean_dec(v_k_3306_);
v_r_3309_ = lean_box(v_res_3308_);
return v_r_3309_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3311_; lean_object* v___x_3312_; 
v___x_3311_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__0));
v___x_3312_ = l_Lean_stringToMessageData(v___x_3311_);
return v___x_3312_;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3314_; lean_object* v___x_3315_; 
v___x_3314_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__2));
v___x_3315_ = l_Lean_stringToMessageData(v___x_3314_);
return v___x_3315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(lean_object* v_a_3316_, lean_object* v_as_3317_, size_t v_sz_3318_, size_t v_i_3319_, lean_object* v_b_3320_, lean_object* v___y_3321_, lean_object* v___y_3322_, lean_object* v___y_3323_){
_start:
{
lean_object* v_a_3326_; uint8_t v___x_3330_; 
v___x_3330_ = lean_usize_dec_lt(v_i_3319_, v_sz_3318_);
if (v___x_3330_ == 0)
{
lean_object* v___x_3331_; 
v___x_3331_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3331_, 0, v_b_3320_);
return v___x_3331_;
}
else
{
lean_object* v_snd_3332_; 
v_snd_3332_ = lean_ctor_get(v_b_3320_, 1);
lean_inc(v_snd_3332_);
if (lean_obj_tag(v_snd_3332_) == 0)
{
lean_object* v_fst_3333_; lean_object* v___x_3335_; uint8_t v_isShared_3336_; uint8_t v_isSharedCheck_3341_; 
v_fst_3333_ = lean_ctor_get(v_b_3320_, 0);
v_isSharedCheck_3341_ = !lean_is_exclusive(v_b_3320_);
if (v_isSharedCheck_3341_ == 0)
{
lean_object* v_unused_3342_; 
v_unused_3342_ = lean_ctor_get(v_b_3320_, 1);
lean_dec(v_unused_3342_);
v___x_3335_ = v_b_3320_;
v_isShared_3336_ = v_isSharedCheck_3341_;
goto v_resetjp_3334_;
}
else
{
lean_inc(v_fst_3333_);
lean_dec(v_b_3320_);
v___x_3335_ = lean_box(0);
v_isShared_3336_ = v_isSharedCheck_3341_;
goto v_resetjp_3334_;
}
v_resetjp_3334_:
{
lean_object* v___x_3338_; 
if (v_isShared_3336_ == 0)
{
v___x_3338_ = v___x_3335_;
goto v_reusejp_3337_;
}
else
{
lean_object* v_reuseFailAlloc_3340_; 
v_reuseFailAlloc_3340_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3340_, 0, v_fst_3333_);
lean_ctor_set(v_reuseFailAlloc_3340_, 1, v_snd_3332_);
v___x_3338_ = v_reuseFailAlloc_3340_;
goto v_reusejp_3337_;
}
v_reusejp_3337_:
{
lean_object* v___x_3339_; 
v___x_3339_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3339_, 0, v___x_3338_);
return v___x_3339_;
}
}
}
else
{
lean_object* v_fst_3343_; lean_object* v___x_3345_; uint8_t v_isShared_3346_; uint8_t v_isSharedCheck_3400_; 
v_fst_3343_ = lean_ctor_get(v_b_3320_, 0);
v_isSharedCheck_3400_ = !lean_is_exclusive(v_b_3320_);
if (v_isSharedCheck_3400_ == 0)
{
lean_object* v_unused_3401_; 
v_unused_3401_ = lean_ctor_get(v_b_3320_, 1);
lean_dec(v_unused_3401_);
v___x_3345_ = v_b_3320_;
v_isShared_3346_ = v_isSharedCheck_3400_;
goto v_resetjp_3344_;
}
else
{
lean_inc(v_fst_3343_);
lean_dec(v_b_3320_);
v___x_3345_ = lean_box(0);
v_isShared_3346_ = v_isSharedCheck_3400_;
goto v_resetjp_3344_;
}
v_resetjp_3344_:
{
lean_object* v_val_3347_; lean_object* v___x_3349_; uint8_t v_isShared_3350_; uint8_t v_isSharedCheck_3399_; 
v_val_3347_ = lean_ctor_get(v_snd_3332_, 0);
v_isSharedCheck_3399_ = !lean_is_exclusive(v_snd_3332_);
if (v_isSharedCheck_3399_ == 0)
{
v___x_3349_ = v_snd_3332_;
v_isShared_3350_ = v_isSharedCheck_3399_;
goto v_resetjp_3348_;
}
else
{
lean_inc(v_val_3347_);
lean_dec(v_snd_3332_);
v___x_3349_ = lean_box(0);
v_isShared_3350_ = v_isSharedCheck_3399_;
goto v_resetjp_3348_;
}
v_resetjp_3348_:
{
lean_object* v_fvarSet_3351_; lean_object* v_a_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; lean_object* v___x_3356_; 
v_fvarSet_3351_ = lean_ctor_get(v_a_3316_, 1);
v_a_3352_ = lean_array_uget_borrowed(v_as_3317_, v_i_3319_);
v___x_3353_ = lean_unsigned_to_nat(1u);
v___x_3354_ = lean_nat_add(v_val_3347_, v___x_3353_);
if (v_isShared_3350_ == 0)
{
lean_ctor_set(v___x_3349_, 0, v___x_3354_);
v___x_3356_ = v___x_3349_;
goto v_reusejp_3355_;
}
else
{
lean_object* v_reuseFailAlloc_3398_; 
v_reuseFailAlloc_3398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3398_, 0, v___x_3354_);
v___x_3356_ = v_reuseFailAlloc_3398_;
goto v_reusejp_3355_;
}
v_reusejp_3355_:
{
lean_object* v___x_3357_; uint8_t v___x_3358_; 
v___x_3357_ = l_Lean_Expr_fvarId_x21(v_a_3352_);
v___x_3358_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v___x_3357_, v_fvarSet_3351_);
if (v___x_3358_ == 0)
{
lean_object* v___x_3359_; 
v___x_3359_ = l_Lean_FVarId_getDecl___redArg(v___x_3357_, v___y_3321_, v___y_3322_, v___y_3323_);
if (lean_obj_tag(v___x_3359_) == 0)
{
lean_object* v_a_3360_; lean_object* v___x_3361_; 
v_a_3360_ = lean_ctor_get(v___x_3359_, 0);
lean_inc(v_a_3360_);
lean_dec_ref_known(v___x_3359_, 1);
v___x_3361_ = l_Lean_LocalDecl_ppAsBinder(v_a_3360_);
if (lean_obj_tag(v___x_3361_) == 1)
{
lean_object* v_val_3362_; lean_object* v___x_3364_; uint8_t v_isShared_3365_; uint8_t v_isSharedCheck_3383_; 
v_val_3362_ = lean_ctor_get(v___x_3361_, 0);
v_isSharedCheck_3383_ = !lean_is_exclusive(v___x_3361_);
if (v_isSharedCheck_3383_ == 0)
{
v___x_3364_ = v___x_3361_;
v_isShared_3365_ = v_isSharedCheck_3383_;
goto v_resetjp_3363_;
}
else
{
lean_inc(v_val_3362_);
lean_dec(v___x_3361_);
v___x_3364_ = lean_box(0);
v_isShared_3365_ = v_isSharedCheck_3383_;
goto v_resetjp_3363_;
}
v_resetjp_3363_:
{
lean_object* v___x_3366_; lean_object* v___x_3367_; lean_object* v___x_3369_; 
v___x_3366_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__1);
v___x_3367_ = l_Nat_reprFast(v_val_3347_);
if (v_isShared_3365_ == 0)
{
lean_ctor_set_tag(v___x_3364_, 3);
lean_ctor_set(v___x_3364_, 0, v___x_3367_);
v___x_3369_ = v___x_3364_;
goto v_reusejp_3368_;
}
else
{
lean_object* v_reuseFailAlloc_3382_; 
v_reuseFailAlloc_3382_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3382_, 0, v___x_3367_);
v___x_3369_ = v_reuseFailAlloc_3382_;
goto v_reusejp_3368_;
}
v_reusejp_3368_:
{
lean_object* v___x_3370_; lean_object* v___x_3371_; lean_object* v___x_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; lean_object* v___x_3380_; 
v___x_3370_ = l_Lean_MessageData_ofFormat(v___x_3369_);
v___x_3371_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3371_, 0, v___x_3366_);
lean_ctor_set(v___x_3371_, 1, v___x_3370_);
v___x_3372_ = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___closed__3);
v___x_3373_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3373_, 0, v___x_3371_);
lean_ctor_set(v___x_3373_, 1, v___x_3372_);
v___x_3374_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3374_, 0, v___x_3373_);
lean_ctor_set(v___x_3374_, 1, v_val_3362_);
v___x_3375_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_3376_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3376_, 0, v___x_3374_);
lean_ctor_set(v___x_3376_, 1, v___x_3375_);
v___x_3377_ = l_Lean_indentD(v___x_3376_);
v___x_3378_ = lean_array_push(v_fst_3343_, v___x_3377_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 1, v___x_3356_);
lean_ctor_set(v___x_3345_, 0, v___x_3378_);
v___x_3380_ = v___x_3345_;
goto v_reusejp_3379_;
}
else
{
lean_object* v_reuseFailAlloc_3381_; 
v_reuseFailAlloc_3381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3381_, 0, v___x_3378_);
lean_ctor_set(v_reuseFailAlloc_3381_, 1, v___x_3356_);
v___x_3380_ = v_reuseFailAlloc_3381_;
goto v_reusejp_3379_;
}
v_reusejp_3379_:
{
v_a_3326_ = v___x_3380_;
goto v___jp_3325_;
}
}
}
}
else
{
lean_object* v___x_3385_; 
lean_dec(v___x_3361_);
lean_dec(v_val_3347_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 1, v___x_3356_);
v___x_3385_ = v___x_3345_;
goto v_reusejp_3384_;
}
else
{
lean_object* v_reuseFailAlloc_3386_; 
v_reuseFailAlloc_3386_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3386_, 0, v_fst_3343_);
lean_ctor_set(v_reuseFailAlloc_3386_, 1, v___x_3356_);
v___x_3385_ = v_reuseFailAlloc_3386_;
goto v_reusejp_3384_;
}
v_reusejp_3384_:
{
v_a_3326_ = v___x_3385_;
goto v___jp_3325_;
}
}
}
else
{
lean_object* v_a_3387_; lean_object* v___x_3389_; uint8_t v_isShared_3390_; uint8_t v_isSharedCheck_3394_; 
lean_dec_ref(v___x_3356_);
lean_dec(v_val_3347_);
lean_del_object(v___x_3345_);
lean_dec(v_fst_3343_);
v_a_3387_ = lean_ctor_get(v___x_3359_, 0);
v_isSharedCheck_3394_ = !lean_is_exclusive(v___x_3359_);
if (v_isSharedCheck_3394_ == 0)
{
v___x_3389_ = v___x_3359_;
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
else
{
lean_inc(v_a_3387_);
lean_dec(v___x_3359_);
v___x_3389_ = lean_box(0);
v_isShared_3390_ = v_isSharedCheck_3394_;
goto v_resetjp_3388_;
}
v_resetjp_3388_:
{
lean_object* v___x_3392_; 
if (v_isShared_3390_ == 0)
{
v___x_3392_ = v___x_3389_;
goto v_reusejp_3391_;
}
else
{
lean_object* v_reuseFailAlloc_3393_; 
v_reuseFailAlloc_3393_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3393_, 0, v_a_3387_);
v___x_3392_ = v_reuseFailAlloc_3393_;
goto v_reusejp_3391_;
}
v_reusejp_3391_:
{
return v___x_3392_;
}
}
}
}
else
{
lean_object* v___x_3396_; 
lean_dec(v___x_3357_);
lean_dec(v_val_3347_);
if (v_isShared_3346_ == 0)
{
lean_ctor_set(v___x_3345_, 1, v___x_3356_);
v___x_3396_ = v___x_3345_;
goto v_reusejp_3395_;
}
else
{
lean_object* v_reuseFailAlloc_3397_; 
v_reuseFailAlloc_3397_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3397_, 0, v_fst_3343_);
lean_ctor_set(v_reuseFailAlloc_3397_, 1, v___x_3356_);
v___x_3396_ = v_reuseFailAlloc_3397_;
goto v_reusejp_3395_;
}
v_reusejp_3395_:
{
v_a_3326_ = v___x_3396_;
goto v___jp_3325_;
}
}
}
}
}
}
}
v___jp_3325_:
{
size_t v___x_3327_; size_t v___x_3328_; 
v___x_3327_ = ((size_t)1ULL);
v___x_3328_ = lean_usize_add(v_i_3319_, v___x_3327_);
v_i_3319_ = v___x_3328_;
v_b_3320_ = v_a_3326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg___boxed(lean_object* v_a_3402_, lean_object* v_as_3403_, lean_object* v_sz_3404_, lean_object* v_i_3405_, lean_object* v_b_3406_, lean_object* v___y_3407_, lean_object* v___y_3408_, lean_object* v___y_3409_, lean_object* v___y_3410_){
_start:
{
size_t v_sz_boxed_3411_; size_t v_i_boxed_3412_; lean_object* v_res_3413_; 
v_sz_boxed_3411_ = lean_unbox_usize(v_sz_3404_);
lean_dec(v_sz_3404_);
v_i_boxed_3412_ = lean_unbox_usize(v_i_3405_);
lean_dec(v_i_3405_);
v_res_3413_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3402_, v_as_3403_, v_sz_boxed_3411_, v_i_boxed_3412_, v_b_3406_, v___y_3407_, v___y_3408_, v___y_3409_);
lean_dec(v___y_3409_);
lean_dec_ref(v___y_3408_);
lean_dec_ref(v___y_3407_);
lean_dec_ref(v_as_3403_);
lean_dec_ref(v_a_3402_);
return v_res_3413_;
}
}
LEAN_EXPORT uint8_t l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(uint8_t v___y_3421_, uint8_t v_suppressElabErrors_3422_, lean_object* v_x_3423_){
_start:
{
if (lean_obj_tag(v_x_3423_) == 1)
{
lean_object* v_pre_3424_; 
v_pre_3424_ = lean_ctor_get(v_x_3423_, 0);
switch(lean_obj_tag(v_pre_3424_))
{
case 1:
{
lean_object* v_pre_3425_; 
v_pre_3425_ = lean_ctor_get(v_pre_3424_, 0);
switch(lean_obj_tag(v_pre_3425_))
{
case 0:
{
lean_object* v_str_3426_; lean_object* v_str_3427_; lean_object* v___x_3428_; uint8_t v___x_3429_; 
v_str_3426_ = lean_ctor_get(v_x_3423_, 1);
v_str_3427_ = lean_ctor_get(v_pre_3424_, 1);
v___x_3428_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__0));
v___x_3429_ = lean_string_dec_eq(v_str_3427_, v___x_3428_);
if (v___x_3429_ == 0)
{
lean_object* v___x_3430_; uint8_t v___x_3431_; 
v___x_3430_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__1));
v___x_3431_ = lean_string_dec_eq(v_str_3427_, v___x_3430_);
if (v___x_3431_ == 0)
{
return v___y_3421_;
}
else
{
lean_object* v___x_3432_; uint8_t v___x_3433_; 
v___x_3432_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__2));
v___x_3433_ = lean_string_dec_eq(v_str_3426_, v___x_3432_);
if (v___x_3433_ == 0)
{
return v___y_3421_;
}
else
{
return v_suppressElabErrors_3422_;
}
}
}
else
{
lean_object* v___x_3434_; uint8_t v___x_3435_; 
v___x_3434_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__3));
v___x_3435_ = lean_string_dec_eq(v_str_3426_, v___x_3434_);
if (v___x_3435_ == 0)
{
return v___y_3421_;
}
else
{
return v_suppressElabErrors_3422_;
}
}
}
case 1:
{
lean_object* v_pre_3436_; 
v_pre_3436_ = lean_ctor_get(v_pre_3425_, 0);
if (lean_obj_tag(v_pre_3436_) == 0)
{
lean_object* v_str_3437_; lean_object* v_str_3438_; lean_object* v_str_3439_; lean_object* v___x_3440_; uint8_t v___x_3441_; 
v_str_3437_ = lean_ctor_get(v_x_3423_, 1);
v_str_3438_ = lean_ctor_get(v_pre_3424_, 1);
v_str_3439_ = lean_ctor_get(v_pre_3425_, 1);
v___x_3440_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__4));
v___x_3441_ = lean_string_dec_eq(v_str_3439_, v___x_3440_);
if (v___x_3441_ == 0)
{
return v___y_3421_;
}
else
{
lean_object* v___x_3442_; uint8_t v___x_3443_; 
v___x_3442_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__5));
v___x_3443_ = lean_string_dec_eq(v_str_3438_, v___x_3442_);
if (v___x_3443_ == 0)
{
return v___y_3421_;
}
else
{
lean_object* v___x_3444_; uint8_t v___x_3445_; 
v___x_3444_ = ((lean_object*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___closed__6));
v___x_3445_ = lean_string_dec_eq(v_str_3437_, v___x_3444_);
if (v___x_3445_ == 0)
{
return v___y_3421_;
}
else
{
return v_suppressElabErrors_3422_;
}
}
}
}
else
{
return v___y_3421_;
}
}
default: 
{
return v___y_3421_;
}
}
}
case 0:
{
lean_object* v_str_3446_; lean_object* v___x_3447_; uint8_t v___x_3448_; 
v_str_3446_ = lean_ctor_get(v_x_3423_, 1);
v___x_3447_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__2));
v___x_3448_ = lean_string_dec_eq(v_str_3446_, v___x_3447_);
if (v___x_3448_ == 0)
{
return v___y_3421_;
}
else
{
return v_suppressElabErrors_3422_;
}
}
default: 
{
return v___y_3421_;
}
}
}
else
{
return v___y_3421_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed(lean_object* v___y_3449_, lean_object* v_suppressElabErrors_3450_, lean_object* v_x_3451_){
_start:
{
uint8_t v___y_11896__boxed_3452_; uint8_t v_suppressElabErrors_boxed_3453_; uint8_t v_res_3454_; lean_object* v_r_3455_; 
v___y_11896__boxed_3452_ = lean_unbox(v___y_3449_);
v_suppressElabErrors_boxed_3453_ = lean_unbox(v_suppressElabErrors_3450_);
v_res_3454_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0(v___y_11896__boxed_3452_, v_suppressElabErrors_boxed_3453_, v_x_3451_);
lean_dec(v_x_3451_);
v_r_3455_ = lean_box(v_res_3454_);
return v_r_3455_;
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(lean_object* v_ref_3456_, lean_object* v_msgData_3457_, uint8_t v_severity_3458_, uint8_t v_isSilent_3459_, lean_object* v___y_3460_, lean_object* v___y_3461_, lean_object* v___y_3462_, lean_object* v___y_3463_){
_start:
{
uint8_t v___y_3466_; lean_object* v___y_3467_; lean_object* v___y_3468_; uint8_t v___y_3469_; lean_object* v___y_3470_; lean_object* v___y_3471_; lean_object* v___y_3472_; lean_object* v___y_3473_; lean_object* v___y_3474_; lean_object* v___y_3502_; lean_object* v___y_3503_; uint8_t v___y_3504_; uint8_t v___y_3505_; uint8_t v___y_3506_; lean_object* v___y_3507_; lean_object* v___y_3508_; lean_object* v___y_3509_; lean_object* v___y_3527_; uint8_t v___y_3528_; lean_object* v___y_3529_; uint8_t v___y_3530_; uint8_t v___y_3531_; lean_object* v___y_3532_; lean_object* v___y_3533_; lean_object* v___y_3534_; lean_object* v___y_3538_; lean_object* v___y_3539_; uint8_t v___y_3540_; lean_object* v___y_3541_; uint8_t v___y_3542_; lean_object* v___y_3543_; uint8_t v___y_3544_; uint8_t v___x_3549_; lean_object* v___y_3551_; lean_object* v___y_3552_; uint8_t v___y_3553_; lean_object* v___y_3554_; lean_object* v___y_3555_; uint8_t v___y_3556_; uint8_t v___y_3557_; uint8_t v___y_3559_; uint8_t v___x_3574_; 
v___x_3549_ = 2;
v___x_3574_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3458_, v___x_3549_);
if (v___x_3574_ == 0)
{
v___y_3559_ = v___x_3574_;
goto v___jp_3558_;
}
else
{
uint8_t v___x_3575_; 
lean_inc_ref(v_msgData_3457_);
v___x_3575_ = l_Lean_MessageData_hasSyntheticSorry(v_msgData_3457_);
v___y_3559_ = v___x_3575_;
goto v___jp_3558_;
}
v___jp_3465_:
{
lean_object* v___x_3475_; lean_object* v_currNamespace_3476_; lean_object* v_openDecls_3477_; lean_object* v_env_3478_; lean_object* v_nextMacroScope_3479_; lean_object* v_ngen_3480_; lean_object* v_auxDeclNGen_3481_; lean_object* v_traceState_3482_; lean_object* v_cache_3483_; lean_object* v_messages_3484_; lean_object* v_infoState_3485_; lean_object* v_snapshotTasks_3486_; lean_object* v___x_3488_; uint8_t v_isShared_3489_; uint8_t v_isSharedCheck_3500_; 
v___x_3475_ = lean_st_ref_take(v___y_3474_);
v_currNamespace_3476_ = lean_ctor_get(v___y_3473_, 6);
v_openDecls_3477_ = lean_ctor_get(v___y_3473_, 7);
v_env_3478_ = lean_ctor_get(v___x_3475_, 0);
v_nextMacroScope_3479_ = lean_ctor_get(v___x_3475_, 1);
v_ngen_3480_ = lean_ctor_get(v___x_3475_, 2);
v_auxDeclNGen_3481_ = lean_ctor_get(v___x_3475_, 3);
v_traceState_3482_ = lean_ctor_get(v___x_3475_, 4);
v_cache_3483_ = lean_ctor_get(v___x_3475_, 5);
v_messages_3484_ = lean_ctor_get(v___x_3475_, 6);
v_infoState_3485_ = lean_ctor_get(v___x_3475_, 7);
v_snapshotTasks_3486_ = lean_ctor_get(v___x_3475_, 8);
v_isSharedCheck_3500_ = !lean_is_exclusive(v___x_3475_);
if (v_isSharedCheck_3500_ == 0)
{
v___x_3488_ = v___x_3475_;
v_isShared_3489_ = v_isSharedCheck_3500_;
goto v_resetjp_3487_;
}
else
{
lean_inc(v_snapshotTasks_3486_);
lean_inc(v_infoState_3485_);
lean_inc(v_messages_3484_);
lean_inc(v_cache_3483_);
lean_inc(v_traceState_3482_);
lean_inc(v_auxDeclNGen_3481_);
lean_inc(v_ngen_3480_);
lean_inc(v_nextMacroScope_3479_);
lean_inc(v_env_3478_);
lean_dec(v___x_3475_);
v___x_3488_ = lean_box(0);
v_isShared_3489_ = v_isSharedCheck_3500_;
goto v_resetjp_3487_;
}
v_resetjp_3487_:
{
lean_object* v___x_3490_; lean_object* v___x_3491_; lean_object* v___x_3492_; lean_object* v___x_3493_; lean_object* v___x_3495_; 
lean_inc(v_openDecls_3477_);
lean_inc(v_currNamespace_3476_);
v___x_3490_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3490_, 0, v_currNamespace_3476_);
lean_ctor_set(v___x_3490_, 1, v_openDecls_3477_);
v___x_3491_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_3491_, 0, v___x_3490_);
lean_ctor_set(v___x_3491_, 1, v___y_3468_);
lean_inc_ref(v___y_3472_);
lean_inc_ref(v___y_3467_);
v___x_3492_ = lean_alloc_ctor(0, 5, 3);
lean_ctor_set(v___x_3492_, 0, v___y_3467_);
lean_ctor_set(v___x_3492_, 1, v___y_3471_);
lean_ctor_set(v___x_3492_, 2, v___y_3470_);
lean_ctor_set(v___x_3492_, 3, v___y_3472_);
lean_ctor_set(v___x_3492_, 4, v___x_3491_);
lean_ctor_set_uint8(v___x_3492_, sizeof(void*)*5, v___y_3469_);
lean_ctor_set_uint8(v___x_3492_, sizeof(void*)*5 + 1, v___y_3466_);
lean_ctor_set_uint8(v___x_3492_, sizeof(void*)*5 + 2, v_isSilent_3459_);
v___x_3493_ = l_Lean_MessageLog_add(v___x_3492_, v_messages_3484_);
if (v_isShared_3489_ == 0)
{
lean_ctor_set(v___x_3488_, 6, v___x_3493_);
v___x_3495_ = v___x_3488_;
goto v_reusejp_3494_;
}
else
{
lean_object* v_reuseFailAlloc_3499_; 
v_reuseFailAlloc_3499_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_3499_, 0, v_env_3478_);
lean_ctor_set(v_reuseFailAlloc_3499_, 1, v_nextMacroScope_3479_);
lean_ctor_set(v_reuseFailAlloc_3499_, 2, v_ngen_3480_);
lean_ctor_set(v_reuseFailAlloc_3499_, 3, v_auxDeclNGen_3481_);
lean_ctor_set(v_reuseFailAlloc_3499_, 4, v_traceState_3482_);
lean_ctor_set(v_reuseFailAlloc_3499_, 5, v_cache_3483_);
lean_ctor_set(v_reuseFailAlloc_3499_, 6, v___x_3493_);
lean_ctor_set(v_reuseFailAlloc_3499_, 7, v_infoState_3485_);
lean_ctor_set(v_reuseFailAlloc_3499_, 8, v_snapshotTasks_3486_);
v___x_3495_ = v_reuseFailAlloc_3499_;
goto v_reusejp_3494_;
}
v_reusejp_3494_:
{
lean_object* v___x_3496_; lean_object* v___x_3497_; lean_object* v___x_3498_; 
v___x_3496_ = lean_st_ref_set(v___y_3474_, v___x_3495_);
v___x_3497_ = lean_box(0);
v___x_3498_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3498_, 0, v___x_3497_);
return v___x_3498_;
}
}
}
v___jp_3501_:
{
lean_object* v___x_3510_; lean_object* v___x_3511_; lean_object* v_a_3512_; lean_object* v___x_3514_; uint8_t v_isShared_3515_; uint8_t v_isSharedCheck_3525_; 
v___x_3510_ = l___private_Lean_Log_0__Lean_MessageData_appendDescriptionWidgetIfNamed(v_msgData_3457_);
v___x_3511_ = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6_spec__7(v___x_3510_, v___y_3460_, v___y_3461_, v___y_3462_, v___y_3463_);
v_a_3512_ = lean_ctor_get(v___x_3511_, 0);
v_isSharedCheck_3525_ = !lean_is_exclusive(v___x_3511_);
if (v_isSharedCheck_3525_ == 0)
{
v___x_3514_ = v___x_3511_;
v_isShared_3515_ = v_isSharedCheck_3525_;
goto v_resetjp_3513_;
}
else
{
lean_inc(v_a_3512_);
lean_dec(v___x_3511_);
v___x_3514_ = lean_box(0);
v_isShared_3515_ = v_isSharedCheck_3525_;
goto v_resetjp_3513_;
}
v_resetjp_3513_:
{
lean_object* v___x_3516_; lean_object* v___x_3517_; lean_object* v___x_3518_; lean_object* v___x_3519_; 
lean_inc_ref_n(v___y_3508_, 2);
v___x_3516_ = l_Lean_FileMap_toPosition(v___y_3508_, v___y_3507_);
lean_dec(v___y_3507_);
v___x_3517_ = l_Lean_FileMap_toPosition(v___y_3508_, v___y_3509_);
lean_dec(v___y_3509_);
v___x_3518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3518_, 0, v___x_3517_);
v___x_3519_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
if (v___y_3506_ == 0)
{
lean_del_object(v___x_3514_);
lean_dec_ref(v___y_3502_);
v___y_3466_ = v___y_3504_;
v___y_3467_ = v___y_3503_;
v___y_3468_ = v_a_3512_;
v___y_3469_ = v___y_3505_;
v___y_3470_ = v___x_3518_;
v___y_3471_ = v___x_3516_;
v___y_3472_ = v___x_3519_;
v___y_3473_ = v___y_3462_;
v___y_3474_ = v___y_3463_;
goto v___jp_3465_;
}
else
{
uint8_t v___x_3520_; 
lean_inc(v_a_3512_);
v___x_3520_ = l_Lean_MessageData_hasTag(v___y_3502_, v_a_3512_);
if (v___x_3520_ == 0)
{
lean_object* v___x_3521_; lean_object* v___x_3523_; 
lean_dec_ref_known(v___x_3518_, 1);
lean_dec_ref(v___x_3516_);
lean_dec(v_a_3512_);
v___x_3521_ = lean_box(0);
if (v_isShared_3515_ == 0)
{
lean_ctor_set(v___x_3514_, 0, v___x_3521_);
v___x_3523_ = v___x_3514_;
goto v_reusejp_3522_;
}
else
{
lean_object* v_reuseFailAlloc_3524_; 
v_reuseFailAlloc_3524_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3524_, 0, v___x_3521_);
v___x_3523_ = v_reuseFailAlloc_3524_;
goto v_reusejp_3522_;
}
v_reusejp_3522_:
{
return v___x_3523_;
}
}
else
{
lean_del_object(v___x_3514_);
v___y_3466_ = v___y_3504_;
v___y_3467_ = v___y_3503_;
v___y_3468_ = v_a_3512_;
v___y_3469_ = v___y_3505_;
v___y_3470_ = v___x_3518_;
v___y_3471_ = v___x_3516_;
v___y_3472_ = v___x_3519_;
v___y_3473_ = v___y_3462_;
v___y_3474_ = v___y_3463_;
goto v___jp_3465_;
}
}
}
}
v___jp_3526_:
{
lean_object* v___x_3535_; 
v___x_3535_ = l_Lean_Syntax_getTailPos_x3f(v___y_3532_, v___y_3530_);
lean_dec(v___y_3532_);
if (lean_obj_tag(v___x_3535_) == 0)
{
lean_inc(v___y_3534_);
v___y_3502_ = v___y_3527_;
v___y_3503_ = v___y_3529_;
v___y_3504_ = v___y_3528_;
v___y_3505_ = v___y_3530_;
v___y_3506_ = v___y_3531_;
v___y_3507_ = v___y_3534_;
v___y_3508_ = v___y_3533_;
v___y_3509_ = v___y_3534_;
goto v___jp_3501_;
}
else
{
lean_object* v_val_3536_; 
v_val_3536_ = lean_ctor_get(v___x_3535_, 0);
lean_inc(v_val_3536_);
lean_dec_ref_known(v___x_3535_, 1);
v___y_3502_ = v___y_3527_;
v___y_3503_ = v___y_3529_;
v___y_3504_ = v___y_3528_;
v___y_3505_ = v___y_3530_;
v___y_3506_ = v___y_3531_;
v___y_3507_ = v___y_3534_;
v___y_3508_ = v___y_3533_;
v___y_3509_ = v_val_3536_;
goto v___jp_3501_;
}
}
v___jp_3537_:
{
lean_object* v_ref_3545_; lean_object* v___x_3546_; 
v_ref_3545_ = l_Lean_replaceRef(v_ref_3456_, v___y_3541_);
v___x_3546_ = l_Lean_Syntax_getPos_x3f(v_ref_3545_, v___y_3540_);
if (lean_obj_tag(v___x_3546_) == 0)
{
lean_object* v___x_3547_; 
v___x_3547_ = lean_unsigned_to_nat(0u);
v___y_3527_ = v___y_3538_;
v___y_3528_ = v___y_3544_;
v___y_3529_ = v___y_3539_;
v___y_3530_ = v___y_3540_;
v___y_3531_ = v___y_3542_;
v___y_3532_ = v_ref_3545_;
v___y_3533_ = v___y_3543_;
v___y_3534_ = v___x_3547_;
goto v___jp_3526_;
}
else
{
lean_object* v_val_3548_; 
v_val_3548_ = lean_ctor_get(v___x_3546_, 0);
lean_inc(v_val_3548_);
lean_dec_ref_known(v___x_3546_, 1);
v___y_3527_ = v___y_3538_;
v___y_3528_ = v___y_3544_;
v___y_3529_ = v___y_3539_;
v___y_3530_ = v___y_3540_;
v___y_3531_ = v___y_3542_;
v___y_3532_ = v_ref_3545_;
v___y_3533_ = v___y_3543_;
v___y_3534_ = v_val_3548_;
goto v___jp_3526_;
}
}
v___jp_3550_:
{
if (v___y_3557_ == 0)
{
v___y_3538_ = v___y_3555_;
v___y_3539_ = v___y_3551_;
v___y_3540_ = v___y_3556_;
v___y_3541_ = v___y_3552_;
v___y_3542_ = v___y_3553_;
v___y_3543_ = v___y_3554_;
v___y_3544_ = v_severity_3458_;
goto v___jp_3537_;
}
else
{
v___y_3538_ = v___y_3555_;
v___y_3539_ = v___y_3551_;
v___y_3540_ = v___y_3556_;
v___y_3541_ = v___y_3552_;
v___y_3542_ = v___y_3553_;
v___y_3543_ = v___y_3554_;
v___y_3544_ = v___x_3549_;
goto v___jp_3537_;
}
}
v___jp_3558_:
{
if (v___y_3559_ == 0)
{
lean_object* v_fileName_3560_; lean_object* v_fileMap_3561_; lean_object* v_options_3562_; lean_object* v_ref_3563_; uint8_t v_suppressElabErrors_3564_; lean_object* v___x_3565_; lean_object* v___x_3566_; lean_object* v___f_3567_; uint8_t v___x_3568_; uint8_t v___x_3569_; 
v_fileName_3560_ = lean_ctor_get(v___y_3462_, 0);
v_fileMap_3561_ = lean_ctor_get(v___y_3462_, 1);
v_options_3562_ = lean_ctor_get(v___y_3462_, 2);
v_ref_3563_ = lean_ctor_get(v___y_3462_, 5);
v_suppressElabErrors_3564_ = lean_ctor_get_uint8(v___y_3462_, sizeof(void*)*14 + 1);
v___x_3565_ = lean_box(v___y_3559_);
v___x_3566_ = lean_box(v_suppressElabErrors_3564_);
v___f_3567_ = lean_alloc_closure((void*)(l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___lam__0___boxed), 3, 2);
lean_closure_set(v___f_3567_, 0, v___x_3565_);
lean_closure_set(v___f_3567_, 1, v___x_3566_);
v___x_3568_ = 1;
v___x_3569_ = l_Lean_instBEqMessageSeverity_beq(v_severity_3458_, v___x_3568_);
if (v___x_3569_ == 0)
{
v___y_3551_ = v_fileName_3560_;
v___y_3552_ = v_ref_3563_;
v___y_3553_ = v_suppressElabErrors_3564_;
v___y_3554_ = v_fileMap_3561_;
v___y_3555_ = v___f_3567_;
v___y_3556_ = v___y_3559_;
v___y_3557_ = v___x_3569_;
goto v___jp_3550_;
}
else
{
lean_object* v___x_3570_; uint8_t v___x_3571_; 
v___x_3570_ = l_Lean_warningAsError;
v___x_3571_ = l_Lean_Option_get___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__4(v_options_3562_, v___x_3570_);
v___y_3551_ = v_fileName_3560_;
v___y_3552_ = v_ref_3563_;
v___y_3553_ = v_suppressElabErrors_3564_;
v___y_3554_ = v_fileMap_3561_;
v___y_3555_ = v___f_3567_;
v___y_3556_ = v___y_3559_;
v___y_3557_ = v___x_3571_;
goto v___jp_3550_;
}
}
else
{
lean_object* v___x_3572_; lean_object* v___x_3573_; 
lean_dec_ref(v_msgData_3457_);
v___x_3572_ = lean_box(0);
v___x_3573_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3573_, 0, v___x_3572_);
return v___x_3573_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5___boxed(lean_object* v_ref_3576_, lean_object* v_msgData_3577_, lean_object* v_severity_3578_, lean_object* v_isSilent_3579_, lean_object* v___y_3580_, lean_object* v___y_3581_, lean_object* v___y_3582_, lean_object* v___y_3583_, lean_object* v___y_3584_){
_start:
{
uint8_t v_severity_boxed_3585_; uint8_t v_isSilent_boxed_3586_; lean_object* v_res_3587_; 
v_severity_boxed_3585_ = lean_unbox(v_severity_3578_);
v_isSilent_boxed_3586_ = lean_unbox(v_isSilent_3579_);
v_res_3587_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3576_, v_msgData_3577_, v_severity_boxed_3585_, v_isSilent_boxed_3586_, v___y_3580_, v___y_3581_, v___y_3582_, v___y_3583_);
lean_dec(v___y_3583_);
lean_dec_ref(v___y_3582_);
lean_dec(v___y_3581_);
lean_dec_ref(v___y_3580_);
lean_dec(v_ref_3576_);
return v_res_3587_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(lean_object* v_msgData_3588_, uint8_t v_severity_3589_, uint8_t v_isSilent_3590_, lean_object* v___y_3591_, lean_object* v___y_3592_, lean_object* v___y_3593_, lean_object* v___y_3594_){
_start:
{
lean_object* v_ref_3596_; lean_object* v___x_3597_; 
v_ref_3596_ = lean_ctor_get(v___y_3593_, 5);
v___x_3597_ = l_Lean_logAt___at___00Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3_spec__5(v_ref_3596_, v_msgData_3588_, v_severity_3589_, v_isSilent_3590_, v___y_3591_, v___y_3592_, v___y_3593_, v___y_3594_);
return v___x_3597_;
}
}
LEAN_EXPORT lean_object* l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3___boxed(lean_object* v_msgData_3598_, lean_object* v_severity_3599_, lean_object* v_isSilent_3600_, lean_object* v___y_3601_, lean_object* v___y_3602_, lean_object* v___y_3603_, lean_object* v___y_3604_, lean_object* v___y_3605_){
_start:
{
uint8_t v_severity_boxed_3606_; uint8_t v_isSilent_boxed_3607_; lean_object* v_res_3608_; 
v_severity_boxed_3606_ = lean_unbox(v_severity_3599_);
v_isSilent_boxed_3607_ = lean_unbox(v_isSilent_3600_);
v_res_3608_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3598_, v_severity_boxed_3606_, v_isSilent_boxed_3607_, v___y_3601_, v___y_3602_, v___y_3603_, v___y_3604_);
lean_dec(v___y_3604_);
lean_dec_ref(v___y_3603_);
lean_dec(v___y_3602_);
lean_dec_ref(v___y_3601_);
return v_res_3608_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(lean_object* v_msgData_3609_, lean_object* v___y_3610_, lean_object* v___y_3611_, lean_object* v___y_3612_, lean_object* v___y_3613_){
_start:
{
uint8_t v___x_3615_; uint8_t v___x_3616_; lean_object* v___x_3617_; 
v___x_3615_ = 1;
v___x_3616_ = 0;
v___x_3617_ = l_Lean_log___at___00Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3_spec__3(v_msgData_3609_, v___x_3615_, v___x_3616_, v___y_3610_, v___y_3611_, v___y_3612_, v___y_3613_);
return v___x_3617_;
}
}
LEAN_EXPORT lean_object* l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3___boxed(lean_object* v_msgData_3618_, lean_object* v___y_3619_, lean_object* v___y_3620_, lean_object* v___y_3621_, lean_object* v___y_3622_, lean_object* v___y_3623_){
_start:
{
lean_object* v_res_3624_; 
v_res_3624_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v_msgData_3618_, v___y_3619_, v___y_3620_, v___y_3621_, v___y_3622_);
lean_dec(v___y_3622_);
lean_dec_ref(v___y_3621_);
lean_dec(v___y_3620_);
lean_dec_ref(v___y_3619_);
return v_res_3624_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3626_; lean_object* v___x_3627_; 
v___x_3626_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__0));
v___x_3627_ = l_Lean_stringToMessageData(v___x_3626_);
return v___x_3627_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3629_; lean_object* v___x_3630_; 
v___x_3629_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__2));
v___x_3630_ = l_Lean_stringToMessageData(v___x_3629_);
return v___x_3630_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4(void){
_start:
{
lean_object* v___x_3631_; lean_object* v___x_3632_; lean_object* v___x_3633_; 
v___x_3631_ = lean_box(0);
v___x_3632_ = lean_unsigned_to_nat(16u);
v___x_3633_ = lean_mk_array(v___x_3632_, v___x_3631_);
return v___x_3633_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3634_; lean_object* v___x_3635_; lean_object* v___x_3636_; 
v___x_3634_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__4);
v___x_3635_ = lean_unsigned_to_nat(0u);
v___x_3636_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3636_, 0, v___x_3635_);
lean_ctor_set(v___x_3636_, 1, v___x_3634_);
return v___x_3636_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_3639_; lean_object* v___x_3640_; lean_object* v___x_3641_; lean_object* v___x_3642_; 
v___x_3639_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__6));
v___x_3640_ = lean_box(1);
v___x_3641_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__5);
v___x_3642_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3642_, 0, v___x_3641_);
lean_ctor_set(v___x_3642_, 1, v___x_3640_);
lean_ctor_set(v___x_3642_, 2, v___x_3639_);
return v___x_3642_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11(void){
_start:
{
lean_object* v___x_3649_; lean_object* v___x_3650_; 
v___x_3649_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__10));
v___x_3650_ = l_Lean_stringToMessageData(v___x_3649_);
return v___x_3650_;
}
}
static lean_object* _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13(void){
_start:
{
lean_object* v___x_3652_; lean_object* v___x_3653_; 
v___x_3652_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__12));
v___x_3653_ = l_Lean_stringToMessageData(v___x_3652_);
return v___x_3653_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0(lean_object* v___x_3655_, lean_object* v_args_3656_, lean_object* v_ty_3657_, lean_object* v___y_3658_, lean_object* v___y_3659_, lean_object* v___y_3660_, lean_object* v___y_3661_){
_start:
{
lean_object* v___y_3664_; lean_object* v___y_3665_; lean_object* v___y_3666_; lean_object* v___x_3680_; lean_object* v___x_3681_; lean_object* v___x_3682_; lean_object* v___y_3738_; lean_object* v___x_3739_; 
v___x_3680_ = lean_unsigned_to_nat(0u);
v___x_3681_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__7);
v___x_3682_ = lean_st_mk_ref(v___x_3681_);
v___x_3739_ = l_Lean_Expr_collectFVars(v_ty_3657_, v___x_3682_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3739_) == 0)
{
lean_object* v___x_3740_; size_t v_sz_3741_; size_t v___x_3742_; lean_object* v___x_3743_; 
lean_dec_ref_known(v___x_3739_, 1);
v___x_3740_ = lean_box(0);
v_sz_3741_ = lean_array_size(v_args_3656_);
v___x_3742_ = ((size_t)0ULL);
v___x_3743_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_args_3656_, v_sz_3741_, v___x_3742_, v___x_3740_, v___x_3682_, v___y_3658_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3743_) == 0)
{
lean_dec_ref_known(v___x_3743_, 1);
goto v___jp_3683_;
}
else
{
v___y_3738_ = v___x_3743_;
goto v___jp_3737_;
}
}
else
{
v___y_3738_ = v___x_3739_;
goto v___jp_3737_;
}
v___jp_3663_:
{
lean_object* v___x_3667_; lean_object* v___x_3668_; lean_object* v___x_3669_; lean_object* v___x_3670_; lean_object* v___x_3671_; lean_object* v___x_3672_; lean_object* v___x_3673_; lean_object* v___x_3674_; lean_object* v___x_3675_; lean_object* v___x_3676_; uint8_t v___x_3677_; 
lean_inc_ref(v___y_3666_);
v___x_3667_ = l_Lean_stringToMessageData(v___y_3666_);
v___x_3668_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3668_, 0, v___y_3665_);
lean_ctor_set(v___x_3668_, 1, v___x_3667_);
v___x_3669_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__1);
v___x_3670_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3670_, 0, v___x_3668_);
lean_ctor_set(v___x_3670_, 1, v___x_3669_);
v___x_3671_ = lean_array_to_list(v___y_3664_);
v___x_3672_ = l_Lean_MessageData_nil;
v___x_3673_ = l_Lean_MessageData_joinSep(v___x_3671_, v___x_3672_);
v___x_3674_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3674_, 0, v___x_3670_);
lean_ctor_set(v___x_3674_, 1, v___x_3673_);
v___x_3675_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__3);
v___x_3676_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3676_, 0, v___x_3674_);
lean_ctor_set(v___x_3676_, 1, v___x_3675_);
v___x_3677_ = l_Lean_Expr_hasSorry(v___x_3655_);
if (v___x_3677_ == 0)
{
lean_object* v___x_3678_; 
v___x_3678_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3676_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
return v___x_3678_;
}
else
{
lean_object* v___x_3679_; 
v___x_3679_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_3676_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
return v___x_3679_;
}
}
v___jp_3683_:
{
lean_object* v___x_3684_; lean_object* v___x_3685_; 
v___x_3684_ = lean_st_ref_get(v___x_3682_);
lean_dec(v___x_3682_);
v___x_3685_ = l_Lean_CollectFVars_State_addDependencies(v___x_3684_, v___y_3658_, v___y_3659_, v___y_3660_, v___y_3661_);
if (lean_obj_tag(v___x_3685_) == 0)
{
lean_object* v_a_3686_; lean_object* v___x_3687_; lean_object* v___x_3688_; size_t v_sz_3689_; size_t v___x_3690_; lean_object* v___x_3691_; 
v_a_3686_ = lean_ctor_get(v___x_3685_, 0);
lean_inc(v_a_3686_);
lean_dec_ref_known(v___x_3685_, 1);
v___x_3687_ = lean_unsigned_to_nat(1u);
v___x_3688_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__9));
v_sz_3689_ = lean_array_size(v_args_3656_);
v___x_3690_ = ((size_t)0ULL);
v___x_3691_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3686_, v_args_3656_, v_sz_3689_, v___x_3690_, v___x_3688_, v___y_3658_, v___y_3660_, v___y_3661_);
lean_dec(v_a_3686_);
if (lean_obj_tag(v___x_3691_) == 0)
{
lean_object* v_a_3692_; lean_object* v___x_3694_; uint8_t v_isShared_3695_; uint8_t v_isSharedCheck_3720_; 
v_a_3692_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3720_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3720_ == 0)
{
v___x_3694_ = v___x_3691_;
v_isShared_3695_ = v_isSharedCheck_3720_;
goto v_resetjp_3693_;
}
else
{
lean_inc(v_a_3692_);
lean_dec(v___x_3691_);
v___x_3694_ = lean_box(0);
v_isShared_3695_ = v_isSharedCheck_3720_;
goto v_resetjp_3693_;
}
v_resetjp_3693_:
{
lean_object* v_fst_3696_; lean_object* v___x_3698_; uint8_t v_isShared_3699_; uint8_t v_isSharedCheck_3718_; 
v_fst_3696_ = lean_ctor_get(v_a_3692_, 0);
v_isSharedCheck_3718_ = !lean_is_exclusive(v_a_3692_);
if (v_isSharedCheck_3718_ == 0)
{
lean_object* v_unused_3719_; 
v_unused_3719_ = lean_ctor_get(v_a_3692_, 1);
lean_dec(v_unused_3719_);
v___x_3698_ = v_a_3692_;
v_isShared_3699_ = v_isSharedCheck_3718_;
goto v_resetjp_3697_;
}
else
{
lean_inc(v_fst_3696_);
lean_dec(v_a_3692_);
v___x_3698_ = lean_box(0);
v_isShared_3699_ = v_isSharedCheck_3718_;
goto v_resetjp_3697_;
}
v_resetjp_3697_:
{
lean_object* v___x_3700_; uint8_t v___x_3701_; 
v___x_3700_ = lean_array_get_size(v_fst_3696_);
v___x_3701_ = lean_nat_dec_eq(v___x_3700_, v___x_3680_);
if (v___x_3701_ == 0)
{
lean_object* v___x_3702_; lean_object* v___x_3703_; lean_object* v___x_3704_; lean_object* v___x_3705_; lean_object* v___x_3707_; 
lean_del_object(v___x_3694_);
v___x_3702_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__11);
v___x_3703_ = l_Nat_reprFast(v___x_3700_);
v___x_3704_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3704_, 0, v___x_3703_);
v___x_3705_ = l_Lean_MessageData_ofFormat(v___x_3704_);
if (v_isShared_3699_ == 0)
{
lean_ctor_set_tag(v___x_3698_, 7);
lean_ctor_set(v___x_3698_, 1, v___x_3705_);
lean_ctor_set(v___x_3698_, 0, v___x_3702_);
v___x_3707_ = v___x_3698_;
goto v_reusejp_3706_;
}
else
{
lean_object* v_reuseFailAlloc_3713_; 
v_reuseFailAlloc_3713_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3713_, 0, v___x_3702_);
lean_ctor_set(v_reuseFailAlloc_3713_, 1, v___x_3705_);
v___x_3707_ = v_reuseFailAlloc_3713_;
goto v_reusejp_3706_;
}
v_reusejp_3706_:
{
lean_object* v___x_3708_; lean_object* v___x_3709_; uint8_t v___x_3710_; 
v___x_3708_ = lean_obj_once(&l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13, &l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13_once, _init_l_Lean_Meta_checkImpossibleInstance___lam__0___closed__13);
v___x_3709_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3709_, 0, v___x_3707_);
lean_ctor_set(v___x_3709_, 1, v___x_3708_);
v___x_3710_ = lean_nat_dec_eq(v___x_3700_, v___x_3687_);
if (v___x_3710_ == 0)
{
lean_object* v___x_3711_; 
v___x_3711_ = ((lean_object*)(l_Lean_Meta_checkImpossibleInstance___lam__0___closed__14));
v___y_3664_ = v_fst_3696_;
v___y_3665_ = v___x_3709_;
v___y_3666_ = v___x_3711_;
goto v___jp_3663_;
}
else
{
lean_object* v___x_3712_; 
v___x_3712_ = ((lean_object*)(l___private_Init_While_0__repeatM_erased___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__10___redArg___closed__0));
v___y_3664_ = v_fst_3696_;
v___y_3665_ = v___x_3709_;
v___y_3666_ = v___x_3712_;
goto v___jp_3663_;
}
}
}
else
{
lean_object* v___x_3714_; lean_object* v___x_3716_; 
lean_del_object(v___x_3698_);
lean_dec(v_fst_3696_);
v___x_3714_ = lean_box(0);
if (v_isShared_3695_ == 0)
{
lean_ctor_set(v___x_3694_, 0, v___x_3714_);
v___x_3716_ = v___x_3694_;
goto v_reusejp_3715_;
}
else
{
lean_object* v_reuseFailAlloc_3717_; 
v_reuseFailAlloc_3717_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3717_, 0, v___x_3714_);
v___x_3716_ = v_reuseFailAlloc_3717_;
goto v_reusejp_3715_;
}
v_reusejp_3715_:
{
return v___x_3716_;
}
}
}
}
}
else
{
lean_object* v_a_3721_; lean_object* v___x_3723_; uint8_t v_isShared_3724_; uint8_t v_isSharedCheck_3728_; 
v_a_3721_ = lean_ctor_get(v___x_3691_, 0);
v_isSharedCheck_3728_ = !lean_is_exclusive(v___x_3691_);
if (v_isSharedCheck_3728_ == 0)
{
v___x_3723_ = v___x_3691_;
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
else
{
lean_inc(v_a_3721_);
lean_dec(v___x_3691_);
v___x_3723_ = lean_box(0);
v_isShared_3724_ = v_isSharedCheck_3728_;
goto v_resetjp_3722_;
}
v_resetjp_3722_:
{
lean_object* v___x_3726_; 
if (v_isShared_3724_ == 0)
{
v___x_3726_ = v___x_3723_;
goto v_reusejp_3725_;
}
else
{
lean_object* v_reuseFailAlloc_3727_; 
v_reuseFailAlloc_3727_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3727_, 0, v_a_3721_);
v___x_3726_ = v_reuseFailAlloc_3727_;
goto v_reusejp_3725_;
}
v_reusejp_3725_:
{
return v___x_3726_;
}
}
}
}
else
{
lean_object* v_a_3729_; lean_object* v___x_3731_; uint8_t v_isShared_3732_; uint8_t v_isSharedCheck_3736_; 
v_a_3729_ = lean_ctor_get(v___x_3685_, 0);
v_isSharedCheck_3736_ = !lean_is_exclusive(v___x_3685_);
if (v_isSharedCheck_3736_ == 0)
{
v___x_3731_ = v___x_3685_;
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
else
{
lean_inc(v_a_3729_);
lean_dec(v___x_3685_);
v___x_3731_ = lean_box(0);
v_isShared_3732_ = v_isSharedCheck_3736_;
goto v_resetjp_3730_;
}
v_resetjp_3730_:
{
lean_object* v___x_3734_; 
if (v_isShared_3732_ == 0)
{
v___x_3734_ = v___x_3731_;
goto v_reusejp_3733_;
}
else
{
lean_object* v_reuseFailAlloc_3735_; 
v_reuseFailAlloc_3735_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3735_, 0, v_a_3729_);
v___x_3734_ = v_reuseFailAlloc_3735_;
goto v_reusejp_3733_;
}
v_reusejp_3733_:
{
return v___x_3734_;
}
}
}
}
v___jp_3737_:
{
if (lean_obj_tag(v___y_3738_) == 0)
{
lean_dec_ref_known(v___y_3738_, 1);
goto v___jp_3683_;
}
else
{
lean_dec(v___x_3682_);
return v___y_3738_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___lam__0___boxed(lean_object* v___x_3744_, lean_object* v_args_3745_, lean_object* v_ty_3746_, lean_object* v___y_3747_, lean_object* v___y_3748_, lean_object* v___y_3749_, lean_object* v___y_3750_, lean_object* v___y_3751_){
_start:
{
lean_object* v_res_3752_; 
v_res_3752_ = l_Lean_Meta_checkImpossibleInstance___lam__0(v___x_3744_, v_args_3745_, v_ty_3746_, v___y_3747_, v___y_3748_, v___y_3749_, v___y_3750_);
lean_dec(v___y_3750_);
lean_dec_ref(v___y_3749_);
lean_dec(v___y_3748_);
lean_dec_ref(v___y_3747_);
lean_dec_ref(v_args_3745_);
lean_dec_ref(v___x_3744_);
return v_res_3752_;
}
}
LEAN_EXPORT uint8_t l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(lean_object* v_e_3753_){
_start:
{
lean_object* v___x_3754_; 
v___x_3754_ = l_Lean_Expr_cleanupAnnotations(v_e_3753_);
switch(lean_obj_tag(v___x_3754_))
{
case 7:
{
lean_object* v_body_3755_; uint8_t v_binderInfo_3756_; uint8_t v___x_3757_; uint8_t v___x_3758_; 
v_body_3755_ = lean_ctor_get(v___x_3754_, 2);
lean_inc_ref(v_body_3755_);
v_binderInfo_3756_ = lean_ctor_get_uint8(v___x_3754_, sizeof(void*)*3 + 8);
lean_dec_ref_known(v___x_3754_, 3);
v___x_3757_ = l_Lean_BinderInfo_isInstImplicit(v_binderInfo_3756_);
v___x_3758_ = lean_bool_not(v___x_3757_);
if (v___x_3758_ == 0)
{
v_e_3753_ = v_body_3755_;
goto _start;
}
else
{
lean_object* v___x_3760_; uint8_t v___x_3761_; uint8_t v___x_3762_; 
v___x_3760_ = lean_unsigned_to_nat(0u);
v___x_3761_ = lean_expr_has_loose_bvar(v_body_3755_, v___x_3760_);
v___x_3762_ = lean_bool_not(v___x_3761_);
if (v___x_3762_ == 0)
{
v_e_3753_ = v_body_3755_;
goto _start;
}
else
{
lean_dec_ref(v_body_3755_);
return v___x_3762_;
}
}
}
case 8:
{
lean_object* v_body_3764_; 
v_body_3764_ = lean_ctor_get(v___x_3754_, 3);
lean_inc_ref(v_body_3764_);
lean_dec_ref_known(v___x_3754_, 4);
v_e_3753_ = v_body_3764_;
goto _start;
}
default: 
{
uint8_t v___x_3766_; 
lean_dec_ref(v___x_3754_);
v___x_3766_ = 0;
return v___x_3766_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0___boxed(lean_object* v_e_3767_){
_start:
{
uint8_t v_res_3768_; lean_object* v_r_3769_; 
v_res_3768_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(v_e_3767_);
v_r_3769_ = lean_box(v_res_3768_);
return v_r_3769_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance(lean_object* v_cinfo_3770_, lean_object* v_a_3771_, lean_object* v_a_3772_, lean_object* v_a_3773_, lean_object* v_a_3774_){
_start:
{
lean_object* v___x_3776_; uint8_t v___x_3777_; 
v___x_3776_ = l_Lean_ConstantInfo_type(v_cinfo_3770_);
lean_inc_ref(v___x_3776_);
v___x_3777_ = l_Lean_Expr_hasUnusedForallBindersWhere___at___00Lean_Meta_checkImpossibleInstance_spec__0(v___x_3776_);
if (v___x_3777_ == 0)
{
lean_object* v___x_3778_; lean_object* v___x_3779_; 
lean_dec_ref(v___x_3776_);
v___x_3778_ = lean_box(0);
v___x_3779_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3779_, 0, v___x_3778_);
return v___x_3779_;
}
else
{
lean_object* v___f_3780_; uint8_t v___x_3781_; lean_object* v___x_3782_; 
lean_inc_ref(v___x_3776_);
v___f_3780_ = lean_alloc_closure((void*)(l_Lean_Meta_checkImpossibleInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3780_, 0, v___x_3776_);
v___x_3781_ = 0;
v___x_3782_ = l_Lean_Meta_forallTelescope___at___00Lean_Meta_checkImpossibleInstance_spec__5___redArg(v___x_3776_, v___f_3780_, v___x_3781_, v_a_3771_, v_a_3772_, v_a_3773_, v_a_3774_);
return v___x_3782_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkImpossibleInstance___boxed(lean_object* v_cinfo_3783_, lean_object* v_a_3784_, lean_object* v_a_3785_, lean_object* v_a_3786_, lean_object* v_a_3787_, lean_object* v_a_3788_){
_start:
{
lean_object* v_res_3789_; 
v_res_3789_ = l_Lean_Meta_checkImpossibleInstance(v_cinfo_3783_, v_a_3784_, v_a_3785_, v_a_3786_, v_a_3787_);
lean_dec(v_a_3787_);
lean_dec_ref(v_a_3786_);
lean_dec(v_a_3785_);
lean_dec_ref(v_a_3784_);
lean_dec_ref(v_cinfo_3783_);
return v_res_3789_;
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(lean_object* v_00_u03b2_3790_, lean_object* v_k_3791_, lean_object* v_t_3792_){
_start:
{
uint8_t v___x_3793_; 
v___x_3793_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___redArg(v_k_3791_, v_t_3792_);
return v___x_3793_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1___boxed(lean_object* v_00_u03b2_3794_, lean_object* v_k_3795_, lean_object* v_t_3796_){
_start:
{
uint8_t v_res_3797_; lean_object* v_r_3798_; 
v_res_3797_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_checkImpossibleInstance_spec__1(v_00_u03b2_3794_, v_k_3795_, v_t_3796_);
lean_dec(v_t_3796_);
lean_dec(v_k_3795_);
v_r_3798_ = lean_box(v_res_3797_);
return v_r_3798_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(lean_object* v_a_3799_, lean_object* v_as_3800_, size_t v_sz_3801_, size_t v_i_3802_, lean_object* v_b_3803_, lean_object* v___y_3804_, lean_object* v___y_3805_, lean_object* v___y_3806_, lean_object* v___y_3807_){
_start:
{
lean_object* v___x_3809_; 
v___x_3809_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___redArg(v_a_3799_, v_as_3800_, v_sz_3801_, v_i_3802_, v_b_3803_, v___y_3804_, v___y_3806_, v___y_3807_);
return v___x_3809_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2___boxed(lean_object* v_a_3810_, lean_object* v_as_3811_, lean_object* v_sz_3812_, lean_object* v_i_3813_, lean_object* v_b_3814_, lean_object* v___y_3815_, lean_object* v___y_3816_, lean_object* v___y_3817_, lean_object* v___y_3818_, lean_object* v___y_3819_){
_start:
{
size_t v_sz_boxed_3820_; size_t v_i_boxed_3821_; lean_object* v_res_3822_; 
v_sz_boxed_3820_ = lean_unbox_usize(v_sz_3812_);
lean_dec(v_sz_3812_);
v_i_boxed_3821_ = lean_unbox_usize(v_i_3813_);
lean_dec(v_i_3813_);
v_res_3822_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__2(v_a_3810_, v_as_3811_, v_sz_boxed_3820_, v_i_boxed_3821_, v_b_3814_, v___y_3815_, v___y_3816_, v___y_3817_, v___y_3818_);
lean_dec(v___y_3818_);
lean_dec_ref(v___y_3817_);
lean_dec(v___y_3816_);
lean_dec_ref(v___y_3815_);
lean_dec_ref(v_as_3811_);
lean_dec_ref(v_a_3810_);
return v_res_3822_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(lean_object* v_as_3823_, size_t v_sz_3824_, size_t v_i_3825_, lean_object* v_b_3826_, lean_object* v___y_3827_, lean_object* v___y_3828_, lean_object* v___y_3829_, lean_object* v___y_3830_, lean_object* v___y_3831_){
_start:
{
lean_object* v___x_3833_; 
v___x_3833_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___redArg(v_as_3823_, v_sz_3824_, v_i_3825_, v_b_3826_, v___y_3827_, v___y_3828_, v___y_3830_, v___y_3831_);
return v___x_3833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4___boxed(lean_object* v_as_3834_, lean_object* v_sz_3835_, lean_object* v_i_3836_, lean_object* v_b_3837_, lean_object* v___y_3838_, lean_object* v___y_3839_, lean_object* v___y_3840_, lean_object* v___y_3841_, lean_object* v___y_3842_, lean_object* v___y_3843_){
_start:
{
size_t v_sz_boxed_3844_; size_t v_i_boxed_3845_; lean_object* v_res_3846_; 
v_sz_boxed_3844_ = lean_unbox_usize(v_sz_3835_);
lean_dec(v_sz_3835_);
v_i_boxed_3845_ = lean_unbox_usize(v_i_3836_);
lean_dec(v_i_3836_);
v_res_3846_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Meta_checkImpossibleInstance_spec__4(v_as_3834_, v_sz_boxed_3844_, v_i_boxed_3845_, v_b_3837_, v___y_3838_, v___y_3839_, v___y_3840_, v___y_3841_, v___y_3842_);
lean_dec(v___y_3842_);
lean_dec_ref(v___y_3841_);
lean_dec(v___y_3840_);
lean_dec_ref(v___y_3839_);
lean_dec(v___y_3838_);
lean_dec_ref(v_as_3834_);
return v_res_3846_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_3848_; lean_object* v___x_3849_; 
v___x_3848_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__0));
v___x_3849_ = l_Lean_stringToMessageData(v___x_3848_);
return v___x_3849_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_3851_; lean_object* v___x_3852_; 
v___x_3851_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__2));
v___x_3852_ = l_Lean_stringToMessageData(v___x_3851_);
return v___x_3852_;
}
}
static lean_object* _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_3854_; lean_object* v___x_3855_; 
v___x_3854_ = ((lean_object*)(l_Lean_Meta_checkNonClassInstance___lam__0___closed__4));
v___x_3855_ = l_Lean_stringToMessageData(v___x_3854_);
return v___x_3855_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0(lean_object* v_c_3856_, lean_object* v_x_3857_, lean_object* v_target_3858_, lean_object* v___y_3859_, lean_object* v___y_3860_, lean_object* v___y_3861_, lean_object* v___y_3862_){
_start:
{
lean_object* v___x_3864_; 
lean_inc_ref(v_target_3858_);
v___x_3864_ = l_Lean_Meta_isClass_x3f(v_target_3858_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
if (lean_obj_tag(v___x_3864_) == 0)
{
lean_object* v_a_3865_; lean_object* v___x_3867_; uint8_t v_isShared_3868_; uint8_t v_isSharedCheck_3883_; 
v_a_3865_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3883_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3883_ == 0)
{
v___x_3867_ = v___x_3864_;
v_isShared_3868_ = v_isSharedCheck_3883_;
goto v_resetjp_3866_;
}
else
{
lean_inc(v_a_3865_);
lean_dec(v___x_3864_);
v___x_3867_ = lean_box(0);
v_isShared_3868_ = v_isSharedCheck_3883_;
goto v_resetjp_3866_;
}
v_resetjp_3866_:
{
if (lean_obj_tag(v_a_3865_) == 0)
{
lean_object* v___x_3869_; lean_object* v___x_3870_; lean_object* v___x_3871_; lean_object* v___x_3872_; lean_object* v___x_3873_; lean_object* v___x_3874_; lean_object* v___x_3875_; lean_object* v___x_3876_; lean_object* v___x_3877_; lean_object* v___x_3878_; 
lean_del_object(v___x_3867_);
v___x_3869_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__1, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__1_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__1);
v___x_3870_ = l_Lean_MessageData_ofExpr(v_c_3856_);
v___x_3871_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3871_, 0, v___x_3869_);
lean_ctor_set(v___x_3871_, 1, v___x_3870_);
v___x_3872_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__3, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__3_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__3);
v___x_3873_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3873_, 0, v___x_3871_);
lean_ctor_set(v___x_3873_, 1, v___x_3872_);
v___x_3874_ = l_Lean_MessageData_ofExpr(v_target_3858_);
v___x_3875_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3875_, 0, v___x_3873_);
lean_ctor_set(v___x_3875_, 1, v___x_3874_);
v___x_3876_ = lean_obj_once(&l_Lean_Meta_checkNonClassInstance___lam__0___closed__5, &l_Lean_Meta_checkNonClassInstance___lam__0___closed__5_once, _init_l_Lean_Meta_checkNonClassInstance___lam__0___closed__5);
v___x_3877_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_3877_, 0, v___x_3875_);
lean_ctor_set(v___x_3877_, 1, v___x_3876_);
v___x_3878_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_3877_, v___y_3859_, v___y_3860_, v___y_3861_, v___y_3862_);
return v___x_3878_;
}
else
{
lean_object* v___x_3879_; lean_object* v___x_3881_; 
lean_dec_ref_known(v_a_3865_, 1);
lean_dec_ref(v_target_3858_);
lean_dec_ref(v_c_3856_);
v___x_3879_ = lean_box(0);
if (v_isShared_3868_ == 0)
{
lean_ctor_set(v___x_3867_, 0, v___x_3879_);
v___x_3881_ = v___x_3867_;
goto v_reusejp_3880_;
}
else
{
lean_object* v_reuseFailAlloc_3882_; 
v_reuseFailAlloc_3882_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3882_, 0, v___x_3879_);
v___x_3881_ = v_reuseFailAlloc_3882_;
goto v_reusejp_3880_;
}
v_reusejp_3880_:
{
return v___x_3881_;
}
}
}
}
else
{
lean_object* v_a_3884_; lean_object* v___x_3886_; uint8_t v_isShared_3887_; uint8_t v_isSharedCheck_3891_; 
lean_dec_ref(v_target_3858_);
lean_dec_ref(v_c_3856_);
v_a_3884_ = lean_ctor_get(v___x_3864_, 0);
v_isSharedCheck_3891_ = !lean_is_exclusive(v___x_3864_);
if (v_isSharedCheck_3891_ == 0)
{
v___x_3886_ = v___x_3864_;
v_isShared_3887_ = v_isSharedCheck_3891_;
goto v_resetjp_3885_;
}
else
{
lean_inc(v_a_3884_);
lean_dec(v___x_3864_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___lam__0___boxed(lean_object* v_c_3892_, lean_object* v_x_3893_, lean_object* v_target_3894_, lean_object* v___y_3895_, lean_object* v___y_3896_, lean_object* v___y_3897_, lean_object* v___y_3898_, lean_object* v___y_3899_){
_start:
{
lean_object* v_res_3900_; 
v_res_3900_ = l_Lean_Meta_checkNonClassInstance___lam__0(v_c_3892_, v_x_3893_, v_target_3894_, v___y_3895_, v___y_3896_, v___y_3897_, v___y_3898_);
lean_dec(v___y_3898_);
lean_dec_ref(v___y_3897_);
lean_dec(v___y_3896_);
lean_dec_ref(v___y_3895_);
lean_dec_ref(v_x_3893_);
return v_res_3900_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance(lean_object* v_c_3901_, lean_object* v_a_3902_, lean_object* v_a_3903_, lean_object* v_a_3904_, lean_object* v_a_3905_){
_start:
{
lean_object* v___x_3907_; 
lean_inc(v_a_3905_);
lean_inc_ref(v_a_3904_);
lean_inc(v_a_3903_);
lean_inc_ref(v_a_3902_);
lean_inc_ref(v_c_3901_);
v___x_3907_ = lean_infer_type(v_c_3901_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
if (lean_obj_tag(v___x_3907_) == 0)
{
lean_object* v_a_3908_; lean_object* v___f_3909_; uint8_t v___x_3910_; lean_object* v___x_3911_; 
v_a_3908_ = lean_ctor_get(v___x_3907_, 0);
lean_inc(v_a_3908_);
lean_dec_ref_known(v___x_3907_, 1);
v___f_3909_ = lean_alloc_closure((void*)(l_Lean_Meta_checkNonClassInstance___lam__0___boxed), 8, 1);
lean_closure_set(v___f_3909_, 0, v_c_3901_);
v___x_3910_ = 0;
v___x_3911_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v_a_3908_, v___f_3909_, v___x_3910_, v___x_3910_, v_a_3902_, v_a_3903_, v_a_3904_, v_a_3905_);
return v___x_3911_;
}
else
{
lean_object* v_a_3912_; lean_object* v___x_3914_; uint8_t v_isShared_3915_; uint8_t v_isSharedCheck_3919_; 
lean_dec_ref(v_c_3901_);
v_a_3912_ = lean_ctor_get(v___x_3907_, 0);
v_isSharedCheck_3919_ = !lean_is_exclusive(v___x_3907_);
if (v_isSharedCheck_3919_ == 0)
{
v___x_3914_ = v___x_3907_;
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
else
{
lean_inc(v_a_3912_);
lean_dec(v___x_3907_);
v___x_3914_ = lean_box(0);
v_isShared_3915_ = v_isSharedCheck_3919_;
goto v_resetjp_3913_;
}
v_resetjp_3913_:
{
lean_object* v___x_3917_; 
if (v_isShared_3915_ == 0)
{
v___x_3917_ = v___x_3914_;
goto v_reusejp_3916_;
}
else
{
lean_object* v_reuseFailAlloc_3918_; 
v_reuseFailAlloc_3918_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3918_, 0, v_a_3912_);
v___x_3917_ = v_reuseFailAlloc_3918_;
goto v_reusejp_3916_;
}
v_reusejp_3916_:
{
return v___x_3917_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_checkNonClassInstance___boxed(lean_object* v_c_3920_, lean_object* v_a_3921_, lean_object* v_a_3922_, lean_object* v_a_3923_, lean_object* v_a_3924_, lean_object* v_a_3925_){
_start:
{
lean_object* v_res_3926_; 
v_res_3926_ = l_Lean_Meta_checkNonClassInstance(v_c_3920_, v_a_3921_, v_a_3922_, v_a_3923_, v_a_3924_);
lean_dec(v_a_3924_);
lean_dec_ref(v_a_3923_);
lean_dec(v_a_3922_);
lean_dec_ref(v_a_3921_);
return v_res_3926_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(lean_object* v_declName_3927_, lean_object* v___y_3928_){
_start:
{
lean_object* v___x_3930_; lean_object* v_env_3931_; lean_object* v___x_3932_; lean_object* v___x_3933_; 
v___x_3930_ = lean_st_ref_get(v___y_3928_);
v_env_3931_ = lean_ctor_get(v___x_3930_, 0);
lean_inc_ref(v_env_3931_);
lean_dec(v___x_3930_);
v___x_3932_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_3931_, v_declName_3927_);
v___x_3933_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3933_, 0, v___x_3932_);
return v___x_3933_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg___boxed(lean_object* v_declName_3934_, lean_object* v___y_3935_, lean_object* v___y_3936_){
_start:
{
lean_object* v_res_3937_; 
v_res_3937_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3934_, v___y_3935_);
lean_dec(v___y_3935_);
return v_res_3937_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(lean_object* v_declName_3938_, lean_object* v___y_3939_, lean_object* v___y_3940_, lean_object* v___y_3941_, lean_object* v___y_3942_){
_start:
{
lean_object* v___x_3944_; 
v___x_3944_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_3938_, v___y_3942_);
return v___x_3944_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___boxed(lean_object* v_declName_3945_, lean_object* v___y_3946_, lean_object* v___y_3947_, lean_object* v___y_3948_, lean_object* v___y_3949_, lean_object* v___y_3950_){
_start:
{
lean_object* v_res_3951_; 
v_res_3951_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1(v_declName_3945_, v___y_3946_, v___y_3947_, v___y_3948_, v___y_3949_);
lean_dec(v___y_3949_);
lean_dec_ref(v___y_3948_);
lean_dec(v___y_3947_);
lean_dec_ref(v___y_3946_);
return v_res_3951_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0(void){
_start:
{
lean_object* v___x_3952_; 
v___x_3952_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_3952_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1(void){
_start:
{
lean_object* v___x_3953_; lean_object* v___x_3954_; 
v___x_3953_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__0);
v___x_3954_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3954_, 0, v___x_3953_);
return v___x_3954_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2(void){
_start:
{
lean_object* v___x_3955_; lean_object* v___x_3956_; 
v___x_3955_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3956_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3956_, 0, v___x_3955_);
lean_ctor_set(v___x_3956_, 1, v___x_3955_);
return v___x_3956_;
}
}
static lean_object* _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3(void){
_start:
{
lean_object* v___x_3957_; lean_object* v___x_3958_; 
v___x_3957_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__1);
v___x_3958_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_3958_, 0, v___x_3957_);
lean_ctor_set(v___x_3958_, 1, v___x_3957_);
lean_ctor_set(v___x_3958_, 2, v___x_3957_);
lean_ctor_set(v___x_3958_, 3, v___x_3957_);
lean_ctor_set(v___x_3958_, 4, v___x_3957_);
lean_ctor_set(v___x_3958_, 5, v___x_3957_);
return v___x_3958_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(lean_object* v_ext_3959_, lean_object* v_b_3960_, uint8_t v_kind_3961_, lean_object* v___y_3962_, lean_object* v___y_3963_, lean_object* v___y_3964_){
_start:
{
lean_object* v_currNamespace_3966_; lean_object* v___x_3967_; lean_object* v_env_3968_; lean_object* v_nextMacroScope_3969_; lean_object* v_ngen_3970_; lean_object* v_auxDeclNGen_3971_; lean_object* v_traceState_3972_; lean_object* v_messages_3973_; lean_object* v_infoState_3974_; lean_object* v_snapshotTasks_3975_; lean_object* v___x_3977_; uint8_t v_isShared_3978_; uint8_t v_isSharedCheck_4002_; 
v_currNamespace_3966_ = lean_ctor_get(v___y_3963_, 6);
v___x_3967_ = lean_st_ref_take(v___y_3964_);
v_env_3968_ = lean_ctor_get(v___x_3967_, 0);
v_nextMacroScope_3969_ = lean_ctor_get(v___x_3967_, 1);
v_ngen_3970_ = lean_ctor_get(v___x_3967_, 2);
v_auxDeclNGen_3971_ = lean_ctor_get(v___x_3967_, 3);
v_traceState_3972_ = lean_ctor_get(v___x_3967_, 4);
v_messages_3973_ = lean_ctor_get(v___x_3967_, 6);
v_infoState_3974_ = lean_ctor_get(v___x_3967_, 7);
v_snapshotTasks_3975_ = lean_ctor_get(v___x_3967_, 8);
v_isSharedCheck_4002_ = !lean_is_exclusive(v___x_3967_);
if (v_isSharedCheck_4002_ == 0)
{
lean_object* v_unused_4003_; 
v_unused_4003_ = lean_ctor_get(v___x_3967_, 5);
lean_dec(v_unused_4003_);
v___x_3977_ = v___x_3967_;
v_isShared_3978_ = v_isSharedCheck_4002_;
goto v_resetjp_3976_;
}
else
{
lean_inc(v_snapshotTasks_3975_);
lean_inc(v_infoState_3974_);
lean_inc(v_messages_3973_);
lean_inc(v_traceState_3972_);
lean_inc(v_auxDeclNGen_3971_);
lean_inc(v_ngen_3970_);
lean_inc(v_nextMacroScope_3969_);
lean_inc(v_env_3968_);
lean_dec(v___x_3967_);
v___x_3977_ = lean_box(0);
v_isShared_3978_ = v_isSharedCheck_4002_;
goto v_resetjp_3976_;
}
v_resetjp_3976_:
{
lean_object* v___x_3979_; lean_object* v___x_3980_; lean_object* v___x_3982_; 
lean_inc(v_currNamespace_3966_);
v___x_3979_ = l_Lean_ScopedEnvExtension_addCore___redArg(v_env_3968_, v_ext_3959_, v_b_3960_, v_kind_3961_, v_currNamespace_3966_);
v___x_3980_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_3978_ == 0)
{
lean_ctor_set(v___x_3977_, 5, v___x_3980_);
lean_ctor_set(v___x_3977_, 0, v___x_3979_);
v___x_3982_ = v___x_3977_;
goto v_reusejp_3981_;
}
else
{
lean_object* v_reuseFailAlloc_4001_; 
v_reuseFailAlloc_4001_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4001_, 0, v___x_3979_);
lean_ctor_set(v_reuseFailAlloc_4001_, 1, v_nextMacroScope_3969_);
lean_ctor_set(v_reuseFailAlloc_4001_, 2, v_ngen_3970_);
lean_ctor_set(v_reuseFailAlloc_4001_, 3, v_auxDeclNGen_3971_);
lean_ctor_set(v_reuseFailAlloc_4001_, 4, v_traceState_3972_);
lean_ctor_set(v_reuseFailAlloc_4001_, 5, v___x_3980_);
lean_ctor_set(v_reuseFailAlloc_4001_, 6, v_messages_3973_);
lean_ctor_set(v_reuseFailAlloc_4001_, 7, v_infoState_3974_);
lean_ctor_set(v_reuseFailAlloc_4001_, 8, v_snapshotTasks_3975_);
v___x_3982_ = v_reuseFailAlloc_4001_;
goto v_reusejp_3981_;
}
v_reusejp_3981_:
{
lean_object* v___x_3983_; lean_object* v___x_3984_; lean_object* v_mctx_3985_; lean_object* v_zetaDeltaFVarIds_3986_; lean_object* v_postponed_3987_; lean_object* v_diag_3988_; lean_object* v___x_3990_; uint8_t v_isShared_3991_; uint8_t v_isSharedCheck_3999_; 
v___x_3983_ = lean_st_ref_set(v___y_3964_, v___x_3982_);
v___x_3984_ = lean_st_ref_take(v___y_3962_);
v_mctx_3985_ = lean_ctor_get(v___x_3984_, 0);
v_zetaDeltaFVarIds_3986_ = lean_ctor_get(v___x_3984_, 2);
v_postponed_3987_ = lean_ctor_get(v___x_3984_, 3);
v_diag_3988_ = lean_ctor_get(v___x_3984_, 4);
v_isSharedCheck_3999_ = !lean_is_exclusive(v___x_3984_);
if (v_isSharedCheck_3999_ == 0)
{
lean_object* v_unused_4000_; 
v_unused_4000_ = lean_ctor_get(v___x_3984_, 1);
lean_dec(v_unused_4000_);
v___x_3990_ = v___x_3984_;
v_isShared_3991_ = v_isSharedCheck_3999_;
goto v_resetjp_3989_;
}
else
{
lean_inc(v_diag_3988_);
lean_inc(v_postponed_3987_);
lean_inc(v_zetaDeltaFVarIds_3986_);
lean_inc(v_mctx_3985_);
lean_dec(v___x_3984_);
v___x_3990_ = lean_box(0);
v_isShared_3991_ = v_isSharedCheck_3999_;
goto v_resetjp_3989_;
}
v_resetjp_3989_:
{
lean_object* v___x_3992_; lean_object* v___x_3994_; 
v___x_3992_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_3991_ == 0)
{
lean_ctor_set(v___x_3990_, 1, v___x_3992_);
v___x_3994_ = v___x_3990_;
goto v_reusejp_3993_;
}
else
{
lean_object* v_reuseFailAlloc_3998_; 
v_reuseFailAlloc_3998_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_3998_, 0, v_mctx_3985_);
lean_ctor_set(v_reuseFailAlloc_3998_, 1, v___x_3992_);
lean_ctor_set(v_reuseFailAlloc_3998_, 2, v_zetaDeltaFVarIds_3986_);
lean_ctor_set(v_reuseFailAlloc_3998_, 3, v_postponed_3987_);
lean_ctor_set(v_reuseFailAlloc_3998_, 4, v_diag_3988_);
v___x_3994_ = v_reuseFailAlloc_3998_;
goto v_reusejp_3993_;
}
v_reusejp_3993_:
{
lean_object* v___x_3995_; lean_object* v___x_3996_; lean_object* v___x_3997_; 
v___x_3995_ = lean_st_ref_set(v___y_3962_, v___x_3994_);
v___x_3996_ = lean_box(0);
v___x_3997_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_3997_, 0, v___x_3996_);
return v___x_3997_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___boxed(lean_object* v_ext_4004_, lean_object* v_b_4005_, lean_object* v_kind_4006_, lean_object* v___y_4007_, lean_object* v___y_4008_, lean_object* v___y_4009_, lean_object* v___y_4010_){
_start:
{
uint8_t v_kind_boxed_4011_; lean_object* v_res_4012_; 
v_kind_boxed_4011_ = lean_unbox(v_kind_4006_);
v_res_4012_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_4004_, v_b_4005_, v_kind_boxed_4011_, v___y_4007_, v___y_4008_, v___y_4009_);
lean_dec(v___y_4009_);
lean_dec_ref(v___y_4008_);
lean_dec(v___y_4007_);
return v_res_4012_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(lean_object* v_00_u03b1_4013_, lean_object* v_00_u03b2_4014_, lean_object* v_00_u03c3_4015_, lean_object* v_ext_4016_, lean_object* v_b_4017_, uint8_t v_kind_4018_, lean_object* v___y_4019_, lean_object* v___y_4020_, lean_object* v___y_4021_, lean_object* v___y_4022_){
_start:
{
lean_object* v___x_4024_; 
v___x_4024_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v_ext_4016_, v_b_4017_, v_kind_4018_, v___y_4020_, v___y_4021_, v___y_4022_);
return v___x_4024_;
}
}
LEAN_EXPORT lean_object* l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___boxed(lean_object* v_00_u03b1_4025_, lean_object* v_00_u03b2_4026_, lean_object* v_00_u03c3_4027_, lean_object* v_ext_4028_, lean_object* v_b_4029_, lean_object* v_kind_4030_, lean_object* v___y_4031_, lean_object* v___y_4032_, lean_object* v___y_4033_, lean_object* v___y_4034_, lean_object* v___y_4035_){
_start:
{
uint8_t v_kind_boxed_4036_; lean_object* v_res_4037_; 
v_kind_boxed_4036_ = lean_unbox(v_kind_4030_);
v_res_4037_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2(v_00_u03b1_4025_, v_00_u03b2_4026_, v_00_u03c3_4027_, v_ext_4028_, v_b_4029_, v_kind_boxed_4036_, v___y_4031_, v___y_4032_, v___y_4033_, v___y_4034_);
lean_dec(v___y_4034_);
lean_dec_ref(v___y_4033_);
lean_dec(v___y_4032_);
lean_dec_ref(v___y_4031_);
return v_res_4037_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(lean_object* v_declName_4038_, lean_object* v___y_4039_){
_start:
{
lean_object* v___x_4041_; lean_object* v_env_4042_; uint8_t v___x_4043_; lean_object* v___x_4044_; lean_object* v___x_4045_; 
v___x_4041_ = lean_st_ref_get(v___y_4039_);
v_env_4042_ = lean_ctor_get(v___x_4041_, 0);
lean_inc_ref(v_env_4042_);
lean_dec(v___x_4041_);
v___x_4043_ = l_Lean_getReducibilityStatusCore(v_env_4042_, v_declName_4038_);
v___x_4044_ = lean_box(v___x_4043_);
v___x_4045_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4045_, 0, v___x_4044_);
return v___x_4045_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg___boxed(lean_object* v_declName_4046_, lean_object* v___y_4047_, lean_object* v___y_4048_){
_start:
{
lean_object* v_res_4049_; 
v_res_4049_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4046_, v___y_4047_);
lean_dec(v___y_4047_);
return v_res_4049_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(lean_object* v_declName_4050_, lean_object* v___y_4051_, lean_object* v___y_4052_, lean_object* v___y_4053_, lean_object* v___y_4054_){
_start:
{
lean_object* v___x_4056_; 
v___x_4056_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4050_, v___y_4054_);
return v___x_4056_;
}
}
LEAN_EXPORT lean_object* l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___boxed(lean_object* v_declName_4057_, lean_object* v___y_4058_, lean_object* v___y_4059_, lean_object* v___y_4060_, lean_object* v___y_4061_, lean_object* v___y_4062_){
_start:
{
lean_object* v_res_4063_; 
v_res_4063_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3(v_declName_4057_, v___y_4058_, v___y_4059_, v___y_4060_, v___y_4061_);
lean_dec(v___y_4061_);
lean_dec_ref(v___y_4060_);
lean_dec(v___y_4059_);
lean_dec_ref(v___y_4058_);
return v_res_4063_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(lean_object* v_ref_4064_, lean_object* v_msg_4065_, lean_object* v___y_4066_, lean_object* v___y_4067_, lean_object* v___y_4068_, lean_object* v___y_4069_){
_start:
{
lean_object* v_fileName_4071_; lean_object* v_fileMap_4072_; lean_object* v_options_4073_; lean_object* v_currRecDepth_4074_; lean_object* v_maxRecDepth_4075_; lean_object* v_ref_4076_; lean_object* v_currNamespace_4077_; lean_object* v_openDecls_4078_; lean_object* v_initHeartbeats_4079_; lean_object* v_maxHeartbeats_4080_; lean_object* v_quotContext_4081_; lean_object* v_currMacroScope_4082_; uint8_t v_diag_4083_; lean_object* v_cancelTk_x3f_4084_; uint8_t v_suppressElabErrors_4085_; lean_object* v_inheritedTraceOptions_4086_; lean_object* v_ref_4087_; lean_object* v___x_4088_; lean_object* v___x_4089_; 
v_fileName_4071_ = lean_ctor_get(v___y_4068_, 0);
v_fileMap_4072_ = lean_ctor_get(v___y_4068_, 1);
v_options_4073_ = lean_ctor_get(v___y_4068_, 2);
v_currRecDepth_4074_ = lean_ctor_get(v___y_4068_, 3);
v_maxRecDepth_4075_ = lean_ctor_get(v___y_4068_, 4);
v_ref_4076_ = lean_ctor_get(v___y_4068_, 5);
v_currNamespace_4077_ = lean_ctor_get(v___y_4068_, 6);
v_openDecls_4078_ = lean_ctor_get(v___y_4068_, 7);
v_initHeartbeats_4079_ = lean_ctor_get(v___y_4068_, 8);
v_maxHeartbeats_4080_ = lean_ctor_get(v___y_4068_, 9);
v_quotContext_4081_ = lean_ctor_get(v___y_4068_, 10);
v_currMacroScope_4082_ = lean_ctor_get(v___y_4068_, 11);
v_diag_4083_ = lean_ctor_get_uint8(v___y_4068_, sizeof(void*)*14);
v_cancelTk_x3f_4084_ = lean_ctor_get(v___y_4068_, 12);
v_suppressElabErrors_4085_ = lean_ctor_get_uint8(v___y_4068_, sizeof(void*)*14 + 1);
v_inheritedTraceOptions_4086_ = lean_ctor_get(v___y_4068_, 13);
v_ref_4087_ = l_Lean_replaceRef(v_ref_4064_, v_ref_4076_);
lean_inc_ref(v_inheritedTraceOptions_4086_);
lean_inc(v_cancelTk_x3f_4084_);
lean_inc(v_currMacroScope_4082_);
lean_inc(v_quotContext_4081_);
lean_inc(v_maxHeartbeats_4080_);
lean_inc(v_initHeartbeats_4079_);
lean_inc(v_openDecls_4078_);
lean_inc(v_currNamespace_4077_);
lean_inc(v_maxRecDepth_4075_);
lean_inc(v_currRecDepth_4074_);
lean_inc_ref(v_options_4073_);
lean_inc_ref(v_fileMap_4072_);
lean_inc_ref(v_fileName_4071_);
v___x_4088_ = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(v___x_4088_, 0, v_fileName_4071_);
lean_ctor_set(v___x_4088_, 1, v_fileMap_4072_);
lean_ctor_set(v___x_4088_, 2, v_options_4073_);
lean_ctor_set(v___x_4088_, 3, v_currRecDepth_4074_);
lean_ctor_set(v___x_4088_, 4, v_maxRecDepth_4075_);
lean_ctor_set(v___x_4088_, 5, v_ref_4087_);
lean_ctor_set(v___x_4088_, 6, v_currNamespace_4077_);
lean_ctor_set(v___x_4088_, 7, v_openDecls_4078_);
lean_ctor_set(v___x_4088_, 8, v_initHeartbeats_4079_);
lean_ctor_set(v___x_4088_, 9, v_maxHeartbeats_4080_);
lean_ctor_set(v___x_4088_, 10, v_quotContext_4081_);
lean_ctor_set(v___x_4088_, 11, v_currMacroScope_4082_);
lean_ctor_set(v___x_4088_, 12, v_cancelTk_x3f_4084_);
lean_ctor_set(v___x_4088_, 13, v_inheritedTraceOptions_4086_);
lean_ctor_set_uint8(v___x_4088_, sizeof(void*)*14, v_diag_4083_);
lean_ctor_set_uint8(v___x_4088_, sizeof(void*)*14 + 1, v_suppressElabErrors_4085_);
v___x_4089_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v_msg_4065_, v___y_4066_, v___y_4067_, v___x_4088_, v___y_4069_);
lean_dec_ref_known(v___x_4088_, 14);
return v___x_4089_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg___boxed(lean_object* v_ref_4090_, lean_object* v_msg_4091_, lean_object* v___y_4092_, lean_object* v___y_4093_, lean_object* v___y_4094_, lean_object* v___y_4095_, lean_object* v___y_4096_){
_start:
{
lean_object* v_res_4097_; 
v_res_4097_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4090_, v_msg_4091_, v___y_4092_, v___y_4093_, v___y_4094_, v___y_4095_);
lean_dec(v___y_4095_);
lean_dec_ref(v___y_4094_);
lean_dec(v___y_4093_);
lean_dec_ref(v___y_4092_);
lean_dec(v_ref_4090_);
return v_res_4097_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0(void){
_start:
{
lean_object* v___x_4098_; 
v___x_4098_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4098_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1(void){
_start:
{
lean_object* v___x_4099_; lean_object* v___x_4100_; 
v___x_4099_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__0);
v___x_4100_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4100_, 0, v___x_4099_);
return v___x_4100_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2(void){
_start:
{
lean_object* v___x_4101_; lean_object* v___x_4102_; lean_object* v___x_4103_; 
v___x_4101_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4102_ = lean_unsigned_to_nat(0u);
v___x_4103_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4103_, 0, v___x_4102_);
lean_ctor_set(v___x_4103_, 1, v___x_4102_);
lean_ctor_set(v___x_4103_, 2, v___x_4102_);
lean_ctor_set(v___x_4103_, 3, v___x_4102_);
lean_ctor_set(v___x_4103_, 4, v___x_4101_);
lean_ctor_set(v___x_4103_, 5, v___x_4101_);
lean_ctor_set(v___x_4103_, 6, v___x_4101_);
lean_ctor_set(v___x_4103_, 7, v___x_4101_);
lean_ctor_set(v___x_4103_, 8, v___x_4101_);
lean_ctor_set(v___x_4103_, 9, v___x_4101_);
return v___x_4103_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3(void){
_start:
{
lean_object* v___x_4104_; lean_object* v___x_4105_; lean_object* v___x_4106_; 
v___x_4104_ = lean_unsigned_to_nat(32u);
v___x_4105_ = lean_mk_empty_array_with_capacity(v___x_4104_);
v___x_4106_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4106_, 0, v___x_4105_);
return v___x_4106_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4(void){
_start:
{
size_t v___x_4107_; lean_object* v___x_4108_; lean_object* v___x_4109_; lean_object* v___x_4110_; lean_object* v___x_4111_; lean_object* v___x_4112_; 
v___x_4107_ = ((size_t)5ULL);
v___x_4108_ = lean_unsigned_to_nat(0u);
v___x_4109_ = lean_unsigned_to_nat(32u);
v___x_4110_ = lean_mk_empty_array_with_capacity(v___x_4109_);
v___x_4111_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4112_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4112_, 0, v___x_4111_);
lean_ctor_set(v___x_4112_, 1, v___x_4110_);
lean_ctor_set(v___x_4112_, 2, v___x_4108_);
lean_ctor_set(v___x_4112_, 3, v___x_4108_);
lean_ctor_set_usize(v___x_4112_, 4, v___x_4107_);
return v___x_4112_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5(void){
_start:
{
lean_object* v___x_4113_; lean_object* v___x_4114_; lean_object* v___x_4115_; lean_object* v___x_4116_; 
v___x_4113_ = lean_box(1);
v___x_4114_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__4);
v___x_4115_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__1);
v___x_4116_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4116_, 0, v___x_4115_);
lean_ctor_set(v___x_4116_, 1, v___x_4114_);
lean_ctor_set(v___x_4116_, 2, v___x_4113_);
return v___x_4116_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7(void){
_start:
{
lean_object* v___x_4118_; lean_object* v___x_4119_; 
v___x_4118_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__6));
v___x_4119_ = l_Lean_stringToMessageData(v___x_4118_);
return v___x_4119_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9(void){
_start:
{
lean_object* v___x_4121_; lean_object* v___x_4122_; 
v___x_4121_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__8));
v___x_4122_ = l_Lean_stringToMessageData(v___x_4121_);
return v___x_4122_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11(void){
_start:
{
lean_object* v___x_4124_; lean_object* v___x_4125_; 
v___x_4124_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__10));
v___x_4125_ = l_Lean_stringToMessageData(v___x_4124_);
return v___x_4125_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13(void){
_start:
{
lean_object* v___x_4127_; lean_object* v___x_4128_; 
v___x_4127_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__12));
v___x_4128_ = l_Lean_stringToMessageData(v___x_4127_);
return v___x_4128_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15(void){
_start:
{
lean_object* v___x_4130_; lean_object* v___x_4131_; 
v___x_4130_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__14));
v___x_4131_ = l_Lean_stringToMessageData(v___x_4130_);
return v___x_4131_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17(void){
_start:
{
lean_object* v___x_4133_; lean_object* v___x_4134_; 
v___x_4133_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__16));
v___x_4134_ = l_Lean_stringToMessageData(v___x_4133_);
return v___x_4134_;
}
}
static lean_object* _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19(void){
_start:
{
lean_object* v___x_4136_; lean_object* v___x_4137_; 
v___x_4136_ = ((lean_object*)(l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__18));
v___x_4137_ = l_Lean_stringToMessageData(v___x_4136_);
return v___x_4137_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(lean_object* v_msg_4138_, lean_object* v_declHint_4139_, lean_object* v___y_4140_){
_start:
{
lean_object* v___x_4142_; lean_object* v_env_4143_; uint8_t v___y_4145_; uint8_t v___x_4201_; uint8_t v___x_4202_; 
v___x_4142_ = lean_st_ref_get(v___y_4140_);
v_env_4143_ = lean_ctor_get(v___x_4142_, 0);
lean_inc_ref(v_env_4143_);
lean_dec(v___x_4142_);
v___x_4201_ = l_Lean_Name_isAnonymous(v_declHint_4139_);
v___x_4202_ = lean_bool_not(v___x_4201_);
if (v___x_4202_ == 0)
{
v___y_4145_ = v___x_4202_;
goto v___jp_4144_;
}
else
{
uint8_t v_isExporting_4203_; 
v_isExporting_4203_ = lean_ctor_get_uint8(v_env_4143_, sizeof(void*)*8);
v___y_4145_ = v_isExporting_4203_;
goto v___jp_4144_;
}
v___jp_4144_:
{
if (v___y_4145_ == 0)
{
lean_object* v___x_4146_; 
lean_dec_ref(v_env_4143_);
lean_dec(v_declHint_4139_);
v___x_4146_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4146_, 0, v_msg_4138_);
return v___x_4146_;
}
else
{
uint8_t v___x_4147_; lean_object* v___x_4148_; uint8_t v___x_4149_; 
v___x_4147_ = 0;
lean_inc_ref(v_env_4143_);
v___x_4148_ = l_Lean_Environment_setExporting(v_env_4143_, v___x_4147_);
lean_inc(v_declHint_4139_);
lean_inc_ref(v___x_4148_);
v___x_4149_ = l_Lean_Environment_contains(v___x_4148_, v_declHint_4139_, v___y_4145_);
if (v___x_4149_ == 0)
{
lean_object* v___x_4150_; 
lean_dec_ref(v___x_4148_);
lean_dec_ref(v_env_4143_);
lean_dec(v_declHint_4139_);
v___x_4150_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4150_, 0, v_msg_4138_);
return v___x_4150_;
}
else
{
lean_object* v___x_4151_; lean_object* v___x_4152_; lean_object* v___x_4153_; lean_object* v___x_4154_; lean_object* v___x_4155_; lean_object* v_c_4156_; lean_object* v___x_4157_; 
v___x_4151_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4152_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
v___x_4153_ = l_Lean_Options_empty;
v___x_4154_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4154_, 0, v___x_4148_);
lean_ctor_set(v___x_4154_, 1, v___x_4151_);
lean_ctor_set(v___x_4154_, 2, v___x_4152_);
lean_ctor_set(v___x_4154_, 3, v___x_4153_);
lean_inc(v_declHint_4139_);
v___x_4155_ = l_Lean_MessageData_ofConstName(v_declHint_4139_, v___x_4147_);
v_c_4156_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_c_4156_, 0, v___x_4154_);
lean_ctor_set(v_c_4156_, 1, v___x_4155_);
v___x_4157_ = l_Lean_Environment_getModuleIdxFor_x3f(v_env_4143_, v_declHint_4139_);
if (lean_obj_tag(v___x_4157_) == 0)
{
lean_object* v___x_4158_; lean_object* v___x_4159_; lean_object* v___x_4160_; lean_object* v___x_4161_; lean_object* v___x_4162_; lean_object* v___x_4163_; lean_object* v___x_4164_; 
lean_dec_ref(v_env_4143_);
lean_dec(v_declHint_4139_);
v___x_4158_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4159_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4159_, 0, v___x_4158_);
lean_ctor_set(v___x_4159_, 1, v_c_4156_);
v___x_4160_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__9);
v___x_4161_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4161_, 0, v___x_4159_);
lean_ctor_set(v___x_4161_, 1, v___x_4160_);
v___x_4162_ = l_Lean_MessageData_note(v___x_4161_);
v___x_4163_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4163_, 0, v_msg_4138_);
lean_ctor_set(v___x_4163_, 1, v___x_4162_);
v___x_4164_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4164_, 0, v___x_4163_);
return v___x_4164_;
}
else
{
lean_object* v_val_4165_; lean_object* v___x_4167_; uint8_t v_isShared_4168_; uint8_t v_isSharedCheck_4200_; 
v_val_4165_ = lean_ctor_get(v___x_4157_, 0);
v_isSharedCheck_4200_ = !lean_is_exclusive(v___x_4157_);
if (v_isSharedCheck_4200_ == 0)
{
v___x_4167_ = v___x_4157_;
v_isShared_4168_ = v_isSharedCheck_4200_;
goto v_resetjp_4166_;
}
else
{
lean_inc(v_val_4165_);
lean_dec(v___x_4157_);
v___x_4167_ = lean_box(0);
v_isShared_4168_ = v_isSharedCheck_4200_;
goto v_resetjp_4166_;
}
v_resetjp_4166_:
{
lean_object* v___x_4169_; lean_object* v___x_4170_; lean_object* v___x_4171_; lean_object* v_mod_4172_; uint8_t v___x_4173_; 
v___x_4169_ = lean_box(0);
v___x_4170_ = l_Lean_Environment_header(v_env_4143_);
lean_dec_ref(v_env_4143_);
v___x_4171_ = l_Lean_EnvironmentHeader_moduleNames(v___x_4170_);
v_mod_4172_ = lean_array_get(v___x_4169_, v___x_4171_, v_val_4165_);
lean_dec(v_val_4165_);
lean_dec_ref(v___x_4171_);
v___x_4173_ = l_Lean_isPrivateName(v_declHint_4139_);
lean_dec(v_declHint_4139_);
if (v___x_4173_ == 0)
{
lean_object* v___x_4174_; lean_object* v___x_4175_; lean_object* v___x_4176_; lean_object* v___x_4177_; lean_object* v___x_4178_; lean_object* v___x_4179_; lean_object* v___x_4180_; lean_object* v___x_4181_; lean_object* v___x_4182_; lean_object* v___x_4183_; lean_object* v___x_4185_; 
v___x_4174_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__11);
v___x_4175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4175_, 0, v___x_4174_);
lean_ctor_set(v___x_4175_, 1, v_c_4156_);
v___x_4176_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__13);
v___x_4177_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4177_, 0, v___x_4175_);
lean_ctor_set(v___x_4177_, 1, v___x_4176_);
v___x_4178_ = l_Lean_MessageData_ofName(v_mod_4172_);
v___x_4179_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4179_, 0, v___x_4177_);
lean_ctor_set(v___x_4179_, 1, v___x_4178_);
v___x_4180_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__15);
v___x_4181_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4181_, 0, v___x_4179_);
lean_ctor_set(v___x_4181_, 1, v___x_4180_);
v___x_4182_ = l_Lean_MessageData_note(v___x_4181_);
v___x_4183_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4183_, 0, v_msg_4138_);
lean_ctor_set(v___x_4183_, 1, v___x_4182_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set_tag(v___x_4167_, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4183_);
v___x_4185_ = v___x_4167_;
goto v_reusejp_4184_;
}
else
{
lean_object* v_reuseFailAlloc_4186_; 
v_reuseFailAlloc_4186_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4186_, 0, v___x_4183_);
v___x_4185_ = v_reuseFailAlloc_4186_;
goto v_reusejp_4184_;
}
v_reusejp_4184_:
{
return v___x_4185_;
}
}
else
{
lean_object* v___x_4187_; lean_object* v___x_4188_; lean_object* v___x_4189_; lean_object* v___x_4190_; lean_object* v___x_4191_; lean_object* v___x_4192_; lean_object* v___x_4193_; lean_object* v___x_4194_; lean_object* v___x_4195_; lean_object* v___x_4196_; lean_object* v___x_4198_; 
v___x_4187_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__7);
v___x_4188_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4188_, 0, v___x_4187_);
lean_ctor_set(v___x_4188_, 1, v_c_4156_);
v___x_4189_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__17);
v___x_4190_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4190_, 0, v___x_4188_);
lean_ctor_set(v___x_4190_, 1, v___x_4189_);
v___x_4191_ = l_Lean_MessageData_ofName(v_mod_4172_);
v___x_4192_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4192_, 0, v___x_4190_);
lean_ctor_set(v___x_4192_, 1, v___x_4191_);
v___x_4193_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__19);
v___x_4194_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4194_, 0, v___x_4192_);
lean_ctor_set(v___x_4194_, 1, v___x_4193_);
v___x_4195_ = l_Lean_MessageData_note(v___x_4194_);
v___x_4196_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4196_, 0, v_msg_4138_);
lean_ctor_set(v___x_4196_, 1, v___x_4195_);
if (v_isShared_4168_ == 0)
{
lean_ctor_set_tag(v___x_4167_, 0);
lean_ctor_set(v___x_4167_, 0, v___x_4196_);
v___x_4198_ = v___x_4167_;
goto v_reusejp_4197_;
}
else
{
lean_object* v_reuseFailAlloc_4199_; 
v_reuseFailAlloc_4199_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4199_, 0, v___x_4196_);
v___x_4198_ = v_reuseFailAlloc_4199_;
goto v_reusejp_4197_;
}
v_reusejp_4197_:
{
return v___x_4198_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___boxed(lean_object* v_msg_4204_, lean_object* v_declHint_4205_, lean_object* v___y_4206_, lean_object* v___y_4207_){
_start:
{
lean_object* v_res_4208_; 
v_res_4208_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4204_, v_declHint_4205_, v___y_4206_);
lean_dec(v___y_4206_);
return v_res_4208_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(lean_object* v_msg_4209_, lean_object* v_declHint_4210_, lean_object* v___y_4211_, lean_object* v___y_4212_, lean_object* v___y_4213_, lean_object* v___y_4214_){
_start:
{
lean_object* v___x_4216_; lean_object* v_a_4217_; lean_object* v___x_4219_; uint8_t v_isShared_4220_; uint8_t v_isSharedCheck_4226_; 
v___x_4216_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4209_, v_declHint_4210_, v___y_4214_);
v_a_4217_ = lean_ctor_get(v___x_4216_, 0);
v_isSharedCheck_4226_ = !lean_is_exclusive(v___x_4216_);
if (v_isSharedCheck_4226_ == 0)
{
v___x_4219_ = v___x_4216_;
v_isShared_4220_ = v_isSharedCheck_4226_;
goto v_resetjp_4218_;
}
else
{
lean_inc(v_a_4217_);
lean_dec(v___x_4216_);
v___x_4219_ = lean_box(0);
v_isShared_4220_ = v_isSharedCheck_4226_;
goto v_resetjp_4218_;
}
v_resetjp_4218_:
{
lean_object* v___x_4221_; lean_object* v___x_4222_; lean_object* v___x_4224_; 
v___x_4221_ = l_Lean_unknownIdentifierMessageTag;
v___x_4222_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_4222_, 0, v___x_4221_);
lean_ctor_set(v___x_4222_, 1, v_a_4217_);
if (v_isShared_4220_ == 0)
{
lean_ctor_set(v___x_4219_, 0, v___x_4222_);
v___x_4224_ = v___x_4219_;
goto v_reusejp_4223_;
}
else
{
lean_object* v_reuseFailAlloc_4225_; 
v_reuseFailAlloc_4225_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4225_, 0, v___x_4222_);
v___x_4224_ = v_reuseFailAlloc_4225_;
goto v_reusejp_4223_;
}
v_reusejp_4223_:
{
return v___x_4224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9___boxed(lean_object* v_msg_4227_, lean_object* v_declHint_4228_, lean_object* v___y_4229_, lean_object* v___y_4230_, lean_object* v___y_4231_, lean_object* v___y_4232_, lean_object* v___y_4233_){
_start:
{
lean_object* v_res_4234_; 
v_res_4234_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4227_, v_declHint_4228_, v___y_4229_, v___y_4230_, v___y_4231_, v___y_4232_);
lean_dec(v___y_4232_);
lean_dec_ref(v___y_4231_);
lean_dec(v___y_4230_);
lean_dec_ref(v___y_4229_);
return v_res_4234_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(lean_object* v_ref_4235_, lean_object* v_msg_4236_, lean_object* v_declHint_4237_, lean_object* v___y_4238_, lean_object* v___y_4239_, lean_object* v___y_4240_, lean_object* v___y_4241_){
_start:
{
lean_object* v___x_4243_; lean_object* v_a_4244_; lean_object* v___x_4245_; 
v___x_4243_ = l_Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9(v_msg_4236_, v_declHint_4237_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
v_a_4244_ = lean_ctor_get(v___x_4243_, 0);
lean_inc(v_a_4244_);
lean_dec_ref(v___x_4243_);
v___x_4245_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4235_, v_a_4244_, v___y_4238_, v___y_4239_, v___y_4240_, v___y_4241_);
return v___x_4245_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg___boxed(lean_object* v_ref_4246_, lean_object* v_msg_4247_, lean_object* v_declHint_4248_, lean_object* v___y_4249_, lean_object* v___y_4250_, lean_object* v___y_4251_, lean_object* v___y_4252_, lean_object* v___y_4253_){
_start:
{
lean_object* v_res_4254_; 
v_res_4254_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4246_, v_msg_4247_, v_declHint_4248_, v___y_4249_, v___y_4250_, v___y_4251_, v___y_4252_);
lean_dec(v___y_4252_);
lean_dec_ref(v___y_4251_);
lean_dec(v___y_4250_);
lean_dec_ref(v___y_4249_);
lean_dec(v_ref_4246_);
return v_res_4254_;
}
}
static lean_object* _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1(void){
_start:
{
lean_object* v___x_4256_; lean_object* v___x_4257_; 
v___x_4256_ = ((lean_object*)(l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__0));
v___x_4257_ = l_Lean_stringToMessageData(v___x_4256_);
return v___x_4257_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(lean_object* v_ref_4258_, lean_object* v_constName_4259_, lean_object* v___y_4260_, lean_object* v___y_4261_, lean_object* v___y_4262_, lean_object* v___y_4263_){
_start:
{
lean_object* v___x_4265_; uint8_t v___x_4266_; lean_object* v___x_4267_; lean_object* v___x_4268_; lean_object* v___x_4269_; lean_object* v___x_4270_; lean_object* v___x_4271_; 
v___x_4265_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_4266_ = 0;
lean_inc(v_constName_4259_);
v___x_4267_ = l_Lean_MessageData_ofConstName(v_constName_4259_, v___x_4266_);
v___x_4268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4268_, 0, v___x_4265_);
lean_ctor_set(v___x_4268_, 1, v___x_4267_);
v___x_4269_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4270_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4270_, 0, v___x_4268_);
lean_ctor_set(v___x_4270_, 1, v___x_4269_);
v___x_4271_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4258_, v___x_4270_, v_constName_4259_, v___y_4260_, v___y_4261_, v___y_4262_, v___y_4263_);
return v___x_4271_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___boxed(lean_object* v_ref_4272_, lean_object* v_constName_4273_, lean_object* v___y_4274_, lean_object* v___y_4275_, lean_object* v___y_4276_, lean_object* v___y_4277_, lean_object* v___y_4278_){
_start:
{
lean_object* v_res_4279_; 
v_res_4279_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4272_, v_constName_4273_, v___y_4274_, v___y_4275_, v___y_4276_, v___y_4277_);
lean_dec(v___y_4277_);
lean_dec_ref(v___y_4276_);
lean_dec(v___y_4275_);
lean_dec_ref(v___y_4274_);
lean_dec(v_ref_4272_);
return v_res_4279_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(lean_object* v_constName_4280_, lean_object* v___y_4281_, lean_object* v___y_4282_, lean_object* v___y_4283_, lean_object* v___y_4284_){
_start:
{
lean_object* v_ref_4286_; lean_object* v___x_4287_; 
v_ref_4286_ = lean_ctor_get(v___y_4283_, 5);
v___x_4287_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4286_, v_constName_4280_, v___y_4281_, v___y_4282_, v___y_4283_, v___y_4284_);
return v___x_4287_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg___boxed(lean_object* v_constName_4288_, lean_object* v___y_4289_, lean_object* v___y_4290_, lean_object* v___y_4291_, lean_object* v___y_4292_, lean_object* v___y_4293_){
_start:
{
lean_object* v_res_4294_; 
v_res_4294_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4288_, v___y_4289_, v___y_4290_, v___y_4291_, v___y_4292_);
lean_dec(v___y_4292_);
lean_dec_ref(v___y_4291_);
lean_dec(v___y_4290_);
lean_dec_ref(v___y_4289_);
return v_res_4294_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(lean_object* v_constName_4295_, lean_object* v___y_4296_, lean_object* v___y_4297_, lean_object* v___y_4298_, lean_object* v___y_4299_){
_start:
{
lean_object* v___x_4301_; lean_object* v_env_4302_; uint8_t v___x_4303_; lean_object* v___x_4304_; 
v___x_4301_ = lean_st_ref_get(v___y_4299_);
v_env_4302_ = lean_ctor_get(v___x_4301_, 0);
lean_inc_ref(v_env_4302_);
lean_dec(v___x_4301_);
v___x_4303_ = 0;
lean_inc(v_constName_4295_);
v___x_4304_ = l_Lean_Environment_find_x3f(v_env_4302_, v_constName_4295_, v___x_4303_);
if (lean_obj_tag(v___x_4304_) == 0)
{
lean_object* v___x_4305_; 
v___x_4305_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4295_, v___y_4296_, v___y_4297_, v___y_4298_, v___y_4299_);
return v___x_4305_;
}
else
{
lean_object* v_val_4306_; lean_object* v___x_4308_; uint8_t v_isShared_4309_; uint8_t v_isSharedCheck_4313_; 
lean_dec(v_constName_4295_);
v_val_4306_ = lean_ctor_get(v___x_4304_, 0);
v_isSharedCheck_4313_ = !lean_is_exclusive(v___x_4304_);
if (v_isSharedCheck_4313_ == 0)
{
v___x_4308_ = v___x_4304_;
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
else
{
lean_inc(v_val_4306_);
lean_dec(v___x_4304_);
v___x_4308_ = lean_box(0);
v_isShared_4309_ = v_isSharedCheck_4313_;
goto v_resetjp_4307_;
}
v_resetjp_4307_:
{
lean_object* v___x_4311_; 
if (v_isShared_4309_ == 0)
{
lean_ctor_set_tag(v___x_4308_, 0);
v___x_4311_ = v___x_4308_;
goto v_reusejp_4310_;
}
else
{
lean_object* v_reuseFailAlloc_4312_; 
v_reuseFailAlloc_4312_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4312_, 0, v_val_4306_);
v___x_4311_ = v_reuseFailAlloc_4312_;
goto v_reusejp_4310_;
}
v_reusejp_4310_:
{
return v___x_4311_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4___boxed(lean_object* v_constName_4314_, lean_object* v___y_4315_, lean_object* v___y_4316_, lean_object* v___y_4317_, lean_object* v___y_4318_, lean_object* v___y_4319_){
_start:
{
lean_object* v_res_4320_; 
v_res_4320_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_constName_4314_, v___y_4315_, v___y_4316_, v___y_4317_, v___y_4318_);
lean_dec(v___y_4318_);
lean_dec_ref(v___y_4317_);
lean_dec(v___y_4316_);
lean_dec_ref(v___y_4315_);
return v_res_4320_;
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(lean_object* v_constName_4321_, lean_object* v___y_4322_, lean_object* v___y_4323_, lean_object* v___y_4324_, lean_object* v___y_4325_){
_start:
{
lean_object* v___x_4327_; lean_object* v_env_4328_; uint8_t v___x_4329_; lean_object* v___x_4330_; 
v___x_4327_ = lean_st_ref_get(v___y_4325_);
v_env_4328_ = lean_ctor_get(v___x_4327_, 0);
lean_inc_ref(v_env_4328_);
lean_dec(v___x_4327_);
v___x_4329_ = 0;
lean_inc(v_constName_4321_);
v___x_4330_ = l_Lean_Environment_findConstVal_x3f(v_env_4328_, v_constName_4321_, v___x_4329_);
if (lean_obj_tag(v___x_4330_) == 0)
{
lean_object* v___x_4331_; 
v___x_4331_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4321_, v___y_4322_, v___y_4323_, v___y_4324_, v___y_4325_);
return v___x_4331_;
}
else
{
lean_object* v_val_4332_; lean_object* v___x_4334_; uint8_t v_isShared_4335_; uint8_t v_isSharedCheck_4339_; 
lean_dec(v_constName_4321_);
v_val_4332_ = lean_ctor_get(v___x_4330_, 0);
v_isSharedCheck_4339_ = !lean_is_exclusive(v___x_4330_);
if (v_isSharedCheck_4339_ == 0)
{
v___x_4334_ = v___x_4330_;
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
else
{
lean_inc(v_val_4332_);
lean_dec(v___x_4330_);
v___x_4334_ = lean_box(0);
v_isShared_4335_ = v_isSharedCheck_4339_;
goto v_resetjp_4333_;
}
v_resetjp_4333_:
{
lean_object* v___x_4337_; 
if (v_isShared_4335_ == 0)
{
lean_ctor_set_tag(v___x_4334_, 0);
v___x_4337_ = v___x_4334_;
goto v_reusejp_4336_;
}
else
{
lean_object* v_reuseFailAlloc_4338_; 
v_reuseFailAlloc_4338_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4338_, 0, v_val_4332_);
v___x_4337_ = v_reuseFailAlloc_4338_;
goto v_reusejp_4336_;
}
v_reusejp_4336_:
{
return v___x_4337_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0___boxed(lean_object* v_constName_4340_, lean_object* v___y_4341_, lean_object* v___y_4342_, lean_object* v___y_4343_, lean_object* v___y_4344_, lean_object* v___y_4345_){
_start:
{
lean_object* v_res_4346_; 
v_res_4346_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4340_, v___y_4341_, v___y_4342_, v___y_4343_, v___y_4344_);
lean_dec(v___y_4344_);
lean_dec_ref(v___y_4343_);
lean_dec(v___y_4342_);
lean_dec_ref(v___y_4341_);
return v_res_4346_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(lean_object* v_a_4347_, lean_object* v_a_4348_){
_start:
{
if (lean_obj_tag(v_a_4347_) == 0)
{
lean_object* v___x_4349_; 
v___x_4349_ = l_List_reverse___redArg(v_a_4348_);
return v___x_4349_;
}
else
{
lean_object* v_head_4350_; lean_object* v_tail_4351_; lean_object* v___x_4353_; uint8_t v_isShared_4354_; uint8_t v_isSharedCheck_4360_; 
v_head_4350_ = lean_ctor_get(v_a_4347_, 0);
v_tail_4351_ = lean_ctor_get(v_a_4347_, 1);
v_isSharedCheck_4360_ = !lean_is_exclusive(v_a_4347_);
if (v_isSharedCheck_4360_ == 0)
{
v___x_4353_ = v_a_4347_;
v_isShared_4354_ = v_isSharedCheck_4360_;
goto v_resetjp_4352_;
}
else
{
lean_inc(v_tail_4351_);
lean_inc(v_head_4350_);
lean_dec(v_a_4347_);
v___x_4353_ = lean_box(0);
v_isShared_4354_ = v_isSharedCheck_4360_;
goto v_resetjp_4352_;
}
v_resetjp_4352_:
{
lean_object* v___x_4355_; lean_object* v___x_4357_; 
v___x_4355_ = l_Lean_mkLevelParam(v_head_4350_);
if (v_isShared_4354_ == 0)
{
lean_ctor_set(v___x_4353_, 1, v_a_4348_);
lean_ctor_set(v___x_4353_, 0, v___x_4355_);
v___x_4357_ = v___x_4353_;
goto v_reusejp_4356_;
}
else
{
lean_object* v_reuseFailAlloc_4359_; 
v_reuseFailAlloc_4359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_4359_, 0, v___x_4355_);
lean_ctor_set(v_reuseFailAlloc_4359_, 1, v_a_4348_);
v___x_4357_ = v_reuseFailAlloc_4359_;
goto v_reusejp_4356_;
}
v_reusejp_4356_:
{
v_a_4347_ = v_tail_4351_;
v_a_4348_ = v___x_4357_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(lean_object* v_constName_4361_, lean_object* v___y_4362_, lean_object* v___y_4363_, lean_object* v___y_4364_, lean_object* v___y_4365_){
_start:
{
lean_object* v___x_4367_; 
lean_inc(v_constName_4361_);
v___x_4367_ = l_Lean_getConstVal___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__0(v_constName_4361_, v___y_4362_, v___y_4363_, v___y_4364_, v___y_4365_);
if (lean_obj_tag(v___x_4367_) == 0)
{
lean_object* v_a_4368_; lean_object* v___x_4370_; uint8_t v_isShared_4371_; uint8_t v_isSharedCheck_4379_; 
v_a_4368_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4379_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4379_ == 0)
{
v___x_4370_ = v___x_4367_;
v_isShared_4371_ = v_isSharedCheck_4379_;
goto v_resetjp_4369_;
}
else
{
lean_inc(v_a_4368_);
lean_dec(v___x_4367_);
v___x_4370_ = lean_box(0);
v_isShared_4371_ = v_isSharedCheck_4379_;
goto v_resetjp_4369_;
}
v_resetjp_4369_:
{
lean_object* v_levelParams_4372_; lean_object* v___x_4373_; lean_object* v___x_4374_; lean_object* v___x_4375_; lean_object* v___x_4377_; 
v_levelParams_4372_ = lean_ctor_get(v_a_4368_, 1);
lean_inc(v_levelParams_4372_);
lean_dec(v_a_4368_);
v___x_4373_ = lean_box(0);
v___x_4374_ = l_List_mapTR_loop___at___00Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0_spec__1(v_levelParams_4372_, v___x_4373_);
v___x_4375_ = l_Lean_mkConst(v_constName_4361_, v___x_4374_);
if (v_isShared_4371_ == 0)
{
lean_ctor_set(v___x_4370_, 0, v___x_4375_);
v___x_4377_ = v___x_4370_;
goto v_reusejp_4376_;
}
else
{
lean_object* v_reuseFailAlloc_4378_; 
v_reuseFailAlloc_4378_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4378_, 0, v___x_4375_);
v___x_4377_ = v_reuseFailAlloc_4378_;
goto v_reusejp_4376_;
}
v_reusejp_4376_:
{
return v___x_4377_;
}
}
}
else
{
lean_object* v_a_4380_; lean_object* v___x_4382_; uint8_t v_isShared_4383_; uint8_t v_isSharedCheck_4387_; 
lean_dec(v_constName_4361_);
v_a_4380_ = lean_ctor_get(v___x_4367_, 0);
v_isSharedCheck_4387_ = !lean_is_exclusive(v___x_4367_);
if (v_isSharedCheck_4387_ == 0)
{
v___x_4382_ = v___x_4367_;
v_isShared_4383_ = v_isSharedCheck_4387_;
goto v_resetjp_4381_;
}
else
{
lean_inc(v_a_4380_);
lean_dec(v___x_4367_);
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
LEAN_EXPORT lean_object* l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0___boxed(lean_object* v_constName_4388_, lean_object* v___y_4389_, lean_object* v___y_4390_, lean_object* v___y_4391_, lean_object* v___y_4392_, lean_object* v___y_4393_){
_start:
{
lean_object* v_res_4394_; 
v_res_4394_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_constName_4388_, v___y_4389_, v___y_4390_, v___y_4391_, v___y_4392_);
lean_dec(v___y_4392_);
lean_dec_ref(v___y_4391_);
lean_dec(v___y_4390_);
lean_dec_ref(v___y_4389_);
return v_res_4394_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__1(void){
_start:
{
lean_object* v___x_4396_; lean_object* v___x_4397_; 
v___x_4396_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__0));
v___x_4397_ = l_Lean_stringToMessageData(v___x_4396_);
return v___x_4397_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__3(void){
_start:
{
lean_object* v___x_4399_; lean_object* v___x_4400_; 
v___x_4399_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__2));
v___x_4400_ = l_Lean_stringToMessageData(v___x_4399_);
return v___x_4400_;
}
}
static lean_object* _init_l_Lean_Meta_addInstance___closed__5(void){
_start:
{
lean_object* v___x_4402_; lean_object* v___x_4403_; 
v___x_4402_ = ((lean_object*)(l_Lean_Meta_addInstance___closed__4));
v___x_4403_ = l_Lean_stringToMessageData(v___x_4402_);
return v___x_4403_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance(lean_object* v_declName_4404_, uint8_t v_attrKind_4405_, lean_object* v_prio_4406_, lean_object* v_a_4407_, lean_object* v_a_4408_, lean_object* v_a_4409_, lean_object* v_a_4410_){
_start:
{
lean_object* v___x_4412_; 
lean_inc(v_declName_4404_);
v___x_4412_ = l_Lean_mkConstWithLevelParams___at___00Lean_Meta_addInstance_spec__0(v_declName_4404_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
if (lean_obj_tag(v___x_4412_) == 0)
{
lean_object* v_a_4413_; lean_object* v___y_4415_; lean_object* v___y_4416_; lean_object* v___y_4417_; lean_object* v___y_4418_; lean_object* v___y_4419_; lean_object* v___y_4443_; lean_object* v___y_4444_; lean_object* v___y_4445_; lean_object* v___y_4446_; lean_object* v___x_4486_; 
v_a_4413_ = lean_ctor_get(v___x_4412_, 0);
lean_inc(v_a_4413_);
lean_dec_ref_known(v___x_4412_, 1);
lean_inc(v_declName_4404_);
v___x_4486_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4404_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
if (lean_obj_tag(v___x_4486_) == 0)
{
lean_object* v_a_4487_; lean_object* v___x_4488_; uint8_t v___x_4489_; 
v_a_4487_ = lean_ctor_get(v___x_4486_, 0);
lean_inc(v_a_4487_);
lean_dec_ref_known(v___x_4486_, 1);
v___x_4488_ = l_Lean_ConstantInfo_type(v_a_4487_);
v___x_4489_ = l_Lean_Expr_hasSorry(v___x_4488_);
lean_dec_ref(v___x_4488_);
if (v___x_4489_ == 0)
{
lean_object* v___x_4490_; 
lean_inc(v_a_4413_);
v___x_4490_ = l_Lean_Meta_checkNonClassInstance(v_a_4413_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
if (lean_obj_tag(v___x_4490_) == 0)
{
lean_object* v___x_4491_; 
lean_dec_ref_known(v___x_4490_, 1);
v___x_4491_ = l_Lean_Meta_checkImpossibleInstance(v_a_4487_, v_a_4407_, v_a_4408_, v_a_4409_, v_a_4410_);
lean_dec(v_a_4487_);
if (lean_obj_tag(v___x_4491_) == 0)
{
lean_dec_ref_known(v___x_4491_, 1);
v___y_4443_ = v_a_4407_;
v___y_4444_ = v_a_4408_;
v___y_4445_ = v_a_4409_;
v___y_4446_ = v_a_4410_;
goto v___jp_4442_;
}
else
{
lean_dec(v_a_4413_);
lean_dec(v_prio_4406_);
lean_dec(v_declName_4404_);
return v___x_4491_;
}
}
else
{
lean_dec(v_a_4487_);
lean_dec(v_a_4413_);
lean_dec(v_prio_4406_);
lean_dec(v_declName_4404_);
return v___x_4490_;
}
}
else
{
lean_dec(v_a_4487_);
v___y_4443_ = v_a_4407_;
v___y_4444_ = v_a_4408_;
v___y_4445_ = v_a_4409_;
v___y_4446_ = v_a_4410_;
goto v___jp_4442_;
}
}
else
{
lean_object* v_a_4492_; lean_object* v___x_4494_; uint8_t v_isShared_4495_; uint8_t v_isSharedCheck_4499_; 
lean_dec(v_a_4413_);
lean_dec(v_prio_4406_);
lean_dec(v_declName_4404_);
v_a_4492_ = lean_ctor_get(v___x_4486_, 0);
v_isSharedCheck_4499_ = !lean_is_exclusive(v___x_4486_);
if (v_isSharedCheck_4499_ == 0)
{
v___x_4494_ = v___x_4486_;
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
else
{
lean_inc(v_a_4492_);
lean_dec(v___x_4486_);
v___x_4494_ = lean_box(0);
v_isShared_4495_ = v_isSharedCheck_4499_;
goto v_resetjp_4493_;
}
v_resetjp_4493_:
{
lean_object* v___x_4497_; 
if (v_isShared_4495_ == 0)
{
v___x_4497_ = v___x_4494_;
goto v_reusejp_4496_;
}
else
{
lean_object* v_reuseFailAlloc_4498_; 
v_reuseFailAlloc_4498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4498_, 0, v_a_4492_);
v___x_4497_ = v_reuseFailAlloc_4498_;
goto v_reusejp_4496_;
}
v_reusejp_4496_:
{
return v___x_4497_;
}
}
}
v___jp_4414_:
{
lean_object* v___x_4420_; lean_object* v_a_4421_; lean_object* v___x_4423_; uint8_t v_isShared_4424_; uint8_t v_isSharedCheck_4441_; 
lean_inc(v_declName_4404_);
v___x_4420_ = l_Lean_getProjectionFnInfo_x3f___at___00Lean_Meta_addInstance_spec__1___redArg(v_declName_4404_, v___y_4419_);
v_a_4421_ = lean_ctor_get(v___x_4420_, 0);
v_isSharedCheck_4441_ = !lean_is_exclusive(v___x_4420_);
if (v_isSharedCheck_4441_ == 0)
{
v___x_4423_ = v___x_4420_;
v_isShared_4424_ = v_isSharedCheck_4441_;
goto v_resetjp_4422_;
}
else
{
lean_inc(v_a_4421_);
lean_dec(v___x_4420_);
v___x_4423_ = lean_box(0);
v_isShared_4424_ = v_isSharedCheck_4441_;
goto v_resetjp_4422_;
}
v_resetjp_4422_:
{
lean_object* v___x_4425_; 
lean_inc(v_a_4413_);
v___x_4425_ = l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder(v_a_4413_, v_a_4421_, v___y_4416_, v___y_4417_, v___y_4418_, v___y_4419_);
if (lean_obj_tag(v___x_4425_) == 0)
{
lean_object* v_a_4426_; lean_object* v___x_4427_; lean_object* v___x_4429_; 
v_a_4426_ = lean_ctor_get(v___x_4425_, 0);
lean_inc(v_a_4426_);
lean_dec_ref_known(v___x_4425_, 1);
v___x_4427_ = l_Lean_Meta_instanceExtension;
if (v_isShared_4424_ == 0)
{
lean_ctor_set_tag(v___x_4423_, 1);
lean_ctor_set(v___x_4423_, 0, v_declName_4404_);
v___x_4429_ = v___x_4423_;
goto v_reusejp_4428_;
}
else
{
lean_object* v_reuseFailAlloc_4432_; 
v_reuseFailAlloc_4432_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4432_, 0, v_declName_4404_);
v___x_4429_ = v_reuseFailAlloc_4432_;
goto v_reusejp_4428_;
}
v_reusejp_4428_:
{
lean_object* v___x_4430_; lean_object* v___x_4431_; 
v___x_4430_ = lean_alloc_ctor(0, 5, 1);
lean_ctor_set(v___x_4430_, 0, v___y_4415_);
lean_ctor_set(v___x_4430_, 1, v_a_4413_);
lean_ctor_set(v___x_4430_, 2, v_prio_4406_);
lean_ctor_set(v___x_4430_, 3, v___x_4429_);
lean_ctor_set(v___x_4430_, 4, v_a_4426_);
lean_ctor_set_uint8(v___x_4430_, sizeof(void*)*5, v_attrKind_4405_);
v___x_4431_ = l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg(v___x_4427_, v___x_4430_, v_attrKind_4405_, v___y_4417_, v___y_4418_, v___y_4419_);
return v___x_4431_;
}
}
else
{
lean_object* v_a_4433_; lean_object* v___x_4435_; uint8_t v_isShared_4436_; uint8_t v_isSharedCheck_4440_; 
lean_del_object(v___x_4423_);
lean_dec_ref(v___y_4415_);
lean_dec(v_a_4413_);
lean_dec(v_prio_4406_);
lean_dec(v_declName_4404_);
v_a_4433_ = lean_ctor_get(v___x_4425_, 0);
v_isSharedCheck_4440_ = !lean_is_exclusive(v___x_4425_);
if (v_isSharedCheck_4440_ == 0)
{
v___x_4435_ = v___x_4425_;
v_isShared_4436_ = v_isSharedCheck_4440_;
goto v_resetjp_4434_;
}
else
{
lean_inc(v_a_4433_);
lean_dec(v___x_4425_);
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
v___jp_4442_:
{
lean_object* v___x_4447_; 
lean_inc(v_a_4413_);
v___x_4447_ = l___private_Lean_Meta_Instances_0__Lean_Meta_mkInstanceKey(v_a_4413_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
if (lean_obj_tag(v___x_4447_) == 0)
{
lean_object* v_a_4448_; lean_object* v___x_4449_; lean_object* v_a_4450_; uint8_t v___x_4451_; 
v_a_4448_ = lean_ctor_get(v___x_4447_, 0);
lean_inc(v_a_4448_);
lean_dec_ref_known(v___x_4447_, 1);
lean_inc(v_declName_4404_);
v___x_4449_ = l_Lean_getReducibilityStatus___at___00Lean_Meta_addInstance_spec__3___redArg(v_declName_4404_, v___y_4446_);
v_a_4450_ = lean_ctor_get(v___x_4449_, 0);
lean_inc(v_a_4450_);
lean_dec_ref(v___x_4449_);
v___x_4451_ = lean_unbox(v_a_4450_);
lean_dec(v_a_4450_);
switch(v___x_4451_)
{
case 0:
{
v___y_4415_ = v_a_4448_;
v___y_4416_ = v___y_4443_;
v___y_4417_ = v___y_4444_;
v___y_4418_ = v___y_4445_;
v___y_4419_ = v___y_4446_;
goto v___jp_4414_;
}
case 4:
{
v___y_4415_ = v_a_4448_;
v___y_4416_ = v___y_4443_;
v___y_4417_ = v___y_4444_;
v___y_4418_ = v___y_4445_;
v___y_4419_ = v___y_4446_;
goto v___jp_4414_;
}
case 3:
{
v___y_4415_ = v_a_4448_;
v___y_4416_ = v___y_4443_;
v___y_4417_ = v___y_4444_;
v___y_4418_ = v___y_4445_;
v___y_4419_ = v___y_4446_;
goto v___jp_4414_;
}
default: 
{
lean_object* v___x_4452_; 
lean_inc(v_declName_4404_);
v___x_4452_ = l_Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4(v_declName_4404_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
if (lean_obj_tag(v___x_4452_) == 0)
{
lean_object* v_a_4453_; uint8_t v___x_4454_; 
v_a_4453_ = lean_ctor_get(v___x_4452_, 0);
lean_inc(v_a_4453_);
lean_dec_ref_known(v___x_4452_, 1);
v___x_4454_ = l_Lean_ConstantInfo_isDefinition(v_a_4453_);
lean_dec(v_a_4453_);
if (v___x_4454_ == 0)
{
lean_object* v___x_4455_; lean_object* v_env_4456_; uint8_t v___x_4457_; 
v___x_4455_ = lean_st_ref_get(v___y_4446_);
v_env_4456_ = lean_ctor_get(v___x_4455_, 0);
lean_inc_ref(v_env_4456_);
lean_dec(v___x_4455_);
lean_inc(v_declName_4404_);
v___x_4457_ = l_Lean_wasOriginallyDefn(v_env_4456_, v_declName_4404_);
if (v___x_4457_ == 0)
{
v___y_4415_ = v_a_4448_;
v___y_4416_ = v___y_4443_;
v___y_4417_ = v___y_4444_;
v___y_4418_ = v___y_4445_;
v___y_4419_ = v___y_4446_;
goto v___jp_4414_;
}
else
{
lean_object* v___x_4458_; lean_object* v___x_4459_; lean_object* v___x_4460_; lean_object* v___x_4461_; lean_object* v___x_4462_; lean_object* v___x_4463_; 
v___x_4458_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4404_);
v___x_4459_ = l_Lean_MessageData_ofName(v_declName_4404_);
v___x_4460_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4460_, 0, v___x_4458_);
lean_ctor_set(v___x_4460_, 1, v___x_4459_);
v___x_4461_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__3, &l_Lean_Meta_addInstance___closed__3_once, _init_l_Lean_Meta_addInstance___closed__3);
v___x_4462_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4462_, 0, v___x_4460_);
lean_ctor_set(v___x_4462_, 1, v___x_4461_);
v___x_4463_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4462_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
if (lean_obj_tag(v___x_4463_) == 0)
{
lean_dec_ref_known(v___x_4463_, 1);
v___y_4415_ = v_a_4448_;
v___y_4416_ = v___y_4443_;
v___y_4417_ = v___y_4444_;
v___y_4418_ = v___y_4445_;
v___y_4419_ = v___y_4446_;
goto v___jp_4414_;
}
else
{
lean_dec(v_a_4448_);
lean_dec(v_a_4413_);
lean_dec(v_prio_4406_);
lean_dec(v_declName_4404_);
return v___x_4463_;
}
}
}
else
{
lean_object* v___x_4464_; lean_object* v___x_4465_; lean_object* v___x_4466_; lean_object* v___x_4467_; lean_object* v___x_4468_; lean_object* v___x_4469_; 
v___x_4464_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__1, &l_Lean_Meta_addInstance___closed__1_once, _init_l_Lean_Meta_addInstance___closed__1);
lean_inc(v_declName_4404_);
v___x_4465_ = l_Lean_MessageData_ofName(v_declName_4404_);
v___x_4466_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4466_, 0, v___x_4464_);
lean_ctor_set(v___x_4466_, 1, v___x_4465_);
v___x_4467_ = lean_obj_once(&l_Lean_Meta_addInstance___closed__5, &l_Lean_Meta_addInstance___closed__5_once, _init_l_Lean_Meta_addInstance___closed__5);
v___x_4468_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4468_, 0, v___x_4466_);
lean_ctor_set(v___x_4468_, 1, v___x_4467_);
v___x_4469_ = l_Lean_logWarning___at___00Lean_Meta_checkImpossibleInstance_spec__3(v___x_4468_, v___y_4443_, v___y_4444_, v___y_4445_, v___y_4446_);
if (lean_obj_tag(v___x_4469_) == 0)
{
lean_dec_ref_known(v___x_4469_, 1);
v___y_4415_ = v_a_4448_;
v___y_4416_ = v___y_4443_;
v___y_4417_ = v___y_4444_;
v___y_4418_ = v___y_4445_;
v___y_4419_ = v___y_4446_;
goto v___jp_4414_;
}
else
{
lean_dec(v_a_4448_);
lean_dec(v_a_4413_);
lean_dec(v_prio_4406_);
lean_dec(v_declName_4404_);
return v___x_4469_;
}
}
}
else
{
lean_object* v_a_4470_; lean_object* v___x_4472_; uint8_t v_isShared_4473_; uint8_t v_isSharedCheck_4477_; 
lean_dec(v_a_4448_);
lean_dec(v_a_4413_);
lean_dec(v_prio_4406_);
lean_dec(v_declName_4404_);
v_a_4470_ = lean_ctor_get(v___x_4452_, 0);
v_isSharedCheck_4477_ = !lean_is_exclusive(v___x_4452_);
if (v_isSharedCheck_4477_ == 0)
{
v___x_4472_ = v___x_4452_;
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
else
{
lean_inc(v_a_4470_);
lean_dec(v___x_4452_);
v___x_4472_ = lean_box(0);
v_isShared_4473_ = v_isSharedCheck_4477_;
goto v_resetjp_4471_;
}
v_resetjp_4471_:
{
lean_object* v___x_4475_; 
if (v_isShared_4473_ == 0)
{
v___x_4475_ = v___x_4472_;
goto v_reusejp_4474_;
}
else
{
lean_object* v_reuseFailAlloc_4476_; 
v_reuseFailAlloc_4476_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4476_, 0, v_a_4470_);
v___x_4475_ = v_reuseFailAlloc_4476_;
goto v_reusejp_4474_;
}
v_reusejp_4474_:
{
return v___x_4475_;
}
}
}
}
}
}
else
{
lean_object* v_a_4478_; lean_object* v___x_4480_; uint8_t v_isShared_4481_; uint8_t v_isSharedCheck_4485_; 
lean_dec(v_a_4413_);
lean_dec(v_prio_4406_);
lean_dec(v_declName_4404_);
v_a_4478_ = lean_ctor_get(v___x_4447_, 0);
v_isSharedCheck_4485_ = !lean_is_exclusive(v___x_4447_);
if (v_isSharedCheck_4485_ == 0)
{
v___x_4480_ = v___x_4447_;
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
else
{
lean_inc(v_a_4478_);
lean_dec(v___x_4447_);
v___x_4480_ = lean_box(0);
v_isShared_4481_ = v_isSharedCheck_4485_;
goto v_resetjp_4479_;
}
v_resetjp_4479_:
{
lean_object* v___x_4483_; 
if (v_isShared_4481_ == 0)
{
v___x_4483_ = v___x_4480_;
goto v_reusejp_4482_;
}
else
{
lean_object* v_reuseFailAlloc_4484_; 
v_reuseFailAlloc_4484_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4484_, 0, v_a_4478_);
v___x_4483_ = v_reuseFailAlloc_4484_;
goto v_reusejp_4482_;
}
v_reusejp_4482_:
{
return v___x_4483_;
}
}
}
}
}
else
{
lean_object* v_a_4500_; lean_object* v___x_4502_; uint8_t v_isShared_4503_; uint8_t v_isSharedCheck_4507_; 
lean_dec(v_prio_4406_);
lean_dec(v_declName_4404_);
v_a_4500_ = lean_ctor_get(v___x_4412_, 0);
v_isSharedCheck_4507_ = !lean_is_exclusive(v___x_4412_);
if (v_isSharedCheck_4507_ == 0)
{
v___x_4502_ = v___x_4412_;
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
else
{
lean_inc(v_a_4500_);
lean_dec(v___x_4412_);
v___x_4502_ = lean_box(0);
v_isShared_4503_ = v_isSharedCheck_4507_;
goto v_resetjp_4501_;
}
v_resetjp_4501_:
{
lean_object* v___x_4505_; 
if (v_isShared_4503_ == 0)
{
v___x_4505_ = v___x_4502_;
goto v_reusejp_4504_;
}
else
{
lean_object* v_reuseFailAlloc_4506_; 
v_reuseFailAlloc_4506_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4506_, 0, v_a_4500_);
v___x_4505_ = v_reuseFailAlloc_4506_;
goto v_reusejp_4504_;
}
v_reusejp_4504_:
{
return v___x_4505_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addInstance___boxed(lean_object* v_declName_4508_, lean_object* v_attrKind_4509_, lean_object* v_prio_4510_, lean_object* v_a_4511_, lean_object* v_a_4512_, lean_object* v_a_4513_, lean_object* v_a_4514_, lean_object* v_a_4515_){
_start:
{
uint8_t v_attrKind_boxed_4516_; lean_object* v_res_4517_; 
v_attrKind_boxed_4516_ = lean_unbox(v_attrKind_4509_);
v_res_4517_ = l_Lean_Meta_addInstance(v_declName_4508_, v_attrKind_boxed_4516_, v_prio_4510_, v_a_4511_, v_a_4512_, v_a_4513_, v_a_4514_);
lean_dec(v_a_4514_);
lean_dec_ref(v_a_4513_);
lean_dec(v_a_4512_);
lean_dec_ref(v_a_4511_);
return v_res_4517_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(lean_object* v_00_u03b1_4518_, lean_object* v_constName_4519_, lean_object* v___y_4520_, lean_object* v___y_4521_, lean_object* v___y_4522_, lean_object* v___y_4523_){
_start:
{
lean_object* v___x_4525_; 
v___x_4525_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___redArg(v_constName_4519_, v___y_4520_, v___y_4521_, v___y_4522_, v___y_4523_);
return v___x_4525_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6___boxed(lean_object* v_00_u03b1_4526_, lean_object* v_constName_4527_, lean_object* v___y_4528_, lean_object* v___y_4529_, lean_object* v___y_4530_, lean_object* v___y_4531_, lean_object* v___y_4532_){
_start:
{
lean_object* v_res_4533_; 
v_res_4533_ = l_Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6(v_00_u03b1_4526_, v_constName_4527_, v___y_4528_, v___y_4529_, v___y_4530_, v___y_4531_);
lean_dec(v___y_4531_);
lean_dec_ref(v___y_4530_);
lean_dec(v___y_4529_);
lean_dec_ref(v___y_4528_);
return v_res_4533_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(lean_object* v_00_u03b1_4534_, lean_object* v_ref_4535_, lean_object* v_constName_4536_, lean_object* v___y_4537_, lean_object* v___y_4538_, lean_object* v___y_4539_, lean_object* v___y_4540_){
_start:
{
lean_object* v___x_4542_; 
v___x_4542_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg(v_ref_4535_, v_constName_4536_, v___y_4537_, v___y_4538_, v___y_4539_, v___y_4540_);
return v___x_4542_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___boxed(lean_object* v_00_u03b1_4543_, lean_object* v_ref_4544_, lean_object* v_constName_4545_, lean_object* v___y_4546_, lean_object* v___y_4547_, lean_object* v___y_4548_, lean_object* v___y_4549_, lean_object* v___y_4550_){
_start:
{
lean_object* v_res_4551_; 
v_res_4551_ = l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7(v_00_u03b1_4543_, v_ref_4544_, v_constName_4545_, v___y_4546_, v___y_4547_, v___y_4548_, v___y_4549_);
lean_dec(v___y_4549_);
lean_dec_ref(v___y_4548_);
lean_dec(v___y_4547_);
lean_dec_ref(v___y_4546_);
lean_dec(v_ref_4544_);
return v_res_4551_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(lean_object* v_00_u03b1_4552_, lean_object* v_ref_4553_, lean_object* v_msg_4554_, lean_object* v_declHint_4555_, lean_object* v___y_4556_, lean_object* v___y_4557_, lean_object* v___y_4558_, lean_object* v___y_4559_){
_start:
{
lean_object* v___x_4561_; 
v___x_4561_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___redArg(v_ref_4553_, v_msg_4554_, v_declHint_4555_, v___y_4556_, v___y_4557_, v___y_4558_, v___y_4559_);
return v___x_4561_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8___boxed(lean_object* v_00_u03b1_4562_, lean_object* v_ref_4563_, lean_object* v_msg_4564_, lean_object* v_declHint_4565_, lean_object* v___y_4566_, lean_object* v___y_4567_, lean_object* v___y_4568_, lean_object* v___y_4569_, lean_object* v___y_4570_){
_start:
{
lean_object* v_res_4571_; 
v_res_4571_ = l_Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8(v_00_u03b1_4562_, v_ref_4563_, v_msg_4564_, v_declHint_4565_, v___y_4566_, v___y_4567_, v___y_4568_, v___y_4569_);
lean_dec(v___y_4569_);
lean_dec_ref(v___y_4568_);
lean_dec(v___y_4567_);
lean_dec_ref(v___y_4566_);
lean_dec(v_ref_4563_);
return v_res_4571_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(lean_object* v_msg_4572_, lean_object* v_declHint_4573_, lean_object* v___y_4574_, lean_object* v___y_4575_, lean_object* v___y_4576_, lean_object* v___y_4577_){
_start:
{
lean_object* v___x_4579_; 
v___x_4579_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg(v_msg_4572_, v_declHint_4573_, v___y_4577_);
return v___x_4579_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___boxed(lean_object* v_msg_4580_, lean_object* v_declHint_4581_, lean_object* v___y_4582_, lean_object* v___y_4583_, lean_object* v___y_4584_, lean_object* v___y_4585_, lean_object* v___y_4586_){
_start:
{
lean_object* v_res_4587_; 
v_res_4587_ = l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10(v_msg_4580_, v_declHint_4581_, v___y_4582_, v___y_4583_, v___y_4584_, v___y_4585_);
lean_dec(v___y_4585_);
lean_dec_ref(v___y_4584_);
lean_dec(v___y_4583_);
lean_dec_ref(v___y_4582_);
return v_res_4587_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(lean_object* v_00_u03b1_4588_, lean_object* v_ref_4589_, lean_object* v_msg_4590_, lean_object* v___y_4591_, lean_object* v___y_4592_, lean_object* v___y_4593_, lean_object* v___y_4594_){
_start:
{
lean_object* v___x_4596_; 
v___x_4596_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___redArg(v_ref_4589_, v_msg_4590_, v___y_4591_, v___y_4592_, v___y_4593_, v___y_4594_);
return v___x_4596_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10___boxed(lean_object* v_00_u03b1_4597_, lean_object* v_ref_4598_, lean_object* v_msg_4599_, lean_object* v___y_4600_, lean_object* v___y_4601_, lean_object* v___y_4602_, lean_object* v___y_4603_, lean_object* v___y_4604_){
_start:
{
lean_object* v_res_4605_; 
v_res_4605_ = l_Lean_throwErrorAt___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__10(v_00_u03b1_4597_, v_ref_4598_, v_msg_4599_, v___y_4600_, v___y_4601_, v___y_4602_, v___y_4603_);
lean_dec(v___y_4603_);
lean_dec_ref(v___y_4602_);
lean_dec(v___y_4601_);
lean_dec_ref(v___y_4600_);
lean_dec(v_ref_4598_);
return v_res_4605_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(lean_object* v_declName_4606_, uint8_t v_s_4607_, lean_object* v___y_4608_, lean_object* v___y_4609_){
_start:
{
lean_object* v___x_4611_; lean_object* v_env_4612_; lean_object* v_nextMacroScope_4613_; lean_object* v_ngen_4614_; lean_object* v_auxDeclNGen_4615_; lean_object* v_traceState_4616_; lean_object* v_messages_4617_; lean_object* v_infoState_4618_; lean_object* v_snapshotTasks_4619_; lean_object* v___x_4621_; uint8_t v_isShared_4622_; uint8_t v_isSharedCheck_4648_; 
v___x_4611_ = lean_st_ref_take(v___y_4609_);
v_env_4612_ = lean_ctor_get(v___x_4611_, 0);
v_nextMacroScope_4613_ = lean_ctor_get(v___x_4611_, 1);
v_ngen_4614_ = lean_ctor_get(v___x_4611_, 2);
v_auxDeclNGen_4615_ = lean_ctor_get(v___x_4611_, 3);
v_traceState_4616_ = lean_ctor_get(v___x_4611_, 4);
v_messages_4617_ = lean_ctor_get(v___x_4611_, 6);
v_infoState_4618_ = lean_ctor_get(v___x_4611_, 7);
v_snapshotTasks_4619_ = lean_ctor_get(v___x_4611_, 8);
v_isSharedCheck_4648_ = !lean_is_exclusive(v___x_4611_);
if (v_isSharedCheck_4648_ == 0)
{
lean_object* v_unused_4649_; 
v_unused_4649_ = lean_ctor_get(v___x_4611_, 5);
lean_dec(v_unused_4649_);
v___x_4621_ = v___x_4611_;
v_isShared_4622_ = v_isSharedCheck_4648_;
goto v_resetjp_4620_;
}
else
{
lean_inc(v_snapshotTasks_4619_);
lean_inc(v_infoState_4618_);
lean_inc(v_messages_4617_);
lean_inc(v_traceState_4616_);
lean_inc(v_auxDeclNGen_4615_);
lean_inc(v_ngen_4614_);
lean_inc(v_nextMacroScope_4613_);
lean_inc(v_env_4612_);
lean_dec(v___x_4611_);
v___x_4621_ = lean_box(0);
v_isShared_4622_ = v_isSharedCheck_4648_;
goto v_resetjp_4620_;
}
v_resetjp_4620_:
{
uint8_t v___x_4623_; lean_object* v___x_4624_; lean_object* v___x_4625_; lean_object* v___x_4626_; lean_object* v___x_4628_; 
v___x_4623_ = 0;
v___x_4624_ = lean_box(0);
v___x_4625_ = l___private_Lean_ReducibilityAttrs_0__Lean_setReducibilityStatusCore(v_env_4612_, v_declName_4606_, v_s_4607_, v___x_4623_, v___x_4624_);
v___x_4626_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4622_ == 0)
{
lean_ctor_set(v___x_4621_, 5, v___x_4626_);
lean_ctor_set(v___x_4621_, 0, v___x_4625_);
v___x_4628_ = v___x_4621_;
goto v_reusejp_4627_;
}
else
{
lean_object* v_reuseFailAlloc_4647_; 
v_reuseFailAlloc_4647_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4647_, 0, v___x_4625_);
lean_ctor_set(v_reuseFailAlloc_4647_, 1, v_nextMacroScope_4613_);
lean_ctor_set(v_reuseFailAlloc_4647_, 2, v_ngen_4614_);
lean_ctor_set(v_reuseFailAlloc_4647_, 3, v_auxDeclNGen_4615_);
lean_ctor_set(v_reuseFailAlloc_4647_, 4, v_traceState_4616_);
lean_ctor_set(v_reuseFailAlloc_4647_, 5, v___x_4626_);
lean_ctor_set(v_reuseFailAlloc_4647_, 6, v_messages_4617_);
lean_ctor_set(v_reuseFailAlloc_4647_, 7, v_infoState_4618_);
lean_ctor_set(v_reuseFailAlloc_4647_, 8, v_snapshotTasks_4619_);
v___x_4628_ = v_reuseFailAlloc_4647_;
goto v_reusejp_4627_;
}
v_reusejp_4627_:
{
lean_object* v___x_4629_; lean_object* v___x_4630_; lean_object* v_mctx_4631_; lean_object* v_zetaDeltaFVarIds_4632_; lean_object* v_postponed_4633_; lean_object* v_diag_4634_; lean_object* v___x_4636_; uint8_t v_isShared_4637_; uint8_t v_isSharedCheck_4645_; 
v___x_4629_ = lean_st_ref_set(v___y_4609_, v___x_4628_);
v___x_4630_ = lean_st_ref_take(v___y_4608_);
v_mctx_4631_ = lean_ctor_get(v___x_4630_, 0);
v_zetaDeltaFVarIds_4632_ = lean_ctor_get(v___x_4630_, 2);
v_postponed_4633_ = lean_ctor_get(v___x_4630_, 3);
v_diag_4634_ = lean_ctor_get(v___x_4630_, 4);
v_isSharedCheck_4645_ = !lean_is_exclusive(v___x_4630_);
if (v_isSharedCheck_4645_ == 0)
{
lean_object* v_unused_4646_; 
v_unused_4646_ = lean_ctor_get(v___x_4630_, 1);
lean_dec(v_unused_4646_);
v___x_4636_ = v___x_4630_;
v_isShared_4637_ = v_isSharedCheck_4645_;
goto v_resetjp_4635_;
}
else
{
lean_inc(v_diag_4634_);
lean_inc(v_postponed_4633_);
lean_inc(v_zetaDeltaFVarIds_4632_);
lean_inc(v_mctx_4631_);
lean_dec(v___x_4630_);
v___x_4636_ = lean_box(0);
v_isShared_4637_ = v_isSharedCheck_4645_;
goto v_resetjp_4635_;
}
v_resetjp_4635_:
{
lean_object* v___x_4638_; lean_object* v___x_4640_; 
v___x_4638_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_4637_ == 0)
{
lean_ctor_set(v___x_4636_, 1, v___x_4638_);
v___x_4640_ = v___x_4636_;
goto v_reusejp_4639_;
}
else
{
lean_object* v_reuseFailAlloc_4644_; 
v_reuseFailAlloc_4644_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_4644_, 0, v_mctx_4631_);
lean_ctor_set(v_reuseFailAlloc_4644_, 1, v___x_4638_);
lean_ctor_set(v_reuseFailAlloc_4644_, 2, v_zetaDeltaFVarIds_4632_);
lean_ctor_set(v_reuseFailAlloc_4644_, 3, v_postponed_4633_);
lean_ctor_set(v_reuseFailAlloc_4644_, 4, v_diag_4634_);
v___x_4640_ = v_reuseFailAlloc_4644_;
goto v_reusejp_4639_;
}
v_reusejp_4639_:
{
lean_object* v___x_4641_; lean_object* v___x_4642_; lean_object* v___x_4643_; 
v___x_4641_ = lean_st_ref_set(v___y_4608_, v___x_4640_);
v___x_4642_ = lean_box(0);
v___x_4643_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4643_, 0, v___x_4642_);
return v___x_4643_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg___boxed(lean_object* v_declName_4650_, lean_object* v_s_4651_, lean_object* v___y_4652_, lean_object* v___y_4653_, lean_object* v___y_4654_){
_start:
{
uint8_t v_s_boxed_4655_; lean_object* v_res_4656_; 
v_s_boxed_4655_ = lean_unbox(v_s_4651_);
v_res_4656_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4650_, v_s_boxed_4655_, v___y_4652_, v___y_4653_);
lean_dec(v___y_4653_);
lean_dec(v___y_4652_);
return v_res_4656_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(lean_object* v_declName_4657_, uint8_t v_s_4658_, lean_object* v___y_4659_, lean_object* v___y_4660_, lean_object* v___y_4661_, lean_object* v___y_4662_){
_start:
{
lean_object* v___x_4664_; 
v___x_4664_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4657_, v_s_4658_, v___y_4660_, v___y_4662_);
return v___x_4664_;
}
}
LEAN_EXPORT lean_object* l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___boxed(lean_object* v_declName_4665_, lean_object* v_s_4666_, lean_object* v___y_4667_, lean_object* v___y_4668_, lean_object* v___y_4669_, lean_object* v___y_4670_, lean_object* v___y_4671_){
_start:
{
uint8_t v_s_boxed_4672_; lean_object* v_res_4673_; 
v_s_boxed_4672_ = lean_unbox(v_s_4666_);
v_res_4673_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0(v_declName_4665_, v_s_boxed_4672_, v___y_4667_, v___y_4668_, v___y_4669_, v___y_4670_);
lean_dec(v___y_4670_);
lean_dec_ref(v___y_4669_);
lean_dec(v___y_4668_);
lean_dec_ref(v___y_4667_);
return v_res_4673_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance(lean_object* v_declName_4674_, uint8_t v_attrKind_4675_, lean_object* v_prio_4676_, lean_object* v_a_4677_, lean_object* v_a_4678_, lean_object* v_a_4679_, lean_object* v_a_4680_){
_start:
{
uint8_t v___x_4682_; lean_object* v___x_4683_; lean_object* v___x_4684_; 
v___x_4682_ = 4;
lean_inc(v_declName_4674_);
v___x_4683_ = l_Lean_setReducibilityStatus___at___00Lean_Meta_registerInstance_spec__0___redArg(v_declName_4674_, v___x_4682_, v_a_4678_, v_a_4680_);
lean_dec_ref(v___x_4683_);
v___x_4684_ = l_Lean_Meta_addInstance(v_declName_4674_, v_attrKind_4675_, v_prio_4676_, v_a_4677_, v_a_4678_, v_a_4679_, v_a_4680_);
return v___x_4684_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_registerInstance___boxed(lean_object* v_declName_4685_, lean_object* v_attrKind_4686_, lean_object* v_prio_4687_, lean_object* v_a_4688_, lean_object* v_a_4689_, lean_object* v_a_4690_, lean_object* v_a_4691_, lean_object* v_a_4692_){
_start:
{
uint8_t v_attrKind_boxed_4693_; lean_object* v_res_4694_; 
v_attrKind_boxed_4693_ = lean_unbox(v_attrKind_4686_);
v_res_4694_ = l_Lean_Meta_registerInstance(v_declName_4685_, v_attrKind_boxed_4693_, v_prio_4687_, v_a_4688_, v_a_4689_, v_a_4690_, v_a_4691_);
lean_dec(v_a_4691_);
lean_dec_ref(v_a_4690_);
lean_dec(v_a_4689_);
lean_dec_ref(v_a_4688_);
return v_res_4694_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v_a_4695_, lean_object* v_x_4696_){
_start:
{
lean_inc_ref(v_a_4695_);
return v_a_4695_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_4697_, lean_object* v_x_4698_){
_start:
{
lean_object* v_res_4699_; 
v_res_4699_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v_a_4697_, v_x_4698_);
lean_dec_ref(v_x_4698_);
lean_dec_ref(v_a_4697_);
return v_res_4699_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(lean_object* v_msgData_4700_, lean_object* v___y_4701_, lean_object* v___y_4702_){
_start:
{
lean_object* v___x_4704_; lean_object* v_env_4705_; lean_object* v_options_4706_; lean_object* v___x_4707_; lean_object* v___x_4708_; lean_object* v___x_4709_; lean_object* v___x_4710_; lean_object* v___x_4711_; lean_object* v___x_4712_; lean_object* v___x_4713_; 
v___x_4704_ = lean_st_ref_get(v___y_4702_);
v_env_4705_ = lean_ctor_get(v___x_4704_, 0);
lean_inc_ref(v_env_4705_);
lean_dec(v___x_4704_);
v_options_4706_ = lean_ctor_get(v___y_4701_, 2);
v___x_4707_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__2);
v___x_4708_ = lean_unsigned_to_nat(32u);
v___x_4709_ = lean_mk_empty_array_with_capacity(v___x_4708_);
lean_dec_ref(v___x_4709_);
v___x_4710_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__5);
lean_inc_ref(v_options_4706_);
v___x_4711_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_4711_, 0, v_env_4705_);
lean_ctor_set(v___x_4711_, 1, v___x_4707_);
lean_ctor_set(v___x_4711_, 2, v___x_4710_);
lean_ctor_set(v___x_4711_, 3, v_options_4706_);
v___x_4712_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v___x_4712_, 0, v___x_4711_);
lean_ctor_set(v___x_4712_, 1, v_msgData_4700_);
v___x_4713_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4713_, 0, v___x_4712_);
return v___x_4713_;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3___boxed(lean_object* v_msgData_4714_, lean_object* v___y_4715_, lean_object* v___y_4716_, lean_object* v___y_4717_){
_start:
{
lean_object* v_res_4718_; 
v_res_4718_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msgData_4714_, v___y_4715_, v___y_4716_);
lean_dec(v___y_4716_);
lean_dec_ref(v___y_4715_);
return v_res_4718_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_msg_4719_, lean_object* v___y_4720_, lean_object* v___y_4721_){
_start:
{
lean_object* v_ref_4723_; lean_object* v___x_4724_; lean_object* v_a_4725_; lean_object* v___x_4727_; uint8_t v_isShared_4728_; uint8_t v_isSharedCheck_4733_; 
v_ref_4723_ = lean_ctor_get(v___y_4720_, 5);
v___x_4724_ = l_Lean_addMessageContextPartial___at___00Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1_spec__3(v_msg_4719_, v___y_4720_, v___y_4721_);
v_a_4725_ = lean_ctor_get(v___x_4724_, 0);
v_isSharedCheck_4733_ = !lean_is_exclusive(v___x_4724_);
if (v_isSharedCheck_4733_ == 0)
{
v___x_4727_ = v___x_4724_;
v_isShared_4728_ = v_isSharedCheck_4733_;
goto v_resetjp_4726_;
}
else
{
lean_inc(v_a_4725_);
lean_dec(v___x_4724_);
v___x_4727_ = lean_box(0);
v_isShared_4728_ = v_isSharedCheck_4733_;
goto v_resetjp_4726_;
}
v_resetjp_4726_:
{
lean_object* v___x_4729_; lean_object* v___x_4731_; 
lean_inc(v_ref_4723_);
v___x_4729_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_4729_, 0, v_ref_4723_);
lean_ctor_set(v___x_4729_, 1, v_a_4725_);
if (v_isShared_4728_ == 0)
{
lean_ctor_set_tag(v___x_4727_, 1);
lean_ctor_set(v___x_4727_, 0, v___x_4729_);
v___x_4731_ = v___x_4727_;
goto v_reusejp_4730_;
}
else
{
lean_object* v_reuseFailAlloc_4732_; 
v_reuseFailAlloc_4732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4732_, 0, v___x_4729_);
v___x_4731_ = v_reuseFailAlloc_4732_;
goto v_reusejp_4730_;
}
v_reusejp_4730_:
{
return v___x_4731_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg___boxed(lean_object* v_msg_4734_, lean_object* v___y_4735_, lean_object* v___y_4736_, lean_object* v___y_4737_){
_start:
{
lean_object* v_res_4738_; 
v_res_4738_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_4734_, v___y_4735_, v___y_4736_);
lean_dec(v___y_4736_);
lean_dec_ref(v___y_4735_);
return v_res_4738_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(lean_object* v_keys_4739_, lean_object* v_i_4740_, lean_object* v_k_4741_){
_start:
{
lean_object* v___x_4742_; uint8_t v___x_4743_; 
v___x_4742_ = lean_array_get_size(v_keys_4739_);
v___x_4743_ = lean_nat_dec_lt(v_i_4740_, v___x_4742_);
if (v___x_4743_ == 0)
{
lean_dec(v_i_4740_);
return v___x_4743_;
}
else
{
lean_object* v_k_x27_4744_; uint8_t v___x_4745_; 
v_k_x27_4744_ = lean_array_fget_borrowed(v_keys_4739_, v_i_4740_);
v___x_4745_ = lean_name_eq(v_k_4741_, v_k_x27_4744_);
if (v___x_4745_ == 0)
{
lean_object* v___x_4746_; lean_object* v___x_4747_; 
v___x_4746_ = lean_unsigned_to_nat(1u);
v___x_4747_ = lean_nat_add(v_i_4740_, v___x_4746_);
lean_dec(v_i_4740_);
v_i_4740_ = v___x_4747_;
goto _start;
}
else
{
lean_dec(v_i_4740_);
return v___x_4745_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg___boxed(lean_object* v_keys_4749_, lean_object* v_i_4750_, lean_object* v_k_4751_){
_start:
{
uint8_t v_res_4752_; lean_object* v_r_4753_; 
v_res_4752_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_4749_, v_i_4750_, v_k_4751_);
lean_dec(v_k_4751_);
lean_dec_ref(v_keys_4749_);
v_r_4753_ = lean_box(v_res_4752_);
return v_r_4753_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(lean_object* v_x_4754_, size_t v_x_4755_, lean_object* v_x_4756_){
_start:
{
if (lean_obj_tag(v_x_4754_) == 0)
{
lean_object* v_es_4757_; lean_object* v___x_4758_; size_t v___x_4759_; size_t v___x_4760_; lean_object* v_j_4761_; lean_object* v___x_4762_; 
v_es_4757_ = lean_ctor_get(v_x_4754_, 0);
v___x_4758_ = lean_box(2);
v___x_4759_ = ((size_t)31ULL);
v___x_4760_ = lean_usize_land(v_x_4755_, v___x_4759_);
v_j_4761_ = lean_usize_to_nat(v___x_4760_);
v___x_4762_ = lean_array_get_borrowed(v___x_4758_, v_es_4757_, v_j_4761_);
lean_dec(v_j_4761_);
switch(lean_obj_tag(v___x_4762_))
{
case 0:
{
lean_object* v_key_4763_; uint8_t v___x_4764_; 
v_key_4763_ = lean_ctor_get(v___x_4762_, 0);
v___x_4764_ = lean_name_eq(v_x_4756_, v_key_4763_);
return v___x_4764_;
}
case 1:
{
lean_object* v_node_4765_; size_t v___x_4766_; size_t v___x_4767_; 
v_node_4765_ = lean_ctor_get(v___x_4762_, 0);
v___x_4766_ = ((size_t)5ULL);
v___x_4767_ = lean_usize_shift_right(v_x_4755_, v___x_4766_);
v_x_4754_ = v_node_4765_;
v_x_4755_ = v___x_4767_;
goto _start;
}
default: 
{
uint8_t v___x_4769_; 
v___x_4769_ = 0;
return v___x_4769_;
}
}
}
else
{
lean_object* v_ks_4770_; lean_object* v___x_4771_; uint8_t v___x_4772_; 
v_ks_4770_ = lean_ctor_get(v_x_4754_, 0);
v___x_4771_ = lean_unsigned_to_nat(0u);
v___x_4772_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_ks_4770_, v___x_4771_, v_x_4756_);
return v___x_4772_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_x_4773_, lean_object* v_x_4774_, lean_object* v_x_4775_){
_start:
{
size_t v_x_2343__boxed_4776_; uint8_t v_res_4777_; lean_object* v_r_4778_; 
v_x_2343__boxed_4776_ = lean_unbox_usize(v_x_4774_);
lean_dec(v_x_4774_);
v_res_4777_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4773_, v_x_2343__boxed_4776_, v_x_4775_);
lean_dec(v_x_4775_);
lean_dec_ref(v_x_4773_);
v_r_4778_ = lean_box(v_res_4777_);
return v_r_4778_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_x_4779_, lean_object* v_x_4780_){
_start:
{
uint64_t v___y_4782_; 
if (lean_obj_tag(v_x_4780_) == 0)
{
uint64_t v___x_4785_; 
v___x_4785_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0);
v___y_4782_ = v___x_4785_;
goto v___jp_4781_;
}
else
{
uint64_t v_hash_4786_; 
v_hash_4786_ = lean_ctor_get_uint64(v_x_4780_, sizeof(void*)*2);
v___y_4782_ = v_hash_4786_;
goto v___jp_4781_;
}
v___jp_4781_:
{
size_t v___x_4783_; uint8_t v___x_4784_; 
v___x_4783_ = lean_uint64_to_usize(v___y_4782_);
v___x_4784_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_4779_, v___x_4783_, v_x_4780_);
return v___x_4784_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_x_4787_, lean_object* v_x_4788_){
_start:
{
uint8_t v_res_4789_; lean_object* v_r_4790_; 
v_res_4789_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_4787_, v_x_4788_);
lean_dec(v_x_4788_);
lean_dec_ref(v_x_4787_);
v_r_4790_ = lean_box(v_res_4789_);
return v_r_4790_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(lean_object* v_d_4791_, lean_object* v_declName_4792_, lean_object* v___y_4793_, lean_object* v___y_4794_){
_start:
{
lean_object* v_instanceNames_4799_; uint8_t v___x_4800_; 
v_instanceNames_4799_ = lean_ctor_get(v_d_4791_, 1);
v___x_4800_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_4799_, v_declName_4792_);
if (v___x_4800_ == 0)
{
lean_object* v___x_4801_; lean_object* v___x_4802_; lean_object* v___x_4803_; lean_object* v___x_4804_; lean_object* v___x_4805_; lean_object* v___x_4806_; lean_object* v_a_4807_; lean_object* v___x_4809_; uint8_t v_isShared_4810_; uint8_t v_isSharedCheck_4814_; 
lean_dec_ref(v_d_4791_);
v___x_4801_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_4802_ = l_Lean_MessageData_ofConstName(v_declName_4792_, v___x_4800_);
v___x_4803_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4803_, 0, v___x_4801_);
lean_ctor_set(v___x_4803_, 1, v___x_4802_);
v___x_4804_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__5, &l_Lean_Meta_Instances_erase___redArg___closed__5_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__5);
v___x_4805_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_4805_, 0, v___x_4803_);
lean_ctor_set(v___x_4805_, 1, v___x_4804_);
v___x_4806_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_4805_, v___y_4793_, v___y_4794_);
v_a_4807_ = lean_ctor_get(v___x_4806_, 0);
v_isSharedCheck_4814_ = !lean_is_exclusive(v___x_4806_);
if (v_isSharedCheck_4814_ == 0)
{
v___x_4809_ = v___x_4806_;
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
else
{
lean_inc(v_a_4807_);
lean_dec(v___x_4806_);
v___x_4809_ = lean_box(0);
v_isShared_4810_ = v_isSharedCheck_4814_;
goto v_resetjp_4808_;
}
v_resetjp_4808_:
{
lean_object* v___x_4812_; 
if (v_isShared_4810_ == 0)
{
v___x_4812_ = v___x_4809_;
goto v_reusejp_4811_;
}
else
{
lean_object* v_reuseFailAlloc_4813_; 
v_reuseFailAlloc_4813_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4813_, 0, v_a_4807_);
v___x_4812_ = v_reuseFailAlloc_4813_;
goto v_reusejp_4811_;
}
v_reusejp_4811_:
{
return v___x_4812_;
}
}
}
else
{
goto v___jp_4796_;
}
v___jp_4796_:
{
lean_object* v___x_4797_; lean_object* v___x_4798_; 
v___x_4797_ = l_Lean_Meta_Instances_eraseCore(v_d_4791_, v_declName_4792_);
v___x_4798_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4798_, 0, v___x_4797_);
return v___x_4798_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0___boxed(lean_object* v_d_4815_, lean_object* v_declName_4816_, lean_object* v___y_4817_, lean_object* v___y_4818_, lean_object* v___y_4819_){
_start:
{
lean_object* v_res_4820_; 
v_res_4820_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v_d_4815_, v_declName_4816_, v___y_4817_, v___y_4818_);
lean_dec(v___y_4818_);
lean_dec_ref(v___y_4817_);
return v_res_4820_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4821_, lean_object* v_declName_4822_, lean_object* v___y_4823_, lean_object* v___y_4824_){
_start:
{
lean_object* v___x_4826_; lean_object* v_env_4827_; lean_object* v___x_4828_; lean_object* v_ext_4829_; lean_object* v_toEnvExtension_4830_; lean_object* v_asyncMode_4831_; lean_object* v___x_4832_; lean_object* v___x_4833_; 
v___x_4826_ = lean_st_ref_get(v___y_4824_);
v_env_4827_ = lean_ctor_get(v___x_4826_, 0);
lean_inc_ref(v_env_4827_);
lean_dec(v___x_4826_);
v___x_4828_ = l_Lean_Meta_instanceExtension;
v_ext_4829_ = lean_ctor_get(v___x_4828_, 1);
v_toEnvExtension_4830_ = lean_ctor_get(v_ext_4829_, 0);
v_asyncMode_4831_ = lean_ctor_get(v_toEnvExtension_4830_, 2);
v___x_4832_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_4821_, v___x_4828_, v_env_4827_, v_asyncMode_4831_);
v___x_4833_ = l_Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0(v___x_4832_, v_declName_4822_, v___y_4823_, v___y_4824_);
if (lean_obj_tag(v___x_4833_) == 0)
{
lean_object* v_a_4834_; lean_object* v___x_4836_; uint8_t v_isShared_4837_; uint8_t v_isSharedCheck_4863_; 
v_a_4834_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4863_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4863_ == 0)
{
v___x_4836_ = v___x_4833_;
v_isShared_4837_ = v_isSharedCheck_4863_;
goto v_resetjp_4835_;
}
else
{
lean_inc(v_a_4834_);
lean_dec(v___x_4833_);
v___x_4836_ = lean_box(0);
v_isShared_4837_ = v_isSharedCheck_4863_;
goto v_resetjp_4835_;
}
v_resetjp_4835_:
{
lean_object* v___x_4838_; lean_object* v_env_4839_; lean_object* v_nextMacroScope_4840_; lean_object* v_ngen_4841_; lean_object* v_auxDeclNGen_4842_; lean_object* v_traceState_4843_; lean_object* v_messages_4844_; lean_object* v_infoState_4845_; lean_object* v_snapshotTasks_4846_; lean_object* v___x_4848_; uint8_t v_isShared_4849_; uint8_t v_isSharedCheck_4861_; 
v___x_4838_ = lean_st_ref_take(v___y_4824_);
v_env_4839_ = lean_ctor_get(v___x_4838_, 0);
v_nextMacroScope_4840_ = lean_ctor_get(v___x_4838_, 1);
v_ngen_4841_ = lean_ctor_get(v___x_4838_, 2);
v_auxDeclNGen_4842_ = lean_ctor_get(v___x_4838_, 3);
v_traceState_4843_ = lean_ctor_get(v___x_4838_, 4);
v_messages_4844_ = lean_ctor_get(v___x_4838_, 6);
v_infoState_4845_ = lean_ctor_get(v___x_4838_, 7);
v_snapshotTasks_4846_ = lean_ctor_get(v___x_4838_, 8);
v_isSharedCheck_4861_ = !lean_is_exclusive(v___x_4838_);
if (v_isSharedCheck_4861_ == 0)
{
lean_object* v_unused_4862_; 
v_unused_4862_ = lean_ctor_get(v___x_4838_, 5);
lean_dec(v_unused_4862_);
v___x_4848_ = v___x_4838_;
v_isShared_4849_ = v_isSharedCheck_4861_;
goto v_resetjp_4847_;
}
else
{
lean_inc(v_snapshotTasks_4846_);
lean_inc(v_infoState_4845_);
lean_inc(v_messages_4844_);
lean_inc(v_traceState_4843_);
lean_inc(v_auxDeclNGen_4842_);
lean_inc(v_ngen_4841_);
lean_inc(v_nextMacroScope_4840_);
lean_inc(v_env_4839_);
lean_dec(v___x_4838_);
v___x_4848_ = lean_box(0);
v_isShared_4849_ = v_isSharedCheck_4861_;
goto v_resetjp_4847_;
}
v_resetjp_4847_:
{
lean_object* v___f_4850_; lean_object* v___x_4851_; lean_object* v___x_4852_; lean_object* v___x_4854_; 
v___f_4850_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 2, 1);
lean_closure_set(v___f_4850_, 0, v_a_4834_);
v___x_4851_ = l_Lean_ScopedEnvExtension_modifyState___redArg(v___x_4828_, v_env_4839_, v___f_4850_);
v___x_4852_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_4849_ == 0)
{
lean_ctor_set(v___x_4848_, 5, v___x_4852_);
lean_ctor_set(v___x_4848_, 0, v___x_4851_);
v___x_4854_ = v___x_4848_;
goto v_reusejp_4853_;
}
else
{
lean_object* v_reuseFailAlloc_4860_; 
v_reuseFailAlloc_4860_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_4860_, 0, v___x_4851_);
lean_ctor_set(v_reuseFailAlloc_4860_, 1, v_nextMacroScope_4840_);
lean_ctor_set(v_reuseFailAlloc_4860_, 2, v_ngen_4841_);
lean_ctor_set(v_reuseFailAlloc_4860_, 3, v_auxDeclNGen_4842_);
lean_ctor_set(v_reuseFailAlloc_4860_, 4, v_traceState_4843_);
lean_ctor_set(v_reuseFailAlloc_4860_, 5, v___x_4852_);
lean_ctor_set(v_reuseFailAlloc_4860_, 6, v_messages_4844_);
lean_ctor_set(v_reuseFailAlloc_4860_, 7, v_infoState_4845_);
lean_ctor_set(v_reuseFailAlloc_4860_, 8, v_snapshotTasks_4846_);
v___x_4854_ = v_reuseFailAlloc_4860_;
goto v_reusejp_4853_;
}
v_reusejp_4853_:
{
lean_object* v___x_4855_; lean_object* v___x_4856_; lean_object* v___x_4858_; 
v___x_4855_ = lean_st_ref_set(v___y_4824_, v___x_4854_);
v___x_4856_ = lean_box(0);
if (v_isShared_4837_ == 0)
{
lean_ctor_set(v___x_4836_, 0, v___x_4856_);
v___x_4858_ = v___x_4836_;
goto v_reusejp_4857_;
}
else
{
lean_object* v_reuseFailAlloc_4859_; 
v_reuseFailAlloc_4859_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4859_, 0, v___x_4856_);
v___x_4858_ = v_reuseFailAlloc_4859_;
goto v_reusejp_4857_;
}
v_reusejp_4857_:
{
return v___x_4858_;
}
}
}
}
}
else
{
lean_object* v_a_4864_; lean_object* v___x_4866_; uint8_t v_isShared_4867_; uint8_t v_isSharedCheck_4871_; 
v_a_4864_ = lean_ctor_get(v___x_4833_, 0);
v_isSharedCheck_4871_ = !lean_is_exclusive(v___x_4833_);
if (v_isSharedCheck_4871_ == 0)
{
v___x_4866_ = v___x_4833_;
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
else
{
lean_inc(v_a_4864_);
lean_dec(v___x_4833_);
v___x_4866_ = lean_box(0);
v_isShared_4867_ = v_isSharedCheck_4871_;
goto v_resetjp_4865_;
}
v_resetjp_4865_:
{
lean_object* v___x_4869_; 
if (v_isShared_4867_ == 0)
{
v___x_4869_ = v___x_4866_;
goto v_reusejp_4868_;
}
else
{
lean_object* v_reuseFailAlloc_4870_; 
v_reuseFailAlloc_4870_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4870_, 0, v_a_4864_);
v___x_4869_ = v_reuseFailAlloc_4870_;
goto v_reusejp_4868_;
}
v_reusejp_4868_:
{
return v___x_4869_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4872_, lean_object* v_declName_4873_, lean_object* v___y_4874_, lean_object* v___y_4875_, lean_object* v___y_4876_){
_start:
{
lean_object* v_res_4877_; 
v_res_4877_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4872_, v_declName_4873_, v___y_4874_, v___y_4875_);
lean_dec(v___y_4875_);
lean_dec_ref(v___y_4874_);
lean_dec_ref(v___x_4872_);
return v_res_4877_;
}
}
static uint64_t _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4884_; uint64_t v___x_4885_; 
v___x_4884_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4885_ = l___private_Lean_Meta_Basic_0__Lean_Meta_Config_toKey(v___x_4884_);
return v___x_4885_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
uint64_t v___x_4886_; lean_object* v___x_4887_; lean_object* v___x_4888_; 
v___x_4886_ = lean_uint64_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4887_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_4888_ = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(v___x_4888_, 0, v___x_4887_);
lean_ctor_set_uint64(v___x_4888_, sizeof(void*)*1, v___x_4886_);
return v___x_4888_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4889_; 
v___x_4889_ = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return v___x_4889_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4890_; lean_object* v___x_4891_; 
v___x_4890_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__3_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4891_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_4891_, 0, v___x_4890_);
return v___x_4891_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4892_; lean_object* v___x_4893_; 
v___x_4892_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4893_ = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(v___x_4893_, 0, v___x_4892_);
lean_ctor_set(v___x_4893_, 1, v___x_4892_);
lean_ctor_set(v___x_4893_, 2, v___x_4892_);
lean_ctor_set(v___x_4893_, 3, v___x_4892_);
lean_ctor_set(v___x_4893_, 4, v___x_4892_);
lean_ctor_set(v___x_4893_, 5, v___x_4892_);
return v___x_4893_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4894_; lean_object* v___x_4895_; 
v___x_4894_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4895_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4895_, 0, v___x_4894_);
lean_ctor_set(v___x_4895_, 1, v___x_4894_);
lean_ctor_set(v___x_4895_, 2, v___x_4894_);
lean_ctor_set(v___x_4895_, 3, v___x_4894_);
lean_ctor_set(v___x_4895_, 4, v___x_4894_);
return v___x_4895_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(lean_object* v___x_4896_, lean_object* v___x_4897_, lean_object* v_declName_4898_, lean_object* v_stx_4899_, uint8_t v_attrKind_4900_, lean_object* v___y_4901_, lean_object* v___y_4902_){
_start:
{
lean_object* v___x_4904_; lean_object* v___x_4905_; lean_object* v___x_4906_; 
v___x_4904_ = lean_unsigned_to_nat(1u);
v___x_4905_ = l_Lean_Syntax_getArg(v_stx_4899_, v___x_4904_);
v___x_4906_ = l_Lean_getAttrParamOptPrio(v___x_4905_, v___y_4901_, v___y_4902_);
if (lean_obj_tag(v___x_4906_) == 0)
{
lean_object* v_a_4907_; uint8_t v___x_4908_; uint8_t v___x_4909_; lean_object* v___x_4910_; lean_object* v___x_4911_; lean_object* v___x_4912_; lean_object* v___x_4913_; lean_object* v___x_4914_; size_t v___x_4915_; lean_object* v___x_4916_; lean_object* v___x_4917_; lean_object* v___x_4918_; lean_object* v___x_4919_; lean_object* v___x_4920_; lean_object* v___x_4921_; lean_object* v___x_4922_; lean_object* v___x_4923_; lean_object* v___x_4924_; lean_object* v___x_4925_; lean_object* v___x_4926_; lean_object* v___x_4927_; 
v_a_4907_ = lean_ctor_get(v___x_4906_, 0);
lean_inc(v_a_4907_);
lean_dec_ref_known(v___x_4906_, 1);
v___x_4908_ = 0;
v___x_4909_ = 1;
v___x_4910_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4911_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4912_ = lean_unsigned_to_nat(32u);
v___x_4913_ = lean_mk_empty_array_with_capacity(v___x_4912_);
v___x_4914_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_4915_ = ((size_t)5ULL);
lean_inc_n(v___x_4896_, 6);
v___x_4916_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_4916_, 0, v___x_4914_);
lean_ctor_set(v___x_4916_, 1, v___x_4913_);
lean_ctor_set(v___x_4916_, 2, v___x_4896_);
lean_ctor_set(v___x_4916_, 3, v___x_4896_);
lean_ctor_set_usize(v___x_4916_, 4, v___x_4915_);
v___x_4917_ = lean_box(1);
lean_inc_ref(v___x_4916_);
v___x_4918_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_4918_, 0, v___x_4911_);
lean_ctor_set(v___x_4918_, 1, v___x_4916_);
lean_ctor_set(v___x_4918_, 2, v___x_4917_);
v___x_4919_ = lean_mk_empty_array_with_capacity(v___x_4896_);
v___x_4920_ = lean_box(0);
lean_inc(v___x_4897_);
v___x_4921_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_4921_, 0, v___x_4910_);
lean_ctor_set(v___x_4921_, 1, v___x_4897_);
lean_ctor_set(v___x_4921_, 2, v___x_4918_);
lean_ctor_set(v___x_4921_, 3, v___x_4919_);
lean_ctor_set(v___x_4921_, 4, v___x_4920_);
lean_ctor_set(v___x_4921_, 5, v___x_4896_);
lean_ctor_set(v___x_4921_, 6, v___x_4920_);
lean_ctor_set_uint8(v___x_4921_, sizeof(void*)*7, v___x_4908_);
lean_ctor_set_uint8(v___x_4921_, sizeof(void*)*7 + 1, v___x_4908_);
lean_ctor_set_uint8(v___x_4921_, sizeof(void*)*7 + 2, v___x_4908_);
lean_ctor_set_uint8(v___x_4921_, sizeof(void*)*7 + 3, v___x_4909_);
v___x_4922_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_4922_, 0, v___x_4896_);
lean_ctor_set(v___x_4922_, 1, v___x_4896_);
lean_ctor_set(v___x_4922_, 2, v___x_4896_);
lean_ctor_set(v___x_4922_, 3, v___x_4896_);
lean_ctor_set(v___x_4922_, 4, v___x_4911_);
lean_ctor_set(v___x_4922_, 5, v___x_4911_);
lean_ctor_set(v___x_4922_, 6, v___x_4911_);
lean_ctor_set(v___x_4922_, 7, v___x_4911_);
lean_ctor_set(v___x_4922_, 8, v___x_4911_);
lean_ctor_set(v___x_4922_, 9, v___x_4911_);
v___x_4923_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4924_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_4925_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_4925_, 0, v___x_4922_);
lean_ctor_set(v___x_4925_, 1, v___x_4923_);
lean_ctor_set(v___x_4925_, 2, v___x_4897_);
lean_ctor_set(v___x_4925_, 3, v___x_4916_);
lean_ctor_set(v___x_4925_, 4, v___x_4924_);
v___x_4926_ = lean_st_mk_ref(v___x_4925_);
v___x_4927_ = l_Lean_Meta_addInstance(v_declName_4898_, v_attrKind_4900_, v_a_4907_, v___x_4921_, v___x_4926_, v___y_4901_, v___y_4902_);
lean_dec_ref_known(v___x_4921_, 7);
if (lean_obj_tag(v___x_4927_) == 0)
{
lean_object* v___x_4929_; uint8_t v_isShared_4930_; uint8_t v_isSharedCheck_4936_; 
v_isSharedCheck_4936_ = !lean_is_exclusive(v___x_4927_);
if (v_isSharedCheck_4936_ == 0)
{
lean_object* v_unused_4937_; 
v_unused_4937_ = lean_ctor_get(v___x_4927_, 0);
lean_dec(v_unused_4937_);
v___x_4929_ = v___x_4927_;
v_isShared_4930_ = v_isSharedCheck_4936_;
goto v_resetjp_4928_;
}
else
{
lean_dec(v___x_4927_);
v___x_4929_ = lean_box(0);
v_isShared_4930_ = v_isSharedCheck_4936_;
goto v_resetjp_4928_;
}
v_resetjp_4928_:
{
lean_object* v___x_4931_; lean_object* v___x_4932_; lean_object* v___x_4934_; 
v___x_4931_ = lean_st_ref_get(v___x_4926_);
lean_dec(v___x_4926_);
lean_dec(v___x_4931_);
v___x_4932_ = lean_box(0);
if (v_isShared_4930_ == 0)
{
lean_ctor_set(v___x_4929_, 0, v___x_4932_);
v___x_4934_ = v___x_4929_;
goto v_reusejp_4933_;
}
else
{
lean_object* v_reuseFailAlloc_4935_; 
v_reuseFailAlloc_4935_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4935_, 0, v___x_4932_);
v___x_4934_ = v_reuseFailAlloc_4935_;
goto v_reusejp_4933_;
}
v_reusejp_4933_:
{
return v___x_4934_;
}
}
}
else
{
lean_dec(v___x_4926_);
return v___x_4927_;
}
}
else
{
lean_object* v_a_4938_; lean_object* v___x_4940_; uint8_t v_isShared_4941_; uint8_t v_isSharedCheck_4945_; 
lean_dec(v_declName_4898_);
lean_dec(v___x_4897_);
lean_dec(v___x_4896_);
v_a_4938_ = lean_ctor_get(v___x_4906_, 0);
v_isSharedCheck_4945_ = !lean_is_exclusive(v___x_4906_);
if (v_isSharedCheck_4945_ == 0)
{
v___x_4940_ = v___x_4906_;
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
else
{
lean_inc(v_a_4938_);
lean_dec(v___x_4906_);
v___x_4940_ = lean_box(0);
v_isShared_4941_ = v_isSharedCheck_4945_;
goto v_resetjp_4939_;
}
v_resetjp_4939_:
{
lean_object* v___x_4943_; 
if (v_isShared_4941_ == 0)
{
v___x_4943_ = v___x_4940_;
goto v_reusejp_4942_;
}
else
{
lean_object* v_reuseFailAlloc_4944_; 
v_reuseFailAlloc_4944_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_4944_, 0, v_a_4938_);
v___x_4943_ = v_reuseFailAlloc_4944_;
goto v_reusejp_4942_;
}
v_reusejp_4942_:
{
return v___x_4943_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v___x_4946_, lean_object* v___x_4947_, lean_object* v_declName_4948_, lean_object* v_stx_4949_, lean_object* v_attrKind_4950_, lean_object* v___y_4951_, lean_object* v___y_4952_, lean_object* v___y_4953_){
_start:
{
uint8_t v_attrKind_boxed_4954_; lean_object* v_res_4955_; 
v_attrKind_boxed_4954_ = lean_unbox(v_attrKind_4950_);
v_res_4955_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(v___x_4946_, v___x_4947_, v_declName_4948_, v_stx_4949_, v_attrKind_boxed_4954_, v___y_4951_, v___y_4952_);
lean_dec(v___y_4952_);
lean_dec_ref(v___y_4951_);
lean_dec(v_stx_4949_);
return v_res_4955_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_4956_; lean_object* v___f_4957_; 
v___x_4956_ = l_Lean_Meta_instInhabitedInstances_default;
v___f_4957_ = lean_alloc_closure((void*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed), 5, 1);
lean_closure_set(v___f_4957_, 0, v___x_4956_);
return v___f_4957_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_5024_; lean_object* v___f_5025_; lean_object* v___x_5026_; lean_object* v___x_5027_; 
v___f_5024_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___f_5025_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5026_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__27_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5027_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5027_, 0, v___x_5026_);
lean_ctor_set(v___x_5027_, 1, v___f_5025_);
lean_ctor_set(v___x_5027_, 2, v___f_5024_);
return v___x_5027_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5029_; lean_object* v___x_5030_; 
v___x_5029_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__28_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_5030_ = l_Lean_registerBuiltinAttribute(v___x_5029_);
return v___x_5030_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5031_){
_start:
{
lean_object* v_res_5032_; 
v_res_5032_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5032_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_5033_, lean_object* v_x_5034_, lean_object* v_x_5035_){
_start:
{
uint8_t v___x_5036_; 
v___x_5036_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_x_5034_, v_x_5035_);
return v___x_5036_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_5037_, lean_object* v_x_5038_, lean_object* v_x_5039_){
_start:
{
uint8_t v_res_5040_; lean_object* v_r_5041_; 
v_res_5040_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_5037_, v_x_5038_, v_x_5039_);
lean_dec(v_x_5039_);
lean_dec_ref(v_x_5038_);
v_r_5041_ = lean_box(v_res_5040_);
return v_r_5041_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b1_5042_, lean_object* v_msg_5043_, lean_object* v___y_5044_, lean_object* v___y_5045_){
_start:
{
lean_object* v___x_5047_; 
v___x_5047_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v_msg_5043_, v___y_5044_, v___y_5045_);
return v___x_5047_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_00_u03b1_5048_, lean_object* v_msg_5049_, lean_object* v___y_5050_, lean_object* v___y_5051_, lean_object* v___y_5052_){
_start:
{
lean_object* v_res_5053_; 
v_res_5053_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1(v_00_u03b1_5048_, v_msg_5049_, v___y_5050_, v___y_5051_);
lean_dec(v___y_5051_);
lean_dec_ref(v___y_5050_);
return v_res_5053_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5054_, lean_object* v_x_5055_, size_t v_x_5056_, lean_object* v_x_5057_){
_start:
{
uint8_t v___x_5058_; 
v___x_5058_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___redArg(v_x_5055_, v_x_5056_, v_x_5057_);
return v___x_5058_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5059_, lean_object* v_x_5060_, lean_object* v_x_5061_, lean_object* v_x_5062_){
_start:
{
size_t v_x_2993__boxed_5063_; uint8_t v_res_5064_; lean_object* v_r_5065_; 
v_x_2993__boxed_5063_ = lean_unbox_usize(v_x_5061_);
lean_dec(v_x_5061_);
v_res_5064_ = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1(v_00_u03b2_5059_, v_x_5060_, v_x_2993__boxed_5063_, v_x_5062_);
lean_dec(v_x_5062_);
lean_dec_ref(v_x_5060_);
v_r_5065_ = lean_box(v_res_5064_);
return v_r_5065_;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(lean_object* v_00_u03b2_5066_, lean_object* v_keys_5067_, lean_object* v_vals_5068_, lean_object* v_heq_5069_, lean_object* v_i_5070_, lean_object* v_k_5071_){
_start:
{
uint8_t v___x_5072_; 
v___x_5072_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___redArg(v_keys_5067_, v_i_5070_, v_k_5071_);
return v___x_5072_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2___boxed(lean_object* v_00_u03b2_5073_, lean_object* v_keys_5074_, lean_object* v_vals_5075_, lean_object* v_heq_5076_, lean_object* v_i_5077_, lean_object* v_k_5078_){
_start:
{
uint8_t v_res_5079_; lean_object* v_r_5080_; 
v_res_5079_ = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0_spec__1_spec__2(v_00_u03b2_5073_, v_keys_5074_, v_vals_5075_, v_heq_5076_, v_i_5077_, v_k_5078_);
lean_dec(v_k_5078_);
lean_dec_ref(v_vals_5075_);
lean_dec_ref(v_keys_5074_);
v_r_5080_ = lean_box(v_res_5079_);
return v_r_5080_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5083_; lean_object* v___x_5084_; lean_object* v___x_5085_; 
v___x_5083_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__23_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5084_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1___closed__0_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_));
v___x_5085_ = l_Lean_addBuiltinDocString(v___x_5083_, v___x_5084_);
return v___x_5085_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2____boxed(lean_object* v_a_5086_){
_start:
{
lean_object* v_res_5087_; 
v_res_5087_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___regBuiltin___private_Lean_Meta_Instances_0__Lean_Meta_initFn_docString__1_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_();
return v_res_5087_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg(lean_object* v_a_5088_){
_start:
{
lean_object* v___x_5090_; lean_object* v_env_5091_; lean_object* v___x_5092_; lean_object* v_ext_5093_; lean_object* v_toEnvExtension_5094_; lean_object* v_asyncMode_5095_; lean_object* v___x_5096_; lean_object* v___x_5097_; lean_object* v_discrTree_5098_; lean_object* v___x_5099_; 
v___x_5090_ = lean_st_ref_get(v_a_5088_);
v_env_5091_ = lean_ctor_get(v___x_5090_, 0);
lean_inc_ref(v_env_5091_);
lean_dec(v___x_5090_);
v___x_5092_ = l_Lean_Meta_instanceExtension;
v_ext_5093_ = lean_ctor_get(v___x_5092_, 1);
v_toEnvExtension_5094_ = lean_ctor_get(v_ext_5093_, 0);
v_asyncMode_5095_ = lean_ctor_get(v_toEnvExtension_5094_, 2);
v___x_5096_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5097_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5096_, v___x_5092_, v_env_5091_, v_asyncMode_5095_);
v_discrTree_5098_ = lean_ctor_get(v___x_5097_, 0);
lean_inc_ref(v_discrTree_5098_);
lean_dec(v___x_5097_);
v___x_5099_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5099_, 0, v_discrTree_5098_);
return v___x_5099_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___redArg___boxed(lean_object* v_a_5100_, lean_object* v_a_5101_){
_start:
{
lean_object* v_res_5102_; 
v_res_5102_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5100_);
lean_dec(v_a_5100_);
return v_res_5102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex(lean_object* v_a_5103_, lean_object* v_a_5104_){
_start:
{
lean_object* v___x_5106_; 
v___x_5106_ = l_Lean_Meta_getGlobalInstancesIndex___redArg(v_a_5104_);
return v___x_5106_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getGlobalInstancesIndex___boxed(lean_object* v_a_5107_, lean_object* v_a_5108_, lean_object* v_a_5109_){
_start:
{
lean_object* v_res_5110_; 
v_res_5110_ = l_Lean_Meta_getGlobalInstancesIndex(v_a_5107_, v_a_5108_);
lean_dec(v_a_5108_);
lean_dec_ref(v_a_5107_);
return v_res_5110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg(lean_object* v_a_5111_){
_start:
{
lean_object* v___x_5113_; lean_object* v_env_5114_; lean_object* v___x_5115_; lean_object* v_ext_5116_; lean_object* v_toEnvExtension_5117_; lean_object* v_asyncMode_5118_; lean_object* v___x_5119_; lean_object* v___x_5120_; lean_object* v_erased_5121_; lean_object* v___x_5122_; 
v___x_5113_ = lean_st_ref_get(v_a_5111_);
v_env_5114_ = lean_ctor_get(v___x_5113_, 0);
lean_inc_ref(v_env_5114_);
lean_dec(v___x_5113_);
v___x_5115_ = l_Lean_Meta_instanceExtension;
v_ext_5116_ = lean_ctor_get(v___x_5115_, 1);
v_toEnvExtension_5117_ = lean_ctor_get(v_ext_5116_, 0);
v_asyncMode_5118_ = lean_ctor_get(v_toEnvExtension_5117_, 2);
v___x_5119_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5120_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5119_, v___x_5115_, v_env_5114_, v_asyncMode_5118_);
v_erased_5121_ = lean_ctor_get(v___x_5120_, 2);
lean_inc_ref(v_erased_5121_);
lean_dec(v___x_5120_);
v___x_5122_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5122_, 0, v_erased_5121_);
return v___x_5122_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___redArg___boxed(lean_object* v_a_5123_, lean_object* v_a_5124_){
_start:
{
lean_object* v_res_5125_; 
v_res_5125_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5123_);
lean_dec(v_a_5123_);
return v_res_5125_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances(lean_object* v_a_5126_, lean_object* v_a_5127_){
_start:
{
lean_object* v___x_5129_; 
v___x_5129_ = l_Lean_Meta_getErasedInstances___redArg(v_a_5127_);
return v___x_5129_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getErasedInstances___boxed(lean_object* v_a_5130_, lean_object* v_a_5131_, lean_object* v_a_5132_){
_start:
{
lean_object* v_res_5133_; 
v_res_5133_ = l_Lean_Meta_getErasedInstances(v_a_5130_, v_a_5131_);
lean_dec(v_a_5131_);
lean_dec_ref(v_a_5130_);
return v_res_5133_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_isInstanceCore(lean_object* v_env_5134_, lean_object* v_declName_5135_){
_start:
{
lean_object* v___x_5136_; lean_object* v_ext_5137_; lean_object* v_toEnvExtension_5138_; lean_object* v_asyncMode_5139_; lean_object* v___x_5140_; lean_object* v___x_5141_; lean_object* v_instanceNames_5142_; uint8_t v___x_5143_; 
v___x_5136_ = l_Lean_Meta_instanceExtension;
v_ext_5137_ = lean_ctor_get(v___x_5136_, 1);
v_toEnvExtension_5138_ = lean_ctor_get(v_ext_5137_, 0);
v_asyncMode_5139_ = lean_ctor_get(v_toEnvExtension_5138_, 2);
v___x_5140_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5141_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5140_, v___x_5136_, v_env_5134_, v_asyncMode_5139_);
v_instanceNames_5142_ = lean_ctor_get(v___x_5141_, 1);
lean_inc_ref(v_instanceNames_5142_);
lean_dec(v___x_5141_);
v___x_5143_ = l_Lean_PersistentHashMap_contains___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__0___redArg(v_instanceNames_5142_, v_declName_5135_);
lean_dec_ref(v_instanceNames_5142_);
return v___x_5143_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstanceCore___boxed(lean_object* v_env_5144_, lean_object* v_declName_5145_){
_start:
{
uint8_t v_res_5146_; lean_object* v_r_5147_; 
v_res_5146_ = l_Lean_Meta_isInstanceCore(v_env_5144_, v_declName_5145_);
lean_dec(v_declName_5145_);
v_r_5147_ = lean_box(v_res_5146_);
return v_r_5147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg(lean_object* v_declName_5148_, lean_object* v_a_5149_){
_start:
{
lean_object* v___x_5151_; lean_object* v_env_5152_; uint8_t v___x_5153_; lean_object* v___x_5154_; lean_object* v___x_5155_; 
v___x_5151_ = lean_st_ref_get(v_a_5149_);
v_env_5152_ = lean_ctor_get(v___x_5151_, 0);
lean_inc_ref(v_env_5152_);
lean_dec(v___x_5151_);
v___x_5153_ = l_Lean_Meta_isInstanceCore(v_env_5152_, v_declName_5148_);
v___x_5154_ = lean_box(v___x_5153_);
v___x_5155_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5155_, 0, v___x_5154_);
return v___x_5155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___redArg___boxed(lean_object* v_declName_5156_, lean_object* v_a_5157_, lean_object* v_a_5158_){
_start:
{
lean_object* v_res_5159_; 
v_res_5159_ = l_Lean_Meta_isInstance___redArg(v_declName_5156_, v_a_5157_);
lean_dec(v_a_5157_);
lean_dec(v_declName_5156_);
return v_res_5159_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance(lean_object* v_declName_5160_, lean_object* v_a_5161_, lean_object* v_a_5162_){
_start:
{
lean_object* v___x_5164_; 
v___x_5164_ = l_Lean_Meta_isInstance___redArg(v_declName_5160_, v_a_5162_);
return v___x_5164_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_isInstance___boxed(lean_object* v_declName_5165_, lean_object* v_a_5166_, lean_object* v_a_5167_, lean_object* v_a_5168_){
_start:
{
lean_object* v_res_5169_; 
v_res_5169_ = l_Lean_Meta_isInstance(v_declName_5165_, v_a_5166_, v_a_5167_);
lean_dec(v_a_5167_);
lean_dec_ref(v_a_5166_);
lean_dec(v_declName_5165_);
return v_res_5169_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(lean_object* v_keys_5170_, lean_object* v_vals_5171_, lean_object* v_i_5172_, lean_object* v_k_5173_){
_start:
{
lean_object* v___x_5174_; uint8_t v___x_5175_; 
v___x_5174_ = lean_array_get_size(v_keys_5170_);
v___x_5175_ = lean_nat_dec_lt(v_i_5172_, v___x_5174_);
if (v___x_5175_ == 0)
{
lean_object* v___x_5176_; 
lean_dec(v_i_5172_);
v___x_5176_ = lean_box(0);
return v___x_5176_;
}
else
{
lean_object* v_k_x27_5177_; uint8_t v___x_5178_; 
v_k_x27_5177_ = lean_array_fget_borrowed(v_keys_5170_, v_i_5172_);
v___x_5178_ = lean_name_eq(v_k_5173_, v_k_x27_5177_);
if (v___x_5178_ == 0)
{
lean_object* v___x_5179_; lean_object* v___x_5180_; 
v___x_5179_ = lean_unsigned_to_nat(1u);
v___x_5180_ = lean_nat_add(v_i_5172_, v___x_5179_);
lean_dec(v_i_5172_);
v_i_5172_ = v___x_5180_;
goto _start;
}
else
{
lean_object* v___x_5182_; lean_object* v___x_5183_; 
v___x_5182_ = lean_array_fget_borrowed(v_vals_5171_, v_i_5172_);
lean_dec(v_i_5172_);
lean_inc(v___x_5182_);
v___x_5183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5183_, 0, v___x_5182_);
return v___x_5183_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg___boxed(lean_object* v_keys_5184_, lean_object* v_vals_5185_, lean_object* v_i_5186_, lean_object* v_k_5187_){
_start:
{
lean_object* v_res_5188_; 
v_res_5188_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5184_, v_vals_5185_, v_i_5186_, v_k_5187_);
lean_dec(v_k_5187_);
lean_dec_ref(v_vals_5185_);
lean_dec_ref(v_keys_5184_);
return v_res_5188_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(lean_object* v_x_5189_, size_t v_x_5190_, lean_object* v_x_5191_){
_start:
{
if (lean_obj_tag(v_x_5189_) == 0)
{
lean_object* v_es_5192_; lean_object* v___x_5193_; size_t v___x_5194_; size_t v___x_5195_; lean_object* v_j_5196_; lean_object* v___x_5197_; 
v_es_5192_ = lean_ctor_get(v_x_5189_, 0);
v___x_5193_ = lean_box(2);
v___x_5194_ = ((size_t)31ULL);
v___x_5195_ = lean_usize_land(v_x_5190_, v___x_5194_);
v_j_5196_ = lean_usize_to_nat(v___x_5195_);
v___x_5197_ = lean_array_get_borrowed(v___x_5193_, v_es_5192_, v_j_5196_);
lean_dec(v_j_5196_);
switch(lean_obj_tag(v___x_5197_))
{
case 0:
{
lean_object* v_key_5198_; lean_object* v_val_5199_; uint8_t v___x_5200_; 
v_key_5198_ = lean_ctor_get(v___x_5197_, 0);
v_val_5199_ = lean_ctor_get(v___x_5197_, 1);
v___x_5200_ = lean_name_eq(v_x_5191_, v_key_5198_);
if (v___x_5200_ == 0)
{
lean_object* v___x_5201_; 
v___x_5201_ = lean_box(0);
return v___x_5201_;
}
else
{
lean_object* v___x_5202_; 
lean_inc(v_val_5199_);
v___x_5202_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_5202_, 0, v_val_5199_);
return v___x_5202_;
}
}
case 1:
{
lean_object* v_node_5203_; size_t v___x_5204_; size_t v___x_5205_; 
v_node_5203_ = lean_ctor_get(v___x_5197_, 0);
v___x_5204_ = ((size_t)5ULL);
v___x_5205_ = lean_usize_shift_right(v_x_5190_, v___x_5204_);
v_x_5189_ = v_node_5203_;
v_x_5190_ = v___x_5205_;
goto _start;
}
default: 
{
lean_object* v___x_5207_; 
v___x_5207_ = lean_box(0);
return v___x_5207_;
}
}
}
else
{
lean_object* v_ks_5208_; lean_object* v_vs_5209_; lean_object* v___x_5210_; lean_object* v___x_5211_; 
v_ks_5208_ = lean_ctor_get(v_x_5189_, 0);
v_vs_5209_ = lean_ctor_get(v_x_5189_, 1);
v___x_5210_ = lean_unsigned_to_nat(0u);
v___x_5211_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_ks_5208_, v_vs_5209_, v___x_5210_, v_x_5191_);
return v___x_5211_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_x_5212_, lean_object* v_x_5213_, lean_object* v_x_5214_){
_start:
{
size_t v_x_479__boxed_5215_; lean_object* v_res_5216_; 
v_x_479__boxed_5215_ = lean_unbox_usize(v_x_5213_);
lean_dec(v_x_5213_);
v_res_5216_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5212_, v_x_479__boxed_5215_, v_x_5214_);
lean_dec(v_x_5214_);
lean_dec_ref(v_x_5212_);
return v_res_5216_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(lean_object* v_x_5217_, lean_object* v_x_5218_){
_start:
{
uint64_t v___y_5220_; 
if (lean_obj_tag(v_x_5218_) == 0)
{
uint64_t v___x_5223_; 
v___x_5223_ = lean_uint64_once(&l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0, &l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0_once, _init_l___private_Lean_Data_PersistentHashMap_0__Lean_PersistentHashMap_insertAux_traverse___at___00Lean_PersistentHashMap_insertAux___at___00Lean_PersistentHashMap_insert___at___00Lean_Meta_addInstanceEntry_spec__1_spec__4_spec__10___redArg___closed__0);
v___y_5220_ = v___x_5223_;
goto v___jp_5219_;
}
else
{
uint64_t v_hash_5224_; 
v_hash_5224_ = lean_ctor_get_uint64(v_x_5218_, sizeof(void*)*2);
v___y_5220_ = v_hash_5224_;
goto v___jp_5219_;
}
v___jp_5219_:
{
size_t v___x_5221_; lean_object* v___x_5222_; 
v___x_5221_ = lean_uint64_to_usize(v___y_5220_);
v___x_5222_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5217_, v___x_5221_, v_x_5218_);
return v___x_5222_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg___boxed(lean_object* v_x_5225_, lean_object* v_x_5226_){
_start:
{
lean_object* v_res_5227_; 
v_res_5227_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5225_, v_x_5226_);
lean_dec(v_x_5226_);
lean_dec_ref(v_x_5225_);
return v_res_5227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg(lean_object* v_declName_5228_, lean_object* v_a_5229_){
_start:
{
lean_object* v___x_5231_; lean_object* v_env_5232_; lean_object* v___x_5233_; lean_object* v_ext_5234_; lean_object* v_toEnvExtension_5235_; lean_object* v_asyncMode_5236_; lean_object* v___x_5237_; lean_object* v___x_5238_; lean_object* v_instanceNames_5239_; lean_object* v___x_5240_; 
v___x_5231_ = lean_st_ref_get(v_a_5229_);
v_env_5232_ = lean_ctor_get(v___x_5231_, 0);
lean_inc_ref(v_env_5232_);
lean_dec(v___x_5231_);
v___x_5233_ = l_Lean_Meta_instanceExtension;
v_ext_5234_ = lean_ctor_get(v___x_5233_, 1);
v_toEnvExtension_5235_ = lean_ctor_get(v_ext_5234_, 0);
v_asyncMode_5236_ = lean_ctor_get(v_toEnvExtension_5235_, 2);
v___x_5237_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5238_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5237_, v___x_5233_, v_env_5232_, v_asyncMode_5236_);
v_instanceNames_5239_ = lean_ctor_get(v___x_5238_, 1);
lean_inc_ref(v_instanceNames_5239_);
lean_dec(v___x_5238_);
v___x_5240_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5239_, v_declName_5228_);
lean_dec_ref(v_instanceNames_5239_);
if (lean_obj_tag(v___x_5240_) == 1)
{
lean_object* v_val_5241_; lean_object* v___x_5243_; uint8_t v_isShared_5244_; uint8_t v_isSharedCheck_5250_; 
v_val_5241_ = lean_ctor_get(v___x_5240_, 0);
v_isSharedCheck_5250_ = !lean_is_exclusive(v___x_5240_);
if (v_isSharedCheck_5250_ == 0)
{
v___x_5243_ = v___x_5240_;
v_isShared_5244_ = v_isSharedCheck_5250_;
goto v_resetjp_5242_;
}
else
{
lean_inc(v_val_5241_);
lean_dec(v___x_5240_);
v___x_5243_ = lean_box(0);
v_isShared_5244_ = v_isSharedCheck_5250_;
goto v_resetjp_5242_;
}
v_resetjp_5242_:
{
lean_object* v_priority_5245_; lean_object* v___x_5247_; 
v_priority_5245_ = lean_ctor_get(v_val_5241_, 2);
lean_inc(v_priority_5245_);
lean_dec(v_val_5241_);
if (v_isShared_5244_ == 0)
{
lean_ctor_set(v___x_5243_, 0, v_priority_5245_);
v___x_5247_ = v___x_5243_;
goto v_reusejp_5246_;
}
else
{
lean_object* v_reuseFailAlloc_5249_; 
v_reuseFailAlloc_5249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5249_, 0, v_priority_5245_);
v___x_5247_ = v_reuseFailAlloc_5249_;
goto v_reusejp_5246_;
}
v_reusejp_5246_:
{
lean_object* v___x_5248_; 
v___x_5248_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5248_, 0, v___x_5247_);
return v___x_5248_;
}
}
}
else
{
lean_object* v___x_5251_; lean_object* v___x_5252_; 
lean_dec(v___x_5240_);
v___x_5251_ = lean_box(0);
v___x_5252_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5252_, 0, v___x_5251_);
return v___x_5252_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___redArg___boxed(lean_object* v_declName_5253_, lean_object* v_a_5254_, lean_object* v_a_5255_){
_start:
{
lean_object* v_res_5256_; 
v_res_5256_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5253_, v_a_5254_);
lean_dec(v_a_5254_);
lean_dec(v_declName_5253_);
return v_res_5256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f(lean_object* v_declName_5257_, lean_object* v_a_5258_, lean_object* v_a_5259_){
_start:
{
lean_object* v___x_5261_; 
v___x_5261_ = l_Lean_Meta_getInstancePriority_x3f___redArg(v_declName_5257_, v_a_5259_);
return v___x_5261_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstancePriority_x3f___boxed(lean_object* v_declName_5262_, lean_object* v_a_5263_, lean_object* v_a_5264_, lean_object* v_a_5265_){
_start:
{
lean_object* v_res_5266_; 
v_res_5266_ = l_Lean_Meta_getInstancePriority_x3f(v_declName_5262_, v_a_5263_, v_a_5264_);
lean_dec(v_a_5264_);
lean_dec_ref(v_a_5263_);
lean_dec(v_declName_5262_);
return v_res_5266_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(lean_object* v_00_u03b2_5267_, lean_object* v_x_5268_, lean_object* v_x_5269_){
_start:
{
lean_object* v___x_5270_; 
v___x_5270_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_x_5268_, v_x_5269_);
return v___x_5270_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___boxed(lean_object* v_00_u03b2_5271_, lean_object* v_x_5272_, lean_object* v_x_5273_){
_start:
{
lean_object* v_res_5274_; 
v_res_5274_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0(v_00_u03b2_5271_, v_x_5272_, v_x_5273_);
lean_dec(v_x_5273_);
lean_dec_ref(v_x_5272_);
return v_res_5274_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(lean_object* v_00_u03b2_5275_, lean_object* v_x_5276_, size_t v_x_5277_, lean_object* v_x_5278_){
_start:
{
lean_object* v___x_5279_; 
v___x_5279_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___redArg(v_x_5276_, v_x_5277_, v_x_5278_);
return v___x_5279_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_5280_, lean_object* v_x_5281_, lean_object* v_x_5282_, lean_object* v_x_5283_){
_start:
{
size_t v_x_593__boxed_5284_; lean_object* v_res_5285_; 
v_x_593__boxed_5284_ = lean_unbox_usize(v_x_5282_);
lean_dec(v_x_5282_);
v_res_5285_ = l_Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0(v_00_u03b2_5280_, v_x_5281_, v_x_593__boxed_5284_, v_x_5283_);
lean_dec(v_x_5283_);
lean_dec_ref(v_x_5281_);
return v_res_5285_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(lean_object* v_00_u03b2_5286_, lean_object* v_keys_5287_, lean_object* v_vals_5288_, lean_object* v_heq_5289_, lean_object* v_i_5290_, lean_object* v_k_5291_){
_start:
{
lean_object* v___x_5292_; 
v___x_5292_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___redArg(v_keys_5287_, v_vals_5288_, v_i_5290_, v_k_5291_);
return v___x_5292_;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1___boxed(lean_object* v_00_u03b2_5293_, lean_object* v_keys_5294_, lean_object* v_vals_5295_, lean_object* v_heq_5296_, lean_object* v_i_5297_, lean_object* v_k_5298_){
_start:
{
lean_object* v_res_5299_; 
v_res_5299_ = l_Lean_PersistentHashMap_findAtAux___at___00Lean_PersistentHashMap_findAux___at___00Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0_spec__0_spec__1(v_00_u03b2_5293_, v_keys_5294_, v_vals_5295_, v_heq_5296_, v_i_5297_, v_k_5298_);
lean_dec(v_k_5298_);
lean_dec_ref(v_vals_5295_);
lean_dec_ref(v_keys_5294_);
return v_res_5299_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg(lean_object* v_declName_5300_, lean_object* v_a_5301_){
_start:
{
lean_object* v___x_5303_; lean_object* v_env_5304_; lean_object* v___x_5305_; lean_object* v_ext_5306_; lean_object* v_toEnvExtension_5307_; lean_object* v_asyncMode_5308_; lean_object* v___x_5309_; lean_object* v___x_5310_; lean_object* v_instanceNames_5311_; lean_object* v___x_5312_; 
v___x_5303_ = lean_st_ref_get(v_a_5301_);
v_env_5304_ = lean_ctor_get(v___x_5303_, 0);
lean_inc_ref(v_env_5304_);
lean_dec(v___x_5303_);
v___x_5305_ = l_Lean_Meta_instanceExtension;
v_ext_5306_ = lean_ctor_get(v___x_5305_, 1);
v_toEnvExtension_5307_ = lean_ctor_get(v_ext_5306_, 0);
v_asyncMode_5308_ = lean_ctor_get(v_toEnvExtension_5307_, 2);
v___x_5309_ = l_Lean_Meta_instInhabitedInstances_default;
v___x_5310_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_5309_, v___x_5305_, v_env_5304_, v_asyncMode_5308_);
v_instanceNames_5311_ = lean_ctor_get(v___x_5310_, 1);
lean_inc_ref(v_instanceNames_5311_);
lean_dec(v___x_5310_);
v___x_5312_ = l_Lean_PersistentHashMap_find_x3f___at___00Lean_Meta_getInstancePriority_x3f_spec__0___redArg(v_instanceNames_5311_, v_declName_5300_);
lean_dec_ref(v_instanceNames_5311_);
if (lean_obj_tag(v___x_5312_) == 1)
{
lean_object* v_val_5313_; lean_object* v___x_5315_; uint8_t v_isShared_5316_; uint8_t v_isSharedCheck_5323_; 
v_val_5313_ = lean_ctor_get(v___x_5312_, 0);
v_isSharedCheck_5323_ = !lean_is_exclusive(v___x_5312_);
if (v_isSharedCheck_5323_ == 0)
{
v___x_5315_ = v___x_5312_;
v_isShared_5316_ = v_isSharedCheck_5323_;
goto v_resetjp_5314_;
}
else
{
lean_inc(v_val_5313_);
lean_dec(v___x_5312_);
v___x_5315_ = lean_box(0);
v_isShared_5316_ = v_isSharedCheck_5323_;
goto v_resetjp_5314_;
}
v_resetjp_5314_:
{
uint8_t v_attrKind_5317_; lean_object* v___x_5318_; lean_object* v___x_5320_; 
v_attrKind_5317_ = lean_ctor_get_uint8(v_val_5313_, sizeof(void*)*5);
lean_dec(v_val_5313_);
v___x_5318_ = lean_box(v_attrKind_5317_);
if (v_isShared_5316_ == 0)
{
lean_ctor_set(v___x_5315_, 0, v___x_5318_);
v___x_5320_ = v___x_5315_;
goto v_reusejp_5319_;
}
else
{
lean_object* v_reuseFailAlloc_5322_; 
v_reuseFailAlloc_5322_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_5322_, 0, v___x_5318_);
v___x_5320_ = v_reuseFailAlloc_5322_;
goto v_reusejp_5319_;
}
v_reusejp_5319_:
{
lean_object* v___x_5321_; 
v___x_5321_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5321_, 0, v___x_5320_);
return v___x_5321_;
}
}
}
else
{
lean_object* v___x_5324_; lean_object* v___x_5325_; 
lean_dec(v___x_5312_);
v___x_5324_ = lean_box(0);
v___x_5325_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5325_, 0, v___x_5324_);
return v___x_5325_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___redArg___boxed(lean_object* v_declName_5326_, lean_object* v_a_5327_, lean_object* v_a_5328_){
_start:
{
lean_object* v_res_5329_; 
v_res_5329_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5326_, v_a_5327_);
lean_dec(v_a_5327_);
lean_dec(v_declName_5326_);
return v_res_5329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f(lean_object* v_declName_5330_, lean_object* v_a_5331_, lean_object* v_a_5332_){
_start:
{
lean_object* v___x_5334_; 
v___x_5334_ = l_Lean_Meta_getInstanceAttrKind_x3f___redArg(v_declName_5330_, v_a_5332_);
return v___x_5334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getInstanceAttrKind_x3f___boxed(lean_object* v_declName_5335_, lean_object* v_a_5336_, lean_object* v_a_5337_, lean_object* v_a_5338_){
_start:
{
lean_object* v_res_5339_; 
v_res_5339_ = l_Lean_Meta_getInstanceAttrKind_x3f(v_declName_5335_, v_a_5336_, v_a_5337_);
lean_dec(v_a_5337_);
lean_dec_ref(v_a_5336_);
lean_dec(v_declName_5335_);
return v_res_5339_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(lean_object* v_k_5344_, lean_object* v_v_5345_, lean_object* v_t_5346_){
_start:
{
if (lean_obj_tag(v_t_5346_) == 0)
{
lean_object* v_size_5347_; lean_object* v_k_5348_; lean_object* v_v_5349_; lean_object* v_l_5350_; lean_object* v_r_5351_; lean_object* v___x_5353_; uint8_t v_isShared_5354_; uint8_t v_isSharedCheck_5632_; 
v_size_5347_ = lean_ctor_get(v_t_5346_, 0);
v_k_5348_ = lean_ctor_get(v_t_5346_, 1);
v_v_5349_ = lean_ctor_get(v_t_5346_, 2);
v_l_5350_ = lean_ctor_get(v_t_5346_, 3);
v_r_5351_ = lean_ctor_get(v_t_5346_, 4);
v_isSharedCheck_5632_ = !lean_is_exclusive(v_t_5346_);
if (v_isSharedCheck_5632_ == 0)
{
v___x_5353_ = v_t_5346_;
v_isShared_5354_ = v_isSharedCheck_5632_;
goto v_resetjp_5352_;
}
else
{
lean_inc(v_r_5351_);
lean_inc(v_l_5350_);
lean_inc(v_v_5349_);
lean_inc(v_k_5348_);
lean_inc(v_size_5347_);
lean_dec(v_t_5346_);
v___x_5353_ = lean_box(0);
v_isShared_5354_ = v_isSharedCheck_5632_;
goto v_resetjp_5352_;
}
v_resetjp_5352_:
{
uint8_t v___x_5355_; 
v___x_5355_ = lean_nat_dec_lt(v_k_5348_, v_k_5344_);
if (v___x_5355_ == 0)
{
uint8_t v___x_5356_; 
v___x_5356_ = lean_nat_dec_eq(v_k_5348_, v_k_5344_);
if (v___x_5356_ == 0)
{
lean_object* v_impl_5357_; lean_object* v___x_5358_; 
lean_dec(v_size_5347_);
v_impl_5357_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5344_, v_v_5345_, v_r_5351_);
v___x_5358_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_l_5350_) == 0)
{
lean_object* v_size_5359_; lean_object* v_size_5360_; lean_object* v_k_5361_; lean_object* v_v_5362_; lean_object* v_l_5363_; lean_object* v_r_5364_; lean_object* v___x_5365_; lean_object* v___x_5366_; uint8_t v___x_5367_; 
v_size_5359_ = lean_ctor_get(v_l_5350_, 0);
v_size_5360_ = lean_ctor_get(v_impl_5357_, 0);
lean_inc(v_size_5360_);
v_k_5361_ = lean_ctor_get(v_impl_5357_, 1);
lean_inc(v_k_5361_);
v_v_5362_ = lean_ctor_get(v_impl_5357_, 2);
lean_inc(v_v_5362_);
v_l_5363_ = lean_ctor_get(v_impl_5357_, 3);
lean_inc(v_l_5363_);
v_r_5364_ = lean_ctor_get(v_impl_5357_, 4);
lean_inc(v_r_5364_);
v___x_5365_ = lean_unsigned_to_nat(3u);
v___x_5366_ = lean_nat_mul(v___x_5365_, v_size_5359_);
v___x_5367_ = lean_nat_dec_lt(v___x_5366_, v_size_5360_);
lean_dec(v___x_5366_);
if (v___x_5367_ == 0)
{
lean_object* v___x_5368_; lean_object* v___x_5369_; lean_object* v___x_5371_; 
lean_dec(v_r_5364_);
lean_dec(v_l_5363_);
lean_dec(v_v_5362_);
lean_dec(v_k_5361_);
v___x_5368_ = lean_nat_add(v___x_5358_, v_size_5359_);
v___x_5369_ = lean_nat_add(v___x_5368_, v_size_5360_);
lean_dec(v_size_5360_);
lean_dec(v___x_5368_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_impl_5357_);
lean_ctor_set(v___x_5353_, 0, v___x_5369_);
v___x_5371_ = v___x_5353_;
goto v_reusejp_5370_;
}
else
{
lean_object* v_reuseFailAlloc_5372_; 
v_reuseFailAlloc_5372_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5372_, 0, v___x_5369_);
lean_ctor_set(v_reuseFailAlloc_5372_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5372_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5372_, 3, v_l_5350_);
lean_ctor_set(v_reuseFailAlloc_5372_, 4, v_impl_5357_);
v___x_5371_ = v_reuseFailAlloc_5372_;
goto v_reusejp_5370_;
}
v_reusejp_5370_:
{
return v___x_5371_;
}
}
else
{
lean_object* v___x_5374_; uint8_t v_isShared_5375_; uint8_t v_isSharedCheck_5436_; 
v_isSharedCheck_5436_ = !lean_is_exclusive(v_impl_5357_);
if (v_isSharedCheck_5436_ == 0)
{
lean_object* v_unused_5437_; lean_object* v_unused_5438_; lean_object* v_unused_5439_; lean_object* v_unused_5440_; lean_object* v_unused_5441_; 
v_unused_5437_ = lean_ctor_get(v_impl_5357_, 4);
lean_dec(v_unused_5437_);
v_unused_5438_ = lean_ctor_get(v_impl_5357_, 3);
lean_dec(v_unused_5438_);
v_unused_5439_ = lean_ctor_get(v_impl_5357_, 2);
lean_dec(v_unused_5439_);
v_unused_5440_ = lean_ctor_get(v_impl_5357_, 1);
lean_dec(v_unused_5440_);
v_unused_5441_ = lean_ctor_get(v_impl_5357_, 0);
lean_dec(v_unused_5441_);
v___x_5374_ = v_impl_5357_;
v_isShared_5375_ = v_isSharedCheck_5436_;
goto v_resetjp_5373_;
}
else
{
lean_dec(v_impl_5357_);
v___x_5374_ = lean_box(0);
v_isShared_5375_ = v_isSharedCheck_5436_;
goto v_resetjp_5373_;
}
v_resetjp_5373_:
{
lean_object* v_size_5376_; lean_object* v_k_5377_; lean_object* v_v_5378_; lean_object* v_l_5379_; lean_object* v_r_5380_; lean_object* v_size_5381_; lean_object* v___x_5382_; lean_object* v___x_5383_; uint8_t v___x_5384_; 
v_size_5376_ = lean_ctor_get(v_l_5363_, 0);
v_k_5377_ = lean_ctor_get(v_l_5363_, 1);
v_v_5378_ = lean_ctor_get(v_l_5363_, 2);
v_l_5379_ = lean_ctor_get(v_l_5363_, 3);
v_r_5380_ = lean_ctor_get(v_l_5363_, 4);
v_size_5381_ = lean_ctor_get(v_r_5364_, 0);
v___x_5382_ = lean_unsigned_to_nat(2u);
v___x_5383_ = lean_nat_mul(v___x_5382_, v_size_5381_);
v___x_5384_ = lean_nat_dec_lt(v_size_5376_, v___x_5383_);
lean_dec(v___x_5383_);
if (v___x_5384_ == 0)
{
lean_object* v___x_5386_; uint8_t v_isShared_5387_; uint8_t v_isSharedCheck_5412_; 
lean_inc(v_r_5380_);
lean_inc(v_l_5379_);
lean_inc(v_v_5378_);
lean_inc(v_k_5377_);
v_isSharedCheck_5412_ = !lean_is_exclusive(v_l_5363_);
if (v_isSharedCheck_5412_ == 0)
{
lean_object* v_unused_5413_; lean_object* v_unused_5414_; lean_object* v_unused_5415_; lean_object* v_unused_5416_; lean_object* v_unused_5417_; 
v_unused_5413_ = lean_ctor_get(v_l_5363_, 4);
lean_dec(v_unused_5413_);
v_unused_5414_ = lean_ctor_get(v_l_5363_, 3);
lean_dec(v_unused_5414_);
v_unused_5415_ = lean_ctor_get(v_l_5363_, 2);
lean_dec(v_unused_5415_);
v_unused_5416_ = lean_ctor_get(v_l_5363_, 1);
lean_dec(v_unused_5416_);
v_unused_5417_ = lean_ctor_get(v_l_5363_, 0);
lean_dec(v_unused_5417_);
v___x_5386_ = v_l_5363_;
v_isShared_5387_ = v_isSharedCheck_5412_;
goto v_resetjp_5385_;
}
else
{
lean_dec(v_l_5363_);
v___x_5386_ = lean_box(0);
v_isShared_5387_ = v_isSharedCheck_5412_;
goto v_resetjp_5385_;
}
v_resetjp_5385_:
{
lean_object* v___x_5388_; lean_object* v___x_5389_; lean_object* v___y_5391_; lean_object* v___y_5392_; lean_object* v___y_5393_; lean_object* v___y_5402_; 
v___x_5388_ = lean_nat_add(v___x_5358_, v_size_5359_);
v___x_5389_ = lean_nat_add(v___x_5388_, v_size_5360_);
lean_dec(v_size_5360_);
if (lean_obj_tag(v_l_5379_) == 0)
{
lean_object* v_size_5410_; 
v_size_5410_ = lean_ctor_get(v_l_5379_, 0);
lean_inc(v_size_5410_);
v___y_5402_ = v_size_5410_;
goto v___jp_5401_;
}
else
{
lean_object* v___x_5411_; 
v___x_5411_ = lean_unsigned_to_nat(0u);
v___y_5402_ = v___x_5411_;
goto v___jp_5401_;
}
v___jp_5390_:
{
lean_object* v___x_5394_; lean_object* v___x_5396_; 
v___x_5394_ = lean_nat_add(v___y_5392_, v___y_5393_);
lean_dec(v___y_5393_);
lean_dec(v___y_5392_);
if (v_isShared_5387_ == 0)
{
lean_ctor_set(v___x_5386_, 4, v_r_5364_);
lean_ctor_set(v___x_5386_, 3, v_r_5380_);
lean_ctor_set(v___x_5386_, 2, v_v_5362_);
lean_ctor_set(v___x_5386_, 1, v_k_5361_);
lean_ctor_set(v___x_5386_, 0, v___x_5394_);
v___x_5396_ = v___x_5386_;
goto v_reusejp_5395_;
}
else
{
lean_object* v_reuseFailAlloc_5400_; 
v_reuseFailAlloc_5400_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5400_, 0, v___x_5394_);
lean_ctor_set(v_reuseFailAlloc_5400_, 1, v_k_5361_);
lean_ctor_set(v_reuseFailAlloc_5400_, 2, v_v_5362_);
lean_ctor_set(v_reuseFailAlloc_5400_, 3, v_r_5380_);
lean_ctor_set(v_reuseFailAlloc_5400_, 4, v_r_5364_);
v___x_5396_ = v_reuseFailAlloc_5400_;
goto v_reusejp_5395_;
}
v_reusejp_5395_:
{
lean_object* v___x_5398_; 
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v___x_5396_);
lean_ctor_set(v___x_5374_, 3, v___y_5391_);
lean_ctor_set(v___x_5374_, 2, v_v_5378_);
lean_ctor_set(v___x_5374_, 1, v_k_5377_);
lean_ctor_set(v___x_5374_, 0, v___x_5389_);
v___x_5398_ = v___x_5374_;
goto v_reusejp_5397_;
}
else
{
lean_object* v_reuseFailAlloc_5399_; 
v_reuseFailAlloc_5399_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5399_, 0, v___x_5389_);
lean_ctor_set(v_reuseFailAlloc_5399_, 1, v_k_5377_);
lean_ctor_set(v_reuseFailAlloc_5399_, 2, v_v_5378_);
lean_ctor_set(v_reuseFailAlloc_5399_, 3, v___y_5391_);
lean_ctor_set(v_reuseFailAlloc_5399_, 4, v___x_5396_);
v___x_5398_ = v_reuseFailAlloc_5399_;
goto v_reusejp_5397_;
}
v_reusejp_5397_:
{
return v___x_5398_;
}
}
}
v___jp_5401_:
{
lean_object* v___x_5403_; lean_object* v___x_5405_; 
v___x_5403_ = lean_nat_add(v___x_5388_, v___y_5402_);
lean_dec(v___y_5402_);
lean_dec(v___x_5388_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_l_5379_);
lean_ctor_set(v___x_5353_, 0, v___x_5403_);
v___x_5405_ = v___x_5353_;
goto v_reusejp_5404_;
}
else
{
lean_object* v_reuseFailAlloc_5409_; 
v_reuseFailAlloc_5409_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5409_, 0, v___x_5403_);
lean_ctor_set(v_reuseFailAlloc_5409_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5409_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5409_, 3, v_l_5350_);
lean_ctor_set(v_reuseFailAlloc_5409_, 4, v_l_5379_);
v___x_5405_ = v_reuseFailAlloc_5409_;
goto v_reusejp_5404_;
}
v_reusejp_5404_:
{
lean_object* v___x_5406_; 
v___x_5406_ = lean_nat_add(v___x_5358_, v_size_5381_);
if (lean_obj_tag(v_r_5380_) == 0)
{
lean_object* v_size_5407_; 
v_size_5407_ = lean_ctor_get(v_r_5380_, 0);
lean_inc(v_size_5407_);
v___y_5391_ = v___x_5405_;
v___y_5392_ = v___x_5406_;
v___y_5393_ = v_size_5407_;
goto v___jp_5390_;
}
else
{
lean_object* v___x_5408_; 
v___x_5408_ = lean_unsigned_to_nat(0u);
v___y_5391_ = v___x_5405_;
v___y_5392_ = v___x_5406_;
v___y_5393_ = v___x_5408_;
goto v___jp_5390_;
}
}
}
}
}
else
{
lean_object* v___x_5418_; lean_object* v___x_5419_; lean_object* v___x_5420_; lean_object* v___x_5422_; 
lean_del_object(v___x_5353_);
v___x_5418_ = lean_nat_add(v___x_5358_, v_size_5359_);
v___x_5419_ = lean_nat_add(v___x_5418_, v_size_5360_);
lean_dec(v_size_5360_);
v___x_5420_ = lean_nat_add(v___x_5418_, v_size_5376_);
lean_dec(v___x_5418_);
lean_inc_ref(v_l_5350_);
if (v_isShared_5375_ == 0)
{
lean_ctor_set(v___x_5374_, 4, v_l_5363_);
lean_ctor_set(v___x_5374_, 3, v_l_5350_);
lean_ctor_set(v___x_5374_, 2, v_v_5349_);
lean_ctor_set(v___x_5374_, 1, v_k_5348_);
lean_ctor_set(v___x_5374_, 0, v___x_5420_);
v___x_5422_ = v___x_5374_;
goto v_reusejp_5421_;
}
else
{
lean_object* v_reuseFailAlloc_5435_; 
v_reuseFailAlloc_5435_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5435_, 0, v___x_5420_);
lean_ctor_set(v_reuseFailAlloc_5435_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5435_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5435_, 3, v_l_5350_);
lean_ctor_set(v_reuseFailAlloc_5435_, 4, v_l_5363_);
v___x_5422_ = v_reuseFailAlloc_5435_;
goto v_reusejp_5421_;
}
v_reusejp_5421_:
{
lean_object* v___x_5424_; uint8_t v_isShared_5425_; uint8_t v_isSharedCheck_5429_; 
v_isSharedCheck_5429_ = !lean_is_exclusive(v_l_5350_);
if (v_isSharedCheck_5429_ == 0)
{
lean_object* v_unused_5430_; lean_object* v_unused_5431_; lean_object* v_unused_5432_; lean_object* v_unused_5433_; lean_object* v_unused_5434_; 
v_unused_5430_ = lean_ctor_get(v_l_5350_, 4);
lean_dec(v_unused_5430_);
v_unused_5431_ = lean_ctor_get(v_l_5350_, 3);
lean_dec(v_unused_5431_);
v_unused_5432_ = lean_ctor_get(v_l_5350_, 2);
lean_dec(v_unused_5432_);
v_unused_5433_ = lean_ctor_get(v_l_5350_, 1);
lean_dec(v_unused_5433_);
v_unused_5434_ = lean_ctor_get(v_l_5350_, 0);
lean_dec(v_unused_5434_);
v___x_5424_ = v_l_5350_;
v_isShared_5425_ = v_isSharedCheck_5429_;
goto v_resetjp_5423_;
}
else
{
lean_dec(v_l_5350_);
v___x_5424_ = lean_box(0);
v_isShared_5425_ = v_isSharedCheck_5429_;
goto v_resetjp_5423_;
}
v_resetjp_5423_:
{
lean_object* v___x_5427_; 
if (v_isShared_5425_ == 0)
{
lean_ctor_set(v___x_5424_, 4, v_r_5364_);
lean_ctor_set(v___x_5424_, 3, v___x_5422_);
lean_ctor_set(v___x_5424_, 2, v_v_5362_);
lean_ctor_set(v___x_5424_, 1, v_k_5361_);
lean_ctor_set(v___x_5424_, 0, v___x_5419_);
v___x_5427_ = v___x_5424_;
goto v_reusejp_5426_;
}
else
{
lean_object* v_reuseFailAlloc_5428_; 
v_reuseFailAlloc_5428_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5428_, 0, v___x_5419_);
lean_ctor_set(v_reuseFailAlloc_5428_, 1, v_k_5361_);
lean_ctor_set(v_reuseFailAlloc_5428_, 2, v_v_5362_);
lean_ctor_set(v_reuseFailAlloc_5428_, 3, v___x_5422_);
lean_ctor_set(v_reuseFailAlloc_5428_, 4, v_r_5364_);
v___x_5427_ = v_reuseFailAlloc_5428_;
goto v_reusejp_5426_;
}
v_reusejp_5426_:
{
return v___x_5427_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5442_; 
v_l_5442_ = lean_ctor_get(v_impl_5357_, 3);
lean_inc(v_l_5442_);
if (lean_obj_tag(v_l_5442_) == 0)
{
lean_object* v_r_5443_; lean_object* v_k_5444_; lean_object* v_v_5445_; lean_object* v___x_5447_; uint8_t v_isShared_5448_; uint8_t v_isSharedCheck_5468_; 
v_r_5443_ = lean_ctor_get(v_impl_5357_, 4);
v_k_5444_ = lean_ctor_get(v_impl_5357_, 1);
v_v_5445_ = lean_ctor_get(v_impl_5357_, 2);
v_isSharedCheck_5468_ = !lean_is_exclusive(v_impl_5357_);
if (v_isSharedCheck_5468_ == 0)
{
lean_object* v_unused_5469_; lean_object* v_unused_5470_; 
v_unused_5469_ = lean_ctor_get(v_impl_5357_, 3);
lean_dec(v_unused_5469_);
v_unused_5470_ = lean_ctor_get(v_impl_5357_, 0);
lean_dec(v_unused_5470_);
v___x_5447_ = v_impl_5357_;
v_isShared_5448_ = v_isSharedCheck_5468_;
goto v_resetjp_5446_;
}
else
{
lean_inc(v_r_5443_);
lean_inc(v_v_5445_);
lean_inc(v_k_5444_);
lean_dec(v_impl_5357_);
v___x_5447_ = lean_box(0);
v_isShared_5448_ = v_isSharedCheck_5468_;
goto v_resetjp_5446_;
}
v_resetjp_5446_:
{
lean_object* v_k_5449_; lean_object* v_v_5450_; lean_object* v___x_5452_; uint8_t v_isShared_5453_; uint8_t v_isSharedCheck_5464_; 
v_k_5449_ = lean_ctor_get(v_l_5442_, 1);
v_v_5450_ = lean_ctor_get(v_l_5442_, 2);
v_isSharedCheck_5464_ = !lean_is_exclusive(v_l_5442_);
if (v_isSharedCheck_5464_ == 0)
{
lean_object* v_unused_5465_; lean_object* v_unused_5466_; lean_object* v_unused_5467_; 
v_unused_5465_ = lean_ctor_get(v_l_5442_, 4);
lean_dec(v_unused_5465_);
v_unused_5466_ = lean_ctor_get(v_l_5442_, 3);
lean_dec(v_unused_5466_);
v_unused_5467_ = lean_ctor_get(v_l_5442_, 0);
lean_dec(v_unused_5467_);
v___x_5452_ = v_l_5442_;
v_isShared_5453_ = v_isSharedCheck_5464_;
goto v_resetjp_5451_;
}
else
{
lean_inc(v_v_5450_);
lean_inc(v_k_5449_);
lean_dec(v_l_5442_);
v___x_5452_ = lean_box(0);
v_isShared_5453_ = v_isSharedCheck_5464_;
goto v_resetjp_5451_;
}
v_resetjp_5451_:
{
lean_object* v___x_5454_; lean_object* v___x_5456_; 
v___x_5454_ = lean_unsigned_to_nat(3u);
lean_inc_n(v_r_5443_, 2);
if (v_isShared_5453_ == 0)
{
lean_ctor_set(v___x_5452_, 4, v_r_5443_);
lean_ctor_set(v___x_5452_, 3, v_r_5443_);
lean_ctor_set(v___x_5452_, 2, v_v_5349_);
lean_ctor_set(v___x_5452_, 1, v_k_5348_);
lean_ctor_set(v___x_5452_, 0, v___x_5358_);
v___x_5456_ = v___x_5452_;
goto v_reusejp_5455_;
}
else
{
lean_object* v_reuseFailAlloc_5463_; 
v_reuseFailAlloc_5463_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5463_, 0, v___x_5358_);
lean_ctor_set(v_reuseFailAlloc_5463_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5463_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5463_, 3, v_r_5443_);
lean_ctor_set(v_reuseFailAlloc_5463_, 4, v_r_5443_);
v___x_5456_ = v_reuseFailAlloc_5463_;
goto v_reusejp_5455_;
}
v_reusejp_5455_:
{
lean_object* v___x_5458_; 
lean_inc(v_r_5443_);
if (v_isShared_5448_ == 0)
{
lean_ctor_set(v___x_5447_, 3, v_r_5443_);
lean_ctor_set(v___x_5447_, 0, v___x_5358_);
v___x_5458_ = v___x_5447_;
goto v_reusejp_5457_;
}
else
{
lean_object* v_reuseFailAlloc_5462_; 
v_reuseFailAlloc_5462_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5462_, 0, v___x_5358_);
lean_ctor_set(v_reuseFailAlloc_5462_, 1, v_k_5444_);
lean_ctor_set(v_reuseFailAlloc_5462_, 2, v_v_5445_);
lean_ctor_set(v_reuseFailAlloc_5462_, 3, v_r_5443_);
lean_ctor_set(v_reuseFailAlloc_5462_, 4, v_r_5443_);
v___x_5458_ = v_reuseFailAlloc_5462_;
goto v_reusejp_5457_;
}
v_reusejp_5457_:
{
lean_object* v___x_5460_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v___x_5458_);
lean_ctor_set(v___x_5353_, 3, v___x_5456_);
lean_ctor_set(v___x_5353_, 2, v_v_5450_);
lean_ctor_set(v___x_5353_, 1, v_k_5449_);
lean_ctor_set(v___x_5353_, 0, v___x_5454_);
v___x_5460_ = v___x_5353_;
goto v_reusejp_5459_;
}
else
{
lean_object* v_reuseFailAlloc_5461_; 
v_reuseFailAlloc_5461_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5461_, 0, v___x_5454_);
lean_ctor_set(v_reuseFailAlloc_5461_, 1, v_k_5449_);
lean_ctor_set(v_reuseFailAlloc_5461_, 2, v_v_5450_);
lean_ctor_set(v_reuseFailAlloc_5461_, 3, v___x_5456_);
lean_ctor_set(v_reuseFailAlloc_5461_, 4, v___x_5458_);
v___x_5460_ = v_reuseFailAlloc_5461_;
goto v_reusejp_5459_;
}
v_reusejp_5459_:
{
return v___x_5460_;
}
}
}
}
}
}
else
{
lean_object* v_r_5471_; 
v_r_5471_ = lean_ctor_get(v_impl_5357_, 4);
lean_inc(v_r_5471_);
if (lean_obj_tag(v_r_5471_) == 0)
{
lean_object* v_k_5472_; lean_object* v_v_5473_; lean_object* v___x_5475_; uint8_t v_isShared_5476_; uint8_t v_isSharedCheck_5484_; 
v_k_5472_ = lean_ctor_get(v_impl_5357_, 1);
v_v_5473_ = lean_ctor_get(v_impl_5357_, 2);
v_isSharedCheck_5484_ = !lean_is_exclusive(v_impl_5357_);
if (v_isSharedCheck_5484_ == 0)
{
lean_object* v_unused_5485_; lean_object* v_unused_5486_; lean_object* v_unused_5487_; 
v_unused_5485_ = lean_ctor_get(v_impl_5357_, 4);
lean_dec(v_unused_5485_);
v_unused_5486_ = lean_ctor_get(v_impl_5357_, 3);
lean_dec(v_unused_5486_);
v_unused_5487_ = lean_ctor_get(v_impl_5357_, 0);
lean_dec(v_unused_5487_);
v___x_5475_ = v_impl_5357_;
v_isShared_5476_ = v_isSharedCheck_5484_;
goto v_resetjp_5474_;
}
else
{
lean_inc(v_v_5473_);
lean_inc(v_k_5472_);
lean_dec(v_impl_5357_);
v___x_5475_ = lean_box(0);
v_isShared_5476_ = v_isSharedCheck_5484_;
goto v_resetjp_5474_;
}
v_resetjp_5474_:
{
lean_object* v___x_5477_; lean_object* v___x_5479_; 
v___x_5477_ = lean_unsigned_to_nat(3u);
if (v_isShared_5476_ == 0)
{
lean_ctor_set(v___x_5475_, 4, v_l_5442_);
lean_ctor_set(v___x_5475_, 2, v_v_5349_);
lean_ctor_set(v___x_5475_, 1, v_k_5348_);
lean_ctor_set(v___x_5475_, 0, v___x_5358_);
v___x_5479_ = v___x_5475_;
goto v_reusejp_5478_;
}
else
{
lean_object* v_reuseFailAlloc_5483_; 
v_reuseFailAlloc_5483_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5483_, 0, v___x_5358_);
lean_ctor_set(v_reuseFailAlloc_5483_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5483_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5483_, 3, v_l_5442_);
lean_ctor_set(v_reuseFailAlloc_5483_, 4, v_l_5442_);
v___x_5479_ = v_reuseFailAlloc_5483_;
goto v_reusejp_5478_;
}
v_reusejp_5478_:
{
lean_object* v___x_5481_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_r_5471_);
lean_ctor_set(v___x_5353_, 3, v___x_5479_);
lean_ctor_set(v___x_5353_, 2, v_v_5473_);
lean_ctor_set(v___x_5353_, 1, v_k_5472_);
lean_ctor_set(v___x_5353_, 0, v___x_5477_);
v___x_5481_ = v___x_5353_;
goto v_reusejp_5480_;
}
else
{
lean_object* v_reuseFailAlloc_5482_; 
v_reuseFailAlloc_5482_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5482_, 0, v___x_5477_);
lean_ctor_set(v_reuseFailAlloc_5482_, 1, v_k_5472_);
lean_ctor_set(v_reuseFailAlloc_5482_, 2, v_v_5473_);
lean_ctor_set(v_reuseFailAlloc_5482_, 3, v___x_5479_);
lean_ctor_set(v_reuseFailAlloc_5482_, 4, v_r_5471_);
v___x_5481_ = v_reuseFailAlloc_5482_;
goto v_reusejp_5480_;
}
v_reusejp_5480_:
{
return v___x_5481_;
}
}
}
}
else
{
lean_object* v___x_5488_; lean_object* v___x_5490_; 
v___x_5488_ = lean_unsigned_to_nat(2u);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_impl_5357_);
lean_ctor_set(v___x_5353_, 3, v_r_5471_);
lean_ctor_set(v___x_5353_, 0, v___x_5488_);
v___x_5490_ = v___x_5353_;
goto v_reusejp_5489_;
}
else
{
lean_object* v_reuseFailAlloc_5491_; 
v_reuseFailAlloc_5491_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5491_, 0, v___x_5488_);
lean_ctor_set(v_reuseFailAlloc_5491_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5491_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5491_, 3, v_r_5471_);
lean_ctor_set(v_reuseFailAlloc_5491_, 4, v_impl_5357_);
v___x_5490_ = v_reuseFailAlloc_5491_;
goto v_reusejp_5489_;
}
v_reusejp_5489_:
{
return v___x_5490_;
}
}
}
}
}
else
{
lean_object* v___x_5493_; 
lean_dec(v_v_5349_);
lean_dec(v_k_5348_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 2, v_v_5345_);
lean_ctor_set(v___x_5353_, 1, v_k_5344_);
v___x_5493_ = v___x_5353_;
goto v_reusejp_5492_;
}
else
{
lean_object* v_reuseFailAlloc_5494_; 
v_reuseFailAlloc_5494_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5494_, 0, v_size_5347_);
lean_ctor_set(v_reuseFailAlloc_5494_, 1, v_k_5344_);
lean_ctor_set(v_reuseFailAlloc_5494_, 2, v_v_5345_);
lean_ctor_set(v_reuseFailAlloc_5494_, 3, v_l_5350_);
lean_ctor_set(v_reuseFailAlloc_5494_, 4, v_r_5351_);
v___x_5493_ = v_reuseFailAlloc_5494_;
goto v_reusejp_5492_;
}
v_reusejp_5492_:
{
return v___x_5493_;
}
}
}
else
{
lean_object* v_impl_5495_; lean_object* v___x_5496_; 
lean_dec(v_size_5347_);
v_impl_5495_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5344_, v_v_5345_, v_l_5350_);
v___x_5496_ = lean_unsigned_to_nat(1u);
if (lean_obj_tag(v_r_5351_) == 0)
{
lean_object* v_size_5497_; lean_object* v_size_5498_; lean_object* v_k_5499_; lean_object* v_v_5500_; lean_object* v_l_5501_; lean_object* v_r_5502_; lean_object* v___x_5503_; lean_object* v___x_5504_; uint8_t v___x_5505_; 
v_size_5497_ = lean_ctor_get(v_r_5351_, 0);
v_size_5498_ = lean_ctor_get(v_impl_5495_, 0);
lean_inc(v_size_5498_);
v_k_5499_ = lean_ctor_get(v_impl_5495_, 1);
lean_inc(v_k_5499_);
v_v_5500_ = lean_ctor_get(v_impl_5495_, 2);
lean_inc(v_v_5500_);
v_l_5501_ = lean_ctor_get(v_impl_5495_, 3);
lean_inc(v_l_5501_);
v_r_5502_ = lean_ctor_get(v_impl_5495_, 4);
lean_inc(v_r_5502_);
v___x_5503_ = lean_unsigned_to_nat(3u);
v___x_5504_ = lean_nat_mul(v___x_5503_, v_size_5497_);
v___x_5505_ = lean_nat_dec_lt(v___x_5504_, v_size_5498_);
lean_dec(v___x_5504_);
if (v___x_5505_ == 0)
{
lean_object* v___x_5506_; lean_object* v___x_5507_; lean_object* v___x_5509_; 
lean_dec(v_r_5502_);
lean_dec(v_l_5501_);
lean_dec(v_v_5500_);
lean_dec(v_k_5499_);
v___x_5506_ = lean_nat_add(v___x_5496_, v_size_5498_);
lean_dec(v_size_5498_);
v___x_5507_ = lean_nat_add(v___x_5506_, v_size_5497_);
lean_dec(v___x_5506_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 3, v_impl_5495_);
lean_ctor_set(v___x_5353_, 0, v___x_5507_);
v___x_5509_ = v___x_5353_;
goto v_reusejp_5508_;
}
else
{
lean_object* v_reuseFailAlloc_5510_; 
v_reuseFailAlloc_5510_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5510_, 0, v___x_5507_);
lean_ctor_set(v_reuseFailAlloc_5510_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5510_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5510_, 3, v_impl_5495_);
lean_ctor_set(v_reuseFailAlloc_5510_, 4, v_r_5351_);
v___x_5509_ = v_reuseFailAlloc_5510_;
goto v_reusejp_5508_;
}
v_reusejp_5508_:
{
return v___x_5509_;
}
}
else
{
lean_object* v___x_5512_; uint8_t v_isShared_5513_; uint8_t v_isSharedCheck_5576_; 
v_isSharedCheck_5576_ = !lean_is_exclusive(v_impl_5495_);
if (v_isSharedCheck_5576_ == 0)
{
lean_object* v_unused_5577_; lean_object* v_unused_5578_; lean_object* v_unused_5579_; lean_object* v_unused_5580_; lean_object* v_unused_5581_; 
v_unused_5577_ = lean_ctor_get(v_impl_5495_, 4);
lean_dec(v_unused_5577_);
v_unused_5578_ = lean_ctor_get(v_impl_5495_, 3);
lean_dec(v_unused_5578_);
v_unused_5579_ = lean_ctor_get(v_impl_5495_, 2);
lean_dec(v_unused_5579_);
v_unused_5580_ = lean_ctor_get(v_impl_5495_, 1);
lean_dec(v_unused_5580_);
v_unused_5581_ = lean_ctor_get(v_impl_5495_, 0);
lean_dec(v_unused_5581_);
v___x_5512_ = v_impl_5495_;
v_isShared_5513_ = v_isSharedCheck_5576_;
goto v_resetjp_5511_;
}
else
{
lean_dec(v_impl_5495_);
v___x_5512_ = lean_box(0);
v_isShared_5513_ = v_isSharedCheck_5576_;
goto v_resetjp_5511_;
}
v_resetjp_5511_:
{
lean_object* v_size_5514_; lean_object* v_size_5515_; lean_object* v_k_5516_; lean_object* v_v_5517_; lean_object* v_l_5518_; lean_object* v_r_5519_; lean_object* v___x_5520_; lean_object* v___x_5521_; uint8_t v___x_5522_; 
v_size_5514_ = lean_ctor_get(v_l_5501_, 0);
v_size_5515_ = lean_ctor_get(v_r_5502_, 0);
v_k_5516_ = lean_ctor_get(v_r_5502_, 1);
v_v_5517_ = lean_ctor_get(v_r_5502_, 2);
v_l_5518_ = lean_ctor_get(v_r_5502_, 3);
v_r_5519_ = lean_ctor_get(v_r_5502_, 4);
v___x_5520_ = lean_unsigned_to_nat(2u);
v___x_5521_ = lean_nat_mul(v___x_5520_, v_size_5514_);
v___x_5522_ = lean_nat_dec_lt(v_size_5515_, v___x_5521_);
lean_dec(v___x_5521_);
if (v___x_5522_ == 0)
{
lean_object* v___x_5524_; uint8_t v_isShared_5525_; uint8_t v_isSharedCheck_5551_; 
lean_inc(v_r_5519_);
lean_inc(v_l_5518_);
lean_inc(v_v_5517_);
lean_inc(v_k_5516_);
v_isSharedCheck_5551_ = !lean_is_exclusive(v_r_5502_);
if (v_isSharedCheck_5551_ == 0)
{
lean_object* v_unused_5552_; lean_object* v_unused_5553_; lean_object* v_unused_5554_; lean_object* v_unused_5555_; lean_object* v_unused_5556_; 
v_unused_5552_ = lean_ctor_get(v_r_5502_, 4);
lean_dec(v_unused_5552_);
v_unused_5553_ = lean_ctor_get(v_r_5502_, 3);
lean_dec(v_unused_5553_);
v_unused_5554_ = lean_ctor_get(v_r_5502_, 2);
lean_dec(v_unused_5554_);
v_unused_5555_ = lean_ctor_get(v_r_5502_, 1);
lean_dec(v_unused_5555_);
v_unused_5556_ = lean_ctor_get(v_r_5502_, 0);
lean_dec(v_unused_5556_);
v___x_5524_ = v_r_5502_;
v_isShared_5525_ = v_isSharedCheck_5551_;
goto v_resetjp_5523_;
}
else
{
lean_dec(v_r_5502_);
v___x_5524_ = lean_box(0);
v_isShared_5525_ = v_isSharedCheck_5551_;
goto v_resetjp_5523_;
}
v_resetjp_5523_:
{
lean_object* v___x_5526_; lean_object* v___x_5527_; lean_object* v___y_5529_; lean_object* v___y_5530_; lean_object* v___y_5531_; lean_object* v___x_5539_; lean_object* v___y_5541_; 
v___x_5526_ = lean_nat_add(v___x_5496_, v_size_5498_);
lean_dec(v_size_5498_);
v___x_5527_ = lean_nat_add(v___x_5526_, v_size_5497_);
lean_dec(v___x_5526_);
v___x_5539_ = lean_nat_add(v___x_5496_, v_size_5514_);
if (lean_obj_tag(v_l_5518_) == 0)
{
lean_object* v_size_5549_; 
v_size_5549_ = lean_ctor_get(v_l_5518_, 0);
lean_inc(v_size_5549_);
v___y_5541_ = v_size_5549_;
goto v___jp_5540_;
}
else
{
lean_object* v___x_5550_; 
v___x_5550_ = lean_unsigned_to_nat(0u);
v___y_5541_ = v___x_5550_;
goto v___jp_5540_;
}
v___jp_5528_:
{
lean_object* v___x_5532_; lean_object* v___x_5534_; 
v___x_5532_ = lean_nat_add(v___y_5529_, v___y_5531_);
lean_dec(v___y_5531_);
lean_dec(v___y_5529_);
if (v_isShared_5525_ == 0)
{
lean_ctor_set(v___x_5524_, 4, v_r_5351_);
lean_ctor_set(v___x_5524_, 3, v_r_5519_);
lean_ctor_set(v___x_5524_, 2, v_v_5349_);
lean_ctor_set(v___x_5524_, 1, v_k_5348_);
lean_ctor_set(v___x_5524_, 0, v___x_5532_);
v___x_5534_ = v___x_5524_;
goto v_reusejp_5533_;
}
else
{
lean_object* v_reuseFailAlloc_5538_; 
v_reuseFailAlloc_5538_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5538_, 0, v___x_5532_);
lean_ctor_set(v_reuseFailAlloc_5538_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5538_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5538_, 3, v_r_5519_);
lean_ctor_set(v_reuseFailAlloc_5538_, 4, v_r_5351_);
v___x_5534_ = v_reuseFailAlloc_5538_;
goto v_reusejp_5533_;
}
v_reusejp_5533_:
{
lean_object* v___x_5536_; 
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 4, v___x_5534_);
lean_ctor_set(v___x_5512_, 3, v___y_5530_);
lean_ctor_set(v___x_5512_, 2, v_v_5517_);
lean_ctor_set(v___x_5512_, 1, v_k_5516_);
lean_ctor_set(v___x_5512_, 0, v___x_5527_);
v___x_5536_ = v___x_5512_;
goto v_reusejp_5535_;
}
else
{
lean_object* v_reuseFailAlloc_5537_; 
v_reuseFailAlloc_5537_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5537_, 0, v___x_5527_);
lean_ctor_set(v_reuseFailAlloc_5537_, 1, v_k_5516_);
lean_ctor_set(v_reuseFailAlloc_5537_, 2, v_v_5517_);
lean_ctor_set(v_reuseFailAlloc_5537_, 3, v___y_5530_);
lean_ctor_set(v_reuseFailAlloc_5537_, 4, v___x_5534_);
v___x_5536_ = v_reuseFailAlloc_5537_;
goto v_reusejp_5535_;
}
v_reusejp_5535_:
{
return v___x_5536_;
}
}
}
v___jp_5540_:
{
lean_object* v___x_5542_; lean_object* v___x_5544_; 
v___x_5542_ = lean_nat_add(v___x_5539_, v___y_5541_);
lean_dec(v___y_5541_);
lean_dec(v___x_5539_);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_l_5518_);
lean_ctor_set(v___x_5353_, 3, v_l_5501_);
lean_ctor_set(v___x_5353_, 2, v_v_5500_);
lean_ctor_set(v___x_5353_, 1, v_k_5499_);
lean_ctor_set(v___x_5353_, 0, v___x_5542_);
v___x_5544_ = v___x_5353_;
goto v_reusejp_5543_;
}
else
{
lean_object* v_reuseFailAlloc_5548_; 
v_reuseFailAlloc_5548_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5548_, 0, v___x_5542_);
lean_ctor_set(v_reuseFailAlloc_5548_, 1, v_k_5499_);
lean_ctor_set(v_reuseFailAlloc_5548_, 2, v_v_5500_);
lean_ctor_set(v_reuseFailAlloc_5548_, 3, v_l_5501_);
lean_ctor_set(v_reuseFailAlloc_5548_, 4, v_l_5518_);
v___x_5544_ = v_reuseFailAlloc_5548_;
goto v_reusejp_5543_;
}
v_reusejp_5543_:
{
lean_object* v___x_5545_; 
v___x_5545_ = lean_nat_add(v___x_5496_, v_size_5497_);
if (lean_obj_tag(v_r_5519_) == 0)
{
lean_object* v_size_5546_; 
v_size_5546_ = lean_ctor_get(v_r_5519_, 0);
lean_inc(v_size_5546_);
v___y_5529_ = v___x_5545_;
v___y_5530_ = v___x_5544_;
v___y_5531_ = v_size_5546_;
goto v___jp_5528_;
}
else
{
lean_object* v___x_5547_; 
v___x_5547_ = lean_unsigned_to_nat(0u);
v___y_5529_ = v___x_5545_;
v___y_5530_ = v___x_5544_;
v___y_5531_ = v___x_5547_;
goto v___jp_5528_;
}
}
}
}
}
else
{
lean_object* v___x_5557_; lean_object* v___x_5558_; lean_object* v___x_5559_; lean_object* v___x_5560_; lean_object* v___x_5562_; 
lean_del_object(v___x_5353_);
v___x_5557_ = lean_nat_add(v___x_5496_, v_size_5498_);
lean_dec(v_size_5498_);
v___x_5558_ = lean_nat_add(v___x_5557_, v_size_5497_);
lean_dec(v___x_5557_);
v___x_5559_ = lean_nat_add(v___x_5496_, v_size_5497_);
v___x_5560_ = lean_nat_add(v___x_5559_, v_size_5515_);
lean_dec(v___x_5559_);
lean_inc_ref(v_r_5351_);
if (v_isShared_5513_ == 0)
{
lean_ctor_set(v___x_5512_, 4, v_r_5351_);
lean_ctor_set(v___x_5512_, 3, v_r_5502_);
lean_ctor_set(v___x_5512_, 2, v_v_5349_);
lean_ctor_set(v___x_5512_, 1, v_k_5348_);
lean_ctor_set(v___x_5512_, 0, v___x_5560_);
v___x_5562_ = v___x_5512_;
goto v_reusejp_5561_;
}
else
{
lean_object* v_reuseFailAlloc_5575_; 
v_reuseFailAlloc_5575_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5575_, 0, v___x_5560_);
lean_ctor_set(v_reuseFailAlloc_5575_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5575_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5575_, 3, v_r_5502_);
lean_ctor_set(v_reuseFailAlloc_5575_, 4, v_r_5351_);
v___x_5562_ = v_reuseFailAlloc_5575_;
goto v_reusejp_5561_;
}
v_reusejp_5561_:
{
lean_object* v___x_5564_; uint8_t v_isShared_5565_; uint8_t v_isSharedCheck_5569_; 
v_isSharedCheck_5569_ = !lean_is_exclusive(v_r_5351_);
if (v_isSharedCheck_5569_ == 0)
{
lean_object* v_unused_5570_; lean_object* v_unused_5571_; lean_object* v_unused_5572_; lean_object* v_unused_5573_; lean_object* v_unused_5574_; 
v_unused_5570_ = lean_ctor_get(v_r_5351_, 4);
lean_dec(v_unused_5570_);
v_unused_5571_ = lean_ctor_get(v_r_5351_, 3);
lean_dec(v_unused_5571_);
v_unused_5572_ = lean_ctor_get(v_r_5351_, 2);
lean_dec(v_unused_5572_);
v_unused_5573_ = lean_ctor_get(v_r_5351_, 1);
lean_dec(v_unused_5573_);
v_unused_5574_ = lean_ctor_get(v_r_5351_, 0);
lean_dec(v_unused_5574_);
v___x_5564_ = v_r_5351_;
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
else
{
lean_dec(v_r_5351_);
v___x_5564_ = lean_box(0);
v_isShared_5565_ = v_isSharedCheck_5569_;
goto v_resetjp_5563_;
}
v_resetjp_5563_:
{
lean_object* v___x_5567_; 
if (v_isShared_5565_ == 0)
{
lean_ctor_set(v___x_5564_, 4, v___x_5562_);
lean_ctor_set(v___x_5564_, 3, v_l_5501_);
lean_ctor_set(v___x_5564_, 2, v_v_5500_);
lean_ctor_set(v___x_5564_, 1, v_k_5499_);
lean_ctor_set(v___x_5564_, 0, v___x_5558_);
v___x_5567_ = v___x_5564_;
goto v_reusejp_5566_;
}
else
{
lean_object* v_reuseFailAlloc_5568_; 
v_reuseFailAlloc_5568_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5568_, 0, v___x_5558_);
lean_ctor_set(v_reuseFailAlloc_5568_, 1, v_k_5499_);
lean_ctor_set(v_reuseFailAlloc_5568_, 2, v_v_5500_);
lean_ctor_set(v_reuseFailAlloc_5568_, 3, v_l_5501_);
lean_ctor_set(v_reuseFailAlloc_5568_, 4, v___x_5562_);
v___x_5567_ = v_reuseFailAlloc_5568_;
goto v_reusejp_5566_;
}
v_reusejp_5566_:
{
return v___x_5567_;
}
}
}
}
}
}
}
else
{
lean_object* v_l_5582_; 
v_l_5582_ = lean_ctor_get(v_impl_5495_, 3);
lean_inc(v_l_5582_);
if (lean_obj_tag(v_l_5582_) == 0)
{
lean_object* v_r_5583_; lean_object* v_k_5584_; lean_object* v_v_5585_; lean_object* v___x_5587_; uint8_t v_isShared_5588_; uint8_t v_isSharedCheck_5596_; 
v_r_5583_ = lean_ctor_get(v_impl_5495_, 4);
v_k_5584_ = lean_ctor_get(v_impl_5495_, 1);
v_v_5585_ = lean_ctor_get(v_impl_5495_, 2);
v_isSharedCheck_5596_ = !lean_is_exclusive(v_impl_5495_);
if (v_isSharedCheck_5596_ == 0)
{
lean_object* v_unused_5597_; lean_object* v_unused_5598_; 
v_unused_5597_ = lean_ctor_get(v_impl_5495_, 3);
lean_dec(v_unused_5597_);
v_unused_5598_ = lean_ctor_get(v_impl_5495_, 0);
lean_dec(v_unused_5598_);
v___x_5587_ = v_impl_5495_;
v_isShared_5588_ = v_isSharedCheck_5596_;
goto v_resetjp_5586_;
}
else
{
lean_inc(v_r_5583_);
lean_inc(v_v_5585_);
lean_inc(v_k_5584_);
lean_dec(v_impl_5495_);
v___x_5587_ = lean_box(0);
v_isShared_5588_ = v_isSharedCheck_5596_;
goto v_resetjp_5586_;
}
v_resetjp_5586_:
{
lean_object* v___x_5589_; lean_object* v___x_5591_; 
v___x_5589_ = lean_unsigned_to_nat(3u);
lean_inc(v_r_5583_);
if (v_isShared_5588_ == 0)
{
lean_ctor_set(v___x_5587_, 3, v_r_5583_);
lean_ctor_set(v___x_5587_, 2, v_v_5349_);
lean_ctor_set(v___x_5587_, 1, v_k_5348_);
lean_ctor_set(v___x_5587_, 0, v___x_5496_);
v___x_5591_ = v___x_5587_;
goto v_reusejp_5590_;
}
else
{
lean_object* v_reuseFailAlloc_5595_; 
v_reuseFailAlloc_5595_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5595_, 0, v___x_5496_);
lean_ctor_set(v_reuseFailAlloc_5595_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5595_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5595_, 3, v_r_5583_);
lean_ctor_set(v_reuseFailAlloc_5595_, 4, v_r_5583_);
v___x_5591_ = v_reuseFailAlloc_5595_;
goto v_reusejp_5590_;
}
v_reusejp_5590_:
{
lean_object* v___x_5593_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v___x_5591_);
lean_ctor_set(v___x_5353_, 3, v_l_5582_);
lean_ctor_set(v___x_5353_, 2, v_v_5585_);
lean_ctor_set(v___x_5353_, 1, v_k_5584_);
lean_ctor_set(v___x_5353_, 0, v___x_5589_);
v___x_5593_ = v___x_5353_;
goto v_reusejp_5592_;
}
else
{
lean_object* v_reuseFailAlloc_5594_; 
v_reuseFailAlloc_5594_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5594_, 0, v___x_5589_);
lean_ctor_set(v_reuseFailAlloc_5594_, 1, v_k_5584_);
lean_ctor_set(v_reuseFailAlloc_5594_, 2, v_v_5585_);
lean_ctor_set(v_reuseFailAlloc_5594_, 3, v_l_5582_);
lean_ctor_set(v_reuseFailAlloc_5594_, 4, v___x_5591_);
v___x_5593_ = v_reuseFailAlloc_5594_;
goto v_reusejp_5592_;
}
v_reusejp_5592_:
{
return v___x_5593_;
}
}
}
}
else
{
lean_object* v_r_5599_; 
v_r_5599_ = lean_ctor_get(v_impl_5495_, 4);
lean_inc(v_r_5599_);
if (lean_obj_tag(v_r_5599_) == 0)
{
lean_object* v_k_5600_; lean_object* v_v_5601_; lean_object* v___x_5603_; uint8_t v_isShared_5604_; uint8_t v_isSharedCheck_5624_; 
v_k_5600_ = lean_ctor_get(v_impl_5495_, 1);
v_v_5601_ = lean_ctor_get(v_impl_5495_, 2);
v_isSharedCheck_5624_ = !lean_is_exclusive(v_impl_5495_);
if (v_isSharedCheck_5624_ == 0)
{
lean_object* v_unused_5625_; lean_object* v_unused_5626_; lean_object* v_unused_5627_; 
v_unused_5625_ = lean_ctor_get(v_impl_5495_, 4);
lean_dec(v_unused_5625_);
v_unused_5626_ = lean_ctor_get(v_impl_5495_, 3);
lean_dec(v_unused_5626_);
v_unused_5627_ = lean_ctor_get(v_impl_5495_, 0);
lean_dec(v_unused_5627_);
v___x_5603_ = v_impl_5495_;
v_isShared_5604_ = v_isSharedCheck_5624_;
goto v_resetjp_5602_;
}
else
{
lean_inc(v_v_5601_);
lean_inc(v_k_5600_);
lean_dec(v_impl_5495_);
v___x_5603_ = lean_box(0);
v_isShared_5604_ = v_isSharedCheck_5624_;
goto v_resetjp_5602_;
}
v_resetjp_5602_:
{
lean_object* v_k_5605_; lean_object* v_v_5606_; lean_object* v___x_5608_; uint8_t v_isShared_5609_; uint8_t v_isSharedCheck_5620_; 
v_k_5605_ = lean_ctor_get(v_r_5599_, 1);
v_v_5606_ = lean_ctor_get(v_r_5599_, 2);
v_isSharedCheck_5620_ = !lean_is_exclusive(v_r_5599_);
if (v_isSharedCheck_5620_ == 0)
{
lean_object* v_unused_5621_; lean_object* v_unused_5622_; lean_object* v_unused_5623_; 
v_unused_5621_ = lean_ctor_get(v_r_5599_, 4);
lean_dec(v_unused_5621_);
v_unused_5622_ = lean_ctor_get(v_r_5599_, 3);
lean_dec(v_unused_5622_);
v_unused_5623_ = lean_ctor_get(v_r_5599_, 0);
lean_dec(v_unused_5623_);
v___x_5608_ = v_r_5599_;
v_isShared_5609_ = v_isSharedCheck_5620_;
goto v_resetjp_5607_;
}
else
{
lean_inc(v_v_5606_);
lean_inc(v_k_5605_);
lean_dec(v_r_5599_);
v___x_5608_ = lean_box(0);
v_isShared_5609_ = v_isSharedCheck_5620_;
goto v_resetjp_5607_;
}
v_resetjp_5607_:
{
lean_object* v___x_5610_; lean_object* v___x_5612_; 
v___x_5610_ = lean_unsigned_to_nat(3u);
if (v_isShared_5609_ == 0)
{
lean_ctor_set(v___x_5608_, 4, v_l_5582_);
lean_ctor_set(v___x_5608_, 3, v_l_5582_);
lean_ctor_set(v___x_5608_, 2, v_v_5601_);
lean_ctor_set(v___x_5608_, 1, v_k_5600_);
lean_ctor_set(v___x_5608_, 0, v___x_5496_);
v___x_5612_ = v___x_5608_;
goto v_reusejp_5611_;
}
else
{
lean_object* v_reuseFailAlloc_5619_; 
v_reuseFailAlloc_5619_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5619_, 0, v___x_5496_);
lean_ctor_set(v_reuseFailAlloc_5619_, 1, v_k_5600_);
lean_ctor_set(v_reuseFailAlloc_5619_, 2, v_v_5601_);
lean_ctor_set(v_reuseFailAlloc_5619_, 3, v_l_5582_);
lean_ctor_set(v_reuseFailAlloc_5619_, 4, v_l_5582_);
v___x_5612_ = v_reuseFailAlloc_5619_;
goto v_reusejp_5611_;
}
v_reusejp_5611_:
{
lean_object* v___x_5614_; 
if (v_isShared_5604_ == 0)
{
lean_ctor_set(v___x_5603_, 4, v_l_5582_);
lean_ctor_set(v___x_5603_, 2, v_v_5349_);
lean_ctor_set(v___x_5603_, 1, v_k_5348_);
lean_ctor_set(v___x_5603_, 0, v___x_5496_);
v___x_5614_ = v___x_5603_;
goto v_reusejp_5613_;
}
else
{
lean_object* v_reuseFailAlloc_5618_; 
v_reuseFailAlloc_5618_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5618_, 0, v___x_5496_);
lean_ctor_set(v_reuseFailAlloc_5618_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5618_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5618_, 3, v_l_5582_);
lean_ctor_set(v_reuseFailAlloc_5618_, 4, v_l_5582_);
v___x_5614_ = v_reuseFailAlloc_5618_;
goto v_reusejp_5613_;
}
v_reusejp_5613_:
{
lean_object* v___x_5616_; 
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v___x_5614_);
lean_ctor_set(v___x_5353_, 3, v___x_5612_);
lean_ctor_set(v___x_5353_, 2, v_v_5606_);
lean_ctor_set(v___x_5353_, 1, v_k_5605_);
lean_ctor_set(v___x_5353_, 0, v___x_5610_);
v___x_5616_ = v___x_5353_;
goto v_reusejp_5615_;
}
else
{
lean_object* v_reuseFailAlloc_5617_; 
v_reuseFailAlloc_5617_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5617_, 0, v___x_5610_);
lean_ctor_set(v_reuseFailAlloc_5617_, 1, v_k_5605_);
lean_ctor_set(v_reuseFailAlloc_5617_, 2, v_v_5606_);
lean_ctor_set(v_reuseFailAlloc_5617_, 3, v___x_5612_);
lean_ctor_set(v_reuseFailAlloc_5617_, 4, v___x_5614_);
v___x_5616_ = v_reuseFailAlloc_5617_;
goto v_reusejp_5615_;
}
v_reusejp_5615_:
{
return v___x_5616_;
}
}
}
}
}
}
else
{
lean_object* v___x_5628_; lean_object* v___x_5630_; 
v___x_5628_ = lean_unsigned_to_nat(2u);
if (v_isShared_5354_ == 0)
{
lean_ctor_set(v___x_5353_, 4, v_r_5599_);
lean_ctor_set(v___x_5353_, 3, v_impl_5495_);
lean_ctor_set(v___x_5353_, 0, v___x_5628_);
v___x_5630_ = v___x_5353_;
goto v_reusejp_5629_;
}
else
{
lean_object* v_reuseFailAlloc_5631_; 
v_reuseFailAlloc_5631_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5631_, 0, v___x_5628_);
lean_ctor_set(v_reuseFailAlloc_5631_, 1, v_k_5348_);
lean_ctor_set(v_reuseFailAlloc_5631_, 2, v_v_5349_);
lean_ctor_set(v_reuseFailAlloc_5631_, 3, v_impl_5495_);
lean_ctor_set(v_reuseFailAlloc_5631_, 4, v_r_5599_);
v___x_5630_ = v_reuseFailAlloc_5631_;
goto v_reusejp_5629_;
}
v_reusejp_5629_:
{
return v___x_5630_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_5633_; lean_object* v___x_5634_; 
v___x_5633_ = lean_unsigned_to_nat(1u);
v___x_5634_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_5634_, 0, v___x_5633_);
lean_ctor_set(v___x_5634_, 1, v_k_5344_);
lean_ctor_set(v___x_5634_, 2, v_v_5345_);
lean_ctor_set(v___x_5634_, 3, v_t_5346_);
lean_ctor_set(v___x_5634_, 4, v_t_5346_);
return v___x_5634_;
}
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(lean_object* v_k_5635_, lean_object* v_t_5636_){
_start:
{
if (lean_obj_tag(v_t_5636_) == 0)
{
lean_object* v_k_5637_; lean_object* v_l_5638_; lean_object* v_r_5639_; uint8_t v___x_5640_; 
v_k_5637_ = lean_ctor_get(v_t_5636_, 1);
v_l_5638_ = lean_ctor_get(v_t_5636_, 3);
v_r_5639_ = lean_ctor_get(v_t_5636_, 4);
v___x_5640_ = lean_nat_dec_lt(v_k_5637_, v_k_5635_);
if (v___x_5640_ == 0)
{
uint8_t v___x_5641_; 
v___x_5641_ = lean_nat_dec_eq(v_k_5637_, v_k_5635_);
if (v___x_5641_ == 0)
{
v_t_5636_ = v_r_5639_;
goto _start;
}
else
{
return v___x_5641_;
}
}
else
{
v_t_5636_ = v_l_5638_;
goto _start;
}
}
else
{
uint8_t v___x_5644_; 
v___x_5644_ = 0;
return v___x_5644_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg___boxed(lean_object* v_k_5645_, lean_object* v_t_5646_){
_start:
{
uint8_t v_res_5647_; lean_object* v_r_5648_; 
v_res_5647_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5645_, v_t_5646_);
lean_dec(v_t_5646_);
lean_dec(v_k_5645_);
v_r_5648_ = lean_box(v_res_5647_);
return v_r_5648_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstanceEntry(lean_object* v_d_5649_, lean_object* v_e_5650_){
_start:
{
lean_object* v_defaultInstances_5651_; lean_object* v_priorities_5652_; lean_object* v___x_5654_; uint8_t v_isShared_5655_; uint8_t v_isSharedCheck_5679_; 
v_defaultInstances_5651_ = lean_ctor_get(v_d_5649_, 0);
v_priorities_5652_ = lean_ctor_get(v_d_5649_, 1);
v_isSharedCheck_5679_ = !lean_is_exclusive(v_d_5649_);
if (v_isSharedCheck_5679_ == 0)
{
v___x_5654_ = v_d_5649_;
v_isShared_5655_ = v_isSharedCheck_5679_;
goto v_resetjp_5653_;
}
else
{
lean_inc(v_priorities_5652_);
lean_inc(v_defaultInstances_5651_);
lean_dec(v_d_5649_);
v___x_5654_ = lean_box(0);
v_isShared_5655_ = v_isSharedCheck_5679_;
goto v_resetjp_5653_;
}
v_resetjp_5653_:
{
lean_object* v_className_5656_; lean_object* v_instanceName_5657_; lean_object* v_priority_5658_; lean_object* v___y_5660_; uint8_t v___x_5676_; 
v_className_5656_ = lean_ctor_get(v_e_5650_, 0);
lean_inc(v_className_5656_);
v_instanceName_5657_ = lean_ctor_get(v_e_5650_, 1);
lean_inc(v_instanceName_5657_);
v_priority_5658_ = lean_ctor_get(v_e_5650_, 2);
lean_inc(v_priority_5658_);
lean_dec_ref(v_e_5650_);
v___x_5676_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_priority_5658_, v_priorities_5652_);
if (v___x_5676_ == 0)
{
lean_object* v___x_5677_; lean_object* v___x_5678_; 
v___x_5677_ = lean_box(0);
lean_inc(v_priority_5658_);
v___x_5678_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_priority_5658_, v___x_5677_, v_priorities_5652_);
v___y_5660_ = v___x_5678_;
goto v___jp_5659_;
}
else
{
v___y_5660_ = v_priorities_5652_;
goto v___jp_5659_;
}
v___jp_5659_:
{
lean_object* v___x_5661_; 
v___x_5661_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_5651_, v_className_5656_);
if (lean_obj_tag(v___x_5661_) == 0)
{
lean_object* v___x_5662_; lean_object* v___x_5663_; lean_object* v___x_5664_; lean_object* v___x_5665_; lean_object* v___x_5667_; 
v___x_5662_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5662_, 0, v_instanceName_5657_);
lean_ctor_set(v___x_5662_, 1, v_priority_5658_);
v___x_5663_ = lean_box(0);
v___x_5664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5664_, 0, v___x_5662_);
lean_ctor_set(v___x_5664_, 1, v___x_5663_);
v___x_5665_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5656_, v___x_5664_, v_defaultInstances_5651_);
if (v_isShared_5655_ == 0)
{
lean_ctor_set(v___x_5654_, 1, v___y_5660_);
lean_ctor_set(v___x_5654_, 0, v___x_5665_);
v___x_5667_ = v___x_5654_;
goto v_reusejp_5666_;
}
else
{
lean_object* v_reuseFailAlloc_5668_; 
v_reuseFailAlloc_5668_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5668_, 0, v___x_5665_);
lean_ctor_set(v_reuseFailAlloc_5668_, 1, v___y_5660_);
v___x_5667_ = v_reuseFailAlloc_5668_;
goto v_reusejp_5666_;
}
v_reusejp_5666_:
{
return v___x_5667_;
}
}
else
{
lean_object* v_val_5669_; lean_object* v___x_5670_; lean_object* v___x_5671_; lean_object* v___x_5672_; lean_object* v___x_5674_; 
v_val_5669_ = lean_ctor_get(v___x_5661_, 0);
lean_inc(v_val_5669_);
lean_dec_ref_known(v___x_5661_, 1);
v___x_5670_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_5670_, 0, v_instanceName_5657_);
lean_ctor_set(v___x_5670_, 1, v_priority_5658_);
v___x_5671_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_5671_, 0, v___x_5670_);
lean_ctor_set(v___x_5671_, 1, v_val_5669_);
v___x_5672_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_className_5656_, v___x_5671_, v_defaultInstances_5651_);
if (v_isShared_5655_ == 0)
{
lean_ctor_set(v___x_5654_, 1, v___y_5660_);
lean_ctor_set(v___x_5654_, 0, v___x_5672_);
v___x_5674_ = v___x_5654_;
goto v_reusejp_5673_;
}
else
{
lean_object* v_reuseFailAlloc_5675_; 
v_reuseFailAlloc_5675_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_5675_, 0, v___x_5672_);
lean_ctor_set(v_reuseFailAlloc_5675_, 1, v___y_5660_);
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
}
}
LEAN_EXPORT uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(lean_object* v_00_u03b2_5680_, lean_object* v_k_5681_, lean_object* v_t_5682_){
_start:
{
uint8_t v___x_5683_; 
v___x_5683_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___redArg(v_k_5681_, v_t_5682_);
return v___x_5683_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0___boxed(lean_object* v_00_u03b2_5684_, lean_object* v_k_5685_, lean_object* v_t_5686_){
_start:
{
uint8_t v_res_5687_; lean_object* v_r_5688_; 
v_res_5687_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_Meta_addDefaultInstanceEntry_spec__0(v_00_u03b2_5684_, v_k_5685_, v_t_5686_);
lean_dec(v_t_5686_);
lean_dec(v_k_5685_);
v_r_5688_ = lean_box(v_res_5687_);
return v_r_5688_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1(lean_object* v_00_u03b2_5689_, lean_object* v_k_5690_, lean_object* v_v_5691_, lean_object* v_t_5692_, lean_object* v_hl_5693_){
_start:
{
lean_object* v___x_5694_; 
v___x_5694_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_Meta_addDefaultInstanceEntry_spec__1___redArg(v_k_5690_, v_v_5691_, v_t_5692_);
return v___x_5694_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(lean_object* v_env_5695_, lean_object* v_as_5696_, size_t v_i_5697_, size_t v_stop_5698_, lean_object* v_b_5699_){
_start:
{
lean_object* v___y_5701_; uint8_t v___x_5705_; 
v___x_5705_ = lean_usize_dec_eq(v_i_5697_, v_stop_5698_);
if (v___x_5705_ == 0)
{
lean_object* v___x_5706_; lean_object* v_instanceName_5707_; uint8_t v___x_5708_; lean_object* v___x_5709_; uint8_t v___x_5710_; 
v___x_5706_ = lean_array_uget_borrowed(v_as_5696_, v_i_5697_);
v_instanceName_5707_ = lean_ctor_get(v___x_5706_, 1);
v___x_5708_ = 1;
lean_inc_ref(v_env_5695_);
v___x_5709_ = l_Lean_Environment_setExporting(v_env_5695_, v___x_5708_);
lean_inc(v_instanceName_5707_);
v___x_5710_ = l_Lean_Environment_contains(v___x_5709_, v_instanceName_5707_, v___x_5705_);
if (v___x_5710_ == 0)
{
v___y_5701_ = v_b_5699_;
goto v___jp_5700_;
}
else
{
lean_object* v___x_5711_; 
lean_inc(v___x_5706_);
v___x_5711_ = lean_array_push(v_b_5699_, v___x_5706_);
v___y_5701_ = v___x_5711_;
goto v___jp_5700_;
}
}
else
{
lean_dec_ref(v_env_5695_);
return v_b_5699_;
}
v___jp_5700_:
{
size_t v___x_5702_; size_t v___x_5703_; 
v___x_5702_ = ((size_t)1ULL);
v___x_5703_ = lean_usize_add(v_i_5697_, v___x_5702_);
v_i_5697_ = v___x_5703_;
v_b_5699_ = v___y_5701_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0___boxed(lean_object* v_env_5712_, lean_object* v_as_5713_, lean_object* v_i_5714_, lean_object* v_stop_5715_, lean_object* v_b_5716_){
_start:
{
size_t v_i_boxed_5717_; size_t v_stop_boxed_5718_; lean_object* v_res_5719_; 
v_i_boxed_5717_ = lean_unbox_usize(v_i_5714_);
lean_dec(v_i_5714_);
v_stop_boxed_5718_ = lean_unbox_usize(v_stop_5715_);
lean_dec(v_stop_5715_);
v_res_5719_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5712_, v_as_5713_, v_i_boxed_5717_, v_stop_boxed_5718_, v_b_5716_);
lean_dec_ref(v_as_5713_);
return v_res_5719_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_env_5722_, lean_object* v_x_5723_, lean_object* v_entries_5724_){
_start:
{
lean_object* v_all_5725_; lean_object* v___x_5726_; lean_object* v___x_5727_; lean_object* v___x_5728_; uint8_t v___x_5729_; 
v_all_5725_ = lean_array_mk(v_entries_5724_);
v___x_5726_ = lean_unsigned_to_nat(0u);
v___x_5727_ = lean_array_get_size(v_all_5725_);
v___x_5728_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0___closed__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5729_ = lean_nat_dec_lt(v___x_5726_, v___x_5727_);
if (v___x_5729_ == 0)
{
lean_object* v___x_5730_; 
lean_dec_ref(v_env_5722_);
v___x_5730_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5730_, 0, v___x_5728_);
lean_ctor_set(v___x_5730_, 1, v___x_5728_);
lean_ctor_set(v___x_5730_, 2, v_all_5725_);
return v___x_5730_;
}
else
{
uint8_t v___x_5731_; 
v___x_5731_ = lean_nat_dec_le(v___x_5727_, v___x_5727_);
if (v___x_5731_ == 0)
{
if (v___x_5729_ == 0)
{
lean_object* v___x_5732_; 
lean_dec_ref(v_env_5722_);
v___x_5732_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5732_, 0, v___x_5728_);
lean_ctor_set(v___x_5732_, 1, v___x_5728_);
lean_ctor_set(v___x_5732_, 2, v_all_5725_);
return v___x_5732_;
}
else
{
size_t v___x_5733_; size_t v___x_5734_; lean_object* v___x_5735_; lean_object* v___x_5736_; 
v___x_5733_ = ((size_t)0ULL);
v___x_5734_ = lean_usize_of_nat(v___x_5727_);
v___x_5735_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5722_, v_all_5725_, v___x_5733_, v___x_5734_, v___x_5728_);
lean_inc_ref(v___x_5735_);
v___x_5736_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5736_, 0, v___x_5735_);
lean_ctor_set(v___x_5736_, 1, v___x_5735_);
lean_ctor_set(v___x_5736_, 2, v_all_5725_);
return v___x_5736_;
}
}
else
{
size_t v___x_5737_; size_t v___x_5738_; lean_object* v___x_5739_; lean_object* v___x_5740_; 
v___x_5737_ = ((size_t)0ULL);
v___x_5738_ = lean_usize_of_nat(v___x_5727_);
v___x_5739_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__0(v_env_5722_, v_all_5725_, v___x_5737_, v___x_5738_, v___x_5728_);
lean_inc_ref(v___x_5739_);
v___x_5740_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5740_, 0, v___x_5739_);
lean_ctor_set(v___x_5740_, 1, v___x_5739_);
lean_ctor_set(v___x_5740_, 2, v_all_5725_);
return v___x_5740_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_env_5741_, lean_object* v_x_5742_, lean_object* v_entries_5743_){
_start:
{
lean_object* v_res_5744_; 
v_res_5744_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_env_5741_, v_x_5742_, v_entries_5743_);
lean_dec_ref(v_x_5742_);
return v_res_5744_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5745_){
_start:
{
lean_object* v___x_5746_; 
v___x_5746_ = lean_array_mk(v_es_5745_);
return v___x_5746_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(lean_object* v_as_5747_, size_t v_i_5748_, size_t v_stop_5749_, lean_object* v_b_5750_){
_start:
{
uint8_t v___x_5751_; 
v___x_5751_ = lean_usize_dec_eq(v_i_5748_, v_stop_5749_);
if (v___x_5751_ == 0)
{
lean_object* v___x_5752_; lean_object* v___x_5753_; size_t v___x_5754_; size_t v___x_5755_; 
v___x_5752_ = lean_array_uget_borrowed(v_as_5747_, v_i_5748_);
lean_inc(v___x_5752_);
v___x_5753_ = l_Lean_Meta_addDefaultInstanceEntry(v_b_5750_, v___x_5752_);
v___x_5754_ = ((size_t)1ULL);
v___x_5755_ = lean_usize_add(v_i_5748_, v___x_5754_);
v_i_5748_ = v___x_5755_;
v_b_5750_ = v___x_5753_;
goto _start;
}
else
{
return v_b_5750_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1___boxed(lean_object* v_as_5757_, lean_object* v_i_5758_, lean_object* v_stop_5759_, lean_object* v_b_5760_){
_start:
{
size_t v_i_boxed_5761_; size_t v_stop_boxed_5762_; lean_object* v_res_5763_; 
v_i_boxed_5761_ = lean_unbox_usize(v_i_5758_);
lean_dec(v_i_5758_);
v_stop_boxed_5762_ = lean_unbox_usize(v_stop_5759_);
lean_dec(v_stop_5759_);
v_res_5763_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v_as_5757_, v_i_boxed_5761_, v_stop_boxed_5762_, v_b_5760_);
lean_dec_ref(v_as_5757_);
return v_res_5763_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_as_5764_, size_t v_i_5765_, size_t v_stop_5766_, lean_object* v_b_5767_){
_start:
{
lean_object* v___y_5769_; uint8_t v___x_5773_; 
v___x_5773_ = lean_usize_dec_eq(v_i_5765_, v_stop_5766_);
if (v___x_5773_ == 0)
{
lean_object* v___x_5774_; lean_object* v___x_5775_; lean_object* v___x_5776_; uint8_t v___x_5777_; 
v___x_5774_ = lean_array_uget_borrowed(v_as_5764_, v_i_5765_);
v___x_5775_ = lean_unsigned_to_nat(0u);
v___x_5776_ = lean_array_get_size(v___x_5774_);
v___x_5777_ = lean_nat_dec_lt(v___x_5775_, v___x_5776_);
if (v___x_5777_ == 0)
{
v___y_5769_ = v_b_5767_;
goto v___jp_5768_;
}
else
{
uint8_t v___x_5778_; 
v___x_5778_ = lean_nat_dec_le(v___x_5776_, v___x_5776_);
if (v___x_5778_ == 0)
{
if (v___x_5777_ == 0)
{
v___y_5769_ = v_b_5767_;
goto v___jp_5768_;
}
else
{
size_t v___x_5779_; size_t v___x_5780_; lean_object* v___x_5781_; 
v___x_5779_ = ((size_t)0ULL);
v___x_5780_ = lean_usize_of_nat(v___x_5776_);
v___x_5781_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5774_, v___x_5779_, v___x_5780_, v_b_5767_);
v___y_5769_ = v___x_5781_;
goto v___jp_5768_;
}
}
else
{
size_t v___x_5782_; size_t v___x_5783_; lean_object* v___x_5784_; 
v___x_5782_ = ((size_t)0ULL);
v___x_5783_ = lean_usize_of_nat(v___x_5776_);
v___x_5784_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__1(v___x_5774_, v___x_5782_, v___x_5783_, v_b_5767_);
v___y_5769_ = v___x_5784_;
goto v___jp_5768_;
}
}
}
else
{
return v_b_5767_;
}
v___jp_5768_:
{
size_t v___x_5770_; size_t v___x_5771_; 
v___x_5770_ = ((size_t)1ULL);
v___x_5771_ = lean_usize_add(v_i_5765_, v___x_5770_);
v_i_5765_ = v___x_5771_;
v_b_5767_ = v___y_5769_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_as_5785_, lean_object* v_i_5786_, lean_object* v_stop_5787_, lean_object* v_b_5788_){
_start:
{
size_t v_i_boxed_5789_; size_t v_stop_boxed_5790_; lean_object* v_res_5791_; 
v_i_boxed_5789_ = lean_unbox_usize(v_i_5786_);
lean_dec(v_i_5786_);
v_stop_boxed_5790_ = lean_unbox_usize(v_stop_5787_);
lean_dec(v_stop_5787_);
v_res_5791_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5785_, v_i_boxed_5789_, v_stop_boxed_5790_, v_b_5788_);
lean_dec_ref(v_as_5785_);
return v_res_5791_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(lean_object* v_initState_5792_, lean_object* v_as_5793_){
_start:
{
lean_object* v___x_5794_; lean_object* v___x_5795_; uint8_t v___x_5796_; 
v___x_5794_ = lean_unsigned_to_nat(0u);
v___x_5795_ = lean_array_get_size(v_as_5793_);
v___x_5796_ = lean_nat_dec_lt(v___x_5794_, v___x_5795_);
if (v___x_5796_ == 0)
{
return v_initState_5792_;
}
else
{
uint8_t v___x_5797_; 
v___x_5797_ = lean_nat_dec_le(v___x_5795_, v___x_5795_);
if (v___x_5797_ == 0)
{
if (v___x_5796_ == 0)
{
return v_initState_5792_;
}
else
{
size_t v___x_5798_; size_t v___x_5799_; lean_object* v___x_5800_; 
v___x_5798_ = ((size_t)0ULL);
v___x_5799_ = lean_usize_of_nat(v___x_5795_);
v___x_5800_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5793_, v___x_5798_, v___x_5799_, v_initState_5792_);
return v___x_5800_;
}
}
else
{
size_t v___x_5801_; size_t v___x_5802_; lean_object* v___x_5803_; 
v___x_5801_ = ((size_t)0ULL);
v___x_5802_ = lean_usize_of_nat(v___x_5795_);
v___x_5803_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1_spec__2(v_as_5793_, v___x_5801_, v___x_5802_, v_initState_5792_);
return v___x_5803_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1___boxed(lean_object* v_initState_5804_, lean_object* v_as_5805_){
_start:
{
lean_object* v_res_5806_; 
v_res_5806_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v_initState_5804_, v_as_5805_);
lean_dec_ref(v_as_5805_);
return v_res_5806_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(lean_object* v_es_5807_){
_start:
{
lean_object* v___x_5808_; lean_object* v___x_5809_; 
v___x_5808_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default___closed__0));
v___x_5809_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2__spec__1(v___x_5808_, v_es_5807_);
return v___x_5809_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_es_5810_){
_start:
{
lean_object* v_res_5811_; 
v_res_5811_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(v_es_5810_);
lean_dec_ref(v_es_5810_);
return v_res_5811_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_5832_; lean_object* v___x_5833_; 
v___x_5832_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__7_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_));
v___x_5833_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_5832_);
return v___x_5833_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2____boxed(lean_object* v_a_5834_){
_start:
{
lean_object* v_res_5835_; 
v_res_5835_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1412103510____hygCtx___hyg_2_();
return v_res_5835_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(lean_object* v_env_5836_, lean_object* v___y_5837_, lean_object* v___y_5838_){
_start:
{
lean_object* v___x_5840_; lean_object* v_nextMacroScope_5841_; lean_object* v_ngen_5842_; lean_object* v_auxDeclNGen_5843_; lean_object* v_traceState_5844_; lean_object* v_messages_5845_; lean_object* v_infoState_5846_; lean_object* v_snapshotTasks_5847_; lean_object* v___x_5849_; uint8_t v_isShared_5850_; uint8_t v_isSharedCheck_5873_; 
v___x_5840_ = lean_st_ref_take(v___y_5838_);
v_nextMacroScope_5841_ = lean_ctor_get(v___x_5840_, 1);
v_ngen_5842_ = lean_ctor_get(v___x_5840_, 2);
v_auxDeclNGen_5843_ = lean_ctor_get(v___x_5840_, 3);
v_traceState_5844_ = lean_ctor_get(v___x_5840_, 4);
v_messages_5845_ = lean_ctor_get(v___x_5840_, 6);
v_infoState_5846_ = lean_ctor_get(v___x_5840_, 7);
v_snapshotTasks_5847_ = lean_ctor_get(v___x_5840_, 8);
v_isSharedCheck_5873_ = !lean_is_exclusive(v___x_5840_);
if (v_isSharedCheck_5873_ == 0)
{
lean_object* v_unused_5874_; lean_object* v_unused_5875_; 
v_unused_5874_ = lean_ctor_get(v___x_5840_, 5);
lean_dec(v_unused_5874_);
v_unused_5875_ = lean_ctor_get(v___x_5840_, 0);
lean_dec(v_unused_5875_);
v___x_5849_ = v___x_5840_;
v_isShared_5850_ = v_isSharedCheck_5873_;
goto v_resetjp_5848_;
}
else
{
lean_inc(v_snapshotTasks_5847_);
lean_inc(v_infoState_5846_);
lean_inc(v_messages_5845_);
lean_inc(v_traceState_5844_);
lean_inc(v_auxDeclNGen_5843_);
lean_inc(v_ngen_5842_);
lean_inc(v_nextMacroScope_5841_);
lean_dec(v___x_5840_);
v___x_5849_ = lean_box(0);
v_isShared_5850_ = v_isSharedCheck_5873_;
goto v_resetjp_5848_;
}
v_resetjp_5848_:
{
lean_object* v___x_5851_; lean_object* v___x_5853_; 
v___x_5851_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__2);
if (v_isShared_5850_ == 0)
{
lean_ctor_set(v___x_5849_, 5, v___x_5851_);
lean_ctor_set(v___x_5849_, 0, v_env_5836_);
v___x_5853_ = v___x_5849_;
goto v_reusejp_5852_;
}
else
{
lean_object* v_reuseFailAlloc_5872_; 
v_reuseFailAlloc_5872_ = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(v_reuseFailAlloc_5872_, 0, v_env_5836_);
lean_ctor_set(v_reuseFailAlloc_5872_, 1, v_nextMacroScope_5841_);
lean_ctor_set(v_reuseFailAlloc_5872_, 2, v_ngen_5842_);
lean_ctor_set(v_reuseFailAlloc_5872_, 3, v_auxDeclNGen_5843_);
lean_ctor_set(v_reuseFailAlloc_5872_, 4, v_traceState_5844_);
lean_ctor_set(v_reuseFailAlloc_5872_, 5, v___x_5851_);
lean_ctor_set(v_reuseFailAlloc_5872_, 6, v_messages_5845_);
lean_ctor_set(v_reuseFailAlloc_5872_, 7, v_infoState_5846_);
lean_ctor_set(v_reuseFailAlloc_5872_, 8, v_snapshotTasks_5847_);
v___x_5853_ = v_reuseFailAlloc_5872_;
goto v_reusejp_5852_;
}
v_reusejp_5852_:
{
lean_object* v___x_5854_; lean_object* v___x_5855_; lean_object* v_mctx_5856_; lean_object* v_zetaDeltaFVarIds_5857_; lean_object* v_postponed_5858_; lean_object* v_diag_5859_; lean_object* v___x_5861_; uint8_t v_isShared_5862_; uint8_t v_isSharedCheck_5870_; 
v___x_5854_ = lean_st_ref_set(v___y_5838_, v___x_5853_);
v___x_5855_ = lean_st_ref_take(v___y_5837_);
v_mctx_5856_ = lean_ctor_get(v___x_5855_, 0);
v_zetaDeltaFVarIds_5857_ = lean_ctor_get(v___x_5855_, 2);
v_postponed_5858_ = lean_ctor_get(v___x_5855_, 3);
v_diag_5859_ = lean_ctor_get(v___x_5855_, 4);
v_isSharedCheck_5870_ = !lean_is_exclusive(v___x_5855_);
if (v_isSharedCheck_5870_ == 0)
{
lean_object* v_unused_5871_; 
v_unused_5871_ = lean_ctor_get(v___x_5855_, 1);
lean_dec(v_unused_5871_);
v___x_5861_ = v___x_5855_;
v_isShared_5862_ = v_isSharedCheck_5870_;
goto v_resetjp_5860_;
}
else
{
lean_inc(v_diag_5859_);
lean_inc(v_postponed_5858_);
lean_inc(v_zetaDeltaFVarIds_5857_);
lean_inc(v_mctx_5856_);
lean_dec(v___x_5855_);
v___x_5861_ = lean_box(0);
v_isShared_5862_ = v_isSharedCheck_5870_;
goto v_resetjp_5860_;
}
v_resetjp_5860_:
{
lean_object* v___x_5863_; lean_object* v___x_5865_; 
v___x_5863_ = lean_obj_once(&l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3, &l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3_once, _init_l_Lean_ScopedEnvExtension_add___at___00Lean_Meta_addInstance_spec__2___redArg___closed__3);
if (v_isShared_5862_ == 0)
{
lean_ctor_set(v___x_5861_, 1, v___x_5863_);
v___x_5865_ = v___x_5861_;
goto v_reusejp_5864_;
}
else
{
lean_object* v_reuseFailAlloc_5869_; 
v_reuseFailAlloc_5869_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v_reuseFailAlloc_5869_, 0, v_mctx_5856_);
lean_ctor_set(v_reuseFailAlloc_5869_, 1, v___x_5863_);
lean_ctor_set(v_reuseFailAlloc_5869_, 2, v_zetaDeltaFVarIds_5857_);
lean_ctor_set(v_reuseFailAlloc_5869_, 3, v_postponed_5858_);
lean_ctor_set(v_reuseFailAlloc_5869_, 4, v_diag_5859_);
v___x_5865_ = v_reuseFailAlloc_5869_;
goto v_reusejp_5864_;
}
v_reusejp_5864_:
{
lean_object* v___x_5866_; lean_object* v___x_5867_; lean_object* v___x_5868_; 
v___x_5866_ = lean_st_ref_set(v___y_5837_, v___x_5865_);
v___x_5867_ = lean_box(0);
v___x_5868_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_5868_, 0, v___x_5867_);
return v___x_5868_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg___boxed(lean_object* v_env_5876_, lean_object* v___y_5877_, lean_object* v___y_5878_, lean_object* v___y_5879_){
_start:
{
lean_object* v_res_5880_; 
v_res_5880_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5876_, v___y_5877_, v___y_5878_);
lean_dec(v___y_5878_);
lean_dec(v___y_5877_);
return v_res_5880_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(lean_object* v_env_5881_, lean_object* v___y_5882_, lean_object* v___y_5883_, lean_object* v___y_5884_, lean_object* v___y_5885_){
_start:
{
lean_object* v___x_5887_; 
v___x_5887_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v_env_5881_, v___y_5883_, v___y_5885_);
return v___x_5887_;
}
}
LEAN_EXPORT lean_object* l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___boxed(lean_object* v_env_5888_, lean_object* v___y_5889_, lean_object* v___y_5890_, lean_object* v___y_5891_, lean_object* v___y_5892_, lean_object* v___y_5893_){
_start:
{
lean_object* v_res_5894_; 
v_res_5894_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0(v_env_5888_, v___y_5889_, v___y_5890_, v___y_5891_, v___y_5892_);
lean_dec(v___y_5892_);
lean_dec_ref(v___y_5891_);
lean_dec(v___y_5890_);
lean_dec_ref(v___y_5889_);
return v_res_5894_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1(void){
_start:
{
lean_object* v___x_5896_; lean_object* v___x_5897_; 
v___x_5896_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__0));
v___x_5897_ = l_Lean_stringToMessageData(v___x_5896_);
return v___x_5897_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3(void){
_start:
{
lean_object* v___x_5899_; lean_object* v___x_5900_; 
v___x_5899_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__2));
v___x_5900_ = l_Lean_stringToMessageData(v___x_5899_);
return v___x_5900_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5(void){
_start:
{
lean_object* v___x_5902_; lean_object* v___x_5903_; 
v___x_5902_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__4));
v___x_5903_ = l_Lean_stringToMessageData(v___x_5902_);
return v___x_5903_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7(void){
_start:
{
lean_object* v___x_5905_; lean_object* v___x_5906_; 
v___x_5905_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__6));
v___x_5906_ = l_Lean_stringToMessageData(v___x_5905_);
return v___x_5906_;
}
}
static lean_object* _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9(void){
_start:
{
lean_object* v___x_5908_; lean_object* v___x_5909_; 
v___x_5908_ = ((lean_object*)(l_Lean_Meta_addDefaultInstance___lam__0___closed__8));
v___x_5909_ = l_Lean_stringToMessageData(v___x_5908_);
return v___x_5909_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0(lean_object* v_declName_5910_, lean_object* v_prio_5911_, lean_object* v_x_5912_, lean_object* v_type_5913_, lean_object* v___y_5914_, lean_object* v___y_5915_, lean_object* v___y_5916_, lean_object* v___y_5917_){
_start:
{
lean_object* v___x_5919_; 
v___x_5919_ = l_Lean_Expr_getAppFn(v_type_5913_);
if (lean_obj_tag(v___x_5919_) == 4)
{
lean_object* v_declName_5920_; lean_object* v___y_5922_; lean_object* v___y_5923_; lean_object* v___y_5924_; lean_object* v___y_5925_; lean_object* v___x_5935_; lean_object* v_env_5936_; uint8_t v___x_5937_; 
v_declName_5920_ = lean_ctor_get(v___x_5919_, 0);
lean_inc(v_declName_5920_);
lean_dec_ref_known(v___x_5919_, 2);
v___x_5935_ = lean_st_ref_get(v___y_5917_);
v_env_5936_ = lean_ctor_get(v___x_5935_, 0);
lean_inc_ref(v_env_5936_);
lean_dec(v___x_5935_);
v___x_5937_ = l_Lean_isClass(v_env_5936_, v_declName_5920_);
if (v___x_5937_ == 0)
{
lean_object* v___x_5938_; lean_object* v___x_5939_; lean_object* v___x_5940_; lean_object* v___x_5941_; lean_object* v___x_5942_; lean_object* v___x_5943_; lean_object* v___x_5944_; lean_object* v___x_5945_; lean_object* v___x_5946_; lean_object* v___x_5947_; lean_object* v___x_5948_; lean_object* v___x_5949_; lean_object* v___x_5950_; lean_object* v___x_5951_; 
lean_dec(v_prio_5911_);
v___x_5938_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5939_ = l_Lean_MessageData_ofConstName(v_declName_5910_, v___x_5937_);
v___x_5940_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5940_, 0, v___x_5938_);
lean_ctor_set(v___x_5940_, 1, v___x_5939_);
v___x_5941_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__3, &l_Lean_Meta_addDefaultInstance___lam__0___closed__3_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__3);
v___x_5942_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5942_, 0, v___x_5940_);
lean_ctor_set(v___x_5942_, 1, v___x_5941_);
lean_inc(v_declName_5920_);
v___x_5943_ = l_Lean_MessageData_ofName(v_declName_5920_);
v___x_5944_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5944_, 0, v___x_5942_);
lean_ctor_set(v___x_5944_, 1, v___x_5943_);
v___x_5945_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__5, &l_Lean_Meta_addDefaultInstance___lam__0___closed__5_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__5);
v___x_5946_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5946_, 0, v___x_5944_);
lean_ctor_set(v___x_5946_, 1, v___x_5945_);
v___x_5947_ = l_Lean_MessageData_ofConstName(v_declName_5920_, v___x_5937_);
v___x_5948_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5948_, 0, v___x_5946_);
lean_ctor_set(v___x_5948_, 1, v___x_5947_);
v___x_5949_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__7, &l_Lean_Meta_addDefaultInstance___lam__0___closed__7_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__7);
v___x_5950_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5950_, 0, v___x_5948_);
lean_ctor_set(v___x_5950_, 1, v___x_5949_);
v___x_5951_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5950_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_);
return v___x_5951_;
}
else
{
v___y_5922_ = v___y_5914_;
v___y_5923_ = v___y_5915_;
v___y_5924_ = v___y_5916_;
v___y_5925_ = v___y_5917_;
goto v___jp_5921_;
}
v___jp_5921_:
{
lean_object* v___x_5926_; lean_object* v_env_5927_; lean_object* v___x_5928_; lean_object* v_toEnvExtension_5929_; lean_object* v_asyncMode_5930_; lean_object* v___x_5931_; lean_object* v___x_5932_; lean_object* v___x_5933_; lean_object* v___x_5934_; 
v___x_5926_ = lean_st_ref_get(v___y_5925_);
v_env_5927_ = lean_ctor_get(v___x_5926_, 0);
lean_inc_ref(v_env_5927_);
lean_dec(v___x_5926_);
v___x_5928_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_5929_ = lean_ctor_get(v___x_5928_, 0);
v_asyncMode_5930_ = lean_ctor_get(v_toEnvExtension_5929_, 2);
v___x_5931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_5931_, 0, v_declName_5920_);
lean_ctor_set(v___x_5931_, 1, v_declName_5910_);
lean_ctor_set(v___x_5931_, 2, v_prio_5911_);
v___x_5932_ = lean_box(0);
v___x_5933_ = l_Lean_PersistentEnvExtension_addEntry___redArg(v___x_5928_, v_env_5927_, v___x_5931_, v_asyncMode_5930_, v___x_5932_);
v___x_5934_ = l_Lean_setEnv___at___00Lean_Meta_addDefaultInstance_spec__0___redArg(v___x_5933_, v___y_5923_, v___y_5925_);
return v___x_5934_;
}
}
else
{
lean_object* v___x_5952_; uint8_t v___x_5953_; lean_object* v___x_5954_; lean_object* v___x_5955_; lean_object* v___x_5956_; lean_object* v___x_5957_; lean_object* v___x_5958_; 
lean_dec_ref(v___x_5919_);
lean_dec(v_prio_5911_);
v___x_5952_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__1, &l_Lean_Meta_addDefaultInstance___lam__0___closed__1_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__1);
v___x_5953_ = 0;
v___x_5954_ = l_Lean_MessageData_ofConstName(v_declName_5910_, v___x_5953_);
v___x_5955_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5955_, 0, v___x_5952_);
lean_ctor_set(v___x_5955_, 1, v___x_5954_);
v___x_5956_ = lean_obj_once(&l_Lean_Meta_addDefaultInstance___lam__0___closed__9, &l_Lean_Meta_addDefaultInstance___lam__0___closed__9_once, _init_l_Lean_Meta_addDefaultInstance___lam__0___closed__9);
v___x_5957_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5957_, 0, v___x_5955_);
lean_ctor_set(v___x_5957_, 1, v___x_5956_);
v___x_5958_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5957_, v___y_5914_, v___y_5915_, v___y_5916_, v___y_5917_);
return v___x_5958_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___lam__0___boxed(lean_object* v_declName_5959_, lean_object* v_prio_5960_, lean_object* v_x_5961_, lean_object* v_type_5962_, lean_object* v___y_5963_, lean_object* v___y_5964_, lean_object* v___y_5965_, lean_object* v___y_5966_, lean_object* v___y_5967_){
_start:
{
lean_object* v_res_5968_; 
v_res_5968_ = l_Lean_Meta_addDefaultInstance___lam__0(v_declName_5959_, v_prio_5960_, v_x_5961_, v_type_5962_, v___y_5963_, v___y_5964_, v___y_5965_, v___y_5966_);
lean_dec(v___y_5966_);
lean_dec_ref(v___y_5965_);
lean_dec(v___y_5964_);
lean_dec_ref(v___y_5963_);
lean_dec_ref(v_type_5962_);
lean_dec_ref(v_x_5961_);
return v_res_5968_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance(lean_object* v_declName_5969_, lean_object* v_prio_5970_, lean_object* v_a_5971_, lean_object* v_a_5972_, lean_object* v_a_5973_, lean_object* v_a_5974_){
_start:
{
lean_object* v___x_5976_; lean_object* v_env_5977_; uint8_t v___x_5978_; lean_object* v___x_5979_; 
v___x_5976_ = lean_st_ref_get(v_a_5974_);
v_env_5977_ = lean_ctor_get(v___x_5976_, 0);
lean_inc_ref(v_env_5977_);
lean_dec(v___x_5976_);
v___x_5978_ = 0;
lean_inc(v_declName_5969_);
v___x_5979_ = l_Lean_Environment_find_x3f(v_env_5977_, v_declName_5969_, v___x_5978_);
if (lean_obj_tag(v___x_5979_) == 0)
{
lean_object* v___x_5980_; lean_object* v___x_5981_; lean_object* v___x_5982_; lean_object* v___x_5983_; lean_object* v___x_5984_; lean_object* v___x_5985_; 
lean_dec(v_prio_5970_);
v___x_5980_ = lean_obj_once(&l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1, &l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1_once, _init_l_Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7___redArg___closed__1);
v___x_5981_ = l_Lean_MessageData_ofConstName(v_declName_5969_, v___x_5978_);
v___x_5982_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5982_, 0, v___x_5980_);
lean_ctor_set(v___x_5982_, 1, v___x_5981_);
v___x_5983_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_5984_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_5984_, 0, v___x_5982_);
lean_ctor_set(v___x_5984_, 1, v___x_5983_);
v___x_5985_ = l_Lean_throwError___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_spec__6___redArg(v___x_5984_, v_a_5971_, v_a_5972_, v_a_5973_, v_a_5974_);
return v___x_5985_;
}
else
{
lean_object* v_val_5986_; lean_object* v___f_5987_; lean_object* v___x_5988_; lean_object* v___x_5989_; 
v_val_5986_ = lean_ctor_get(v___x_5979_, 0);
lean_inc(v_val_5986_);
lean_dec_ref_known(v___x_5979_, 1);
v___f_5987_ = lean_alloc_closure((void*)(l_Lean_Meta_addDefaultInstance___lam__0___boxed), 9, 2);
lean_closure_set(v___f_5987_, 0, v_declName_5969_);
lean_closure_set(v___f_5987_, 1, v_prio_5970_);
v___x_5988_ = l_Lean_ConstantInfo_type(v_val_5986_);
lean_dec(v_val_5986_);
v___x_5989_ = l_Lean_Meta_forallTelescopeReducing___at___00__private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder_getSemiOutParamPositionsOf_spec__1___redArg(v___x_5988_, v___f_5987_, v___x_5978_, v___x_5978_, v_a_5971_, v_a_5972_, v_a_5973_, v_a_5974_);
return v___x_5989_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_addDefaultInstance___boxed(lean_object* v_declName_5990_, lean_object* v_prio_5991_, lean_object* v_a_5992_, lean_object* v_a_5993_, lean_object* v_a_5994_, lean_object* v_a_5995_, lean_object* v_a_5996_){
_start:
{
lean_object* v_res_5997_; 
v_res_5997_ = l_Lean_Meta_addDefaultInstance(v_declName_5990_, v_prio_5991_, v_a_5992_, v_a_5993_, v_a_5994_, v_a_5995_);
lean_dec(v_a_5995_);
lean_dec_ref(v_a_5994_);
lean_dec(v_a_5993_);
lean_dec_ref(v_a_5992_);
return v_res_5997_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1(void){
_start:
{
lean_object* v___x_5999_; lean_object* v___x_6000_; 
v___x_5999_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__0));
v___x_6000_ = l_Lean_stringToMessageData(v___x_5999_);
return v___x_6000_;
}
}
static lean_object* _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3(void){
_start:
{
lean_object* v___x_6002_; lean_object* v___x_6003_; 
v___x_6002_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__2));
v___x_6003_ = l_Lean_stringToMessageData(v___x_6002_);
return v___x_6003_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(lean_object* v_name_6007_, uint8_t v_kind_6008_, lean_object* v___y_6009_, lean_object* v___y_6010_){
_start:
{
lean_object* v___x_6012_; lean_object* v___x_6013_; lean_object* v___x_6014_; lean_object* v___x_6015_; lean_object* v___x_6016_; lean_object* v___y_6018_; 
v___x_6012_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__1);
v___x_6013_ = l_Lean_MessageData_ofName(v_name_6007_);
v___x_6014_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6014_, 0, v___x_6012_);
lean_ctor_set(v___x_6014_, 1, v___x_6013_);
v___x_6015_ = lean_obj_once(&l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3, &l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3_once, _init_l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__3);
v___x_6016_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6016_, 0, v___x_6014_);
lean_ctor_set(v___x_6016_, 1, v___x_6015_);
switch(v_kind_6008_)
{
case 0:
{
lean_object* v___x_6025_; 
v___x_6025_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__4));
v___y_6018_ = v___x_6025_;
goto v___jp_6017_;
}
case 1:
{
lean_object* v___x_6026_; 
v___x_6026_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__5));
v___y_6018_ = v___x_6026_;
goto v___jp_6017_;
}
default: 
{
lean_object* v___x_6027_; 
v___x_6027_ = ((lean_object*)(l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___closed__6));
v___y_6018_ = v___x_6027_;
goto v___jp_6017_;
}
}
v___jp_6017_:
{
lean_object* v___x_6019_; lean_object* v___x_6020_; lean_object* v___x_6021_; lean_object* v___x_6022_; lean_object* v___x_6023_; lean_object* v___x_6024_; 
lean_inc_ref(v___y_6018_);
v___x_6019_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_6019_, 0, v___y_6018_);
v___x_6020_ = l_Lean_MessageData_ofFormat(v___x_6019_);
v___x_6021_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6021_, 0, v___x_6016_);
lean_ctor_set(v___x_6021_, 1, v___x_6020_);
v___x_6022_ = lean_obj_once(&l_Lean_Meta_Instances_erase___redArg___closed__3, &l_Lean_Meta_Instances_erase___redArg___closed__3_once, _init_l_Lean_Meta_Instances_erase___redArg___closed__3);
v___x_6023_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6023_, 0, v___x_6021_);
lean_ctor_set(v___x_6023_, 1, v___x_6022_);
v___x_6024_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6023_, v___y_6009_, v___y_6010_);
return v___x_6024_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_name_6028_, lean_object* v_kind_6029_, lean_object* v___y_6030_, lean_object* v___y_6031_, lean_object* v___y_6032_){
_start:
{
uint8_t v_kind_boxed_6033_; lean_object* v_res_6034_; 
v_kind_boxed_6033_ = lean_unbox(v_kind_6029_);
v_res_6034_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6028_, v_kind_boxed_6033_, v___y_6030_, v___y_6031_);
lean_dec(v___y_6031_);
lean_dec_ref(v___y_6030_);
return v_res_6034_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6035_, lean_object* v___x_6036_, lean_object* v___x_6037_, lean_object* v_declName_6038_, lean_object* v_stx_6039_, uint8_t v_kind_6040_, lean_object* v___y_6041_, lean_object* v___y_6042_){
_start:
{
lean_object* v___x_6044_; lean_object* v___x_6045_; lean_object* v___x_6046_; 
v___x_6044_ = lean_unsigned_to_nat(1u);
v___x_6045_ = l_Lean_Syntax_getArg(v_stx_6039_, v___x_6044_);
v___x_6046_ = l_Lean_getAttrParamOptPrio(v___x_6045_, v___y_6041_, v___y_6042_);
if (lean_obj_tag(v___x_6046_) == 0)
{
lean_object* v_a_6047_; lean_object* v___y_6049_; lean_object* v___y_6050_; uint8_t v___x_6081_; uint8_t v___x_6082_; 
v_a_6047_ = lean_ctor_get(v___x_6046_, 0);
lean_inc(v_a_6047_);
lean_dec_ref_known(v___x_6046_, 1);
v___x_6081_ = 0;
v___x_6082_ = l_Lean_instBEqAttributeKind_beq(v_kind_6040_, v___x_6081_);
if (v___x_6082_ == 0)
{
lean_object* v___x_6083_; 
lean_dec(v_a_6047_);
lean_dec(v_declName_6038_);
lean_dec(v___x_6036_);
lean_dec(v___x_6035_);
v___x_6083_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v___x_6037_, v_kind_6040_, v___y_6041_, v___y_6042_);
return v___x_6083_;
}
else
{
lean_dec(v___x_6037_);
v___y_6049_ = v___y_6041_;
v___y_6050_ = v___y_6042_;
goto v___jp_6048_;
}
v___jp_6048_:
{
uint8_t v___x_6051_; uint8_t v___x_6052_; lean_object* v___x_6053_; lean_object* v___x_6054_; lean_object* v___x_6055_; lean_object* v___x_6056_; lean_object* v___x_6057_; size_t v___x_6058_; lean_object* v___x_6059_; lean_object* v___x_6060_; lean_object* v___x_6061_; lean_object* v___x_6062_; lean_object* v___x_6063_; lean_object* v___x_6064_; lean_object* v___x_6065_; lean_object* v___x_6066_; lean_object* v___x_6067_; lean_object* v___x_6068_; lean_object* v___x_6069_; lean_object* v___x_6070_; 
v___x_6051_ = 0;
v___x_6052_ = 1;
v___x_6053_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__2_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6054_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__4_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6055_ = lean_unsigned_to_nat(32u);
v___x_6056_ = lean_mk_empty_array_with_capacity(v___x_6055_);
v___x_6057_ = lean_obj_once(&l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3, &l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3_once, _init_l_Lean_mkUnknownIdentifierMessageCore___at___00Lean_mkUnknownIdentifierMessage___at___00Lean_throwUnknownIdentifierAt___at___00Lean_throwUnknownConstantAt___at___00Lean_throwUnknownConstant___at___00Lean_getConstInfo___at___00Lean_Meta_addInstance_spec__4_spec__6_spec__7_spec__8_spec__9_spec__10___redArg___closed__3);
v___x_6058_ = ((size_t)5ULL);
lean_inc_n(v___x_6035_, 6);
v___x_6059_ = lean_alloc_ctor(0, 4, sizeof(size_t)*1);
lean_ctor_set(v___x_6059_, 0, v___x_6057_);
lean_ctor_set(v___x_6059_, 1, v___x_6056_);
lean_ctor_set(v___x_6059_, 2, v___x_6035_);
lean_ctor_set(v___x_6059_, 3, v___x_6035_);
lean_ctor_set_usize(v___x_6059_, 4, v___x_6058_);
v___x_6060_ = lean_box(1);
lean_inc_ref(v___x_6059_);
v___x_6061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_6061_, 0, v___x_6054_);
lean_ctor_set(v___x_6061_, 1, v___x_6059_);
lean_ctor_set(v___x_6061_, 2, v___x_6060_);
v___x_6062_ = lean_mk_empty_array_with_capacity(v___x_6035_);
v___x_6063_ = lean_box(0);
lean_inc(v___x_6036_);
v___x_6064_ = lean_alloc_ctor(0, 7, 4);
lean_ctor_set(v___x_6064_, 0, v___x_6053_);
lean_ctor_set(v___x_6064_, 1, v___x_6036_);
lean_ctor_set(v___x_6064_, 2, v___x_6061_);
lean_ctor_set(v___x_6064_, 3, v___x_6062_);
lean_ctor_set(v___x_6064_, 4, v___x_6063_);
lean_ctor_set(v___x_6064_, 5, v___x_6035_);
lean_ctor_set(v___x_6064_, 6, v___x_6063_);
lean_ctor_set_uint8(v___x_6064_, sizeof(void*)*7, v___x_6051_);
lean_ctor_set_uint8(v___x_6064_, sizeof(void*)*7 + 1, v___x_6051_);
lean_ctor_set_uint8(v___x_6064_, sizeof(void*)*7 + 2, v___x_6051_);
lean_ctor_set_uint8(v___x_6064_, sizeof(void*)*7 + 3, v___x_6052_);
v___x_6065_ = lean_alloc_ctor(0, 10, 0);
lean_ctor_set(v___x_6065_, 0, v___x_6035_);
lean_ctor_set(v___x_6065_, 1, v___x_6035_);
lean_ctor_set(v___x_6065_, 2, v___x_6035_);
lean_ctor_set(v___x_6065_, 3, v___x_6035_);
lean_ctor_set(v___x_6065_, 4, v___x_6054_);
lean_ctor_set(v___x_6065_, 5, v___x_6054_);
lean_ctor_set(v___x_6065_, 6, v___x_6054_);
lean_ctor_set(v___x_6065_, 7, v___x_6054_);
lean_ctor_set(v___x_6065_, 8, v___x_6054_);
lean_ctor_set(v___x_6065_, 9, v___x_6054_);
v___x_6066_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__5_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6067_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__2___closed__6_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2_);
v___x_6068_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_6068_, 0, v___x_6065_);
lean_ctor_set(v___x_6068_, 1, v___x_6066_);
lean_ctor_set(v___x_6068_, 2, v___x_6036_);
lean_ctor_set(v___x_6068_, 3, v___x_6059_);
lean_ctor_set(v___x_6068_, 4, v___x_6067_);
v___x_6069_ = lean_st_mk_ref(v___x_6068_);
v___x_6070_ = l_Lean_Meta_addDefaultInstance(v_declName_6038_, v_a_6047_, v___x_6064_, v___x_6069_, v___y_6049_, v___y_6050_);
lean_dec_ref_known(v___x_6064_, 7);
if (lean_obj_tag(v___x_6070_) == 0)
{
lean_object* v___x_6072_; uint8_t v_isShared_6073_; uint8_t v_isSharedCheck_6079_; 
v_isSharedCheck_6079_ = !lean_is_exclusive(v___x_6070_);
if (v_isSharedCheck_6079_ == 0)
{
lean_object* v_unused_6080_; 
v_unused_6080_ = lean_ctor_get(v___x_6070_, 0);
lean_dec(v_unused_6080_);
v___x_6072_ = v___x_6070_;
v_isShared_6073_ = v_isSharedCheck_6079_;
goto v_resetjp_6071_;
}
else
{
lean_dec(v___x_6070_);
v___x_6072_ = lean_box(0);
v_isShared_6073_ = v_isSharedCheck_6079_;
goto v_resetjp_6071_;
}
v_resetjp_6071_:
{
lean_object* v___x_6074_; lean_object* v___x_6075_; lean_object* v___x_6077_; 
v___x_6074_ = lean_st_ref_get(v___x_6069_);
lean_dec(v___x_6069_);
lean_dec(v___x_6074_);
v___x_6075_ = lean_box(0);
if (v_isShared_6073_ == 0)
{
lean_ctor_set(v___x_6072_, 0, v___x_6075_);
v___x_6077_ = v___x_6072_;
goto v_reusejp_6076_;
}
else
{
lean_object* v_reuseFailAlloc_6078_; 
v_reuseFailAlloc_6078_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6078_, 0, v___x_6075_);
v___x_6077_ = v_reuseFailAlloc_6078_;
goto v_reusejp_6076_;
}
v_reusejp_6076_:
{
return v___x_6077_;
}
}
}
else
{
lean_dec(v___x_6069_);
return v___x_6070_;
}
}
}
else
{
lean_object* v_a_6084_; lean_object* v___x_6086_; uint8_t v_isShared_6087_; uint8_t v_isSharedCheck_6091_; 
lean_dec(v_declName_6038_);
lean_dec(v___x_6037_);
lean_dec(v___x_6036_);
lean_dec(v___x_6035_);
v_a_6084_ = lean_ctor_get(v___x_6046_, 0);
v_isSharedCheck_6091_ = !lean_is_exclusive(v___x_6046_);
if (v_isSharedCheck_6091_ == 0)
{
v___x_6086_ = v___x_6046_;
v_isShared_6087_ = v_isSharedCheck_6091_;
goto v_resetjp_6085_;
}
else
{
lean_inc(v_a_6084_);
lean_dec(v___x_6046_);
v___x_6086_ = lean_box(0);
v_isShared_6087_ = v_isSharedCheck_6091_;
goto v_resetjp_6085_;
}
v_resetjp_6085_:
{
lean_object* v___x_6089_; 
if (v_isShared_6087_ == 0)
{
v___x_6089_ = v___x_6086_;
goto v_reusejp_6088_;
}
else
{
lean_object* v_reuseFailAlloc_6090_; 
v_reuseFailAlloc_6090_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_6090_, 0, v_a_6084_);
v___x_6089_ = v_reuseFailAlloc_6090_;
goto v_reusejp_6088_;
}
v_reusejp_6088_:
{
return v___x_6089_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6092_, lean_object* v___x_6093_, lean_object* v___x_6094_, lean_object* v_declName_6095_, lean_object* v_stx_6096_, lean_object* v_kind_6097_, lean_object* v___y_6098_, lean_object* v___y_6099_, lean_object* v___y_6100_){
_start:
{
uint8_t v_kind_boxed_6101_; lean_object* v_res_6102_; 
v_kind_boxed_6101_ = lean_unbox(v_kind_6097_);
v_res_6102_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6092_, v___x_6093_, v___x_6094_, v_declName_6095_, v_stx_6096_, v_kind_boxed_6101_, v___y_6098_, v___y_6099_);
lean_dec(v___y_6099_);
lean_dec_ref(v___y_6098_);
lean_dec(v_stx_6096_);
return v_res_6102_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6104_; lean_object* v___x_6105_; 
v___x_6104_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__0_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6105_ = l_Lean_stringToMessageData(v___x_6104_);
return v___x_6105_;
}
}
static lean_object* _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_6107_; lean_object* v___x_6108_; 
v___x_6107_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__2_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6108_ = l_Lean_stringToMessageData(v___x_6107_);
return v___x_6108_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(lean_object* v___x_6109_, lean_object* v_decl_6110_, lean_object* v___y_6111_, lean_object* v___y_6112_){
_start:
{
lean_object* v___x_6114_; lean_object* v___x_6115_; lean_object* v___x_6116_; lean_object* v___x_6117_; lean_object* v___x_6118_; lean_object* v___x_6119_; 
v___x_6114_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6115_ = l_Lean_MessageData_ofName(v___x_6109_);
v___x_6116_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6116_, 0, v___x_6114_);
lean_ctor_set(v___x_6116_, 1, v___x_6115_);
v___x_6117_ = lean_obj_once(&l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_, &l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_);
v___x_6118_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_6118_, 0, v___x_6116_);
lean_ctor_set(v___x_6118_, 1, v___x_6117_);
v___x_6119_ = l_Lean_throwError___at___00Lean_Meta_Instances_erase___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_1841422150____hygCtx___hyg_2__spec__0_spec__1___redArg(v___x_6118_, v___y_6111_, v___y_6112_);
return v___x_6119_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v___x_6120_, lean_object* v_decl_6121_, lean_object* v___y_6122_, lean_object* v___y_6123_, lean_object* v___y_6124_){
_start:
{
lean_object* v_res_6125_; 
v_res_6125_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___lam__1_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(v___x_6120_, v_decl_6121_, v___y_6122_, v___y_6123_);
lean_dec(v___y_6123_);
lean_dec_ref(v___y_6122_);
lean_dec(v_decl_6121_);
return v_res_6125_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_6158_; lean_object* v___x_6159_; lean_object* v___x_6160_; 
v___x_6158_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__3_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6159_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_initFn___closed__10_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_));
v___x_6160_ = l_Lean_registerBuiltinAttribute(v___x_6159_);
if (lean_obj_tag(v___x_6160_) == 0)
{
lean_object* v___x_6161_; uint8_t v___x_6162_; lean_object* v___x_6163_; 
lean_dec_ref_known(v___x_6160_, 1);
v___x_6161_ = ((lean_object*)(l___private_Lean_Meta_Instances_0__Lean_Meta_computeSynthOrder___lam__0___closed__1));
v___x_6162_ = 0;
v___x_6163_ = l_Lean_registerTraceClass(v___x_6161_, v___x_6162_, v___x_6158_);
return v___x_6163_;
}
else
{
return v___x_6160_;
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2____boxed(lean_object* v_a_6164_){
_start:
{
lean_object* v_res_6165_; 
v_res_6165_ = l___private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2_();
return v_res_6165_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_6166_, lean_object* v_name_6167_, uint8_t v_kind_6168_, lean_object* v___y_6169_, lean_object* v___y_6170_){
_start:
{
lean_object* v___x_6172_; 
v___x_6172_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___redArg(v_name_6167_, v_kind_6168_, v___y_6169_, v___y_6170_);
return v___x_6172_;
}
}
LEAN_EXPORT lean_object* l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_6173_, lean_object* v_name_6174_, lean_object* v_kind_6175_, lean_object* v___y_6176_, lean_object* v___y_6177_, lean_object* v___y_6178_){
_start:
{
uint8_t v_kind_boxed_6179_; lean_object* v_res_6180_; 
v_kind_boxed_6179_ = lean_unbox(v_kind_6175_);
v_res_6180_ = l_Lean_throwAttrMustBeGlobal___at___00__private_Lean_Meta_Instances_0__Lean_Meta_initFn_00___x40_Lean_Meta_Instances_397728026____hygCtx___hyg_2__spec__0(v_00_u03b1_6173_, v_name_6174_, v_kind_boxed_6179_, v___y_6176_, v___y_6177_);
lean_dec(v___y_6177_);
lean_dec_ref(v___y_6176_);
return v_res_6180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0(lean_object* v___x_6181_, lean_object* v_toPure_6182_, lean_object* v_____do__lift_6183_){
_start:
{
lean_object* v___x_6184_; lean_object* v_toEnvExtension_6185_; lean_object* v_asyncMode_6186_; lean_object* v___x_6187_; lean_object* v___x_6188_; lean_object* v_priorities_6189_; lean_object* v___x_6190_; 
v___x_6184_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6185_ = lean_ctor_get(v___x_6184_, 0);
v_asyncMode_6186_ = lean_ctor_get(v_toEnvExtension_6185_, 2);
v___x_6187_ = lean_box(0);
v___x_6188_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6181_, v___x_6184_, v_____do__lift_6183_, v_asyncMode_6186_, v___x_6187_);
v_priorities_6189_ = lean_ctor_get(v___x_6188_, 1);
lean_inc(v_priorities_6189_);
lean_dec(v___x_6188_);
v___x_6190_ = lean_apply_2(v_toPure_6182_, lean_box(0), v_priorities_6189_);
return v___x_6190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities___redArg(lean_object* v_inst_6191_, lean_object* v_inst_6192_){
_start:
{
lean_object* v_toApplicative_6193_; lean_object* v_toBind_6194_; lean_object* v_getEnv_6195_; lean_object* v_toPure_6196_; lean_object* v___x_6197_; lean_object* v___f_6198_; lean_object* v___x_6199_; 
v_toApplicative_6193_ = lean_ctor_get(v_inst_6191_, 0);
lean_inc_ref(v_toApplicative_6193_);
v_toBind_6194_ = lean_ctor_get(v_inst_6191_, 1);
lean_inc(v_toBind_6194_);
lean_dec_ref(v_inst_6191_);
v_getEnv_6195_ = lean_ctor_get(v_inst_6192_, 0);
lean_inc(v_getEnv_6195_);
lean_dec_ref(v_inst_6192_);
v_toPure_6196_ = lean_ctor_get(v_toApplicative_6193_, 1);
lean_inc(v_toPure_6196_);
lean_dec_ref(v_toApplicative_6193_);
v___x_6197_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6198_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstancesPriorities___redArg___lam__0), 3, 2);
lean_closure_set(v___f_6198_, 0, v___x_6197_);
lean_closure_set(v___f_6198_, 1, v_toPure_6196_);
v___x_6199_ = lean_apply_4(v_toBind_6194_, lean_box(0), lean_box(0), v_getEnv_6195_, v___f_6198_);
return v___x_6199_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstancesPriorities(lean_object* v_m_6200_, lean_object* v_inst_6201_, lean_object* v_inst_6202_){
_start:
{
lean_object* v___x_6203_; 
v___x_6203_ = l_Lean_Meta_getDefaultInstancesPriorities___redArg(v_inst_6201_, v_inst_6202_);
return v___x_6203_;
}
}
LEAN_EXPORT uint8_t l_Lean_Meta_getDefaultInstances___redArg___lam__0(lean_object* v_env_6204_, uint8_t v_isExporting_6205_, lean_object* v_x_6206_){
_start:
{
lean_object* v_fst_6207_; uint8_t v___x_6208_; 
v_fst_6207_ = lean_ctor_get(v_x_6206_, 0);
lean_inc(v_fst_6207_);
lean_dec_ref(v_x_6206_);
v___x_6208_ = l_Lean_Environment_contains(v_env_6204_, v_fst_6207_, v_isExporting_6205_);
return v___x_6208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed(lean_object* v_env_6209_, lean_object* v_isExporting_6210_, lean_object* v_x_6211_){
_start:
{
uint8_t v_isExporting_boxed_6212_; uint8_t v_res_6213_; lean_object* v_r_6214_; 
v_isExporting_boxed_6212_ = lean_unbox(v_isExporting_6210_);
v_res_6213_ = l_Lean_Meta_getDefaultInstances___redArg___lam__0(v_env_6209_, v_isExporting_boxed_6212_, v_x_6211_);
v_r_6214_ = lean_box(v_res_6213_);
return v_r_6214_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1(lean_object* v___x_6215_, lean_object* v_toApplicative_6216_, lean_object* v_className_6217_, lean_object* v_env_6218_){
_start:
{
lean_object* v___y_6220_; lean_object* v___x_6230_; lean_object* v_toEnvExtension_6231_; lean_object* v_asyncMode_6232_; lean_object* v___x_6233_; lean_object* v___x_6234_; lean_object* v_defaultInstances_6235_; lean_object* v___x_6236_; 
v___x_6230_ = l_Lean_Meta_defaultInstanceExtension;
v_toEnvExtension_6231_ = lean_ctor_get(v___x_6230_, 0);
v_asyncMode_6232_ = lean_ctor_get(v_toEnvExtension_6231_, 2);
v___x_6233_ = lean_box(0);
lean_inc_ref(v_env_6218_);
v___x_6234_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_6215_, v___x_6230_, v_env_6218_, v_asyncMode_6232_, v___x_6233_);
v_defaultInstances_6235_ = lean_ctor_get(v___x_6234_, 0);
lean_inc(v_defaultInstances_6235_);
lean_dec(v___x_6234_);
v___x_6236_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_defaultInstances_6235_, v_className_6217_);
lean_dec(v_defaultInstances_6235_);
if (lean_obj_tag(v___x_6236_) == 0)
{
lean_object* v___x_6237_; 
v___x_6237_ = lean_box(0);
v___y_6220_ = v___x_6237_;
goto v___jp_6219_;
}
else
{
lean_object* v_val_6238_; 
v_val_6238_ = lean_ctor_get(v___x_6236_, 0);
lean_inc(v_val_6238_);
lean_dec_ref_known(v___x_6236_, 1);
v___y_6220_ = v_val_6238_;
goto v___jp_6219_;
}
v___jp_6219_:
{
uint8_t v_isExporting_6221_; 
v_isExporting_6221_ = lean_ctor_get_uint8(v_env_6218_, sizeof(void*)*8);
if (v_isExporting_6221_ == 0)
{
lean_object* v_toPure_6222_; lean_object* v___x_6223_; 
lean_dec_ref(v_env_6218_);
v_toPure_6222_ = lean_ctor_get(v_toApplicative_6216_, 1);
lean_inc(v_toPure_6222_);
lean_dec_ref(v_toApplicative_6216_);
v___x_6223_ = lean_apply_2(v_toPure_6222_, lean_box(0), v___y_6220_);
return v___x_6223_;
}
else
{
lean_object* v_toPure_6224_; lean_object* v___x_6225_; lean_object* v___f_6226_; lean_object* v___x_6227_; lean_object* v___x_6228_; lean_object* v___x_6229_; 
v_toPure_6224_ = lean_ctor_get(v_toApplicative_6216_, 1);
lean_inc(v_toPure_6224_);
lean_dec_ref(v_toApplicative_6216_);
v___x_6225_ = lean_box(v_isExporting_6221_);
v___f_6226_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_6226_, 0, v_env_6218_);
lean_closure_set(v___f_6226_, 1, v___x_6225_);
v___x_6227_ = lean_box(0);
v___x_6228_ = l_List_filterTR_loop___redArg(v___f_6226_, v___y_6220_, v___x_6227_);
v___x_6229_ = lean_apply_2(v_toPure_6224_, lean_box(0), v___x_6228_);
return v___x_6229_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed(lean_object* v___x_6239_, lean_object* v_toApplicative_6240_, lean_object* v_className_6241_, lean_object* v_env_6242_){
_start:
{
lean_object* v_res_6243_; 
v_res_6243_ = l_Lean_Meta_getDefaultInstances___redArg___lam__1(v___x_6239_, v_toApplicative_6240_, v_className_6241_, v_env_6242_);
lean_dec(v_className_6241_);
return v_res_6243_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances___redArg(lean_object* v_inst_6244_, lean_object* v_inst_6245_, lean_object* v_className_6246_){
_start:
{
lean_object* v_toApplicative_6247_; lean_object* v_toBind_6248_; lean_object* v_getEnv_6249_; lean_object* v___x_6250_; lean_object* v___f_6251_; lean_object* v___x_6252_; 
v_toApplicative_6247_ = lean_ctor_get(v_inst_6244_, 0);
lean_inc_ref(v_toApplicative_6247_);
v_toBind_6248_ = lean_ctor_get(v_inst_6244_, 1);
lean_inc(v_toBind_6248_);
lean_dec_ref(v_inst_6244_);
v_getEnv_6249_ = lean_ctor_get(v_inst_6245_, 0);
lean_inc(v_getEnv_6249_);
lean_dec_ref(v_inst_6245_);
v___x_6250_ = ((lean_object*)(l_Lean_Meta_instInhabitedDefaultInstances_default));
v___f_6251_ = lean_alloc_closure((void*)(l_Lean_Meta_getDefaultInstances___redArg___lam__1___boxed), 4, 3);
lean_closure_set(v___f_6251_, 0, v___x_6250_);
lean_closure_set(v___f_6251_, 1, v_toApplicative_6247_);
lean_closure_set(v___f_6251_, 2, v_className_6246_);
v___x_6252_ = lean_apply_4(v_toBind_6248_, lean_box(0), lean_box(0), v_getEnv_6249_, v___f_6251_);
return v___x_6252_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_getDefaultInstances(lean_object* v_m_6253_, lean_object* v_inst_6254_, lean_object* v_inst_6255_, lean_object* v_className_6256_){
_start:
{
lean_object* v___x_6257_; 
v___x_6257_ = l_Lean_Meta_getDefaultInstances___redArg(v_inst_6254_, v_inst_6255_, v_className_6256_);
return v___x_6257_;
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
